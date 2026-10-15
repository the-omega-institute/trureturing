/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover539
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_8_4454_1499849 : frontier 13 ⟨1499849, by decide⟩
    (prefixCache 8 4454) (prefixPartial 8 4454) = false := by
  decide +kernel

theorem node_context_8_4454_1499849 : EJMOriginalGlobalDAGData.nodes 13 ⟨1499849, by decide⟩ =
    .split (coordinate 8) (![⟨1499459, by decide⟩,⟨1499697, by decide⟩,⟨1499802, by decide⟩,⟨1499848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4454_1499849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4454 ⟨1499849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4454
    ⟨1499849, by decide⟩ (by decide) (![⟨1499459, by decide⟩,⟨1499697, by decide⟩,⟨1499802, by decide⟩,⟨1499848, by decide⟩]) unmarked_context_8_4454_1499849 node_context_8_4454_1499849
  intro a
  fin_cases a
  · exact context_9_17816_1499459
  · exact context_9_17817_1499697
  · exact context_9_17818_1499802
  · exact context_9_17819_1499848

theorem selected_cut_51843 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71280) = some ⟨10, 1, 0, 1468246, 71280, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71280_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71280 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71280 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71280, 1, 1048576⟩
    (by decide) selected_cut_51843

theorem selected_cut_51844 : selected 10 ⟨1499919, by decide⟩
    (prefixPartial 11 285124) = some ⟨11, 2, 0, 1499919, 285124, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_285124_1499919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285124 ⟨1499919, by decide⟩ :=
  accepted_of_selected 11 285124 ⟨1499919, by decide⟩ ⟨11, 2, 0, 1499919, 285124, 3337, 262144⟩
    (by decide) selected_cut_51844

theorem selected_cut_51845 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285125) = some ⟨11, 1, 0, 1468419, 285125, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285125_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285125 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285125 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285125, 1, 262144⟩
    (by decide) selected_cut_51845

theorem selected_cut_51846 : selected 10 ⟨1500002, by decide⟩
    (prefixPartial 11 285126) = some ⟨11, 2, 0, 1500002, 285126, 3349, 262144⟩ := by
  decide +kernel

theorem context_11_285126_1500002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285126 ⟨1500002, by decide⟩ :=
  accepted_of_selected 11 285126 ⟨1500002, by decide⟩ ⟨11, 2, 0, 1500002, 285126, 3349, 262144⟩
    (by decide) selected_cut_51846

theorem selected_cut_51847 : selected 10 ⟨1500033, by decide⟩
    (prefixPartial 11 285127) = some ⟨11, 2, 0, 1500033, 285127, 1441, 262144⟩ := by
  decide +kernel

theorem context_11_285127_1500033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285127 ⟨1500033, by decide⟩ :=
  accepted_of_selected 11 285127 ⟨1500033, by decide⟩ ⟨11, 2, 0, 1500033, 285127, 1441, 262144⟩
    (by decide) selected_cut_51847

theorem unmarked_context_10_71281_1500034 : frontier 11 ⟨1500034, by decide⟩
    (prefixCache 10 71281) (prefixPartial 10 71281) = false := by
  decide +kernel

theorem node_context_10_71281_1500034 : EJMOriginalGlobalDAGData.nodes 11 ⟨1500034, by decide⟩ =
    .split (coordinate 10) (![⟨1499919, by decide⟩,⟨1468419, by decide⟩,⟨1500002, by decide⟩,⟨1500033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71281_1500034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71281 ⟨1500034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71281
    ⟨1500034, by decide⟩ (by decide) (![⟨1499919, by decide⟩,⟨1468419, by decide⟩,⟨1500002, by decide⟩,⟨1500033, by decide⟩]) unmarked_context_10_71281_1500034 node_context_10_71281_1500034
  intro a
  fin_cases a
  · exact context_11_285124_1499919
  · exact context_11_285125_1468419
  · exact context_11_285126_1500002
  · exact context_11_285127_1500033

theorem selected_cut_51848 : selected 10 ⟨1500103, by decide⟩
    (prefixPartial 11 285128) = some ⟨11, 2, 0, 1500103, 285128, 4093, 262144⟩ := by
  decide +kernel

theorem context_11_285128_1500103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285128 ⟨1500103, by decide⟩ :=
  accepted_of_selected 11 285128 ⟨1500103, by decide⟩ ⟨11, 2, 0, 1500103, 285128, 4093, 262144⟩
    (by decide) selected_cut_51848

theorem selected_cut_51849 : selected 10 ⟨1500141, by decide⟩
    (prefixPartial 11 285129) = some ⟨11, 2, 0, 1500141, 285129, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_285129_1500141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285129 ⟨1500141, by decide⟩ :=
  accepted_of_selected 11 285129 ⟨1500141, by decide⟩ ⟨11, 2, 0, 1500141, 285129, 2237, 262144⟩
    (by decide) selected_cut_51849

theorem selected_cut_51850 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285130) = some ⟨11, 1, 0, 1468743, 285130, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285130_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285130 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285130 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285130, 1, 262144⟩
    (by decide) selected_cut_51850

theorem selected_cut_51851 : selected 10 ⟨1500176, by decide⟩
    (prefixPartial 11 285131) = some ⟨11, 2, 0, 1500176, 285131, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_285131_1500176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285131 ⟨1500176, by decide⟩ :=
  accepted_of_selected 11 285131 ⟨1500176, by decide⟩ ⟨11, 2, 0, 1500176, 285131, 2309, 262144⟩
    (by decide) selected_cut_51851

theorem unmarked_context_10_71282_1500177 : frontier 11 ⟨1500177, by decide⟩
    (prefixCache 10 71282) (prefixPartial 10 71282) = false := by
  decide +kernel

theorem node_context_10_71282_1500177 : EJMOriginalGlobalDAGData.nodes 11 ⟨1500177, by decide⟩ =
    .split (coordinate 10) (![⟨1500103, by decide⟩,⟨1500141, by decide⟩,⟨1468743, by decide⟩,⟨1500176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71282_1500177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71282 ⟨1500177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71282
    ⟨1500177, by decide⟩ (by decide) (![⟨1500103, by decide⟩,⟨1500141, by decide⟩,⟨1468743, by decide⟩,⟨1500176, by decide⟩]) unmarked_context_10_71282_1500177 node_context_10_71282_1500177
  intro a
  fin_cases a
  · exact context_11_285128_1500103
  · exact context_11_285129_1500141
  · exact context_11_285130_1468743
  · exact context_11_285131_1500176

theorem selected_cut_51852 : selected 10 ⟨1500256, by decide⟩
    (prefixPartial 11 285132) = some ⟨11, 2, 0, 1500256, 285132, 3929, 262144⟩ := by
  decide +kernel

theorem context_11_285132_1500256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285132 ⟨1500256, by decide⟩ :=
  accepted_of_selected 11 285132 ⟨1500256, by decide⟩ ⟨11, 2, 0, 1500256, 285132, 3929, 262144⟩
    (by decide) selected_cut_51852

theorem selected_cut_51853 : selected 10 ⟨1500294, by decide⟩
    (prefixPartial 11 285133) = some ⟨11, 2, 0, 1500294, 285133, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_285133_1500294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285133 ⟨1500294, by decide⟩ :=
  accepted_of_selected 11 285133 ⟨1500294, by decide⟩ ⟨11, 2, 0, 1500294, 285133, 2145, 262144⟩
    (by decide) selected_cut_51853

theorem selected_cut_51854 : selected 10 ⟨1500338, by decide⟩
    (prefixPartial 11 285134) = some ⟨11, 2, 0, 1500338, 285134, 2293, 262144⟩ := by
  decide +kernel

theorem context_11_285134_1500338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285134 ⟨1500338, by decide⟩ :=
  accepted_of_selected 11 285134 ⟨1500338, by decide⟩ ⟨11, 2, 0, 1500338, 285134, 2293, 262144⟩
    (by decide) selected_cut_51854

theorem selected_cut_51855 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285135) = some ⟨11, 1, 0, 1470044, 285135, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285135_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285135 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285135 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285135, 1, 262144⟩
    (by decide) selected_cut_51855

theorem unmarked_context_10_71283_1500339 : frontier 11 ⟨1500339, by decide⟩
    (prefixCache 10 71283) (prefixPartial 10 71283) = false := by
  decide +kernel

theorem node_context_10_71283_1500339 : EJMOriginalGlobalDAGData.nodes 11 ⟨1500339, by decide⟩ =
    .split (coordinate 10) (![⟨1500256, by decide⟩,⟨1500294, by decide⟩,⟨1500338, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71283_1500339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71283 ⟨1500339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71283
    ⟨1500339, by decide⟩ (by decide) (![⟨1500256, by decide⟩,⟨1500294, by decide⟩,⟨1500338, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71283_1500339 node_context_10_71283_1500339
  intro a
  fin_cases a
  · exact context_11_285132_1500256
  · exact context_11_285133_1500294
  · exact context_11_285134_1500338
  · exact context_11_285135_1470044

theorem unmarked_context_9_17820_1500340 : frontier 12 ⟨1500340, by decide⟩
    (prefixCache 9 17820) (prefixPartial 9 17820) = false := by
  decide +kernel

theorem node_context_9_17820_1500340 : EJMOriginalGlobalDAGData.nodes 12 ⟨1500340, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1500034, by decide⟩,⟨1500177, by decide⟩,⟨1500339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17820_1500340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17820 ⟨1500340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17820
    ⟨1500340, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1500034, by decide⟩,⟨1500177, by decide⟩,⟨1500339, by decide⟩]) unmarked_context_9_17820_1500340 node_context_9_17820_1500340
  intro a
  fin_cases a
  · exact context_10_71280_1468246
  · exact context_10_71281_1500034
  · exact context_10_71282_1500177
  · exact context_10_71283_1500339

theorem selected_cut_51856 : selected 11 ⟨1500411, by decide⟩
    (prefixPartial 10 71284) = some ⟨10, 2, 0, 1500411, 71284, 3245, 1048576⟩ := by
  decide +kernel

theorem context_10_71284_1500411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71284 ⟨1500411, by decide⟩ :=
  accepted_of_selected 10 71284 ⟨1500411, by decide⟩ ⟨10, 2, 0, 1500411, 71284, 3245, 1048576⟩
    (by decide) selected_cut_51856

theorem selected_cut_51857 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71285) = some ⟨10, 1, 0, 1468874, 71285, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71285_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71285 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71285 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71285, 1, 1048576⟩
    (by decide) selected_cut_51857

theorem selected_cut_51858 : selected 10 ⟨1500439, by decide⟩
    (prefixPartial 11 285144) = some ⟨11, 2, 0, 1500439, 285144, 1473, 262144⟩ := by
  decide +kernel

theorem context_11_285144_1500439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285144 ⟨1500439, by decide⟩ :=
  accepted_of_selected 11 285144 ⟨1500439, by decide⟩ ⟨11, 2, 0, 1500439, 285144, 1473, 262144⟩
    (by decide) selected_cut_51858

theorem selected_cut_51859 : selected 10 ⟨1500480, by decide⟩
    (prefixPartial 11 285145) = some ⟨11, 2, 0, 1500480, 285145, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_285145_1500480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285145 ⟨1500480, by decide⟩ :=
  accepted_of_selected 11 285145 ⟨1500480, by decide⟩ ⟨11, 2, 0, 1500480, 285145, 1521, 262144⟩
    (by decide) selected_cut_51859

theorem selected_cut_51860 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285146) = some ⟨11, 1, 0, 1468743, 285146, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285146_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285146 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285146 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285146, 1, 262144⟩
    (by decide) selected_cut_51860

theorem selected_cut_51861 : selected 10 ⟨1500507, by decide⟩
    (prefixPartial 11 285147) = some ⟨11, 2, 0, 1500507, 285147, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_285147_1500507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285147 ⟨1500507, by decide⟩ :=
  accepted_of_selected 11 285147 ⟨1500507, by decide⟩ ⟨11, 2, 0, 1500507, 285147, 1257, 262144⟩
    (by decide) selected_cut_51861

theorem unmarked_context_10_71286_1500508 : frontier 11 ⟨1500508, by decide⟩
    (prefixCache 10 71286) (prefixPartial 10 71286) = false := by
  decide +kernel

theorem node_context_10_71286_1500508 : EJMOriginalGlobalDAGData.nodes 11 ⟨1500508, by decide⟩ =
    .split (coordinate 10) (![⟨1500439, by decide⟩,⟨1500480, by decide⟩,⟨1468743, by decide⟩,⟨1500507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71286_1500508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71286 ⟨1500508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71286
    ⟨1500508, by decide⟩ (by decide) (![⟨1500439, by decide⟩,⟨1500480, by decide⟩,⟨1468743, by decide⟩,⟨1500507, by decide⟩]) unmarked_context_10_71286_1500508 node_context_10_71286_1500508
  intro a
  fin_cases a
  · exact context_11_285144_1500439
  · exact context_11_285145_1500480
  · exact context_11_285146_1468743
  · exact context_11_285147_1500507

theorem selected_cut_51862 : selected 11 ⟨1500580, by decide⟩
    (prefixPartial 10 71287) = some ⟨10, 2, 0, 1500580, 71287, 3701, 1048576⟩ := by
  decide +kernel

theorem context_10_71287_1500580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71287 ⟨1500580, by decide⟩ :=
  accepted_of_selected 10 71287 ⟨1500580, by decide⟩ ⟨10, 2, 0, 1500580, 71287, 3701, 1048576⟩
    (by decide) selected_cut_51862

theorem unmarked_context_9_17821_1500581 : frontier 12 ⟨1500581, by decide⟩
    (prefixCache 9 17821) (prefixPartial 9 17821) = false := by
  decide +kernel

theorem node_context_9_17821_1500581 : EJMOriginalGlobalDAGData.nodes 12 ⟨1500581, by decide⟩ =
    .split (coordinate 9) (![⟨1500411, by decide⟩,⟨1468874, by decide⟩,⟨1500508, by decide⟩,⟨1500580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17821_1500581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17821 ⟨1500581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17821
    ⟨1500581, by decide⟩ (by decide) (![⟨1500411, by decide⟩,⟨1468874, by decide⟩,⟨1500508, by decide⟩,⟨1500580, by decide⟩]) unmarked_context_9_17821_1500581 node_context_9_17821_1500581
  intro a
  fin_cases a
  · exact context_10_71284_1500411
  · exact context_10_71285_1468874
  · exact context_10_71286_1500508
  · exact context_10_71287_1500580

theorem selected_cut_51863 : selected 11 ⟨1500641, by decide⟩
    (prefixPartial 10 71288) = some ⟨10, 2, 0, 1500641, 71288, 3533, 1048576⟩ := by
  decide +kernel

theorem context_10_71288_1500641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71288 ⟨1500641, by decide⟩ :=
  accepted_of_selected 10 71288 ⟨1500641, by decide⟩ ⟨10, 2, 0, 1500641, 71288, 3533, 1048576⟩
    (by decide) selected_cut_51863

theorem selected_cut_51864 : selected 11 ⟨1500733, by decide⟩
    (prefixPartial 10 71289) = some ⟨10, 2, 0, 1500733, 71289, 3157, 1048576⟩ := by
  decide +kernel

theorem context_10_71289_1500733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71289 ⟨1500733, by decide⟩ :=
  accepted_of_selected 10 71289 ⟨1500733, by decide⟩ ⟨10, 2, 0, 1500733, 71289, 3157, 1048576⟩
    (by decide) selected_cut_51864

theorem selected_cut_51865 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71290) = some ⟨10, 1, 0, 1469103, 71290, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71290_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71290 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71290 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71290, 1, 1048576⟩
    (by decide) selected_cut_51865

theorem selected_cut_51866 : selected 11 ⟨1500783, by decide⟩
    (prefixPartial 10 71291) = some ⟨10, 2, 0, 1500783, 71291, 2485, 1048576⟩ := by
  decide +kernel

theorem context_10_71291_1500783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71291 ⟨1500783, by decide⟩ :=
  accepted_of_selected 10 71291 ⟨1500783, by decide⟩ ⟨10, 2, 0, 1500783, 71291, 2485, 1048576⟩
    (by decide) selected_cut_51866

theorem unmarked_context_9_17822_1500784 : frontier 12 ⟨1500784, by decide⟩
    (prefixCache 9 17822) (prefixPartial 9 17822) = false := by
  decide +kernel

theorem node_context_9_17822_1500784 : EJMOriginalGlobalDAGData.nodes 12 ⟨1500784, by decide⟩ =
    .split (coordinate 9) (![⟨1500641, by decide⟩,⟨1500733, by decide⟩,⟨1469103, by decide⟩,⟨1500783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17822_1500784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17822 ⟨1500784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17822
    ⟨1500784, by decide⟩ (by decide) (![⟨1500641, by decide⟩,⟨1500733, by decide⟩,⟨1469103, by decide⟩,⟨1500783, by decide⟩]) unmarked_context_9_17822_1500784 node_context_9_17822_1500784
  intro a
  fin_cases a
  · exact context_10_71288_1500641
  · exact context_10_71289_1500733
  · exact context_10_71290_1469103
  · exact context_10_71291_1500783

theorem selected_cut_51867 : selected 12 ⟨1500842, by decide⟩
    (prefixPartial 9 17823) = some ⟨9, 2, 0, 1500842, 17823, 2537, 4194304⟩ := by
  decide +kernel

theorem context_9_17823_1500842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17823 ⟨1500842, by decide⟩ :=
  accepted_of_selected 9 17823 ⟨1500842, by decide⟩ ⟨9, 2, 0, 1500842, 17823, 2537, 4194304⟩
    (by decide) selected_cut_51867

theorem unmarked_context_8_4455_1500843 : frontier 13 ⟨1500843, by decide⟩
    (prefixCache 8 4455) (prefixPartial 8 4455) = false := by
  decide +kernel

theorem node_context_8_4455_1500843 : EJMOriginalGlobalDAGData.nodes 13 ⟨1500843, by decide⟩ =
    .split (coordinate 8) (![⟨1500340, by decide⟩,⟨1500581, by decide⟩,⟨1500784, by decide⟩,⟨1500842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4455_1500843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4455 ⟨1500843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4455
    ⟨1500843, by decide⟩ (by decide) (![⟨1500340, by decide⟩,⟨1500581, by decide⟩,⟨1500784, by decide⟩,⟨1500842, by decide⟩]) unmarked_context_8_4455_1500843 node_context_8_4455_1500843
  intro a
  fin_cases a
  · exact context_9_17820_1500340
  · exact context_9_17821_1500581
  · exact context_9_17822_1500784
  · exact context_9_17823_1500842

theorem unmarked_context_7_1113_1500844 : frontier 14 ⟨1500844, by decide⟩
    (prefixCache 7 1113) (prefixPartial 7 1113) = false := by
  decide +kernel

theorem node_context_7_1113_1500844 : EJMOriginalGlobalDAGData.nodes 14 ⟨1500844, by decide⟩ =
    .split (coordinate 7) (![⟨1498137, by decide⟩,⟨1498857, by decide⟩,⟨1499849, by decide⟩,⟨1500843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1113_1500844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1113 ⟨1500844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1113
    ⟨1500844, by decide⟩ (by decide) (![⟨1498137, by decide⟩,⟨1498857, by decide⟩,⟨1499849, by decide⟩,⟨1500843, by decide⟩]) unmarked_context_7_1113_1500844 node_context_7_1113_1500844
  intro a
  fin_cases a
  · exact context_8_4452_1498137
  · exact context_8_4453_1498857
  · exact context_8_4454_1499849
  · exact context_8_4455_1500843

theorem selected_cut_51868 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71296) = some ⟨10, 1, 0, 1468246, 71296, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71296_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71296 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71296 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71296, 1, 1048576⟩
    (by decide) selected_cut_51868

theorem selected_cut_51869 : selected 10 ⟨1500908, by decide⟩
    (prefixPartial 11 285188) = some ⟨11, 2, 0, 1500908, 285188, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_285188_1500908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285188 ⟨1500908, by decide⟩ :=
  accepted_of_selected 11 285188 ⟨1500908, by decide⟩ ⟨11, 2, 0, 1500908, 285188, 2809, 262144⟩
    (by decide) selected_cut_51869

theorem selected_cut_51870 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285189) = some ⟨11, 1, 0, 1468419, 285189, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285189_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285189 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285189 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285189, 1, 262144⟩
    (by decide) selected_cut_51870

theorem selected_cut_51871 : selected 10 ⟨1500959, by decide⟩
    (prefixPartial 11 285190) = some ⟨11, 2, 0, 1500959, 285190, 2537, 262144⟩ := by
  decide +kernel

theorem context_11_285190_1500959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285190 ⟨1500959, by decide⟩ :=
  accepted_of_selected 11 285190 ⟨1500959, by decide⟩ ⟨11, 2, 0, 1500959, 285190, 2537, 262144⟩
    (by decide) selected_cut_51871

theorem selected_cut_51872 : selected 10 ⟨1501007, by decide⟩
    (prefixPartial 11 285191) = some ⟨11, 2, 0, 1501007, 285191, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_285191_1501007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285191 ⟨1501007, by decide⟩ :=
  accepted_of_selected 11 285191 ⟨1501007, by decide⟩ ⟨11, 2, 0, 1501007, 285191, 2497, 262144⟩
    (by decide) selected_cut_51872

theorem unmarked_context_10_71297_1501008 : frontier 11 ⟨1501008, by decide⟩
    (prefixCache 10 71297) (prefixPartial 10 71297) = false := by
  decide +kernel

theorem node_context_10_71297_1501008 : EJMOriginalGlobalDAGData.nodes 11 ⟨1501008, by decide⟩ =
    .split (coordinate 10) (![⟨1500908, by decide⟩,⟨1468419, by decide⟩,⟨1500959, by decide⟩,⟨1501007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71297_1501008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71297 ⟨1501008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71297
    ⟨1501008, by decide⟩ (by decide) (![⟨1500908, by decide⟩,⟨1468419, by decide⟩,⟨1500959, by decide⟩,⟨1501007, by decide⟩]) unmarked_context_10_71297_1501008 node_context_10_71297_1501008
  intro a
  fin_cases a
  · exact context_11_285188_1500908
  · exact context_11_285189_1468419
  · exact context_11_285190_1500959
  · exact context_11_285191_1501007

theorem selected_cut_51873 : selected 10 ⟨1501009, by decide⟩
    (prefixPartial 11 285192) = some ⟨11, 2, 0, 1501009, 285192, 5, 262144⟩ := by
  decide +kernel

theorem context_11_285192_1501009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285192 ⟨1501009, by decide⟩ :=
  accepted_of_selected 11 285192 ⟨1501009, by decide⟩ ⟨11, 2, 0, 1501009, 285192, 5, 262144⟩
    (by decide) selected_cut_51873

theorem selected_cut_51874 : selected 10 ⟨1501049, by decide⟩
    (prefixPartial 11 285193) = some ⟨11, 2, 0, 1501049, 285193, 2285, 262144⟩ := by
  decide +kernel

theorem context_11_285193_1501049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285193 ⟨1501049, by decide⟩ :=
  accepted_of_selected 11 285193 ⟨1501049, by decide⟩ ⟨11, 2, 0, 1501049, 285193, 2285, 262144⟩
    (by decide) selected_cut_51874

theorem selected_cut_51875 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285194) = some ⟨11, 1, 0, 1468743, 285194, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285194_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285194 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285194 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285194, 1, 262144⟩
    (by decide) selected_cut_51875

theorem selected_cut_51876 : selected 10 ⟨1501084, by decide⟩
    (prefixPartial 11 285195) = some ⟨11, 2, 0, 1501084, 285195, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_285195_1501084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285195 ⟨1501084, by decide⟩ :=
  accepted_of_selected 11 285195 ⟨1501084, by decide⟩ ⟨11, 2, 0, 1501084, 285195, 2157, 262144⟩
    (by decide) selected_cut_51876

theorem unmarked_context_10_71298_1501085 : frontier 11 ⟨1501085, by decide⟩
    (prefixCache 10 71298) (prefixPartial 10 71298) = false := by
  decide +kernel

theorem node_context_10_71298_1501085 : EJMOriginalGlobalDAGData.nodes 11 ⟨1501085, by decide⟩ =
    .split (coordinate 10) (![⟨1501009, by decide⟩,⟨1501049, by decide⟩,⟨1468743, by decide⟩,⟨1501084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71298_1501085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71298 ⟨1501085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71298
    ⟨1501085, by decide⟩ (by decide) (![⟨1501009, by decide⟩,⟨1501049, by decide⟩,⟨1468743, by decide⟩,⟨1501084, by decide⟩]) unmarked_context_10_71298_1501085 node_context_10_71298_1501085
  intro a
  fin_cases a
  · exact context_11_285192_1501009
  · exact context_11_285193_1501049
  · exact context_11_285194_1468743
  · exact context_11_285195_1501084

theorem selected_cut_51877 : selected 10 ⟨1501133, by decide⟩
    (prefixPartial 11 285196) = some ⟨11, 2, 0, 1501133, 285196, 2365, 262144⟩ := by
  decide +kernel

theorem context_11_285196_1501133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285196 ⟨1501133, by decide⟩ :=
  accepted_of_selected 11 285196 ⟨1501133, by decide⟩ ⟨11, 2, 0, 1501133, 285196, 2365, 262144⟩
    (by decide) selected_cut_51877

theorem selected_cut_51878 : selected 10 ⟨1501175, by decide⟩
    (prefixPartial 11 285197) = some ⟨11, 2, 0, 1501175, 285197, 2365, 262144⟩ := by
  decide +kernel

theorem context_11_285197_1501175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285197 ⟨1501175, by decide⟩ :=
  accepted_of_selected 11 285197 ⟨1501175, by decide⟩ ⟨11, 2, 0, 1501175, 285197, 2365, 262144⟩
    (by decide) selected_cut_51878

theorem selected_cut_51879 : selected 10 ⟨1501209, by decide⟩
    (prefixPartial 11 285198) = some ⟨11, 2, 0, 1501209, 285198, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_285198_1501209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285198 ⟨1501209, by decide⟩ :=
  accepted_of_selected 11 285198 ⟨1501209, by decide⟩ ⟨11, 2, 0, 1501209, 285198, 1993, 262144⟩
    (by decide) selected_cut_51879

theorem selected_cut_51880 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285199) = some ⟨11, 1, 0, 1470044, 285199, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285199_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285199 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285199 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285199, 1, 262144⟩
    (by decide) selected_cut_51880

theorem unmarked_context_10_71299_1501210 : frontier 11 ⟨1501210, by decide⟩
    (prefixCache 10 71299) (prefixPartial 10 71299) = false := by
  decide +kernel

theorem node_context_10_71299_1501210 : EJMOriginalGlobalDAGData.nodes 11 ⟨1501210, by decide⟩ =
    .split (coordinate 10) (![⟨1501133, by decide⟩,⟨1501175, by decide⟩,⟨1501209, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71299_1501210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71299 ⟨1501210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71299
    ⟨1501210, by decide⟩ (by decide) (![⟨1501133, by decide⟩,⟨1501175, by decide⟩,⟨1501209, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71299_1501210 node_context_10_71299_1501210
  intro a
  fin_cases a
  · exact context_11_285196_1501133
  · exact context_11_285197_1501175
  · exact context_11_285198_1501209
  · exact context_11_285199_1470044

theorem unmarked_context_9_17824_1501211 : frontier 12 ⟨1501211, by decide⟩
    (prefixCache 9 17824) (prefixPartial 9 17824) = false := by
  decide +kernel

theorem node_context_9_17824_1501211 : EJMOriginalGlobalDAGData.nodes 12 ⟨1501211, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1501008, by decide⟩,⟨1501085, by decide⟩,⟨1501210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17824_1501211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17824 ⟨1501211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17824
    ⟨1501211, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1501008, by decide⟩,⟨1501085, by decide⟩,⟨1501210, by decide⟩]) unmarked_context_9_17824_1501211 node_context_9_17824_1501211
  intro a
  fin_cases a
  · exact context_10_71296_1468246
  · exact context_10_71297_1501008
  · exact context_10_71298_1501085
  · exact context_10_71299_1501210

theorem selected_cut_51881 : selected 11 ⟨1501261, by decide⟩
    (prefixPartial 10 71300) = some ⟨10, 2, 0, 1501261, 71300, 3085, 1048576⟩ := by
  decide +kernel

theorem context_10_71300_1501261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71300 ⟨1501261, by decide⟩ :=
  accepted_of_selected 10 71300 ⟨1501261, by decide⟩ ⟨10, 2, 0, 1501261, 71300, 3085, 1048576⟩
    (by decide) selected_cut_51881

theorem selected_cut_51882 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71301) = some ⟨10, 1, 0, 1468874, 71301, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71301_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71301 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71301 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71301, 1, 1048576⟩
    (by decide) selected_cut_51882

theorem selected_cut_51883 : selected 11 ⟨1501350, by decide⟩
    (prefixPartial 10 71302) = some ⟨10, 2, 0, 1501350, 71302, 3777, 1048576⟩ := by
  decide +kernel

theorem context_10_71302_1501350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71302 ⟨1501350, by decide⟩ :=
  accepted_of_selected 10 71302 ⟨1501350, by decide⟩ ⟨10, 2, 0, 1501350, 71302, 3777, 1048576⟩
    (by decide) selected_cut_51883

theorem selected_cut_51884 : selected 10 ⟨1501376, by decide⟩
    (prefixPartial 11 285212) = some ⟨11, 2, 0, 1501376, 285212, 1317, 262144⟩ := by
  decide +kernel

theorem context_11_285212_1501376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285212 ⟨1501376, by decide⟩ :=
  accepted_of_selected 11 285212 ⟨1501376, by decide⟩ ⟨11, 2, 0, 1501376, 285212, 1317, 262144⟩
    (by decide) selected_cut_51884

theorem selected_cut_51885 : selected 10 ⟨1501408, by decide⟩
    (prefixPartial 11 285213) = some ⟨11, 2, 0, 1501408, 285213, 1869, 262144⟩ := by
  decide +kernel

theorem context_11_285213_1501408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285213 ⟨1501408, by decide⟩ :=
  accepted_of_selected 11 285213 ⟨1501408, by decide⟩ ⟨11, 2, 0, 1501408, 285213, 1869, 262144⟩
    (by decide) selected_cut_51885

theorem selected_cut_51886 : selected 10 ⟨1501425, by decide⟩
    (prefixPartial 11 285214) = some ⟨11, 2, 0, 1501425, 285214, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_285214_1501425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285214 ⟨1501425, by decide⟩ :=
  accepted_of_selected 11 285214 ⟨1501425, by decide⟩ ⟨11, 2, 0, 1501425, 285214, 1101, 262144⟩
    (by decide) selected_cut_51886

theorem selected_cut_51887 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285215) = some ⟨11, 1, 0, 1470044, 285215, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285215_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285215 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285215 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285215, 1, 262144⟩
    (by decide) selected_cut_51887

theorem unmarked_context_10_71303_1501426 : frontier 11 ⟨1501426, by decide⟩
    (prefixCache 10 71303) (prefixPartial 10 71303) = false := by
  decide +kernel

theorem node_context_10_71303_1501426 : EJMOriginalGlobalDAGData.nodes 11 ⟨1501426, by decide⟩ =
    .split (coordinate 10) (![⟨1501376, by decide⟩,⟨1501408, by decide⟩,⟨1501425, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71303_1501426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71303 ⟨1501426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71303
    ⟨1501426, by decide⟩ (by decide) (![⟨1501376, by decide⟩,⟨1501408, by decide⟩,⟨1501425, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71303_1501426 node_context_10_71303_1501426
  intro a
  fin_cases a
  · exact context_11_285212_1501376
  · exact context_11_285213_1501408
  · exact context_11_285214_1501425
  · exact context_11_285215_1470044

theorem unmarked_context_9_17825_1501427 : frontier 12 ⟨1501427, by decide⟩
    (prefixCache 9 17825) (prefixPartial 9 17825) = false := by
  decide +kernel

theorem node_context_9_17825_1501427 : EJMOriginalGlobalDAGData.nodes 12 ⟨1501427, by decide⟩ =
    .split (coordinate 9) (![⟨1501261, by decide⟩,⟨1468874, by decide⟩,⟨1501350, by decide⟩,⟨1501426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17825_1501427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17825 ⟨1501427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17825
    ⟨1501427, by decide⟩ (by decide) (![⟨1501261, by decide⟩,⟨1468874, by decide⟩,⟨1501350, by decide⟩,⟨1501426, by decide⟩]) unmarked_context_9_17825_1501427 node_context_9_17825_1501427
  intro a
  fin_cases a
  · exact context_10_71300_1501261
  · exact context_10_71301_1468874
  · exact context_10_71302_1501350
  · exact context_10_71303_1501426

theorem selected_cut_51888 : selected 11 ⟨1501476, by decide⟩
    (prefixPartial 10 71304) = some ⟨10, 2, 0, 1501476, 71304, 2665, 1048576⟩ := by
  decide +kernel

theorem context_10_71304_1501476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71304 ⟨1501476, by decide⟩ :=
  accepted_of_selected 10 71304 ⟨1501476, by decide⟩ ⟨10, 2, 0, 1501476, 71304, 2665, 1048576⟩
    (by decide) selected_cut_51888

theorem selected_cut_51889 : selected 11 ⟨1501534, by decide⟩
    (prefixPartial 10 71305) = some ⟨10, 2, 0, 1501534, 71305, 3105, 1048576⟩ := by
  decide +kernel

theorem context_10_71305_1501534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71305 ⟨1501534, by decide⟩ :=
  accepted_of_selected 10 71305 ⟨1501534, by decide⟩ ⟨10, 2, 0, 1501534, 71305, 3105, 1048576⟩
    (by decide) selected_cut_51889

theorem selected_cut_51890 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71306) = some ⟨10, 1, 0, 1469103, 71306, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71306_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71306 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71306 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71306, 1, 1048576⟩
    (by decide) selected_cut_51890

theorem selected_cut_51891 : selected 11 ⟨1501573, by decide⟩
    (prefixPartial 10 71307) = some ⟨10, 2, 0, 1501573, 71307, 2197, 1048576⟩ := by
  decide +kernel

theorem context_10_71307_1501573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71307 ⟨1501573, by decide⟩ :=
  accepted_of_selected 10 71307 ⟨1501573, by decide⟩ ⟨10, 2, 0, 1501573, 71307, 2197, 1048576⟩
    (by decide) selected_cut_51891

theorem unmarked_context_9_17826_1501574 : frontier 12 ⟨1501574, by decide⟩
    (prefixCache 9 17826) (prefixPartial 9 17826) = false := by
  decide +kernel

theorem node_context_9_17826_1501574 : EJMOriginalGlobalDAGData.nodes 12 ⟨1501574, by decide⟩ =
    .split (coordinate 9) (![⟨1501476, by decide⟩,⟨1501534, by decide⟩,⟨1469103, by decide⟩,⟨1501573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17826_1501574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17826 ⟨1501574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17826
    ⟨1501574, by decide⟩ (by decide) (![⟨1501476, by decide⟩,⟨1501534, by decide⟩,⟨1469103, by decide⟩,⟨1501573, by decide⟩]) unmarked_context_9_17826_1501574 node_context_9_17826_1501574
  intro a
  fin_cases a
  · exact context_10_71304_1501476
  · exact context_10_71305_1501534
  · exact context_10_71306_1469103
  · exact context_10_71307_1501573

theorem selected_cut_51892 : selected 12 ⟨1501635, by decide⟩
    (prefixPartial 9 17827) = some ⟨9, 2, 0, 1501635, 17827, 2933, 4194304⟩ := by
  decide +kernel

theorem context_9_17827_1501635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17827 ⟨1501635, by decide⟩ :=
  accepted_of_selected 9 17827 ⟨1501635, by decide⟩ ⟨9, 2, 0, 1501635, 17827, 2933, 4194304⟩
    (by decide) selected_cut_51892

theorem unmarked_context_8_4456_1501636 : frontier 13 ⟨1501636, by decide⟩
    (prefixCache 8 4456) (prefixPartial 8 4456) = false := by
  decide +kernel

theorem node_context_8_4456_1501636 : EJMOriginalGlobalDAGData.nodes 13 ⟨1501636, by decide⟩ =
    .split (coordinate 8) (![⟨1501211, by decide⟩,⟨1501427, by decide⟩,⟨1501574, by decide⟩,⟨1501635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4456_1501636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4456 ⟨1501636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4456
    ⟨1501636, by decide⟩ (by decide) (![⟨1501211, by decide⟩,⟨1501427, by decide⟩,⟨1501574, by decide⟩,⟨1501635, by decide⟩]) unmarked_context_8_4456_1501636 node_context_8_4456_1501636
  intro a
  fin_cases a
  · exact context_9_17824_1501211
  · exact context_9_17825_1501427
  · exact context_9_17826_1501574
  · exact context_9_17827_1501635

theorem selected_cut_51893 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71312) = some ⟨10, 1, 0, 1468246, 71312, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71312_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71312 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71312 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71312, 1, 1048576⟩
    (by decide) selected_cut_51893

theorem selected_cut_51894 : selected 10 ⟨1501742, by decide⟩
    (prefixPartial 11 285252) = some ⟨11, 2, 0, 1501742, 285252, 2705, 262144⟩ := by
  decide +kernel

theorem context_11_285252_1501742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285252 ⟨1501742, by decide⟩ :=
  accepted_of_selected 11 285252 ⟨1501742, by decide⟩ ⟨11, 2, 0, 1501742, 285252, 2705, 262144⟩
    (by decide) selected_cut_51894

theorem selected_cut_51895 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285253) = some ⟨11, 1, 0, 1468419, 285253, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285253_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285253 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285253 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285253, 1, 262144⟩
    (by decide) selected_cut_51895

theorem selected_cut_51896 : selected 10 ⟨1501824, by decide⟩
    (prefixPartial 11 285254) = some ⟨11, 2, 0, 1501824, 285254, 1509, 262144⟩ := by
  decide +kernel

theorem context_11_285254_1501824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285254 ⟨1501824, by decide⟩ :=
  accepted_of_selected 11 285254 ⟨1501824, by decide⟩ ⟨11, 2, 0, 1501824, 285254, 1509, 262144⟩
    (by decide) selected_cut_51896

theorem selected_cut_51897 : selected 10 ⟨1501892, by decide⟩
    (prefixPartial 11 285255) = some ⟨11, 2, 0, 1501892, 285255, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_285255_1501892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285255 ⟨1501892, by decide⟩ :=
  accepted_of_selected 11 285255 ⟨1501892, by decide⟩ ⟨11, 2, 0, 1501892, 285255, 2265, 262144⟩
    (by decide) selected_cut_51897

theorem unmarked_context_10_71313_1501893 : frontier 11 ⟨1501893, by decide⟩
    (prefixCache 10 71313) (prefixPartial 10 71313) = false := by
  decide +kernel

theorem node_context_10_71313_1501893 : EJMOriginalGlobalDAGData.nodes 11 ⟨1501893, by decide⟩ =
    .split (coordinate 10) (![⟨1501742, by decide⟩,⟨1468419, by decide⟩,⟨1501824, by decide⟩,⟨1501892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71313_1501893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71313 ⟨1501893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71313
    ⟨1501893, by decide⟩ (by decide) (![⟨1501742, by decide⟩,⟨1468419, by decide⟩,⟨1501824, by decide⟩,⟨1501892, by decide⟩]) unmarked_context_10_71313_1501893 node_context_10_71313_1501893
  intro a
  fin_cases a
  · exact context_11_285252_1501742
  · exact context_11_285253_1468419
  · exact context_11_285254_1501824
  · exact context_11_285255_1501892

theorem selected_cut_51898 : selected 11 ⟨1502000, by decide⟩
    (prefixPartial 10 71314) = some ⟨10, 2, 0, 1502000, 71314, 4001, 1048576⟩ := by
  decide +kernel

theorem context_10_71314_1502000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71314 ⟨1502000, by decide⟩ :=
  accepted_of_selected 10 71314 ⟨1502000, by decide⟩ ⟨10, 2, 0, 1502000, 71314, 4001, 1048576⟩
    (by decide) selected_cut_51898

theorem selected_cut_51899 : selected 10 ⟨1502087, by decide⟩
    (prefixPartial 11 285260) = some ⟨11, 2, 0, 1502087, 285260, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_285260_1502087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285260 ⟨1502087, by decide⟩ :=
  accepted_of_selected 11 285260 ⟨1502087, by decide⟩ ⟨11, 2, 0, 1502087, 285260, 2153, 262144⟩
    (by decide) selected_cut_51899

theorem selected_cut_51900 : selected 10 ⟨1502137, by decide⟩
    (prefixPartial 11 285261) = some ⟨11, 2, 0, 1502137, 285261, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_285261_1502137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285261 ⟨1502137, by decide⟩ :=
  accepted_of_selected 11 285261 ⟨1502137, by decide⟩ ⟨11, 2, 0, 1502137, 285261, 1717, 262144⟩
    (by decide) selected_cut_51900

theorem selected_cut_51901 : selected 10 ⟨1502194, by decide⟩
    (prefixPartial 11 285262) = some ⟨11, 2, 0, 1502194, 285262, 1073, 262144⟩ := by
  decide +kernel

theorem context_11_285262_1502194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285262 ⟨1502194, by decide⟩ :=
  accepted_of_selected 11 285262 ⟨1502194, by decide⟩ ⟨11, 2, 0, 1502194, 285262, 1073, 262144⟩
    (by decide) selected_cut_51901

theorem selected_cut_51902 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285263) = some ⟨11, 1, 0, 1470044, 285263, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285263_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285263 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285263 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285263, 1, 262144⟩
    (by decide) selected_cut_51902

theorem unmarked_context_10_71315_1502195 : frontier 11 ⟨1502195, by decide⟩
    (prefixCache 10 71315) (prefixPartial 10 71315) = false := by
  decide +kernel

theorem node_context_10_71315_1502195 : EJMOriginalGlobalDAGData.nodes 11 ⟨1502195, by decide⟩ =
    .split (coordinate 10) (![⟨1502087, by decide⟩,⟨1502137, by decide⟩,⟨1502194, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71315_1502195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71315 ⟨1502195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71315
    ⟨1502195, by decide⟩ (by decide) (![⟨1502087, by decide⟩,⟨1502137, by decide⟩,⟨1502194, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71315_1502195 node_context_10_71315_1502195
  intro a
  fin_cases a
  · exact context_11_285260_1502087
  · exact context_11_285261_1502137
  · exact context_11_285262_1502194
  · exact context_11_285263_1470044

theorem unmarked_context_9_17828_1502196 : frontier 12 ⟨1502196, by decide⟩
    (prefixCache 9 17828) (prefixPartial 9 17828) = false := by
  decide +kernel

theorem node_context_9_17828_1502196 : EJMOriginalGlobalDAGData.nodes 12 ⟨1502196, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1501893, by decide⟩,⟨1502000, by decide⟩,⟨1502195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17828_1502196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17828 ⟨1502196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17828
    ⟨1502196, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1501893, by decide⟩,⟨1502000, by decide⟩,⟨1502195, by decide⟩]) unmarked_context_9_17828_1502196 node_context_9_17828_1502196
  intro a
  fin_cases a
  · exact context_10_71312_1468246
  · exact context_10_71313_1501893
  · exact context_10_71314_1502000
  · exact context_10_71315_1502195

theorem selected_cut_51903 : selected 11 ⟨1502251, by decide⟩
    (prefixPartial 10 71316) = some ⟨10, 2, 0, 1502251, 71316, 1537, 1048576⟩ := by
  decide +kernel

theorem context_10_71316_1502251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71316 ⟨1502251, by decide⟩ :=
  accepted_of_selected 10 71316 ⟨1502251, by decide⟩ ⟨10, 2, 0, 1502251, 71316, 1537, 1048576⟩
    (by decide) selected_cut_51903

theorem selected_cut_51904 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71317) = some ⟨10, 1, 0, 1468874, 71317, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71317_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71317 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71317 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71317, 1, 1048576⟩
    (by decide) selected_cut_51904

theorem selected_cut_51905 : selected 11 ⟨1502327, by decide⟩
    (prefixPartial 10 71318) = some ⟨10, 2, 0, 1502327, 71318, 1957, 1048576⟩ := by
  decide +kernel

theorem context_10_71318_1502327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71318 ⟨1502327, by decide⟩ :=
  accepted_of_selected 10 71318 ⟨1502327, by decide⟩ ⟨10, 2, 0, 1502327, 71318, 1957, 1048576⟩
    (by decide) selected_cut_51905

theorem selected_cut_51906 : selected 11 ⟨1502389, by decide⟩
    (prefixPartial 10 71319) = some ⟨10, 2, 0, 1502389, 71319, 1405, 1048576⟩ := by
  decide +kernel

theorem context_10_71319_1502389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71319 ⟨1502389, by decide⟩ :=
  accepted_of_selected 10 71319 ⟨1502389, by decide⟩ ⟨10, 2, 0, 1502389, 71319, 1405, 1048576⟩
    (by decide) selected_cut_51906

theorem unmarked_context_9_17829_1502390 : frontier 12 ⟨1502390, by decide⟩
    (prefixCache 9 17829) (prefixPartial 9 17829) = false := by
  decide +kernel

theorem node_context_9_17829_1502390 : EJMOriginalGlobalDAGData.nodes 12 ⟨1502390, by decide⟩ =
    .split (coordinate 9) (![⟨1502251, by decide⟩,⟨1468874, by decide⟩,⟨1502327, by decide⟩,⟨1502389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17829_1502390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17829 ⟨1502390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17829
    ⟨1502390, by decide⟩ (by decide) (![⟨1502251, by decide⟩,⟨1468874, by decide⟩,⟨1502327, by decide⟩,⟨1502389, by decide⟩]) unmarked_context_9_17829_1502390 node_context_9_17829_1502390
  intro a
  fin_cases a
  · exact context_10_71316_1502251
  · exact context_10_71317_1468874
  · exact context_10_71318_1502327
  · exact context_10_71319_1502389

theorem selected_cut_51907 : selected 12 ⟨1502453, by decide⟩
    (prefixPartial 9 17830) = some ⟨9, 2, 0, 1502453, 17830, 1229, 4194304⟩ := by
  decide +kernel

theorem context_9_17830_1502453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17830 ⟨1502453, by decide⟩ :=
  accepted_of_selected 9 17830 ⟨1502453, by decide⟩ ⟨9, 2, 0, 1502453, 17830, 1229, 4194304⟩
    (by decide) selected_cut_51907

theorem selected_cut_51908 : selected 12 ⟨1502488, by decide⟩
    (prefixPartial 9 17831) = some ⟨9, 2, 0, 1502488, 17831, 261, 4194304⟩ := by
  decide +kernel

theorem context_9_17831_1502488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17831 ⟨1502488, by decide⟩ :=
  accepted_of_selected 9 17831 ⟨1502488, by decide⟩ ⟨9, 2, 0, 1502488, 17831, 261, 4194304⟩
    (by decide) selected_cut_51908

theorem unmarked_context_8_4457_1502489 : frontier 13 ⟨1502489, by decide⟩
    (prefixCache 8 4457) (prefixPartial 8 4457) = false := by
  decide +kernel

theorem node_context_8_4457_1502489 : EJMOriginalGlobalDAGData.nodes 13 ⟨1502489, by decide⟩ =
    .split (coordinate 8) (![⟨1502196, by decide⟩,⟨1502390, by decide⟩,⟨1502453, by decide⟩,⟨1502488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4457_1502489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4457 ⟨1502489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4457
    ⟨1502489, by decide⟩ (by decide) (![⟨1502196, by decide⟩,⟨1502390, by decide⟩,⟨1502453, by decide⟩,⟨1502488, by decide⟩]) unmarked_context_8_4457_1502489 node_context_8_4457_1502489
  intro a
  fin_cases a
  · exact context_9_17828_1502196
  · exact context_9_17829_1502390
  · exact context_9_17830_1502453
  · exact context_9_17831_1502488

theorem selected_cut_51909 : selected 13 ⟨1502490, by decide⟩
    (prefixPartial 8 4458) = some ⟨8, 1, 0, 1502490, 4458, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4458_1502490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4458 ⟨1502490, by decide⟩ :=
  accepted_of_selected 8 4458 ⟨1502490, by decide⟩ ⟨8, 1, 0, 1502490, 4458, 1, 16777216⟩
    (by decide) selected_cut_51909

theorem selected_cut_51910 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71344) = some ⟨10, 1, 0, 1468246, 71344, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71344_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71344 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71344 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71344, 1, 1048576⟩
    (by decide) selected_cut_51910

theorem selected_cut_51911 : selected 10 ⟨1502577, by decide⟩
    (prefixPartial 11 285380) = some ⟨11, 2, 0, 1502577, 285380, 3481, 262144⟩ := by
  decide +kernel

theorem context_11_285380_1502577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285380 ⟨1502577, by decide⟩ :=
  accepted_of_selected 11 285380 ⟨1502577, by decide⟩ ⟨11, 2, 0, 1502577, 285380, 3481, 262144⟩
    (by decide) selected_cut_51911

theorem selected_cut_51912 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285381) = some ⟨11, 1, 0, 1468419, 285381, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285381_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285381 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285381 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285381, 1, 262144⟩
    (by decide) selected_cut_51912

theorem selected_cut_51913 : selected 10 ⟨1502656, by decide⟩
    (prefixPartial 11 285382) = some ⟨11, 2, 0, 1502656, 285382, 2965, 262144⟩ := by
  decide +kernel

theorem context_11_285382_1502656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285382 ⟨1502656, by decide⟩ :=
  accepted_of_selected 11 285382 ⟨1502656, by decide⟩ ⟨11, 2, 0, 1502656, 285382, 2965, 262144⟩
    (by decide) selected_cut_51913

theorem selected_cut_51914 : selected 10 ⟨1502706, by decide⟩
    (prefixPartial 11 285383) = some ⟨11, 2, 0, 1502706, 285383, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_285383_1502706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285383 ⟨1502706, by decide⟩ :=
  accepted_of_selected 11 285383 ⟨1502706, by decide⟩ ⟨11, 2, 0, 1502706, 285383, 2917, 262144⟩
    (by decide) selected_cut_51914

theorem unmarked_context_10_71345_1502707 : frontier 11 ⟨1502707, by decide⟩
    (prefixCache 10 71345) (prefixPartial 10 71345) = false := by
  decide +kernel

theorem node_context_10_71345_1502707 : EJMOriginalGlobalDAGData.nodes 11 ⟨1502707, by decide⟩ =
    .split (coordinate 10) (![⟨1502577, by decide⟩,⟨1468419, by decide⟩,⟨1502656, by decide⟩,⟨1502706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71345_1502707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71345 ⟨1502707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71345
    ⟨1502707, by decide⟩ (by decide) (![⟨1502577, by decide⟩,⟨1468419, by decide⟩,⟨1502656, by decide⟩,⟨1502706, by decide⟩]) unmarked_context_10_71345_1502707 node_context_10_71345_1502707
  intro a
  fin_cases a
  · exact context_11_285380_1502577
  · exact context_11_285381_1468419
  · exact context_11_285382_1502656
  · exact context_11_285383_1502706

theorem selected_cut_51915 : selected 10 ⟨1502796, by decide⟩
    (prefixPartial 11 285384) = some ⟨11, 2, 0, 1502796, 285384, 2637, 262144⟩ := by
  decide +kernel

theorem context_11_285384_1502796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285384 ⟨1502796, by decide⟩ :=
  accepted_of_selected 11 285384 ⟨1502796, by decide⟩ ⟨11, 2, 0, 1502796, 285384, 2637, 262144⟩
    (by decide) selected_cut_51915

theorem selected_cut_51916 : selected 10 ⟨1502842, by decide⟩
    (prefixPartial 11 285385) = some ⟨11, 2, 0, 1502842, 285385, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_285385_1502842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285385 ⟨1502842, by decide⟩ :=
  accepted_of_selected 11 285385 ⟨1502842, by decide⟩ ⟨11, 2, 0, 1502842, 285385, 2541, 262144⟩
    (by decide) selected_cut_51916

theorem selected_cut_51917 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285386) = some ⟨11, 1, 0, 1468743, 285386, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285386_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285386 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285386 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285386, 1, 262144⟩
    (by decide) selected_cut_51917

theorem selected_cut_51918 : selected 10 ⟨1502882, by decide⟩
    (prefixPartial 11 285387) = some ⟨11, 2, 0, 1502882, 285387, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_285387_1502882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285387 ⟨1502882, by decide⟩ :=
  accepted_of_selected 11 285387 ⟨1502882, by decide⟩ ⟨11, 2, 0, 1502882, 285387, 2361, 262144⟩
    (by decide) selected_cut_51918

theorem unmarked_context_10_71346_1502883 : frontier 11 ⟨1502883, by decide⟩
    (prefixCache 10 71346) (prefixPartial 10 71346) = false := by
  decide +kernel

theorem node_context_10_71346_1502883 : EJMOriginalGlobalDAGData.nodes 11 ⟨1502883, by decide⟩ =
    .split (coordinate 10) (![⟨1502796, by decide⟩,⟨1502842, by decide⟩,⟨1468743, by decide⟩,⟨1502882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71346_1502883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71346 ⟨1502883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71346
    ⟨1502883, by decide⟩ (by decide) (![⟨1502796, by decide⟩,⟨1502842, by decide⟩,⟨1468743, by decide⟩,⟨1502882, by decide⟩]) unmarked_context_10_71346_1502883 node_context_10_71346_1502883
  intro a
  fin_cases a
  · exact context_11_285384_1502796
  · exact context_11_285385_1502842
  · exact context_11_285386_1468743
  · exact context_11_285387_1502882

theorem selected_cut_51919 : selected 9 ⟨1470651, by decide⟩
    (prefixPartial 12 1141552) = some ⟨12, 1, 0, 1470651, 1141552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1141552_1470651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1141552 ⟨1470651, by decide⟩ :=
  accepted_of_selected 12 1141552 ⟨1470651, by decide⟩ ⟨12, 1, 0, 1470651, 1141552, 1, 65536⟩
    (by decide) selected_cut_51919

theorem selected_cut_51920 : selected 9 ⟨1502911, by decide⟩
    (prefixPartial 12 1141553) = some ⟨12, 2, 0, 1502911, 1141553, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_1141553_1502911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1141553 ⟨1502911, by decide⟩ :=
  accepted_of_selected 12 1141553 ⟨1502911, by decide⟩ ⟨12, 2, 0, 1502911, 1141553, 1377, 65536⟩
    (by decide) selected_cut_51920

theorem selected_cut_51921 : selected 9 ⟨1502942, by decide⟩
    (prefixPartial 12 1141554) = some ⟨12, 2, 0, 1502942, 1141554, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_1141554_1502942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1141554 ⟨1502942, by decide⟩ :=
  accepted_of_selected 12 1141554 ⟨1502942, by decide⟩ ⟨12, 2, 0, 1502942, 1141554, 1397, 65536⟩
    (by decide) selected_cut_51921

theorem selected_cut_51922 : selected 9 ⟨1502971, by decide⟩
    (prefixPartial 12 1141555) = some ⟨12, 2, 0, 1502971, 1141555, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_1141555_1502971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1141555 ⟨1502971, by decide⟩ :=
  accepted_of_selected 12 1141555 ⟨1502971, by decide⟩ ⟨12, 2, 0, 1502971, 1141555, 1429, 65536⟩
    (by decide) selected_cut_51922

theorem unmarked_context_11_285388_1502972 : frontier 10 ⟨1502972, by decide⟩
    (prefixCache 11 285388) (prefixPartial 11 285388) = false := by
  decide +kernel

theorem node_context_11_285388_1502972 : EJMOriginalGlobalDAGData.nodes 10 ⟨1502972, by decide⟩ =
    .split (coordinate 11) (![⟨1470651, by decide⟩,⟨1502911, by decide⟩,⟨1502942, by decide⟩,⟨1502971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_285388_1502972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285388 ⟨1502972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 285388
    ⟨1502972, by decide⟩ (by decide) (![⟨1470651, by decide⟩,⟨1502911, by decide⟩,⟨1502942, by decide⟩,⟨1502971, by decide⟩]) unmarked_context_11_285388_1502972 node_context_11_285388_1502972
  intro a
  fin_cases a
  · exact context_12_1141552_1470651
  · exact context_12_1141553_1502911
  · exact context_12_1141554_1502942
  · exact context_12_1141555_1502971

theorem selected_cut_51923 : selected 10 ⟨1503029, by decide⟩
    (prefixPartial 11 285389) = some ⟨11, 2, 0, 1503029, 285389, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_285389_1503029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285389 ⟨1503029, by decide⟩ :=
  accepted_of_selected 11 285389 ⟨1503029, by decide⟩ ⟨11, 2, 0, 1503029, 285389, 2549, 262144⟩
    (by decide) selected_cut_51923

theorem selected_cut_51924 : selected 10 ⟨1503087, by decide⟩
    (prefixPartial 11 285390) = some ⟨11, 2, 0, 1503087, 285390, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_285390_1503087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285390 ⟨1503087, by decide⟩ :=
  accepted_of_selected 11 285390 ⟨1503087, by decide⟩ ⟨11, 2, 0, 1503087, 285390, 1533, 262144⟩
    (by decide) selected_cut_51924

theorem selected_cut_51925 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285391) = some ⟨11, 1, 0, 1470044, 285391, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285391_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285391 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285391 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285391, 1, 262144⟩
    (by decide) selected_cut_51925

theorem unmarked_context_10_71347_1503088 : frontier 11 ⟨1503088, by decide⟩
    (prefixCache 10 71347) (prefixPartial 10 71347) = false := by
  decide +kernel

theorem node_context_10_71347_1503088 : EJMOriginalGlobalDAGData.nodes 11 ⟨1503088, by decide⟩ =
    .split (coordinate 10) (![⟨1502972, by decide⟩,⟨1503029, by decide⟩,⟨1503087, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71347_1503088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71347 ⟨1503088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71347
    ⟨1503088, by decide⟩ (by decide) (![⟨1502972, by decide⟩,⟨1503029, by decide⟩,⟨1503087, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71347_1503088 node_context_10_71347_1503088
  intro a
  fin_cases a
  · exact context_11_285388_1502972
  · exact context_11_285389_1503029
  · exact context_11_285390_1503087
  · exact context_11_285391_1470044

theorem unmarked_context_9_17836_1503089 : frontier 12 ⟨1503089, by decide⟩
    (prefixCache 9 17836) (prefixPartial 9 17836) = false := by
  decide +kernel

theorem node_context_9_17836_1503089 : EJMOriginalGlobalDAGData.nodes 12 ⟨1503089, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1502707, by decide⟩,⟨1502883, by decide⟩,⟨1503088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17836_1503089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17836 ⟨1503089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17836
    ⟨1503089, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1502707, by decide⟩,⟨1502883, by decide⟩,⟨1503088, by decide⟩]) unmarked_context_9_17836_1503089 node_context_9_17836_1503089
  intro a
  fin_cases a
  · exact context_10_71344_1468246
  · exact context_10_71345_1502707
  · exact context_10_71346_1502883
  · exact context_10_71347_1503088

theorem selected_cut_51926 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 285392) = some ⟨11, 1, 0, 434745, 285392, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285392_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285392 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 285392 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 285392, 1, 262144⟩
    (by decide) selected_cut_51926

theorem selected_cut_51927 : selected 10 ⟨1503125, by decide⟩
    (prefixPartial 11 285393) = some ⟨11, 2, 0, 1503125, 285393, 1601, 262144⟩ := by
  decide +kernel

theorem context_11_285393_1503125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285393 ⟨1503125, by decide⟩ :=
  accepted_of_selected 11 285393 ⟨1503125, by decide⟩ ⟨11, 2, 0, 1503125, 285393, 1601, 262144⟩
    (by decide) selected_cut_51927

theorem selected_cut_51928 : selected 10 ⟨1503156, by decide⟩
    (prefixPartial 11 285394) = some ⟨11, 2, 0, 1503156, 285394, 1509, 262144⟩ := by
  decide +kernel

theorem context_11_285394_1503156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285394 ⟨1503156, by decide⟩ :=
  accepted_of_selected 11 285394 ⟨1503156, by decide⟩ ⟨11, 2, 0, 1503156, 285394, 1509, 262144⟩
    (by decide) selected_cut_51928

theorem selected_cut_51929 : selected 10 ⟨1503175, by decide⟩
    (prefixPartial 11 285395) = some ⟨11, 2, 0, 1503175, 285395, 997, 262144⟩ := by
  decide +kernel

theorem context_11_285395_1503175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285395 ⟨1503175, by decide⟩ :=
  accepted_of_selected 11 285395 ⟨1503175, by decide⟩ ⟨11, 2, 0, 1503175, 285395, 997, 262144⟩
    (by decide) selected_cut_51929

theorem unmarked_context_10_71348_1503176 : frontier 11 ⟨1503176, by decide⟩
    (prefixCache 10 71348) (prefixPartial 10 71348) = false := by
  decide +kernel

theorem node_context_10_71348_1503176 : EJMOriginalGlobalDAGData.nodes 11 ⟨1503176, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1503125, by decide⟩,⟨1503156, by decide⟩,⟨1503175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71348_1503176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71348 ⟨1503176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71348
    ⟨1503176, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1503125, by decide⟩,⟨1503156, by decide⟩,⟨1503175, by decide⟩]) unmarked_context_10_71348_1503176 node_context_10_71348_1503176
  intro a
  fin_cases a
  · exact context_11_285392_434745
  · exact context_11_285393_1503125
  · exact context_11_285394_1503156
  · exact context_11_285395_1503175

theorem selected_cut_51930 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71349) = some ⟨10, 1, 0, 1468874, 71349, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71349_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71349 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71349 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71349, 1, 1048576⟩
    (by decide) selected_cut_51930

theorem selected_cut_51931 : selected 11 ⟨1503292, by decide⟩
    (prefixPartial 10 71350) = some ⟨10, 2, 0, 1503292, 71350, 4085, 1048576⟩ := by
  decide +kernel

theorem context_10_71350_1503292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71350 ⟨1503292, by decide⟩ :=
  accepted_of_selected 10 71350 ⟨1503292, by decide⟩ ⟨10, 2, 0, 1503292, 71350, 4085, 1048576⟩
    (by decide) selected_cut_51931

theorem selected_cut_51932 : selected 11 ⟨1503366, by decide⟩
    (prefixPartial 10 71351) = some ⟨10, 2, 0, 1503366, 71351, 3985, 1048576⟩ := by
  decide +kernel

theorem context_10_71351_1503366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71351 ⟨1503366, by decide⟩ :=
  accepted_of_selected 10 71351 ⟨1503366, by decide⟩ ⟨10, 2, 0, 1503366, 71351, 3985, 1048576⟩
    (by decide) selected_cut_51932

theorem unmarked_context_9_17837_1503367 : frontier 12 ⟨1503367, by decide⟩
    (prefixCache 9 17837) (prefixPartial 9 17837) = false := by
  decide +kernel

theorem node_context_9_17837_1503367 : EJMOriginalGlobalDAGData.nodes 12 ⟨1503367, by decide⟩ =
    .split (coordinate 9) (![⟨1503176, by decide⟩,⟨1468874, by decide⟩,⟨1503292, by decide⟩,⟨1503366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17837_1503367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17837 ⟨1503367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17837
    ⟨1503367, by decide⟩ (by decide) (![⟨1503176, by decide⟩,⟨1468874, by decide⟩,⟨1503292, by decide⟩,⟨1503366, by decide⟩]) unmarked_context_9_17837_1503367 node_context_9_17837_1503367
  intro a
  fin_cases a
  · exact context_10_71348_1503176
  · exact context_10_71349_1468874
  · exact context_10_71350_1503292
  · exact context_10_71351_1503366

theorem selected_cut_51933 : selected 11 ⟨1503418, by decide⟩
    (prefixPartial 10 71352) = some ⟨10, 2, 0, 1503418, 71352, 2721, 1048576⟩ := by
  decide +kernel

theorem context_10_71352_1503418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71352 ⟨1503418, by decide⟩ :=
  accepted_of_selected 10 71352 ⟨1503418, by decide⟩ ⟨10, 2, 0, 1503418, 71352, 2721, 1048576⟩
    (by decide) selected_cut_51933

theorem selected_cut_51934 : selected 11 ⟨1503476, by decide⟩
    (prefixPartial 10 71353) = some ⟨10, 2, 0, 1503476, 71353, 3029, 1048576⟩ := by
  decide +kernel

theorem context_10_71353_1503476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71353 ⟨1503476, by decide⟩ :=
  accepted_of_selected 10 71353 ⟨1503476, by decide⟩ ⟨10, 2, 0, 1503476, 71353, 3029, 1048576⟩
    (by decide) selected_cut_51934

theorem selected_cut_51935 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71354) = some ⟨10, 1, 0, 1469103, 71354, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71354_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71354 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71354 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71354, 1, 1048576⟩
    (by decide) selected_cut_51935

theorem selected_cut_51936 : selected 11 ⟨1503534, by decide⟩
    (prefixPartial 10 71355) = some ⟨10, 2, 0, 1503534, 71355, 2101, 1048576⟩ := by
  decide +kernel

theorem context_10_71355_1503534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71355 ⟨1503534, by decide⟩ :=
  accepted_of_selected 10 71355 ⟨1503534, by decide⟩ ⟨10, 2, 0, 1503534, 71355, 2101, 1048576⟩
    (by decide) selected_cut_51936

theorem unmarked_context_9_17838_1503535 : frontier 12 ⟨1503535, by decide⟩
    (prefixCache 9 17838) (prefixPartial 9 17838) = false := by
  decide +kernel

theorem node_context_9_17838_1503535 : EJMOriginalGlobalDAGData.nodes 12 ⟨1503535, by decide⟩ =
    .split (coordinate 9) (![⟨1503418, by decide⟩,⟨1503476, by decide⟩,⟨1469103, by decide⟩,⟨1503534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17838_1503535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17838 ⟨1503535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17838
    ⟨1503535, by decide⟩ (by decide) (![⟨1503418, by decide⟩,⟨1503476, by decide⟩,⟨1469103, by decide⟩,⟨1503534, by decide⟩]) unmarked_context_9_17838_1503535 node_context_9_17838_1503535
  intro a
  fin_cases a
  · exact context_10_71352_1503418
  · exact context_10_71353_1503476
  · exact context_10_71354_1469103
  · exact context_10_71355_1503534

theorem selected_cut_51937 : selected 12 ⟨1503608, by decide⟩
    (prefixPartial 9 17839) = some ⟨9, 2, 0, 1503608, 17839, 2381, 4194304⟩ := by
  decide +kernel

theorem context_9_17839_1503608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17839 ⟨1503608, by decide⟩ :=
  accepted_of_selected 9 17839 ⟨1503608, by decide⟩ ⟨9, 2, 0, 1503608, 17839, 2381, 4194304⟩
    (by decide) selected_cut_51937

theorem unmarked_context_8_4459_1503609 : frontier 13 ⟨1503609, by decide⟩
    (prefixCache 8 4459) (prefixPartial 8 4459) = false := by
  decide +kernel

theorem node_context_8_4459_1503609 : EJMOriginalGlobalDAGData.nodes 13 ⟨1503609, by decide⟩ =
    .split (coordinate 8) (![⟨1503089, by decide⟩,⟨1503367, by decide⟩,⟨1503535, by decide⟩,⟨1503608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4459_1503609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4459 ⟨1503609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4459
    ⟨1503609, by decide⟩ (by decide) (![⟨1503089, by decide⟩,⟨1503367, by decide⟩,⟨1503535, by decide⟩,⟨1503608, by decide⟩]) unmarked_context_8_4459_1503609 node_context_8_4459_1503609
  intro a
  fin_cases a
  · exact context_9_17836_1503089
  · exact context_9_17837_1503367
  · exact context_9_17838_1503535
  · exact context_9_17839_1503608

theorem unmarked_context_7_1114_1503610 : frontier 14 ⟨1503610, by decide⟩
    (prefixCache 7 1114) (prefixPartial 7 1114) = false := by
  decide +kernel

theorem node_context_7_1114_1503610 : EJMOriginalGlobalDAGData.nodes 14 ⟨1503610, by decide⟩ =
    .split (coordinate 7) (![⟨1501636, by decide⟩,⟨1502489, by decide⟩,⟨1502490, by decide⟩,⟨1503609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1114_1503610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1114 ⟨1503610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1114
    ⟨1503610, by decide⟩ (by decide) (![⟨1501636, by decide⟩,⟨1502489, by decide⟩,⟨1502490, by decide⟩,⟨1503609, by decide⟩]) unmarked_context_7_1114_1503610 node_context_7_1114_1503610
  intro a
  fin_cases a
  · exact context_8_4456_1501636
  · exact context_8_4457_1502489
  · exact context_8_4458_1502490
  · exact context_8_4459_1503609

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
