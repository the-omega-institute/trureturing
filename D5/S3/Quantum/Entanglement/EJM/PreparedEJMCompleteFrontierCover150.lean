/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover149
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14404 : selected 8 ⟨372175, by decide⟩
    (prefixPartial 13 108796) = some ⟨13, 2, 0, 372175, 108796, 81, 16384⟩ := by
  decide +kernel

theorem context_13_108796_372175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108796 ⟨372175, by decide⟩ :=
  accepted_of_selected 13 108796 ⟨372175, by decide⟩ ⟨13, 2, 0, 372175, 108796, 81, 16384⟩
    (by decide) selected_cut_14404

theorem selected_cut_14405 : selected 8 ⟨372201, by decide⟩
    (prefixPartial 13 108797) = some ⟨13, 2, 0, 372201, 108797, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_108797_372201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108797 ⟨372201, by decide⟩ :=
  accepted_of_selected 13 108797 ⟨372201, by decide⟩ ⟨13, 2, 0, 372201, 108797, 2501, 16384⟩
    (by decide) selected_cut_14405

theorem selected_cut_14406 : selected 8 ⟨372215, by decide⟩
    (prefixPartial 13 108798) = some ⟨13, 2, 0, 372215, 108798, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_108798_372215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108798 ⟨372215, by decide⟩ :=
  accepted_of_selected 13 108798 ⟨372215, by decide⟩ ⟨13, 2, 0, 372215, 108798, 1377, 16384⟩
    (by decide) selected_cut_14406

theorem selected_cut_14407 : selected 8 ⟨372220, by decide⟩
    (prefixPartial 13 108799) = some ⟨13, 2, 0, 372220, 108799, 949, 16384⟩ := by
  decide +kernel

theorem context_13_108799_372220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108799 ⟨372220, by decide⟩ :=
  accepted_of_selected 13 108799 ⟨372220, by decide⟩ ⟨13, 2, 0, 372220, 108799, 949, 16384⟩
    (by decide) selected_cut_14407

theorem unmarked_context_12_27199_372221 : frontier 9 ⟨372221, by decide⟩
    (prefixCache 12 27199) (prefixPartial 12 27199) = false := by
  decide +kernel

theorem node_context_12_27199_372221 : EJMOriginalGlobalDAGData.nodes 9 ⟨372221, by decide⟩ =
    .split (coordinate 12) (![⟨372175, by decide⟩,⟨372201, by decide⟩,⟨372215, by decide⟩,⟨372220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27199_372221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27199 ⟨372221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27199
    ⟨372221, by decide⟩ (by decide) (![⟨372175, by decide⟩,⟨372201, by decide⟩,⟨372215, by decide⟩,⟨372220, by decide⟩]) unmarked_context_12_27199_372221 node_context_12_27199_372221
  intro a
  fin_cases a
  · exact context_13_108796_372175
  · exact context_13_108797_372201
  · exact context_13_108798_372215
  · exact context_13_108799_372220

theorem unmarked_context_11_6799_372222 : frontier 10 ⟨372222, by decide⟩
    (prefixCache 11 6799) (prefixPartial 11 6799) = false := by
  decide +kernel

theorem node_context_11_6799_372222 : EJMOriginalGlobalDAGData.nodes 10 ⟨372222, by decide⟩ =
    .split (coordinate 11) (![⟨372064, by decide⟩,⟨372117, by decide⟩,⟨372171, by decide⟩,⟨372221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6799_372222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6799 ⟨372222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6799
    ⟨372222, by decide⟩ (by decide) (![⟨372064, by decide⟩,⟨372117, by decide⟩,⟨372171, by decide⟩,⟨372221, by decide⟩]) unmarked_context_11_6799_372222 node_context_11_6799_372222
  intro a
  fin_cases a
  · exact context_12_27196_372064
  · exact context_12_27197_372117
  · exact context_12_27198_372171
  · exact context_12_27199_372221

theorem unmarked_context_10_1699_372223 : frontier 11 ⟨372223, by decide⟩
    (prefixCache 10 1699) (prefixPartial 10 1699) = false := by
  decide +kernel

theorem node_context_10_1699_372223 : EJMOriginalGlobalDAGData.nodes 11 ⟨372223, by decide⟩ =
    .split (coordinate 10) (![⟨371508, by decide⟩,⟨371728, by decide⟩,⟨372016, by decide⟩,⟨372222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1699_372223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1699 ⟨372223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1699
    ⟨372223, by decide⟩ (by decide) (![⟨371508, by decide⟩,⟨371728, by decide⟩,⟨372016, by decide⟩,⟨372222, by decide⟩]) unmarked_context_10_1699_372223 node_context_10_1699_372223
  intro a
  fin_cases a
  · exact context_11_6796_371508
  · exact context_11_6797_371728
  · exact context_11_6798_372016
  · exact context_11_6799_372222

theorem unmarked_context_9_424_372224 : frontier 12 ⟨372224, by decide⟩
    (prefixCache 9 424) (prefixPartial 9 424) = false := by
  decide +kernel

theorem node_context_9_424_372224 : EJMOriginalGlobalDAGData.nodes 12 ⟨372224, by decide⟩ =
    .split (coordinate 9) (![⟨368957, by decide⟩,⟨370268, by decide⟩,⟨371250, by decide⟩,⟨372223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_424_372224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 424 ⟨372224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 424
    ⟨372224, by decide⟩ (by decide) (![⟨368957, by decide⟩,⟨370268, by decide⟩,⟨371250, by decide⟩,⟨372223, by decide⟩]) unmarked_context_9_424_372224 node_context_9_424_372224
  intro a
  fin_cases a
  · exact context_10_1696_368957
  · exact context_10_1697_370268
  · exact context_10_1698_371250
  · exact context_10_1699_372223

theorem selected_cut_14408 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108800) = some ⟨13, 1, 0, 3444, 108800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108800, 1, 16384⟩
    (by decide) selected_cut_14408

theorem selected_cut_14409 : selected 8 ⟨372260, by decide⟩
    (prefixPartial 13 108801) = some ⟨13, 2, 0, 372260, 108801, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_108801_372260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108801 ⟨372260, by decide⟩ :=
  accepted_of_selected 13 108801 ⟨372260, by decide⟩ ⟨13, 2, 0, 372260, 108801, 2957, 16384⟩
    (by decide) selected_cut_14409

theorem selected_cut_14410 : selected 8 ⟨372278, by decide⟩
    (prefixPartial 13 108802) = some ⟨13, 2, 0, 372278, 108802, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_108802_372278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108802 ⟨372278, by decide⟩ :=
  accepted_of_selected 13 108802 ⟨372278, by decide⟩ ⟨13, 2, 0, 372278, 108802, 1261, 16384⟩
    (by decide) selected_cut_14410

theorem selected_cut_14411 : selected 8 ⟨372285, by decide⟩
    (prefixPartial 13 108803) = some ⟨13, 2, 0, 372285, 108803, 853, 16384⟩ := by
  decide +kernel

theorem context_13_108803_372285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108803 ⟨372285, by decide⟩ :=
  accepted_of_selected 13 108803 ⟨372285, by decide⟩ ⟨13, 2, 0, 372285, 108803, 853, 16384⟩
    (by decide) selected_cut_14411

theorem unmarked_context_12_27200_372286 : frontier 9 ⟨372286, by decide⟩
    (prefixCache 12 27200) (prefixPartial 12 27200) = false := by
  decide +kernel

theorem node_context_12_27200_372286 : EJMOriginalGlobalDAGData.nodes 9 ⟨372286, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372260, by decide⟩,⟨372278, by decide⟩,⟨372285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27200_372286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27200 ⟨372286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27200
    ⟨372286, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372260, by decide⟩,⟨372278, by decide⟩,⟨372285, by decide⟩]) unmarked_context_12_27200_372286 node_context_12_27200_372286
  intro a
  fin_cases a
  · exact context_13_108800_3444
  · exact context_13_108801_372260
  · exact context_13_108802_372278
  · exact context_13_108803_372285

theorem selected_cut_14412 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108804) = some ⟨13, 1, 0, 3444, 108804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108804, 1, 16384⟩
    (by decide) selected_cut_14412

theorem selected_cut_14413 : selected 8 ⟨372361, by decide⟩
    (prefixPartial 13 108805) = some ⟨13, 2, 0, 372361, 108805, 4065, 16384⟩ := by
  decide +kernel

theorem context_13_108805_372361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108805 ⟨372361, by decide⟩ :=
  accepted_of_selected 13 108805 ⟨372361, by decide⟩ ⟨13, 2, 0, 372361, 108805, 4065, 16384⟩
    (by decide) selected_cut_14413

theorem selected_cut_14414 : selected 8 ⟨372382, by decide⟩
    (prefixPartial 13 108806) = some ⟨13, 2, 0, 372382, 108806, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_108806_372382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108806 ⟨372382, by decide⟩ :=
  accepted_of_selected 13 108806 ⟨372382, by decide⟩ ⟨13, 2, 0, 372382, 108806, 1653, 16384⟩
    (by decide) selected_cut_14414

theorem selected_cut_14415 : selected 8 ⟨372393, by decide⟩
    (prefixPartial 13 108807) = some ⟨13, 2, 0, 372393, 108807, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_108807_372393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108807 ⟨372393, by decide⟩ :=
  accepted_of_selected 13 108807 ⟨372393, by decide⟩ ⟨13, 2, 0, 372393, 108807, 1241, 16384⟩
    (by decide) selected_cut_14415

theorem unmarked_context_12_27201_372394 : frontier 9 ⟨372394, by decide⟩
    (prefixCache 12 27201) (prefixPartial 12 27201) = false := by
  decide +kernel

theorem node_context_12_27201_372394 : EJMOriginalGlobalDAGData.nodes 9 ⟨372394, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372361, by decide⟩,⟨372382, by decide⟩,⟨372393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27201_372394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27201 ⟨372394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27201
    ⟨372394, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372361, by decide⟩,⟨372382, by decide⟩,⟨372393, by decide⟩]) unmarked_context_12_27201_372394 node_context_12_27201_372394
  intro a
  fin_cases a
  · exact context_13_108804_3444
  · exact context_13_108805_372361
  · exact context_13_108806_372382
  · exact context_13_108807_372393

theorem selected_cut_14416 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108808) = some ⟨13, 1, 0, 3444, 108808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108808, 1, 16384⟩
    (by decide) selected_cut_14416

theorem selected_cut_14417 : selected 8 ⟨372432, by decide⟩
    (prefixPartial 13 108809) = some ⟨13, 2, 0, 372432, 108809, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_108809_372432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108809 ⟨372432, by decide⟩ :=
  accepted_of_selected 13 108809 ⟨372432, by decide⟩ ⟨13, 2, 0, 372432, 108809, 2789, 16384⟩
    (by decide) selected_cut_14417

theorem selected_cut_14418 : selected 8 ⟨372452, by decide⟩
    (prefixPartial 13 108810) = some ⟨13, 2, 0, 372452, 108810, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_108810_372452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108810 ⟨372452, by decide⟩ :=
  accepted_of_selected 13 108810 ⟨372452, by decide⟩ ⟨13, 2, 0, 372452, 108810, 1233, 16384⟩
    (by decide) selected_cut_14418

theorem selected_cut_14419 : selected 8 ⟨372457, by decide⟩
    (prefixPartial 13 108811) = some ⟨13, 2, 0, 372457, 108811, 845, 16384⟩ := by
  decide +kernel

theorem context_13_108811_372457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108811 ⟨372457, by decide⟩ :=
  accepted_of_selected 13 108811 ⟨372457, by decide⟩ ⟨13, 2, 0, 372457, 108811, 845, 16384⟩
    (by decide) selected_cut_14419

theorem unmarked_context_12_27202_372458 : frontier 9 ⟨372458, by decide⟩
    (prefixCache 12 27202) (prefixPartial 12 27202) = false := by
  decide +kernel

theorem node_context_12_27202_372458 : EJMOriginalGlobalDAGData.nodes 9 ⟨372458, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372432, by decide⟩,⟨372452, by decide⟩,⟨372457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27202_372458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27202 ⟨372458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27202
    ⟨372458, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372432, by decide⟩,⟨372452, by decide⟩,⟨372457, by decide⟩]) unmarked_context_12_27202_372458 node_context_12_27202_372458
  intro a
  fin_cases a
  · exact context_13_108808_3444
  · exact context_13_108809_372432
  · exact context_13_108810_372452
  · exact context_13_108811_372457

theorem selected_cut_14420 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108812) = some ⟨13, 1, 0, 3444, 108812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108812, 1, 16384⟩
    (by decide) selected_cut_14420

theorem selected_cut_14421 : selected 8 ⟨372512, by decide⟩
    (prefixPartial 13 108813) = some ⟨13, 2, 0, 372512, 108813, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_108813_372512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108813 ⟨372512, by decide⟩ :=
  accepted_of_selected 13 108813 ⟨372512, by decide⟩ ⟨13, 2, 0, 372512, 108813, 3161, 16384⟩
    (by decide) selected_cut_14421

theorem selected_cut_14422 : selected 8 ⟨372529, by decide⟩
    (prefixPartial 13 108814) = some ⟨13, 2, 0, 372529, 108814, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_108814_372529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108814 ⟨372529, by decide⟩ :=
  accepted_of_selected 13 108814 ⟨372529, by decide⟩ ⟨13, 2, 0, 372529, 108814, 1401, 16384⟩
    (by decide) selected_cut_14422

theorem selected_cut_14423 : selected 8 ⟨372537, by decide⟩
    (prefixPartial 13 108815) = some ⟨13, 2, 0, 372537, 108815, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_108815_372537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108815 ⟨372537, by decide⟩ :=
  accepted_of_selected 13 108815 ⟨372537, by decide⟩ ⟨13, 2, 0, 372537, 108815, 1009, 16384⟩
    (by decide) selected_cut_14423

theorem unmarked_context_12_27203_372538 : frontier 9 ⟨372538, by decide⟩
    (prefixCache 12 27203) (prefixPartial 12 27203) = false := by
  decide +kernel

theorem node_context_12_27203_372538 : EJMOriginalGlobalDAGData.nodes 9 ⟨372538, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372512, by decide⟩,⟨372529, by decide⟩,⟨372537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27203_372538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27203 ⟨372538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27203
    ⟨372538, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372512, by decide⟩,⟨372529, by decide⟩,⟨372537, by decide⟩]) unmarked_context_12_27203_372538 node_context_12_27203_372538
  intro a
  fin_cases a
  · exact context_13_108812_3444
  · exact context_13_108813_372512
  · exact context_13_108814_372529
  · exact context_13_108815_372537

theorem unmarked_context_11_6800_372539 : frontier 10 ⟨372539, by decide⟩
    (prefixCache 11 6800) (prefixPartial 11 6800) = false := by
  decide +kernel

theorem node_context_11_6800_372539 : EJMOriginalGlobalDAGData.nodes 10 ⟨372539, by decide⟩ =
    .split (coordinate 11) (![⟨372286, by decide⟩,⟨372394, by decide⟩,⟨372458, by decide⟩,⟨372538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6800_372539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6800 ⟨372539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6800
    ⟨372539, by decide⟩ (by decide) (![⟨372286, by decide⟩,⟨372394, by decide⟩,⟨372458, by decide⟩,⟨372538, by decide⟩]) unmarked_context_11_6800_372539 node_context_11_6800_372539
  intro a
  fin_cases a
  · exact context_12_27200_372286
  · exact context_12_27201_372394
  · exact context_12_27202_372458
  · exact context_12_27203_372538

theorem selected_cut_14424 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108816) = some ⟨13, 1, 0, 3444, 108816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108816, 1, 16384⟩
    (by decide) selected_cut_14424

theorem selected_cut_14425 : selected 8 ⟨372591, by decide⟩
    (prefixPartial 13 108817) = some ⟨13, 2, 0, 372591, 108817, 3057, 16384⟩ := by
  decide +kernel

theorem context_13_108817_372591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108817 ⟨372591, by decide⟩ :=
  accepted_of_selected 13 108817 ⟨372591, by decide⟩ ⟨13, 2, 0, 372591, 108817, 3057, 16384⟩
    (by decide) selected_cut_14425

theorem selected_cut_14426 : selected 8 ⟨372612, by decide⟩
    (prefixPartial 13 108818) = some ⟨13, 2, 0, 372612, 108818, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_108818_372612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108818 ⟨372612, by decide⟩ :=
  accepted_of_selected 13 108818 ⟨372612, by decide⟩ ⟨13, 2, 0, 372612, 108818, 1553, 16384⟩
    (by decide) selected_cut_14426

theorem selected_cut_14427 : selected 8 ⟨372622, by decide⟩
    (prefixPartial 13 108819) = some ⟨13, 2, 0, 372622, 108819, 953, 16384⟩ := by
  decide +kernel

theorem context_13_108819_372622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108819 ⟨372622, by decide⟩ :=
  accepted_of_selected 13 108819 ⟨372622, by decide⟩ ⟨13, 2, 0, 372622, 108819, 953, 16384⟩
    (by decide) selected_cut_14427

theorem unmarked_context_12_27204_372623 : frontier 9 ⟨372623, by decide⟩
    (prefixCache 12 27204) (prefixPartial 12 27204) = false := by
  decide +kernel

theorem node_context_12_27204_372623 : EJMOriginalGlobalDAGData.nodes 9 ⟨372623, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372591, by decide⟩,⟨372612, by decide⟩,⟨372622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27204_372623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27204 ⟨372623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27204
    ⟨372623, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372591, by decide⟩,⟨372612, by decide⟩,⟨372622, by decide⟩]) unmarked_context_12_27204_372623 node_context_12_27204_372623
  intro a
  fin_cases a
  · exact context_13_108816_3444
  · exact context_13_108817_372591
  · exact context_13_108818_372612
  · exact context_13_108819_372622

theorem selected_cut_14428 : selected 9 ⟨246771, by decide⟩
    (prefixPartial 12 27205) = some ⟨12, 1, 0, 246771, 27205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27205_246771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27205 ⟨246771, by decide⟩ :=
  accepted_of_selected 12 27205 ⟨246771, by decide⟩ ⟨12, 1, 0, 246771, 27205, 1, 65536⟩
    (by decide) selected_cut_14428

theorem selected_cut_14429 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108824) = some ⟨13, 1, 0, 3444, 108824, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108824_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108824 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108824 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108824, 1, 16384⟩
    (by decide) selected_cut_14429

theorem selected_cut_14430 : selected 8 ⟨372667, by decide⟩
    (prefixPartial 13 108825) = some ⟨13, 2, 0, 372667, 108825, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_108825_372667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108825 ⟨372667, by decide⟩ :=
  accepted_of_selected 13 108825 ⟨372667, by decide⟩ ⟨13, 2, 0, 372667, 108825, 2693, 16384⟩
    (by decide) selected_cut_14430

theorem selected_cut_14431 : selected 8 ⟨372688, by decide⟩
    (prefixPartial 13 108826) = some ⟨13, 2, 0, 372688, 108826, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_108826_372688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108826 ⟨372688, by decide⟩ :=
  accepted_of_selected 13 108826 ⟨372688, by decide⟩ ⟨13, 2, 0, 372688, 108826, 1481, 16384⟩
    (by decide) selected_cut_14431

theorem selected_cut_14432 : selected 8 ⟨372698, by decide⟩
    (prefixPartial 13 108827) = some ⟨13, 2, 0, 372698, 108827, 973, 16384⟩ := by
  decide +kernel

theorem context_13_108827_372698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108827 ⟨372698, by decide⟩ :=
  accepted_of_selected 13 108827 ⟨372698, by decide⟩ ⟨13, 2, 0, 372698, 108827, 973, 16384⟩
    (by decide) selected_cut_14432

theorem unmarked_context_12_27206_372699 : frontier 9 ⟨372699, by decide⟩
    (prefixCache 12 27206) (prefixPartial 12 27206) = false := by
  decide +kernel

theorem node_context_12_27206_372699 : EJMOriginalGlobalDAGData.nodes 9 ⟨372699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372667, by decide⟩,⟨372688, by decide⟩,⟨372698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27206_372699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27206 ⟨372699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27206
    ⟨372699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372667, by decide⟩,⟨372688, by decide⟩,⟨372698, by decide⟩]) unmarked_context_12_27206_372699 node_context_12_27206_372699
  intro a
  fin_cases a
  · exact context_13_108824_3444
  · exact context_13_108825_372667
  · exact context_13_108826_372688
  · exact context_13_108827_372698

theorem selected_cut_14433 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108828) = some ⟨13, 1, 0, 3444, 108828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108828, 1, 16384⟩
    (by decide) selected_cut_14433

theorem selected_cut_14434 : selected 8 ⟨372745, by decide⟩
    (prefixPartial 13 108829) = some ⟨13, 2, 0, 372745, 108829, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_108829_372745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108829 ⟨372745, by decide⟩ :=
  accepted_of_selected 13 108829 ⟨372745, by decide⟩ ⟨13, 2, 0, 372745, 108829, 2909, 16384⟩
    (by decide) selected_cut_14434

theorem selected_cut_14435 : selected 8 ⟨372764, by decide⟩
    (prefixPartial 13 108830) = some ⟨13, 2, 0, 372764, 108830, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_108830_372764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108830 ⟨372764, by decide⟩ :=
  accepted_of_selected 13 108830 ⟨372764, by decide⟩ ⟨13, 2, 0, 372764, 108830, 1585, 16384⟩
    (by decide) selected_cut_14435

theorem selected_cut_14436 : selected 8 ⟨372773, by decide⟩
    (prefixPartial 13 108831) = some ⟨13, 2, 0, 372773, 108831, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_108831_372773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108831 ⟨372773, by decide⟩ :=
  accepted_of_selected 13 108831 ⟨372773, by decide⟩ ⟨13, 2, 0, 372773, 108831, 1085, 16384⟩
    (by decide) selected_cut_14436

theorem unmarked_context_12_27207_372774 : frontier 9 ⟨372774, by decide⟩
    (prefixCache 12 27207) (prefixPartial 12 27207) = false := by
  decide +kernel

theorem node_context_12_27207_372774 : EJMOriginalGlobalDAGData.nodes 9 ⟨372774, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372745, by decide⟩,⟨372764, by decide⟩,⟨372773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27207_372774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27207 ⟨372774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27207
    ⟨372774, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372745, by decide⟩,⟨372764, by decide⟩,⟨372773, by decide⟩]) unmarked_context_12_27207_372774 node_context_12_27207_372774
  intro a
  fin_cases a
  · exact context_13_108828_3444
  · exact context_13_108829_372745
  · exact context_13_108830_372764
  · exact context_13_108831_372773

theorem unmarked_context_11_6801_372775 : frontier 10 ⟨372775, by decide⟩
    (prefixCache 11 6801) (prefixPartial 11 6801) = false := by
  decide +kernel

theorem node_context_11_6801_372775 : EJMOriginalGlobalDAGData.nodes 10 ⟨372775, by decide⟩ =
    .split (coordinate 11) (![⟨372623, by decide⟩,⟨246771, by decide⟩,⟨372699, by decide⟩,⟨372774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6801_372775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6801 ⟨372775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6801
    ⟨372775, by decide⟩ (by decide) (![⟨372623, by decide⟩,⟨246771, by decide⟩,⟨372699, by decide⟩,⟨372774, by decide⟩]) unmarked_context_11_6801_372775 node_context_11_6801_372775
  intro a
  fin_cases a
  · exact context_12_27204_372623
  · exact context_12_27205_246771
  · exact context_12_27206_372699
  · exact context_12_27207_372774

theorem selected_cut_14437 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108832) = some ⟨13, 1, 0, 3444, 108832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108832, 1, 16384⟩
    (by decide) selected_cut_14437

theorem selected_cut_14438 : selected 8 ⟨372808, by decide⟩
    (prefixPartial 13 108833) = some ⟨13, 2, 0, 372808, 108833, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_108833_372808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108833 ⟨372808, by decide⟩ :=
  accepted_of_selected 13 108833 ⟨372808, by decide⟩ ⟨13, 2, 0, 372808, 108833, 2245, 16384⟩
    (by decide) selected_cut_14438

theorem selected_cut_14439 : selected 8 ⟨372826, by decide⟩
    (prefixPartial 13 108834) = some ⟨13, 2, 0, 372826, 108834, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_108834_372826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108834 ⟨372826, by decide⟩ :=
  accepted_of_selected 13 108834 ⟨372826, by decide⟩ ⟨13, 2, 0, 372826, 108834, 1277, 16384⟩
    (by decide) selected_cut_14439

theorem selected_cut_14440 : selected 8 ⟨372837, by decide⟩
    (prefixPartial 13 108835) = some ⟨13, 2, 0, 372837, 108835, 885, 16384⟩ := by
  decide +kernel

theorem context_13_108835_372837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108835 ⟨372837, by decide⟩ :=
  accepted_of_selected 13 108835 ⟨372837, by decide⟩ ⟨13, 2, 0, 372837, 108835, 885, 16384⟩
    (by decide) selected_cut_14440

theorem unmarked_context_12_27208_372838 : frontier 9 ⟨372838, by decide⟩
    (prefixCache 12 27208) (prefixPartial 12 27208) = false := by
  decide +kernel

theorem node_context_12_27208_372838 : EJMOriginalGlobalDAGData.nodes 9 ⟨372838, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372808, by decide⟩,⟨372826, by decide⟩,⟨372837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27208_372838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27208 ⟨372838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27208
    ⟨372838, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372808, by decide⟩,⟨372826, by decide⟩,⟨372837, by decide⟩]) unmarked_context_12_27208_372838 node_context_12_27208_372838
  intro a
  fin_cases a
  · exact context_13_108832_3444
  · exact context_13_108833_372808
  · exact context_13_108834_372826
  · exact context_13_108835_372837

theorem selected_cut_14441 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108836) = some ⟨13, 1, 0, 3444, 108836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108836, 1, 16384⟩
    (by decide) selected_cut_14441

theorem selected_cut_14442 : selected 8 ⟨372883, by decide⟩
    (prefixPartial 13 108837) = some ⟨13, 2, 0, 372883, 108837, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_108837_372883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108837 ⟨372883, by decide⟩ :=
  accepted_of_selected 13 108837 ⟨372883, by decide⟩ ⟨13, 2, 0, 372883, 108837, 2861, 16384⟩
    (by decide) selected_cut_14442

theorem selected_cut_14443 : selected 8 ⟨372902, by decide⟩
    (prefixPartial 13 108838) = some ⟨13, 2, 0, 372902, 108838, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_108838_372902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108838 ⟨372902, by decide⟩ :=
  accepted_of_selected 13 108838 ⟨372902, by decide⟩ ⟨13, 2, 0, 372902, 108838, 1625, 16384⟩
    (by decide) selected_cut_14443

theorem selected_cut_14444 : selected 8 ⟨372915, by decide⟩
    (prefixPartial 13 108839) = some ⟨13, 2, 0, 372915, 108839, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_108839_372915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108839 ⟨372915, by decide⟩ :=
  accepted_of_selected 13 108839 ⟨372915, by decide⟩ ⟨13, 2, 0, 372915, 108839, 1233, 16384⟩
    (by decide) selected_cut_14444

theorem unmarked_context_12_27209_372916 : frontier 9 ⟨372916, by decide⟩
    (prefixCache 12 27209) (prefixPartial 12 27209) = false := by
  decide +kernel

theorem node_context_12_27209_372916 : EJMOriginalGlobalDAGData.nodes 9 ⟨372916, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372883, by decide⟩,⟨372902, by decide⟩,⟨372915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27209_372916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27209 ⟨372916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27209
    ⟨372916, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372883, by decide⟩,⟨372902, by decide⟩,⟨372915, by decide⟩]) unmarked_context_12_27209_372916 node_context_12_27209_372916
  intro a
  fin_cases a
  · exact context_13_108836_3444
  · exact context_13_108837_372883
  · exact context_13_108838_372902
  · exact context_13_108839_372915

theorem selected_cut_14445 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108840) = some ⟨13, 1, 0, 3444, 108840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108840, 1, 16384⟩
    (by decide) selected_cut_14445

theorem selected_cut_14446 : selected 8 ⟨372970, by decide⟩
    (prefixPartial 13 108841) = some ⟨13, 2, 0, 372970, 108841, 3501, 16384⟩ := by
  decide +kernel

theorem context_13_108841_372970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108841 ⟨372970, by decide⟩ :=
  accepted_of_selected 13 108841 ⟨372970, by decide⟩ ⟨13, 2, 0, 372970, 108841, 3501, 16384⟩
    (by decide) selected_cut_14446

theorem selected_cut_14447 : selected 8 ⟨373005, by decide⟩
    (prefixPartial 13 108842) = some ⟨13, 2, 0, 373005, 108842, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_108842_373005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108842 ⟨373005, by decide⟩ :=
  accepted_of_selected 13 108842 ⟨373005, by decide⟩ ⟨13, 2, 0, 373005, 108842, 2297, 16384⟩
    (by decide) selected_cut_14447

theorem selected_cut_14448 : selected 8 ⟨373018, by decide⟩
    (prefixPartial 13 108843) = some ⟨13, 2, 0, 373018, 108843, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_108843_373018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108843 ⟨373018, by decide⟩ :=
  accepted_of_selected 13 108843 ⟨373018, by decide⟩ ⟨13, 2, 0, 373018, 108843, 1321, 16384⟩
    (by decide) selected_cut_14448

theorem unmarked_context_12_27210_373019 : frontier 9 ⟨373019, by decide⟩
    (prefixCache 12 27210) (prefixPartial 12 27210) = false := by
  decide +kernel

theorem node_context_12_27210_373019 : EJMOriginalGlobalDAGData.nodes 9 ⟨373019, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨372970, by decide⟩,⟨373005, by decide⟩,⟨373018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27210_373019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27210 ⟨373019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27210
    ⟨373019, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨372970, by decide⟩,⟨373005, by decide⟩,⟨373018, by decide⟩]) unmarked_context_12_27210_373019 node_context_12_27210_373019
  intro a
  fin_cases a
  · exact context_13_108840_3444
  · exact context_13_108841_372970
  · exact context_13_108842_373005
  · exact context_13_108843_373018

theorem selected_cut_14449 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108844) = some ⟨13, 1, 0, 3444, 108844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108844, 1, 16384⟩
    (by decide) selected_cut_14449

theorem selected_cut_14450 : selected 8 ⟨373046, by decide⟩
    (prefixPartial 13 108845) = some ⟨13, 2, 0, 373046, 108845, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_108845_373046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108845 ⟨373046, by decide⟩ :=
  accepted_of_selected 13 108845 ⟨373046, by decide⟩ ⟨13, 2, 0, 373046, 108845, 2301, 16384⟩
    (by decide) selected_cut_14450

theorem selected_cut_14451 : selected 8 ⟨373064, by decide⟩
    (prefixPartial 13 108846) = some ⟨13, 2, 0, 373064, 108846, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_108846_373064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108846 ⟨373064, by decide⟩ :=
  accepted_of_selected 13 108846 ⟨373064, by decide⟩ ⟨13, 2, 0, 373064, 108846, 1197, 16384⟩
    (by decide) selected_cut_14451

theorem selected_cut_14452 : selected 8 ⟨373073, by decide⟩
    (prefixPartial 13 108847) = some ⟨13, 2, 0, 373073, 108847, 925, 16384⟩ := by
  decide +kernel

theorem context_13_108847_373073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108847 ⟨373073, by decide⟩ :=
  accepted_of_selected 13 108847 ⟨373073, by decide⟩ ⟨13, 2, 0, 373073, 108847, 925, 16384⟩
    (by decide) selected_cut_14452

theorem unmarked_context_12_27211_373074 : frontier 9 ⟨373074, by decide⟩
    (prefixCache 12 27211) (prefixPartial 12 27211) = false := by
  decide +kernel

theorem node_context_12_27211_373074 : EJMOriginalGlobalDAGData.nodes 9 ⟨373074, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373046, by decide⟩,⟨373064, by decide⟩,⟨373073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27211_373074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27211 ⟨373074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27211
    ⟨373074, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373046, by decide⟩,⟨373064, by decide⟩,⟨373073, by decide⟩]) unmarked_context_12_27211_373074 node_context_12_27211_373074
  intro a
  fin_cases a
  · exact context_13_108844_3444
  · exact context_13_108845_373046
  · exact context_13_108846_373064
  · exact context_13_108847_373073

theorem unmarked_context_11_6802_373075 : frontier 10 ⟨373075, by decide⟩
    (prefixCache 11 6802) (prefixPartial 11 6802) = false := by
  decide +kernel

theorem node_context_11_6802_373075 : EJMOriginalGlobalDAGData.nodes 10 ⟨373075, by decide⟩ =
    .split (coordinate 11) (![⟨372838, by decide⟩,⟨372916, by decide⟩,⟨373019, by decide⟩,⟨373074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6802_373075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6802 ⟨373075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6802
    ⟨373075, by decide⟩ (by decide) (![⟨372838, by decide⟩,⟨372916, by decide⟩,⟨373019, by decide⟩,⟨373074, by decide⟩]) unmarked_context_11_6802_373075 node_context_11_6802_373075
  intro a
  fin_cases a
  · exact context_12_27208_372838
  · exact context_12_27209_372916
  · exact context_12_27210_373019
  · exact context_12_27211_373074

theorem selected_cut_14453 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108848) = some ⟨13, 1, 0, 3444, 108848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108848, 1, 16384⟩
    (by decide) selected_cut_14453

theorem selected_cut_14454 : selected 8 ⟨373107, by decide⟩
    (prefixPartial 13 108849) = some ⟨13, 2, 0, 373107, 108849, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_108849_373107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108849 ⟨373107, by decide⟩ :=
  accepted_of_selected 13 108849 ⟨373107, by decide⟩ ⟨13, 2, 0, 373107, 108849, 2229, 16384⟩
    (by decide) selected_cut_14454

theorem selected_cut_14455 : selected 8 ⟨373125, by decide⟩
    (prefixPartial 13 108850) = some ⟨13, 2, 0, 373125, 108850, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_108850_373125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108850 ⟨373125, by decide⟩ :=
  accepted_of_selected 13 108850 ⟨373125, by decide⟩ ⟨13, 2, 0, 373125, 108850, 1481, 16384⟩
    (by decide) selected_cut_14455

theorem selected_cut_14456 : selected 8 ⟨373136, by decide⟩
    (prefixPartial 13 108851) = some ⟨13, 2, 0, 373136, 108851, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_108851_373136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108851 ⟨373136, by decide⟩ :=
  accepted_of_selected 13 108851 ⟨373136, by decide⟩ ⟨13, 2, 0, 373136, 108851, 1065, 16384⟩
    (by decide) selected_cut_14456

theorem unmarked_context_12_27212_373137 : frontier 9 ⟨373137, by decide⟩
    (prefixCache 12 27212) (prefixPartial 12 27212) = false := by
  decide +kernel

theorem node_context_12_27212_373137 : EJMOriginalGlobalDAGData.nodes 9 ⟨373137, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373107, by decide⟩,⟨373125, by decide⟩,⟨373136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27212_373137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27212 ⟨373137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27212
    ⟨373137, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373107, by decide⟩,⟨373125, by decide⟩,⟨373136, by decide⟩]) unmarked_context_12_27212_373137 node_context_12_27212_373137
  intro a
  fin_cases a
  · exact context_13_108848_3444
  · exact context_13_108849_373107
  · exact context_13_108850_373125
  · exact context_13_108851_373136

theorem selected_cut_14457 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108852) = some ⟨13, 1, 0, 3444, 108852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108852, 1, 16384⟩
    (by decide) selected_cut_14457

theorem selected_cut_14458 : selected 8 ⟨373193, by decide⟩
    (prefixPartial 13 108853) = some ⟨13, 2, 0, 373193, 108853, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_108853_373193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108853 ⟨373193, by decide⟩ :=
  accepted_of_selected 13 108853 ⟨373193, by decide⟩ ⟨13, 2, 0, 373193, 108853, 3073, 16384⟩
    (by decide) selected_cut_14458

theorem selected_cut_14459 : selected 8 ⟨373224, by decide⟩
    (prefixPartial 13 108854) = some ⟨13, 2, 0, 373224, 108854, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_108854_373224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108854 ⟨373224, by decide⟩ :=
  accepted_of_selected 13 108854 ⟨373224, by decide⟩ ⟨13, 2, 0, 373224, 108854, 1841, 16384⟩
    (by decide) selected_cut_14459

theorem selected_cut_14460 : selected 8 ⟨373238, by decide⟩
    (prefixPartial 13 108855) = some ⟨13, 2, 0, 373238, 108855, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_108855_373238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108855 ⟨373238, by decide⟩ :=
  accepted_of_selected 13 108855 ⟨373238, by decide⟩ ⟨13, 2, 0, 373238, 108855, 1253, 16384⟩
    (by decide) selected_cut_14460

theorem unmarked_context_12_27213_373239 : frontier 9 ⟨373239, by decide⟩
    (prefixCache 12 27213) (prefixPartial 12 27213) = false := by
  decide +kernel

theorem node_context_12_27213_373239 : EJMOriginalGlobalDAGData.nodes 9 ⟨373239, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373193, by decide⟩,⟨373224, by decide⟩,⟨373238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27213_373239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27213 ⟨373239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27213
    ⟨373239, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373193, by decide⟩,⟨373224, by decide⟩,⟨373238, by decide⟩]) unmarked_context_12_27213_373239 node_context_12_27213_373239
  intro a
  fin_cases a
  · exact context_13_108852_3444
  · exact context_13_108853_373193
  · exact context_13_108854_373224
  · exact context_13_108855_373238

theorem selected_cut_14461 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108856) = some ⟨13, 1, 0, 3444, 108856, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108856_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108856 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108856 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108856, 1, 16384⟩
    (by decide) selected_cut_14461

theorem selected_cut_14462 : selected 8 ⟨373273, by decide⟩
    (prefixPartial 13 108857) = some ⟨13, 2, 0, 373273, 108857, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_108857_373273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108857 ⟨373273, by decide⟩ :=
  accepted_of_selected 13 108857 ⟨373273, by decide⟩ ⟨13, 2, 0, 373273, 108857, 2025, 16384⟩
    (by decide) selected_cut_14462

theorem selected_cut_14463 : selected 8 ⟨373291, by decide⟩
    (prefixPartial 13 108858) = some ⟨13, 2, 0, 373291, 108858, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_108858_373291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108858 ⟨373291, by decide⟩ :=
  accepted_of_selected 13 108858 ⟨373291, by decide⟩ ⟨13, 2, 0, 373291, 108858, 1365, 16384⟩
    (by decide) selected_cut_14463

theorem selected_cut_14464 : selected 8 ⟨373303, by decide⟩
    (prefixPartial 13 108859) = some ⟨13, 2, 0, 373303, 108859, 877, 16384⟩ := by
  decide +kernel

theorem context_13_108859_373303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108859 ⟨373303, by decide⟩ :=
  accepted_of_selected 13 108859 ⟨373303, by decide⟩ ⟨13, 2, 0, 373303, 108859, 877, 16384⟩
    (by decide) selected_cut_14464

theorem unmarked_context_12_27214_373304 : frontier 9 ⟨373304, by decide⟩
    (prefixCache 12 27214) (prefixPartial 12 27214) = false := by
  decide +kernel

theorem node_context_12_27214_373304 : EJMOriginalGlobalDAGData.nodes 9 ⟨373304, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373273, by decide⟩,⟨373291, by decide⟩,⟨373303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27214_373304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27214 ⟨373304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27214
    ⟨373304, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373273, by decide⟩,⟨373291, by decide⟩,⟨373303, by decide⟩]) unmarked_context_12_27214_373304 node_context_12_27214_373304
  intro a
  fin_cases a
  · exact context_13_108856_3444
  · exact context_13_108857_373273
  · exact context_13_108858_373291
  · exact context_13_108859_373303

theorem selected_cut_14465 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108860) = some ⟨13, 1, 0, 3444, 108860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108860, 1, 16384⟩
    (by decide) selected_cut_14465

theorem selected_cut_14466 : selected 8 ⟨373333, by decide⟩
    (prefixPartial 13 108861) = some ⟨13, 2, 0, 373333, 108861, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_108861_373333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108861 ⟨373333, by decide⟩ :=
  accepted_of_selected 13 108861 ⟨373333, by decide⟩ ⟨13, 2, 0, 373333, 108861, 2065, 16384⟩
    (by decide) selected_cut_14466

theorem selected_cut_14467 : selected 8 ⟨373353, by decide⟩
    (prefixPartial 13 108862) = some ⟨13, 2, 0, 373353, 108862, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_108862_373353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108862 ⟨373353, by decide⟩ :=
  accepted_of_selected 13 108862 ⟨373353, by decide⟩ ⟨13, 2, 0, 373353, 108862, 1489, 16384⟩
    (by decide) selected_cut_14467

theorem selected_cut_14468 : selected 8 ⟨373362, by decide⟩
    (prefixPartial 13 108863) = some ⟨13, 2, 0, 373362, 108863, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_108863_373362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108863 ⟨373362, by decide⟩ :=
  accepted_of_selected 13 108863 ⟨373362, by decide⟩ ⟨13, 2, 0, 373362, 108863, 1021, 16384⟩
    (by decide) selected_cut_14468

theorem unmarked_context_12_27215_373363 : frontier 9 ⟨373363, by decide⟩
    (prefixCache 12 27215) (prefixPartial 12 27215) = false := by
  decide +kernel

theorem node_context_12_27215_373363 : EJMOriginalGlobalDAGData.nodes 9 ⟨373363, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373333, by decide⟩,⟨373353, by decide⟩,⟨373362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27215_373363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27215 ⟨373363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27215
    ⟨373363, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373333, by decide⟩,⟨373353, by decide⟩,⟨373362, by decide⟩]) unmarked_context_12_27215_373363 node_context_12_27215_373363
  intro a
  fin_cases a
  · exact context_13_108860_3444
  · exact context_13_108861_373333
  · exact context_13_108862_373353
  · exact context_13_108863_373362

theorem unmarked_context_11_6803_373364 : frontier 10 ⟨373364, by decide⟩
    (prefixCache 11 6803) (prefixPartial 11 6803) = false := by
  decide +kernel

theorem node_context_11_6803_373364 : EJMOriginalGlobalDAGData.nodes 10 ⟨373364, by decide⟩ =
    .split (coordinate 11) (![⟨373137, by decide⟩,⟨373239, by decide⟩,⟨373304, by decide⟩,⟨373363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6803_373364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6803 ⟨373364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6803
    ⟨373364, by decide⟩ (by decide) (![⟨373137, by decide⟩,⟨373239, by decide⟩,⟨373304, by decide⟩,⟨373363, by decide⟩]) unmarked_context_11_6803_373364 node_context_11_6803_373364
  intro a
  fin_cases a
  · exact context_12_27212_373137
  · exact context_12_27213_373239
  · exact context_12_27214_373304
  · exact context_12_27215_373363

theorem unmarked_context_10_1700_373365 : frontier 11 ⟨373365, by decide⟩
    (prefixCache 10 1700) (prefixPartial 10 1700) = false := by
  decide +kernel

theorem node_context_10_1700_373365 : EJMOriginalGlobalDAGData.nodes 11 ⟨373365, by decide⟩ =
    .split (coordinate 10) (![⟨372539, by decide⟩,⟨372775, by decide⟩,⟨373075, by decide⟩,⟨373364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1700_373365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1700 ⟨373365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1700
    ⟨373365, by decide⟩ (by decide) (![⟨372539, by decide⟩,⟨372775, by decide⟩,⟨373075, by decide⟩,⟨373364, by decide⟩]) unmarked_context_10_1700_373365 node_context_10_1700_373365
  intro a
  fin_cases a
  · exact context_11_6800_372539
  · exact context_11_6801_372775
  · exact context_11_6802_373075
  · exact context_11_6803_373364

theorem selected_cut_14469 : selected 9 ⟨373402, by decide⟩
    (prefixPartial 12 27216) = some ⟨12, 2, 0, 373402, 27216, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_27216_373402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27216 ⟨373402, by decide⟩ :=
  accepted_of_selected 12 27216 ⟨373402, by decide⟩ ⟨12, 2, 0, 373402, 27216, 3833, 65536⟩
    (by decide) selected_cut_14469

theorem selected_cut_14470 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27217) = some ⟨12, 1, 0, 170504, 27217, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27217_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27217 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27217 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27217, 1, 65536⟩
    (by decide) selected_cut_14470

theorem selected_cut_14471 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108872) = some ⟨13, 1, 0, 3444, 108872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108872, 1, 16384⟩
    (by decide) selected_cut_14471

theorem selected_cut_14472 : selected 8 ⟨373427, by decide⟩
    (prefixPartial 13 108873) = some ⟨13, 2, 0, 373427, 108873, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_108873_373427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108873 ⟨373427, by decide⟩ :=
  accepted_of_selected 13 108873 ⟨373427, by decide⟩ ⟨13, 2, 0, 373427, 108873, 2057, 16384⟩
    (by decide) selected_cut_14472

theorem selected_cut_14473 : selected 8 ⟨373446, by decide⟩
    (prefixPartial 13 108874) = some ⟨13, 2, 0, 373446, 108874, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_108874_373446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108874 ⟨373446, by decide⟩ :=
  accepted_of_selected 13 108874 ⟨373446, by decide⟩ ⟨13, 2, 0, 373446, 108874, 1233, 16384⟩
    (by decide) selected_cut_14473

theorem selected_cut_14474 : selected 8 ⟨373454, by decide⟩
    (prefixPartial 13 108875) = some ⟨13, 2, 0, 373454, 108875, 909, 16384⟩ := by
  decide +kernel

theorem context_13_108875_373454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108875 ⟨373454, by decide⟩ :=
  accepted_of_selected 13 108875 ⟨373454, by decide⟩ ⟨13, 2, 0, 373454, 108875, 909, 16384⟩
    (by decide) selected_cut_14474

theorem unmarked_context_12_27218_373455 : frontier 9 ⟨373455, by decide⟩
    (prefixCache 12 27218) (prefixPartial 12 27218) = false := by
  decide +kernel

theorem node_context_12_27218_373455 : EJMOriginalGlobalDAGData.nodes 9 ⟨373455, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373427, by decide⟩,⟨373446, by decide⟩,⟨373454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27218_373455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27218 ⟨373455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27218
    ⟨373455, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373427, by decide⟩,⟨373446, by decide⟩,⟨373454, by decide⟩]) unmarked_context_12_27218_373455 node_context_12_27218_373455
  intro a
  fin_cases a
  · exact context_13_108872_3444
  · exact context_13_108873_373427
  · exact context_13_108874_373446
  · exact context_13_108875_373454

theorem selected_cut_14475 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108876) = some ⟨13, 1, 0, 3444, 108876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108876, 1, 16384⟩
    (by decide) selected_cut_14475

theorem selected_cut_14476 : selected 8 ⟨373493, by decide⟩
    (prefixPartial 13 108877) = some ⟨13, 2, 0, 373493, 108877, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_108877_373493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108877 ⟨373493, by decide⟩ :=
  accepted_of_selected 13 108877 ⟨373493, by decide⟩ ⟨13, 2, 0, 373493, 108877, 2421, 16384⟩
    (by decide) selected_cut_14476

theorem selected_cut_14477 : selected 8 ⟨373509, by decide⟩
    (prefixPartial 13 108878) = some ⟨13, 2, 0, 373509, 108878, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_108878_373509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108878 ⟨373509, by decide⟩ :=
  accepted_of_selected 13 108878 ⟨373509, by decide⟩ ⟨13, 2, 0, 373509, 108878, 1557, 16384⟩
    (by decide) selected_cut_14477

theorem selected_cut_14478 : selected 8 ⟨373519, by decide⟩
    (prefixPartial 13 108879) = some ⟨13, 2, 0, 373519, 108879, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_108879_373519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108879 ⟨373519, by decide⟩ :=
  accepted_of_selected 13 108879 ⟨373519, by decide⟩ ⟨13, 2, 0, 373519, 108879, 1061, 16384⟩
    (by decide) selected_cut_14478

theorem unmarked_context_12_27219_373520 : frontier 9 ⟨373520, by decide⟩
    (prefixCache 12 27219) (prefixPartial 12 27219) = false := by
  decide +kernel

theorem node_context_12_27219_373520 : EJMOriginalGlobalDAGData.nodes 9 ⟨373520, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373493, by decide⟩,⟨373509, by decide⟩,⟨373519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27219_373520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27219 ⟨373520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27219
    ⟨373520, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373493, by decide⟩,⟨373509, by decide⟩,⟨373519, by decide⟩]) unmarked_context_12_27219_373520 node_context_12_27219_373520
  intro a
  fin_cases a
  · exact context_13_108876_3444
  · exact context_13_108877_373493
  · exact context_13_108878_373509
  · exact context_13_108879_373519

theorem unmarked_context_11_6804_373521 : frontier 10 ⟨373521, by decide⟩
    (prefixCache 11 6804) (prefixPartial 11 6804) = false := by
  decide +kernel

theorem node_context_11_6804_373521 : EJMOriginalGlobalDAGData.nodes 10 ⟨373521, by decide⟩ =
    .split (coordinate 11) (![⟨373402, by decide⟩,⟨170504, by decide⟩,⟨373455, by decide⟩,⟨373520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6804_373521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6804 ⟨373521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6804
    ⟨373521, by decide⟩ (by decide) (![⟨373402, by decide⟩,⟨170504, by decide⟩,⟨373455, by decide⟩,⟨373520, by decide⟩]) unmarked_context_11_6804_373521 node_context_11_6804_373521
  intro a
  fin_cases a
  · exact context_12_27216_373402
  · exact context_12_27217_170504
  · exact context_12_27218_373455
  · exact context_12_27219_373520

theorem selected_cut_14479 : selected 9 ⟨373564, by decide⟩
    (prefixPartial 12 27220) = some ⟨12, 2, 0, 373564, 27220, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_27220_373564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27220 ⟨373564, by decide⟩ :=
  accepted_of_selected 12 27220 ⟨373564, by decide⟩ ⟨12, 2, 0, 373564, 27220, 3869, 65536⟩
    (by decide) selected_cut_14479

theorem selected_cut_14480 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27221) = some ⟨12, 1, 0, 170504, 27221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27221_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27221 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27221 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27221, 1, 65536⟩
    (by decide) selected_cut_14480

theorem selected_cut_14481 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108888) = some ⟨13, 1, 0, 3444, 108888, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108888_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108888 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108888 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108888, 1, 16384⟩
    (by decide) selected_cut_14481

theorem selected_cut_14482 : selected 8 ⟨373583, by decide⟩
    (prefixPartial 13 108889) = some ⟨13, 2, 0, 373583, 108889, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_108889_373583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108889 ⟨373583, by decide⟩ :=
  accepted_of_selected 13 108889 ⟨373583, by decide⟩ ⟨13, 2, 0, 373583, 108889, 1713, 16384⟩
    (by decide) selected_cut_14482

theorem selected_cut_14483 : selected 8 ⟨373602, by decide⟩
    (prefixPartial 13 108890) = some ⟨13, 2, 0, 373602, 108890, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_108890_373602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108890 ⟨373602, by decide⟩ :=
  accepted_of_selected 13 108890 ⟨373602, by decide⟩ ⟨13, 2, 0, 373602, 108890, 1405, 16384⟩
    (by decide) selected_cut_14483

theorem selected_cut_14484 : selected 8 ⟨373610, by decide⟩
    (prefixPartial 13 108891) = some ⟨13, 2, 0, 373610, 108891, 993, 16384⟩ := by
  decide +kernel

theorem context_13_108891_373610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108891 ⟨373610, by decide⟩ :=
  accepted_of_selected 13 108891 ⟨373610, by decide⟩ ⟨13, 2, 0, 373610, 108891, 993, 16384⟩
    (by decide) selected_cut_14484

theorem unmarked_context_12_27222_373611 : frontier 9 ⟨373611, by decide⟩
    (prefixCache 12 27222) (prefixPartial 12 27222) = false := by
  decide +kernel

theorem node_context_12_27222_373611 : EJMOriginalGlobalDAGData.nodes 9 ⟨373611, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373583, by decide⟩,⟨373602, by decide⟩,⟨373610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27222_373611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27222 ⟨373611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27222
    ⟨373611, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373583, by decide⟩,⟨373602, by decide⟩,⟨373610, by decide⟩]) unmarked_context_12_27222_373611 node_context_12_27222_373611
  intro a
  fin_cases a
  · exact context_13_108888_3444
  · exact context_13_108889_373583
  · exact context_13_108890_373602
  · exact context_13_108891_373610

theorem selected_cut_14485 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108892) = some ⟨13, 1, 0, 3444, 108892, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108892_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108892 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108892 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108892, 1, 16384⟩
    (by decide) selected_cut_14485

theorem selected_cut_14486 : selected 8 ⟨373636, by decide⟩
    (prefixPartial 13 108893) = some ⟨13, 2, 0, 373636, 108893, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_108893_373636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108893 ⟨373636, by decide⟩ :=
  accepted_of_selected 13 108893 ⟨373636, by decide⟩ ⟨13, 2, 0, 373636, 108893, 1877, 16384⟩
    (by decide) selected_cut_14486

theorem selected_cut_14487 : selected 8 ⟨373655, by decide⟩
    (prefixPartial 13 108894) = some ⟨13, 2, 0, 373655, 108894, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_108894_373655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108894 ⟨373655, by decide⟩ :=
  accepted_of_selected 13 108894 ⟨373655, by decide⟩ ⟨13, 2, 0, 373655, 108894, 1653, 16384⟩
    (by decide) selected_cut_14487

theorem selected_cut_14488 : selected 8 ⟨373664, by decide⟩
    (prefixPartial 13 108895) = some ⟨13, 2, 0, 373664, 108895, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_108895_373664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108895 ⟨373664, by decide⟩ :=
  accepted_of_selected 13 108895 ⟨373664, by decide⟩ ⟨13, 2, 0, 373664, 108895, 1137, 16384⟩
    (by decide) selected_cut_14488

theorem unmarked_context_12_27223_373665 : frontier 9 ⟨373665, by decide⟩
    (prefixCache 12 27223) (prefixPartial 12 27223) = false := by
  decide +kernel

theorem node_context_12_27223_373665 : EJMOriginalGlobalDAGData.nodes 9 ⟨373665, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373636, by decide⟩,⟨373655, by decide⟩,⟨373664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27223_373665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27223 ⟨373665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27223
    ⟨373665, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373636, by decide⟩,⟨373655, by decide⟩,⟨373664, by decide⟩]) unmarked_context_12_27223_373665 node_context_12_27223_373665
  intro a
  fin_cases a
  · exact context_13_108892_3444
  · exact context_13_108893_373636
  · exact context_13_108894_373655
  · exact context_13_108895_373664

theorem unmarked_context_11_6805_373666 : frontier 10 ⟨373666, by decide⟩
    (prefixCache 11 6805) (prefixPartial 11 6805) = false := by
  decide +kernel

theorem node_context_11_6805_373666 : EJMOriginalGlobalDAGData.nodes 10 ⟨373666, by decide⟩ =
    .split (coordinate 11) (![⟨373564, by decide⟩,⟨170504, by decide⟩,⟨373611, by decide⟩,⟨373665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6805_373666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6805 ⟨373666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6805
    ⟨373666, by decide⟩ (by decide) (![⟨373564, by decide⟩,⟨170504, by decide⟩,⟨373611, by decide⟩,⟨373665, by decide⟩]) unmarked_context_11_6805_373666 node_context_11_6805_373666
  intro a
  fin_cases a
  · exact context_12_27220_373564
  · exact context_12_27221_170504
  · exact context_12_27222_373611
  · exact context_12_27223_373665

theorem selected_cut_14489 : selected 9 ⟨373701, by decide⟩
    (prefixPartial 12 27224) = some ⟨12, 2, 0, 373701, 27224, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_27224_373701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27224 ⟨373701, by decide⟩ :=
  accepted_of_selected 12 27224 ⟨373701, by decide⟩ ⟨12, 2, 0, 373701, 27224, 2945, 65536⟩
    (by decide) selected_cut_14489

theorem selected_cut_14490 : selected 9 ⟨373737, by decide⟩
    (prefixPartial 12 27225) = some ⟨12, 2, 0, 373737, 27225, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_27225_373737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27225 ⟨373737, by decide⟩ :=
  accepted_of_selected 12 27225 ⟨373737, by decide⟩ ⟨12, 2, 0, 373737, 27225, 1673, 65536⟩
    (by decide) selected_cut_14490

theorem selected_cut_14491 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108904) = some ⟨13, 1, 0, 3444, 108904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108904, 1, 16384⟩
    (by decide) selected_cut_14491

theorem selected_cut_14492 : selected 8 ⟨373764, by decide⟩
    (prefixPartial 13 108905) = some ⟨13, 2, 0, 373764, 108905, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_108905_373764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108905 ⟨373764, by decide⟩ :=
  accepted_of_selected 13 108905 ⟨373764, by decide⟩ ⟨13, 2, 0, 373764, 108905, 2205, 16384⟩
    (by decide) selected_cut_14492

theorem selected_cut_14493 : selected 8 ⟨373789, by decide⟩
    (prefixPartial 13 108906) = some ⟨13, 2, 0, 373789, 108906, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_108906_373789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108906 ⟨373789, by decide⟩ :=
  accepted_of_selected 13 108906 ⟨373789, by decide⟩ ⟨13, 2, 0, 373789, 108906, 2173, 16384⟩
    (by decide) selected_cut_14493

theorem selected_cut_14494 : selected 8 ⟨373800, by decide⟩
    (prefixPartial 13 108907) = some ⟨13, 2, 0, 373800, 108907, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_108907_373800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108907 ⟨373800, by decide⟩ :=
  accepted_of_selected 13 108907 ⟨373800, by decide⟩ ⟨13, 2, 0, 373800, 108907, 1161, 16384⟩
    (by decide) selected_cut_14494

theorem unmarked_context_12_27226_373801 : frontier 9 ⟨373801, by decide⟩
    (prefixCache 12 27226) (prefixPartial 12 27226) = false := by
  decide +kernel

theorem node_context_12_27226_373801 : EJMOriginalGlobalDAGData.nodes 9 ⟨373801, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373764, by decide⟩,⟨373789, by decide⟩,⟨373800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27226_373801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27226 ⟨373801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27226
    ⟨373801, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373764, by decide⟩,⟨373789, by decide⟩,⟨373800, by decide⟩]) unmarked_context_12_27226_373801 node_context_12_27226_373801
  intro a
  fin_cases a
  · exact context_13_108904_3444
  · exact context_13_108905_373764
  · exact context_13_108906_373789
  · exact context_13_108907_373800

theorem selected_cut_14495 : selected 9 ⟨373846, by decide⟩
    (prefixPartial 12 27227) = some ⟨12, 2, 0, 373846, 27227, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_27227_373846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27227 ⟨373846, by decide⟩ :=
  accepted_of_selected 12 27227 ⟨373846, by decide⟩ ⟨12, 2, 0, 373846, 27227, 3573, 65536⟩
    (by decide) selected_cut_14495

theorem unmarked_context_11_6806_373847 : frontier 10 ⟨373847, by decide⟩
    (prefixCache 11 6806) (prefixPartial 11 6806) = false := by
  decide +kernel

theorem node_context_11_6806_373847 : EJMOriginalGlobalDAGData.nodes 10 ⟨373847, by decide⟩ =
    .split (coordinate 11) (![⟨373701, by decide⟩,⟨373737, by decide⟩,⟨373801, by decide⟩,⟨373846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6806_373847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6806 ⟨373847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6806
    ⟨373847, by decide⟩ (by decide) (![⟨373701, by decide⟩,⟨373737, by decide⟩,⟨373801, by decide⟩,⟨373846, by decide⟩]) unmarked_context_11_6806_373847 node_context_11_6806_373847
  intro a
  fin_cases a
  · exact context_12_27224_373701
  · exact context_12_27225_373737
  · exact context_12_27226_373801
  · exact context_12_27227_373846

theorem selected_cut_14496 : selected 9 ⟨373889, by decide⟩
    (prefixPartial 12 27228) = some ⟨12, 2, 0, 373889, 27228, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_27228_373889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27228 ⟨373889, by decide⟩ :=
  accepted_of_selected 12 27228 ⟨373889, by decide⟩ ⟨12, 2, 0, 373889, 27228, 3337, 65536⟩
    (by decide) selected_cut_14496

theorem selected_cut_14497 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108916) = some ⟨13, 1, 0, 3444, 108916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108916, 1, 16384⟩
    (by decide) selected_cut_14497

theorem selected_cut_14498 : selected 8 ⟨373915, by decide⟩
    (prefixPartial 13 108917) = some ⟨13, 2, 0, 373915, 108917, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_108917_373915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108917 ⟨373915, by decide⟩ :=
  accepted_of_selected 13 108917 ⟨373915, by decide⟩ ⟨13, 2, 0, 373915, 108917, 1837, 16384⟩
    (by decide) selected_cut_14498

theorem selected_cut_14499 : selected 8 ⟨373939, by decide⟩
    (prefixPartial 13 108918) = some ⟨13, 2, 0, 373939, 108918, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_108918_373939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108918 ⟨373939, by decide⟩ :=
  accepted_of_selected 13 108918 ⟨373939, by decide⟩ ⟨13, 2, 0, 373939, 108918, 1865, 16384⟩
    (by decide) selected_cut_14499

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
