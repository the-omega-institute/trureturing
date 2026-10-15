/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover267
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_88100_652031 : frontier 9 ⟨652031, by decide⟩
    (prefixCache 12 88100) (prefixPartial 12 88100) = false := by
  decide +kernel

theorem node_context_12_88100_652031 : EJMOriginalGlobalDAGData.nodes 9 ⟨652031, by decide⟩ =
    .split (coordinate 12) (![⟨651962, by decide⟩,⟨652008, by decide⟩,⟨652025, by decide⟩,⟨652030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88100_652031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88100 ⟨652031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88100
    ⟨652031, by decide⟩ (by decide) (![⟨651962, by decide⟩,⟨652008, by decide⟩,⟨652025, by decide⟩,⟨652030, by decide⟩]) unmarked_context_12_88100_652031 node_context_12_88100_652031
  intro a
  fin_cases a
  · exact context_13_352400_651962
  · exact context_13_352401_652008
  · exact context_13_352402_652025
  · exact context_13_352403_652030

theorem selected_cut_25731 : selected 8 ⟨652045, by decide⟩
    (prefixPartial 13 352404) = some ⟨13, 2, 0, 652045, 352404, 949, 16384⟩ := by
  decide +kernel

theorem context_13_352404_652045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352404 ⟨652045, by decide⟩ :=
  accepted_of_selected 13 352404 ⟨652045, by decide⟩ ⟨13, 2, 0, 652045, 352404, 949, 16384⟩
    (by decide) selected_cut_25731

theorem selected_cut_25732 : selected 8 ⟨652075, by decide⟩
    (prefixPartial 13 352405) = some ⟨13, 2, 0, 652075, 352405, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_352405_652075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352405 ⟨652075, by decide⟩ :=
  accepted_of_selected 13 352405 ⟨652075, by decide⟩ ⟨13, 2, 0, 652075, 352405, 1693, 16384⟩
    (by decide) selected_cut_25732

theorem selected_cut_25733 : selected 8 ⟨652088, by decide⟩
    (prefixPartial 13 352406) = some ⟨13, 2, 0, 652088, 352406, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_352406_652088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352406 ⟨652088, by decide⟩ :=
  accepted_of_selected 13 352406 ⟨652088, by decide⟩ ⟨13, 2, 0, 652088, 352406, 1141, 16384⟩
    (by decide) selected_cut_25733

theorem selected_cut_25734 : selected 8 ⟨652094, by decide⟩
    (prefixPartial 13 352407) = some ⟨13, 2, 0, 652094, 352407, 809, 16384⟩ := by
  decide +kernel

theorem context_13_352407_652094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352407 ⟨652094, by decide⟩ :=
  accepted_of_selected 13 352407 ⟨652094, by decide⟩ ⟨13, 2, 0, 652094, 352407, 809, 16384⟩
    (by decide) selected_cut_25734

theorem unmarked_context_12_88101_652095 : frontier 9 ⟨652095, by decide⟩
    (prefixCache 12 88101) (prefixPartial 12 88101) = false := by
  decide +kernel

theorem node_context_12_88101_652095 : EJMOriginalGlobalDAGData.nodes 9 ⟨652095, by decide⟩ =
    .split (coordinate 12) (![⟨652045, by decide⟩,⟨652075, by decide⟩,⟨652088, by decide⟩,⟨652094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88101_652095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88101 ⟨652095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88101
    ⟨652095, by decide⟩ (by decide) (![⟨652045, by decide⟩,⟨652075, by decide⟩,⟨652088, by decide⟩,⟨652094, by decide⟩]) unmarked_context_12_88101_652095 node_context_12_88101_652095
  intro a
  fin_cases a
  · exact context_13_352404_652045
  · exact context_13_352405_652075
  · exact context_13_352406_652088
  · exact context_13_352407_652094

theorem selected_cut_25735 : selected 8 ⟨652114, by decide⟩
    (prefixPartial 13 352408) = some ⟨13, 2, 0, 652114, 352408, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_352408_652114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352408 ⟨652114, by decide⟩ :=
  accepted_of_selected 13 352408 ⟨652114, by decide⟩ ⟨13, 2, 0, 652114, 352408, 1249, 16384⟩
    (by decide) selected_cut_25735

theorem selected_cut_25736 : selected 8 ⟨652147, by decide⟩
    (prefixPartial 13 352409) = some ⟨13, 2, 0, 652147, 352409, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_352409_652147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352409 ⟨652147, by decide⟩ :=
  accepted_of_selected 13 352409 ⟨652147, by decide⟩ ⟨13, 2, 0, 652147, 352409, 2533, 16384⟩
    (by decide) selected_cut_25736

theorem selected_cut_25737 : selected 8 ⟨652161, by decide⟩
    (prefixPartial 13 352410) = some ⟨13, 2, 0, 652161, 352410, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_352410_652161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352410 ⟨652161, by decide⟩ :=
  accepted_of_selected 13 352410 ⟨652161, by decide⟩ ⟨13, 2, 0, 652161, 352410, 1417, 16384⟩
    (by decide) selected_cut_25737

theorem selected_cut_25738 : selected 8 ⟨652168, by decide⟩
    (prefixPartial 13 352411) = some ⟨13, 2, 0, 652168, 352411, 913, 16384⟩ := by
  decide +kernel

theorem context_13_352411_652168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352411 ⟨652168, by decide⟩ :=
  accepted_of_selected 13 352411 ⟨652168, by decide⟩ ⟨13, 2, 0, 652168, 352411, 913, 16384⟩
    (by decide) selected_cut_25738

theorem unmarked_context_12_88102_652169 : frontier 9 ⟨652169, by decide⟩
    (prefixCache 12 88102) (prefixPartial 12 88102) = false := by
  decide +kernel

theorem node_context_12_88102_652169 : EJMOriginalGlobalDAGData.nodes 9 ⟨652169, by decide⟩ =
    .split (coordinate 12) (![⟨652114, by decide⟩,⟨652147, by decide⟩,⟨652161, by decide⟩,⟨652168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88102_652169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88102 ⟨652169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88102
    ⟨652169, by decide⟩ (by decide) (![⟨652114, by decide⟩,⟨652147, by decide⟩,⟨652161, by decide⟩,⟨652168, by decide⟩]) unmarked_context_12_88102_652169 node_context_12_88102_652169
  intro a
  fin_cases a
  · exact context_13_352408_652114
  · exact context_13_352409_652147
  · exact context_13_352410_652161
  · exact context_13_352411_652168

theorem selected_cut_25739 : selected 8 ⟨652188, by decide⟩
    (prefixPartial 13 352412) = some ⟨13, 2, 0, 652188, 352412, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_352412_652188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352412 ⟨652188, by decide⟩ :=
  accepted_of_selected 13 352412 ⟨652188, by decide⟩ ⟨13, 2, 0, 652188, 352412, 1145, 16384⟩
    (by decide) selected_cut_25739

theorem selected_cut_25740 : selected 8 ⟨652227, by decide⟩
    (prefixPartial 13 352413) = some ⟨13, 2, 0, 652227, 352413, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_352413_652227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352413 ⟨652227, by decide⟩ :=
  accepted_of_selected 13 352413 ⟨652227, by decide⟩ ⟨13, 2, 0, 652227, 352413, 2693, 16384⟩
    (by decide) selected_cut_25740

theorem selected_cut_25741 : selected 8 ⟨652240, by decide⟩
    (prefixPartial 13 352414) = some ⟨13, 2, 0, 652240, 352414, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_352414_652240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352414 ⟨652240, by decide⟩ :=
  accepted_of_selected 13 352414 ⟨652240, by decide⟩ ⟨13, 2, 0, 652240, 352414, 1253, 16384⟩
    (by decide) selected_cut_25741

theorem selected_cut_25742 : selected 8 ⟨652246, by decide⟩
    (prefixPartial 13 352415) = some ⟨13, 2, 0, 652246, 352415, 805, 16384⟩ := by
  decide +kernel

theorem context_13_352415_652246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352415 ⟨652246, by decide⟩ :=
  accepted_of_selected 13 352415 ⟨652246, by decide⟩ ⟨13, 2, 0, 652246, 352415, 805, 16384⟩
    (by decide) selected_cut_25742

theorem unmarked_context_12_88103_652247 : frontier 9 ⟨652247, by decide⟩
    (prefixCache 12 88103) (prefixPartial 12 88103) = false := by
  decide +kernel

theorem node_context_12_88103_652247 : EJMOriginalGlobalDAGData.nodes 9 ⟨652247, by decide⟩ =
    .split (coordinate 12) (![⟨652188, by decide⟩,⟨652227, by decide⟩,⟨652240, by decide⟩,⟨652246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88103_652247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88103 ⟨652247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88103
    ⟨652247, by decide⟩ (by decide) (![⟨652188, by decide⟩,⟨652227, by decide⟩,⟨652240, by decide⟩,⟨652246, by decide⟩]) unmarked_context_12_88103_652247 node_context_12_88103_652247
  intro a
  fin_cases a
  · exact context_13_352412_652188
  · exact context_13_352413_652227
  · exact context_13_352414_652240
  · exact context_13_352415_652246

theorem unmarked_context_11_22025_652248 : frontier 10 ⟨652248, by decide⟩
    (prefixCache 11 22025) (prefixPartial 11 22025) = false := by
  decide +kernel

theorem node_context_11_22025_652248 : EJMOriginalGlobalDAGData.nodes 10 ⟨652248, by decide⟩ =
    .split (coordinate 11) (![⟨652031, by decide⟩,⟨652095, by decide⟩,⟨652169, by decide⟩,⟨652247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22025_652248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22025 ⟨652248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22025
    ⟨652248, by decide⟩ (by decide) (![⟨652031, by decide⟩,⟨652095, by decide⟩,⟨652169, by decide⟩,⟨652247, by decide⟩]) unmarked_context_11_22025_652248 node_context_11_22025_652248
  intro a
  fin_cases a
  · exact context_12_88100_652031
  · exact context_12_88101_652095
  · exact context_12_88102_652169
  · exact context_12_88103_652247

theorem selected_cut_25743 : selected 9 ⟨224339, by decide⟩
    (prefixPartial 12 88104) = some ⟨12, 1, 0, 224339, 88104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88104_224339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88104 ⟨224339, by decide⟩ :=
  accepted_of_selected 12 88104 ⟨224339, by decide⟩ ⟨12, 1, 0, 224339, 88104, 1, 65536⟩
    (by decide) selected_cut_25743

theorem selected_cut_25744 : selected 8 ⟨652275, by decide⟩
    (prefixPartial 13 352420) = some ⟨13, 2, 0, 652275, 352420, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_352420_652275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352420 ⟨652275, by decide⟩ :=
  accepted_of_selected 13 352420 ⟨652275, by decide⟩ ⟨13, 2, 0, 652275, 352420, 1445, 16384⟩
    (by decide) selected_cut_25744

theorem selected_cut_25745 : selected 8 ⟨652323, by decide⟩
    (prefixPartial 13 352421) = some ⟨13, 2, 0, 652323, 352421, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_352421_652323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352421 ⟨652323, by decide⟩ :=
  accepted_of_selected 13 352421 ⟨652323, by decide⟩ ⟨13, 2, 0, 652323, 352421, 2601, 16384⟩
    (by decide) selected_cut_25745

theorem selected_cut_25746 : selected 8 ⟨652352, by decide⟩
    (prefixPartial 13 352422) = some ⟨13, 2, 0, 652352, 352422, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_352422_652352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352422 ⟨652352, by decide⟩ :=
  accepted_of_selected 13 352422 ⟨652352, by decide⟩ ⟨13, 2, 0, 652352, 352422, 1785, 16384⟩
    (by decide) selected_cut_25746

theorem selected_cut_25747 : selected 8 ⟨652365, by decide⟩
    (prefixPartial 13 352423) = some ⟨13, 2, 0, 652365, 352423, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_352423_652365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352423 ⟨652365, by decide⟩ :=
  accepted_of_selected 13 352423 ⟨652365, by decide⟩ ⟨13, 2, 0, 652365, 352423, 1089, 16384⟩
    (by decide) selected_cut_25747

theorem unmarked_context_12_88105_652366 : frontier 9 ⟨652366, by decide⟩
    (prefixCache 12 88105) (prefixPartial 12 88105) = false := by
  decide +kernel

theorem node_context_12_88105_652366 : EJMOriginalGlobalDAGData.nodes 9 ⟨652366, by decide⟩ =
    .split (coordinate 12) (![⟨652275, by decide⟩,⟨652323, by decide⟩,⟨652352, by decide⟩,⟨652365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88105_652366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88105 ⟨652366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88105
    ⟨652366, by decide⟩ (by decide) (![⟨652275, by decide⟩,⟨652323, by decide⟩,⟨652352, by decide⟩,⟨652365, by decide⟩]) unmarked_context_12_88105_652366 node_context_12_88105_652366
  intro a
  fin_cases a
  · exact context_13_352420_652275
  · exact context_13_352421_652323
  · exact context_13_352422_652352
  · exact context_13_352423_652365

theorem selected_cut_25748 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 88106) = some ⟨12, 1, 0, 224365, 88106, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88106_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88106 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 88106 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 88106, 1, 65536⟩
    (by decide) selected_cut_25748

theorem selected_cut_25749 : selected 8 ⟨652397, by decide⟩
    (prefixPartial 13 352428) = some ⟨13, 2, 0, 652397, 352428, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_352428_652397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352428 ⟨652397, by decide⟩ :=
  accepted_of_selected 13 352428 ⟨652397, by decide⟩ ⟨13, 2, 0, 652397, 352428, 1453, 16384⟩
    (by decide) selected_cut_25749

theorem selected_cut_25750 : selected 8 ⟨652477, by decide⟩
    (prefixPartial 13 352429) = some ⟨13, 2, 0, 652477, 352429, 3601, 16384⟩ := by
  decide +kernel

theorem context_13_352429_652477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352429 ⟨652477, by decide⟩ :=
  accepted_of_selected 13 352429 ⟨652477, by decide⟩ ⟨13, 2, 0, 652477, 352429, 3601, 16384⟩
    (by decide) selected_cut_25750

theorem selected_cut_25751 : selected 8 ⟨652497, by decide⟩
    (prefixPartial 13 352430) = some ⟨13, 2, 0, 652497, 352430, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_352430_652497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352430 ⟨652497, by decide⟩ :=
  accepted_of_selected 13 352430 ⟨652497, by decide⟩ ⟨13, 2, 0, 652497, 352430, 1697, 16384⟩
    (by decide) selected_cut_25751

theorem selected_cut_25752 : selected 8 ⟨652506, by decide⟩
    (prefixPartial 13 352431) = some ⟨13, 2, 0, 652506, 352431, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_352431_652506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352431 ⟨652506, by decide⟩ :=
  accepted_of_selected 13 352431 ⟨652506, by decide⟩ ⟨13, 2, 0, 652506, 352431, 1065, 16384⟩
    (by decide) selected_cut_25752

theorem unmarked_context_12_88107_652507 : frontier 9 ⟨652507, by decide⟩
    (prefixCache 12 88107) (prefixPartial 12 88107) = false := by
  decide +kernel

theorem node_context_12_88107_652507 : EJMOriginalGlobalDAGData.nodes 9 ⟨652507, by decide⟩ =
    .split (coordinate 12) (![⟨652397, by decide⟩,⟨652477, by decide⟩,⟨652497, by decide⟩,⟨652506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88107_652507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88107 ⟨652507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88107
    ⟨652507, by decide⟩ (by decide) (![⟨652397, by decide⟩,⟨652477, by decide⟩,⟨652497, by decide⟩,⟨652506, by decide⟩]) unmarked_context_12_88107_652507 node_context_12_88107_652507
  intro a
  fin_cases a
  · exact context_13_352428_652397
  · exact context_13_352429_652477
  · exact context_13_352430_652497
  · exact context_13_352431_652506

theorem unmarked_context_11_22026_652508 : frontier 10 ⟨652508, by decide⟩
    (prefixCache 11 22026) (prefixPartial 11 22026) = false := by
  decide +kernel

theorem node_context_11_22026_652508 : EJMOriginalGlobalDAGData.nodes 10 ⟨652508, by decide⟩ =
    .split (coordinate 11) (![⟨224339, by decide⟩,⟨652366, by decide⟩,⟨224365, by decide⟩,⟨652507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22026_652508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22026 ⟨652508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22026
    ⟨652508, by decide⟩ (by decide) (![⟨224339, by decide⟩,⟨652366, by decide⟩,⟨224365, by decide⟩,⟨652507, by decide⟩]) unmarked_context_11_22026_652508 node_context_11_22026_652508
  intro a
  fin_cases a
  · exact context_12_88104_224339
  · exact context_12_88105_652366
  · exact context_12_88106_224365
  · exact context_12_88107_652507

theorem selected_cut_25753 : selected 8 ⟨652519, by decide⟩
    (prefixPartial 13 352432) = some ⟨13, 2, 0, 652519, 352432, 665, 16384⟩ := by
  decide +kernel

theorem context_13_352432_652519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352432 ⟨652519, by decide⟩ :=
  accepted_of_selected 13 352432 ⟨652519, by decide⟩ ⟨13, 2, 0, 652519, 352432, 665, 16384⟩
    (by decide) selected_cut_25753

theorem selected_cut_25754 : selected 8 ⟨652554, by decide⟩
    (prefixPartial 13 352433) = some ⟨13, 2, 0, 652554, 352433, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_352433_652554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352433 ⟨652554, by decide⟩ :=
  accepted_of_selected 13 352433 ⟨652554, by decide⟩ ⟨13, 2, 0, 652554, 352433, 2197, 16384⟩
    (by decide) selected_cut_25754

theorem selected_cut_25755 : selected 8 ⟨652577, by decide⟩
    (prefixPartial 13 352434) = some ⟨13, 2, 0, 652577, 352434, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_352434_652577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352434 ⟨652577, by decide⟩ :=
  accepted_of_selected 13 352434 ⟨652577, by decide⟩ ⟨13, 2, 0, 652577, 352434, 1557, 16384⟩
    (by decide) selected_cut_25755

theorem selected_cut_25756 : selected 8 ⟨652582, by decide⟩
    (prefixPartial 13 352435) = some ⟨13, 2, 0, 652582, 352435, 865, 16384⟩ := by
  decide +kernel

theorem context_13_352435_652582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352435 ⟨652582, by decide⟩ :=
  accepted_of_selected 13 352435 ⟨652582, by decide⟩ ⟨13, 2, 0, 652582, 352435, 865, 16384⟩
    (by decide) selected_cut_25756

theorem unmarked_context_12_88108_652583 : frontier 9 ⟨652583, by decide⟩
    (prefixCache 12 88108) (prefixPartial 12 88108) = false := by
  decide +kernel

theorem node_context_12_88108_652583 : EJMOriginalGlobalDAGData.nodes 9 ⟨652583, by decide⟩ =
    .split (coordinate 12) (![⟨652519, by decide⟩,⟨652554, by decide⟩,⟨652577, by decide⟩,⟨652582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88108_652583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88108 ⟨652583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88108
    ⟨652583, by decide⟩ (by decide) (![⟨652519, by decide⟩,⟨652554, by decide⟩,⟨652577, by decide⟩,⟨652582, by decide⟩]) unmarked_context_12_88108_652583 node_context_12_88108_652583
  intro a
  fin_cases a
  · exact context_13_352432_652519
  · exact context_13_352433_652554
  · exact context_13_352434_652577
  · exact context_13_352435_652582

theorem selected_cut_25757 : selected 8 ⟨652597, by decide⟩
    (prefixPartial 13 352436) = some ⟨13, 2, 0, 652597, 352436, 769, 16384⟩ := by
  decide +kernel

theorem context_13_352436_652597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352436 ⟨652597, by decide⟩ :=
  accepted_of_selected 13 352436 ⟨652597, by decide⟩ ⟨13, 2, 0, 652597, 352436, 769, 16384⟩
    (by decide) selected_cut_25757

theorem selected_cut_25758 : selected 8 ⟨652625, by decide⟩
    (prefixPartial 13 352437) = some ⟨13, 2, 0, 652625, 352437, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_352437_652625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352437 ⟨652625, by decide⟩ :=
  accepted_of_selected 13 352437 ⟨652625, by decide⟩ ⟨13, 2, 0, 652625, 352437, 1949, 16384⟩
    (by decide) selected_cut_25758

theorem selected_cut_25759 : selected 8 ⟨652649, by decide⟩
    (prefixPartial 13 352438) = some ⟨13, 2, 0, 652649, 352438, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_352438_652649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352438 ⟨652649, by decide⟩ :=
  accepted_of_selected 13 352438 ⟨652649, by decide⟩ ⟨13, 2, 0, 652649, 352438, 1613, 16384⟩
    (by decide) selected_cut_25759

theorem selected_cut_25760 : selected 8 ⟨652656, by decide⟩
    (prefixPartial 13 352439) = some ⟨13, 2, 0, 652656, 352439, 889, 16384⟩ := by
  decide +kernel

theorem context_13_352439_652656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352439 ⟨652656, by decide⟩ :=
  accepted_of_selected 13 352439 ⟨652656, by decide⟩ ⟨13, 2, 0, 652656, 352439, 889, 16384⟩
    (by decide) selected_cut_25760

theorem unmarked_context_12_88109_652657 : frontier 9 ⟨652657, by decide⟩
    (prefixCache 12 88109) (prefixPartial 12 88109) = false := by
  decide +kernel

theorem node_context_12_88109_652657 : EJMOriginalGlobalDAGData.nodes 9 ⟨652657, by decide⟩ =
    .split (coordinate 12) (![⟨652597, by decide⟩,⟨652625, by decide⟩,⟨652649, by decide⟩,⟨652656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88109_652657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88109 ⟨652657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88109
    ⟨652657, by decide⟩ (by decide) (![⟨652597, by decide⟩,⟨652625, by decide⟩,⟨652649, by decide⟩,⟨652656, by decide⟩]) unmarked_context_12_88109_652657 node_context_12_88109_652657
  intro a
  fin_cases a
  · exact context_13_352436_652597
  · exact context_13_352437_652625
  · exact context_13_352438_652649
  · exact context_13_352439_652656

theorem selected_cut_25761 : selected 8 ⟨652670, by decide⟩
    (prefixPartial 13 352440) = some ⟨13, 2, 0, 652670, 352440, 817, 16384⟩ := by
  decide +kernel

theorem context_13_352440_652670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352440 ⟨652670, by decide⟩ :=
  accepted_of_selected 13 352440 ⟨652670, by decide⟩ ⟨13, 2, 0, 652670, 352440, 817, 16384⟩
    (by decide) selected_cut_25761

theorem selected_cut_25762 : selected 8 ⟨652711, by decide⟩
    (prefixPartial 13 352441) = some ⟨13, 2, 0, 652711, 352441, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_352441_652711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352441 ⟨652711, by decide⟩ :=
  accepted_of_selected 13 352441 ⟨652711, by decide⟩ ⟨13, 2, 0, 652711, 352441, 2505, 16384⟩
    (by decide) selected_cut_25762

theorem selected_cut_25763 : selected 8 ⟨652733, by decide⟩
    (prefixPartial 13 352442) = some ⟨13, 2, 0, 652733, 352442, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_352442_652733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352442 ⟨652733, by decide⟩ :=
  accepted_of_selected 13 352442 ⟨652733, by decide⟩ ⟨13, 2, 0, 652733, 352442, 1749, 16384⟩
    (by decide) selected_cut_25763

theorem selected_cut_25764 : selected 8 ⟨652739, by decide⟩
    (prefixPartial 13 352443) = some ⟨13, 2, 0, 652739, 352443, 865, 16384⟩ := by
  decide +kernel

theorem context_13_352443_652739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352443 ⟨652739, by decide⟩ :=
  accepted_of_selected 13 352443 ⟨652739, by decide⟩ ⟨13, 2, 0, 652739, 352443, 865, 16384⟩
    (by decide) selected_cut_25764

theorem unmarked_context_12_88110_652740 : frontier 9 ⟨652740, by decide⟩
    (prefixCache 12 88110) (prefixPartial 12 88110) = false := by
  decide +kernel

theorem node_context_12_88110_652740 : EJMOriginalGlobalDAGData.nodes 9 ⟨652740, by decide⟩ =
    .split (coordinate 12) (![⟨652670, by decide⟩,⟨652711, by decide⟩,⟨652733, by decide⟩,⟨652739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88110_652740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88110 ⟨652740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88110
    ⟨652740, by decide⟩ (by decide) (![⟨652670, by decide⟩,⟨652711, by decide⟩,⟨652733, by decide⟩,⟨652739, by decide⟩]) unmarked_context_12_88110_652740 node_context_12_88110_652740
  intro a
  fin_cases a
  · exact context_13_352440_652670
  · exact context_13_352441_652711
  · exact context_13_352442_652733
  · exact context_13_352443_652739

theorem selected_cut_25765 : selected 8 ⟨652750, by decide⟩
    (prefixPartial 13 352444) = some ⟨13, 2, 0, 652750, 352444, 677, 16384⟩ := by
  decide +kernel

theorem context_13_352444_652750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352444 ⟨652750, by decide⟩ :=
  accepted_of_selected 13 352444 ⟨652750, by decide⟩ ⟨13, 2, 0, 652750, 352444, 677, 16384⟩
    (by decide) selected_cut_25765

theorem selected_cut_25766 : selected 8 ⟨652792, by decide⟩
    (prefixPartial 13 352445) = some ⟨13, 2, 0, 652792, 352445, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_352445_652792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352445 ⟨652792, by decide⟩ :=
  accepted_of_selected 13 352445 ⟨652792, by decide⟩ ⟨13, 2, 0, 652792, 352445, 2469, 16384⟩
    (by decide) selected_cut_25766

theorem selected_cut_25767 : selected 8 ⟨652808, by decide⟩
    (prefixPartial 13 352446) = some ⟨13, 2, 0, 652808, 352446, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_352446_652808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352446 ⟨652808, by decide⟩ :=
  accepted_of_selected 13 352446 ⟨652808, by decide⟩ ⟨13, 2, 0, 652808, 352446, 1317, 16384⟩
    (by decide) selected_cut_25767

theorem selected_cut_25768 : selected 8 ⟨652814, by decide⟩
    (prefixPartial 13 352447) = some ⟨13, 2, 0, 652814, 352447, 793, 16384⟩ := by
  decide +kernel

theorem context_13_352447_652814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352447 ⟨652814, by decide⟩ :=
  accepted_of_selected 13 352447 ⟨652814, by decide⟩ ⟨13, 2, 0, 652814, 352447, 793, 16384⟩
    (by decide) selected_cut_25768

theorem unmarked_context_12_88111_652815 : frontier 9 ⟨652815, by decide⟩
    (prefixCache 12 88111) (prefixPartial 12 88111) = false := by
  decide +kernel

theorem node_context_12_88111_652815 : EJMOriginalGlobalDAGData.nodes 9 ⟨652815, by decide⟩ =
    .split (coordinate 12) (![⟨652750, by decide⟩,⟨652792, by decide⟩,⟨652808, by decide⟩,⟨652814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88111_652815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88111 ⟨652815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88111
    ⟨652815, by decide⟩ (by decide) (![⟨652750, by decide⟩,⟨652792, by decide⟩,⟨652808, by decide⟩,⟨652814, by decide⟩]) unmarked_context_12_88111_652815 node_context_12_88111_652815
  intro a
  fin_cases a
  · exact context_13_352444_652750
  · exact context_13_352445_652792
  · exact context_13_352446_652808
  · exact context_13_352447_652814

theorem unmarked_context_11_22027_652816 : frontier 10 ⟨652816, by decide⟩
    (prefixCache 11 22027) (prefixPartial 11 22027) = false := by
  decide +kernel

theorem node_context_11_22027_652816 : EJMOriginalGlobalDAGData.nodes 10 ⟨652816, by decide⟩ =
    .split (coordinate 11) (![⟨652583, by decide⟩,⟨652657, by decide⟩,⟨652740, by decide⟩,⟨652815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22027_652816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22027 ⟨652816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22027
    ⟨652816, by decide⟩ (by decide) (![⟨652583, by decide⟩,⟨652657, by decide⟩,⟨652740, by decide⟩,⟨652815, by decide⟩]) unmarked_context_11_22027_652816 node_context_11_22027_652816
  intro a
  fin_cases a
  · exact context_12_88108_652583
  · exact context_12_88109_652657
  · exact context_12_88110_652740
  · exact context_12_88111_652815

theorem unmarked_context_10_5506_652817 : frontier 11 ⟨652817, by decide⟩
    (prefixCache 10 5506) (prefixPartial 10 5506) = false := by
  decide +kernel

theorem node_context_10_5506_652817 : EJMOriginalGlobalDAGData.nodes 11 ⟨652817, by decide⟩ =
    .split (coordinate 10) (![⟨651950, by decide⟩,⟨652248, by decide⟩,⟨652508, by decide⟩,⟨652816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5506_652817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5506 ⟨652817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5506
    ⟨652817, by decide⟩ (by decide) (![⟨651950, by decide⟩,⟨652248, by decide⟩,⟨652508, by decide⟩,⟨652816, by decide⟩]) unmarked_context_10_5506_652817 node_context_10_5506_652817
  intro a
  fin_cases a
  · exact context_11_22024_651950
  · exact context_11_22025_652248
  · exact context_11_22026_652508
  · exact context_11_22027_652816

theorem selected_cut_25769 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 88112) = some ⟨12, 1, 0, 641337, 88112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88112_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88112 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 88112 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 88112, 1, 65536⟩
    (by decide) selected_cut_25769

theorem selected_cut_25770 : selected 8 ⟨652832, by decide⟩
    (prefixPartial 13 352452) = some ⟨13, 2, 0, 652832, 352452, 673, 16384⟩ := by
  decide +kernel

theorem context_13_352452_652832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352452 ⟨652832, by decide⟩ :=
  accepted_of_selected 13 352452 ⟨652832, by decide⟩ ⟨13, 2, 0, 652832, 352452, 673, 16384⟩
    (by decide) selected_cut_25770

theorem selected_cut_25771 : selected 8 ⟨652862, by decide⟩
    (prefixPartial 13 352453) = some ⟨13, 2, 0, 652862, 352453, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_352453_652862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352453 ⟨652862, by decide⟩ :=
  accepted_of_selected 13 352453 ⟨652862, by decide⟩ ⟨13, 2, 0, 652862, 352453, 1905, 16384⟩
    (by decide) selected_cut_25771

theorem selected_cut_25772 : selected 8 ⟨652877, by decide⟩
    (prefixPartial 13 352454) = some ⟨13, 2, 0, 652877, 352454, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_352454_652877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352454 ⟨652877, by decide⟩ :=
  accepted_of_selected 13 352454 ⟨652877, by decide⟩ ⟨13, 2, 0, 652877, 352454, 1285, 16384⟩
    (by decide) selected_cut_25772

theorem selected_cut_25773 : selected 8 ⟨652881, by decide⟩
    (prefixPartial 13 352455) = some ⟨13, 2, 0, 652881, 352455, 761, 16384⟩ := by
  decide +kernel

theorem context_13_352455_652881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352455 ⟨652881, by decide⟩ :=
  accepted_of_selected 13 352455 ⟨652881, by decide⟩ ⟨13, 2, 0, 652881, 352455, 761, 16384⟩
    (by decide) selected_cut_25773

theorem unmarked_context_12_88113_652882 : frontier 9 ⟨652882, by decide⟩
    (prefixCache 12 88113) (prefixPartial 12 88113) = false := by
  decide +kernel

theorem node_context_12_88113_652882 : EJMOriginalGlobalDAGData.nodes 9 ⟨652882, by decide⟩ =
    .split (coordinate 12) (![⟨652832, by decide⟩,⟨652862, by decide⟩,⟨652877, by decide⟩,⟨652881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88113_652882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88113 ⟨652882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88113
    ⟨652882, by decide⟩ (by decide) (![⟨652832, by decide⟩,⟨652862, by decide⟩,⟨652877, by decide⟩,⟨652881, by decide⟩]) unmarked_context_12_88113_652882 node_context_12_88113_652882
  intro a
  fin_cases a
  · exact context_13_352452_652832
  · exact context_13_352453_652862
  · exact context_13_352454_652877
  · exact context_13_352455_652881

theorem selected_cut_25774 : selected 8 ⟨652896, by decide⟩
    (prefixPartial 13 352456) = some ⟨13, 2, 0, 652896, 352456, 641, 16384⟩ := by
  decide +kernel

theorem context_13_352456_652896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352456 ⟨652896, by decide⟩ :=
  accepted_of_selected 13 352456 ⟨652896, by decide⟩ ⟨13, 2, 0, 652896, 352456, 641, 16384⟩
    (by decide) selected_cut_25774

theorem selected_cut_25775 : selected 8 ⟨652920, by decide⟩
    (prefixPartial 13 352457) = some ⟨13, 2, 0, 652920, 352457, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_352457_652920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352457 ⟨652920, by decide⟩ :=
  accepted_of_selected 13 352457 ⟨652920, by decide⟩ ⟨13, 2, 0, 652920, 352457, 2197, 16384⟩
    (by decide) selected_cut_25775

theorem selected_cut_25776 : selected 8 ⟨652942, by decide⟩
    (prefixPartial 13 352458) = some ⟨13, 2, 0, 652942, 352458, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_352458_652942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352458 ⟨652942, by decide⟩ :=
  accepted_of_selected 13 352458 ⟨652942, by decide⟩ ⟨13, 2, 0, 652942, 352458, 1501, 16384⟩
    (by decide) selected_cut_25776

theorem selected_cut_25777 : selected 8 ⟨652948, by decide⟩
    (prefixPartial 13 352459) = some ⟨13, 2, 0, 652948, 352459, 821, 16384⟩ := by
  decide +kernel

theorem context_13_352459_652948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352459 ⟨652948, by decide⟩ :=
  accepted_of_selected 13 352459 ⟨652948, by decide⟩ ⟨13, 2, 0, 652948, 352459, 821, 16384⟩
    (by decide) selected_cut_25777

theorem unmarked_context_12_88114_652949 : frontier 9 ⟨652949, by decide⟩
    (prefixCache 12 88114) (prefixPartial 12 88114) = false := by
  decide +kernel

theorem node_context_12_88114_652949 : EJMOriginalGlobalDAGData.nodes 9 ⟨652949, by decide⟩ =
    .split (coordinate 12) (![⟨652896, by decide⟩,⟨652920, by decide⟩,⟨652942, by decide⟩,⟨652948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88114_652949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88114 ⟨652949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88114
    ⟨652949, by decide⟩ (by decide) (![⟨652896, by decide⟩,⟨652920, by decide⟩,⟨652942, by decide⟩,⟨652948, by decide⟩]) unmarked_context_12_88114_652949 node_context_12_88114_652949
  intro a
  fin_cases a
  · exact context_13_352456_652896
  · exact context_13_352457_652920
  · exact context_13_352458_652942
  · exact context_13_352459_652948

theorem selected_cut_25778 : selected 8 ⟨652965, by decide⟩
    (prefixPartial 13 352460) = some ⟨13, 2, 0, 652965, 352460, 653, 16384⟩ := by
  decide +kernel

theorem context_13_352460_652965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352460 ⟨652965, by decide⟩ :=
  accepted_of_selected 13 352460 ⟨652965, by decide⟩ ⟨13, 2, 0, 652965, 352460, 653, 16384⟩
    (by decide) selected_cut_25778

theorem selected_cut_25779 : selected 8 ⟨653003, by decide⟩
    (prefixPartial 13 352461) = some ⟨13, 2, 0, 653003, 352461, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_352461_653003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352461 ⟨653003, by decide⟩ :=
  accepted_of_selected 13 352461 ⟨653003, by decide⟩ ⟨13, 2, 0, 653003, 352461, 2541, 16384⟩
    (by decide) selected_cut_25779

theorem selected_cut_25780 : selected 8 ⟨653024, by decide⟩
    (prefixPartial 13 352462) = some ⟨13, 2, 0, 653024, 352462, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_352462_653024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352462 ⟨653024, by decide⟩ :=
  accepted_of_selected 13 352462 ⟨653024, by decide⟩ ⟨13, 2, 0, 653024, 352462, 1701, 16384⟩
    (by decide) selected_cut_25780

theorem selected_cut_25781 : selected 8 ⟨653028, by decide⟩
    (prefixPartial 13 352463) = some ⟨13, 2, 0, 653028, 352463, 725, 16384⟩ := by
  decide +kernel

theorem context_13_352463_653028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352463 ⟨653028, by decide⟩ :=
  accepted_of_selected 13 352463 ⟨653028, by decide⟩ ⟨13, 2, 0, 653028, 352463, 725, 16384⟩
    (by decide) selected_cut_25781

theorem unmarked_context_12_88115_653029 : frontier 9 ⟨653029, by decide⟩
    (prefixCache 12 88115) (prefixPartial 12 88115) = false := by
  decide +kernel

theorem node_context_12_88115_653029 : EJMOriginalGlobalDAGData.nodes 9 ⟨653029, by decide⟩ =
    .split (coordinate 12) (![⟨652965, by decide⟩,⟨653003, by decide⟩,⟨653024, by decide⟩,⟨653028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88115_653029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88115 ⟨653029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88115
    ⟨653029, by decide⟩ (by decide) (![⟨652965, by decide⟩,⟨653003, by decide⟩,⟨653024, by decide⟩,⟨653028, by decide⟩]) unmarked_context_12_88115_653029 node_context_12_88115_653029
  intro a
  fin_cases a
  · exact context_13_352460_652965
  · exact context_13_352461_653003
  · exact context_13_352462_653024
  · exact context_13_352463_653028

theorem unmarked_context_11_22028_653030 : frontier 10 ⟨653030, by decide⟩
    (prefixCache 11 22028) (prefixPartial 11 22028) = false := by
  decide +kernel

theorem node_context_11_22028_653030 : EJMOriginalGlobalDAGData.nodes 10 ⟨653030, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨652882, by decide⟩,⟨652949, by decide⟩,⟨653029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22028_653030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22028 ⟨653030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22028
    ⟨653030, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨652882, by decide⟩,⟨652949, by decide⟩,⟨653029, by decide⟩]) unmarked_context_11_22028_653030 node_context_11_22028_653030
  intro a
  fin_cases a
  · exact context_12_88112_641337
  · exact context_12_88113_652882
  · exact context_12_88114_652949
  · exact context_12_88115_653029

theorem selected_cut_25782 : selected 8 ⟨653035, by decide⟩
    (prefixPartial 13 352464) = some ⟨13, 2, 0, 653035, 352464, 421, 16384⟩ := by
  decide +kernel

theorem context_13_352464_653035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352464 ⟨653035, by decide⟩ :=
  accepted_of_selected 13 352464 ⟨653035, by decide⟩ ⟨13, 2, 0, 653035, 352464, 421, 16384⟩
    (by decide) selected_cut_25782

theorem selected_cut_25783 : selected 8 ⟨653067, by decide⟩
    (prefixPartial 13 352465) = some ⟨13, 2, 0, 653067, 352465, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_352465_653067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352465 ⟨653067, by decide⟩ :=
  accepted_of_selected 13 352465 ⟨653067, by decide⟩ ⟨13, 2, 0, 653067, 352465, 2277, 16384⟩
    (by decide) selected_cut_25783

theorem selected_cut_25784 : selected 8 ⟨653087, by decide⟩
    (prefixPartial 13 352466) = some ⟨13, 2, 0, 653087, 352466, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_352466_653087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352466 ⟨653087, by decide⟩ :=
  accepted_of_selected 13 352466 ⟨653087, by decide⟩ ⟨13, 2, 0, 653087, 352466, 1505, 16384⟩
    (by decide) selected_cut_25784

theorem selected_cut_25785 : selected 8 ⟨653093, by decide⟩
    (prefixPartial 13 352467) = some ⟨13, 2, 0, 653093, 352467, 785, 16384⟩ := by
  decide +kernel

theorem context_13_352467_653093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352467 ⟨653093, by decide⟩ :=
  accepted_of_selected 13 352467 ⟨653093, by decide⟩ ⟨13, 2, 0, 653093, 352467, 785, 16384⟩
    (by decide) selected_cut_25785

theorem unmarked_context_12_88116_653094 : frontier 9 ⟨653094, by decide⟩
    (prefixCache 12 88116) (prefixPartial 12 88116) = false := by
  decide +kernel

theorem node_context_12_88116_653094 : EJMOriginalGlobalDAGData.nodes 9 ⟨653094, by decide⟩ =
    .split (coordinate 12) (![⟨653035, by decide⟩,⟨653067, by decide⟩,⟨653087, by decide⟩,⟨653093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88116_653094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88116 ⟨653094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88116
    ⟨653094, by decide⟩ (by decide) (![⟨653035, by decide⟩,⟨653067, by decide⟩,⟨653087, by decide⟩,⟨653093, by decide⟩]) unmarked_context_12_88116_653094 node_context_12_88116_653094
  intro a
  fin_cases a
  · exact context_13_352464_653035
  · exact context_13_352465_653067
  · exact context_13_352466_653087
  · exact context_13_352467_653093

theorem selected_cut_25786 : selected 8 ⟨653105, by decide⟩
    (prefixPartial 13 352468) = some ⟨13, 2, 0, 653105, 352468, 481, 16384⟩ := by
  decide +kernel

theorem context_13_352468_653105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352468 ⟨653105, by decide⟩ :=
  accepted_of_selected 13 352468 ⟨653105, by decide⟩ ⟨13, 2, 0, 653105, 352468, 481, 16384⟩
    (by decide) selected_cut_25786

theorem selected_cut_25787 : selected 8 ⟨653134, by decide⟩
    (prefixPartial 13 352469) = some ⟨13, 2, 0, 653134, 352469, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_352469_653134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352469 ⟨653134, by decide⟩ :=
  accepted_of_selected 13 352469 ⟨653134, by decide⟩ ⟨13, 2, 0, 653134, 352469, 1909, 16384⟩
    (by decide) selected_cut_25787

theorem selected_cut_25788 : selected 8 ⟨653151, by decide⟩
    (prefixPartial 13 352470) = some ⟨13, 2, 0, 653151, 352470, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_352470_653151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352470 ⟨653151, by decide⟩ :=
  accepted_of_selected 13 352470 ⟨653151, by decide⟩ ⟨13, 2, 0, 653151, 352470, 1305, 16384⟩
    (by decide) selected_cut_25788

theorem selected_cut_25789 : selected 8 ⟨653155, by decide⟩
    (prefixPartial 13 352471) = some ⟨13, 2, 0, 653155, 352471, 741, 16384⟩ := by
  decide +kernel

theorem context_13_352471_653155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352471 ⟨653155, by decide⟩ :=
  accepted_of_selected 13 352471 ⟨653155, by decide⟩ ⟨13, 2, 0, 653155, 352471, 741, 16384⟩
    (by decide) selected_cut_25789

theorem unmarked_context_12_88117_653156 : frontier 9 ⟨653156, by decide⟩
    (prefixCache 12 88117) (prefixPartial 12 88117) = false := by
  decide +kernel

theorem node_context_12_88117_653156 : EJMOriginalGlobalDAGData.nodes 9 ⟨653156, by decide⟩ =
    .split (coordinate 12) (![⟨653105, by decide⟩,⟨653134, by decide⟩,⟨653151, by decide⟩,⟨653155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88117_653156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88117 ⟨653156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88117
    ⟨653156, by decide⟩ (by decide) (![⟨653105, by decide⟩,⟨653134, by decide⟩,⟨653151, by decide⟩,⟨653155, by decide⟩]) unmarked_context_12_88117_653156 node_context_12_88117_653156
  intro a
  fin_cases a
  · exact context_13_352468_653105
  · exact context_13_352469_653134
  · exact context_13_352470_653151
  · exact context_13_352471_653155

theorem selected_cut_25790 : selected 8 ⟨653166, by decide⟩
    (prefixPartial 13 352472) = some ⟨13, 2, 0, 653166, 352472, 581, 16384⟩ := by
  decide +kernel

theorem context_13_352472_653166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352472 ⟨653166, by decide⟩ :=
  accepted_of_selected 13 352472 ⟨653166, by decide⟩ ⟨13, 2, 0, 653166, 352472, 581, 16384⟩
    (by decide) selected_cut_25790

theorem selected_cut_25791 : selected 8 ⟨653197, by decide⟩
    (prefixPartial 13 352473) = some ⟨13, 2, 0, 653197, 352473, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_352473_653197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352473 ⟨653197, by decide⟩ :=
  accepted_of_selected 13 352473 ⟨653197, by decide⟩ ⟨13, 2, 0, 653197, 352473, 2585, 16384⟩
    (by decide) selected_cut_25791

theorem selected_cut_25792 : selected 8 ⟨653212, by decide⟩
    (prefixPartial 13 352474) = some ⟨13, 2, 0, 653212, 352474, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_352474_653212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352474 ⟨653212, by decide⟩ :=
  accepted_of_selected 13 352474 ⟨653212, by decide⟩ ⟨13, 2, 0, 653212, 352474, 1525, 16384⟩
    (by decide) selected_cut_25792

theorem selected_cut_25793 : selected 8 ⟨653216, by decide⟩
    (prefixPartial 13 352475) = some ⟨13, 2, 0, 653216, 352475, 761, 16384⟩ := by
  decide +kernel

theorem context_13_352475_653216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352475 ⟨653216, by decide⟩ :=
  accepted_of_selected 13 352475 ⟨653216, by decide⟩ ⟨13, 2, 0, 653216, 352475, 761, 16384⟩
    (by decide) selected_cut_25793

theorem unmarked_context_12_88118_653217 : frontier 9 ⟨653217, by decide⟩
    (prefixCache 12 88118) (prefixPartial 12 88118) = false := by
  decide +kernel

theorem node_context_12_88118_653217 : EJMOriginalGlobalDAGData.nodes 9 ⟨653217, by decide⟩ =
    .split (coordinate 12) (![⟨653166, by decide⟩,⟨653197, by decide⟩,⟨653212, by decide⟩,⟨653216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88118_653217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88118 ⟨653217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88118
    ⟨653217, by decide⟩ (by decide) (![⟨653166, by decide⟩,⟨653197, by decide⟩,⟨653212, by decide⟩,⟨653216, by decide⟩]) unmarked_context_12_88118_653217 node_context_12_88118_653217
  intro a
  fin_cases a
  · exact context_13_352472_653166
  · exact context_13_352473_653197
  · exact context_13_352474_653212
  · exact context_13_352475_653216

theorem selected_cut_25794 : selected 8 ⟨653227, by decide⟩
    (prefixPartial 13 352476) = some ⟨13, 2, 0, 653227, 352476, 485, 16384⟩ := by
  decide +kernel

theorem context_13_352476_653227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352476 ⟨653227, by decide⟩ :=
  accepted_of_selected 13 352476 ⟨653227, by decide⟩ ⟨13, 2, 0, 653227, 352476, 485, 16384⟩
    (by decide) selected_cut_25794

theorem selected_cut_25795 : selected 8 ⟨653287, by decide⟩
    (prefixPartial 13 352477) = some ⟨13, 2, 0, 653287, 352477, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_352477_653287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352477 ⟨653287, by decide⟩ :=
  accepted_of_selected 13 352477 ⟨653287, by decide⟩ ⟨13, 2, 0, 653287, 352477, 2957, 16384⟩
    (by decide) selected_cut_25795

theorem selected_cut_25796 : selected 8 ⟨653306, by decide⟩
    (prefixPartial 13 352478) = some ⟨13, 2, 0, 653306, 352478, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_352478_653306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352478 ⟨653306, by decide⟩ :=
  accepted_of_selected 13 352478 ⟨653306, by decide⟩ ⟨13, 2, 0, 653306, 352478, 1605, 16384⟩
    (by decide) selected_cut_25796

theorem selected_cut_25797 : selected 8 ⟨653310, by decide⟩
    (prefixPartial 13 352479) = some ⟨13, 2, 0, 653310, 352479, 721, 16384⟩ := by
  decide +kernel

theorem context_13_352479_653310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352479 ⟨653310, by decide⟩ :=
  accepted_of_selected 13 352479 ⟨653310, by decide⟩ ⟨13, 2, 0, 653310, 352479, 721, 16384⟩
    (by decide) selected_cut_25797

theorem unmarked_context_12_88119_653311 : frontier 9 ⟨653311, by decide⟩
    (prefixCache 12 88119) (prefixPartial 12 88119) = false := by
  decide +kernel

theorem node_context_12_88119_653311 : EJMOriginalGlobalDAGData.nodes 9 ⟨653311, by decide⟩ =
    .split (coordinate 12) (![⟨653227, by decide⟩,⟨653287, by decide⟩,⟨653306, by decide⟩,⟨653310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88119_653311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88119 ⟨653311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88119
    ⟨653311, by decide⟩ (by decide) (![⟨653227, by decide⟩,⟨653287, by decide⟩,⟨653306, by decide⟩,⟨653310, by decide⟩]) unmarked_context_12_88119_653311 node_context_12_88119_653311
  intro a
  fin_cases a
  · exact context_13_352476_653227
  · exact context_13_352477_653287
  · exact context_13_352478_653306
  · exact context_13_352479_653310

theorem unmarked_context_11_22029_653312 : frontier 10 ⟨653312, by decide⟩
    (prefixCache 11 22029) (prefixPartial 11 22029) = false := by
  decide +kernel

theorem node_context_11_22029_653312 : EJMOriginalGlobalDAGData.nodes 10 ⟨653312, by decide⟩ =
    .split (coordinate 11) (![⟨653094, by decide⟩,⟨653156, by decide⟩,⟨653217, by decide⟩,⟨653311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22029_653312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22029 ⟨653312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22029
    ⟨653312, by decide⟩ (by decide) (![⟨653094, by decide⟩,⟨653156, by decide⟩,⟨653217, by decide⟩,⟨653311, by decide⟩]) unmarked_context_11_22029_653312 node_context_11_22029_653312
  intro a
  fin_cases a
  · exact context_12_88116_653094
  · exact context_12_88117_653156
  · exact context_12_88118_653217
  · exact context_12_88119_653311

theorem selected_cut_25798 : selected 8 ⟨653319, by decide⟩
    (prefixPartial 13 352480) = some ⟨13, 2, 0, 653319, 352480, 321, 16384⟩ := by
  decide +kernel

theorem context_13_352480_653319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352480 ⟨653319, by decide⟩ :=
  accepted_of_selected 13 352480 ⟨653319, by decide⟩ ⟨13, 2, 0, 653319, 352480, 321, 16384⟩
    (by decide) selected_cut_25798

theorem selected_cut_25799 : selected 8 ⟨653349, by decide⟩
    (prefixPartial 13 352481) = some ⟨13, 2, 0, 653349, 352481, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_352481_653349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352481 ⟨653349, by decide⟩ :=
  accepted_of_selected 13 352481 ⟨653349, by decide⟩ ⟨13, 2, 0, 653349, 352481, 2273, 16384⟩
    (by decide) selected_cut_25799

theorem selected_cut_25800 : selected 8 ⟨653370, by decide⟩
    (prefixPartial 13 352482) = some ⟨13, 2, 0, 653370, 352482, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_352482_653370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352482 ⟨653370, by decide⟩ :=
  accepted_of_selected 13 352482 ⟨653370, by decide⟩ ⟨13, 2, 0, 653370, 352482, 1717, 16384⟩
    (by decide) selected_cut_25800

theorem selected_cut_25801 : selected 8 ⟨653376, by decide⟩
    (prefixPartial 13 352483) = some ⟨13, 2, 0, 653376, 352483, 729, 16384⟩ := by
  decide +kernel

theorem context_13_352483_653376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352483 ⟨653376, by decide⟩ :=
  accepted_of_selected 13 352483 ⟨653376, by decide⟩ ⟨13, 2, 0, 653376, 352483, 729, 16384⟩
    (by decide) selected_cut_25801

theorem unmarked_context_12_88120_653377 : frontier 9 ⟨653377, by decide⟩
    (prefixCache 12 88120) (prefixPartial 12 88120) = false := by
  decide +kernel

theorem node_context_12_88120_653377 : EJMOriginalGlobalDAGData.nodes 9 ⟨653377, by decide⟩ =
    .split (coordinate 12) (![⟨653319, by decide⟩,⟨653349, by decide⟩,⟨653370, by decide⟩,⟨653376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88120_653377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88120 ⟨653377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88120
    ⟨653377, by decide⟩ (by decide) (![⟨653319, by decide⟩,⟨653349, by decide⟩,⟨653370, by decide⟩,⟨653376, by decide⟩]) unmarked_context_12_88120_653377 node_context_12_88120_653377
  intro a
  fin_cases a
  · exact context_13_352480_653319
  · exact context_13_352481_653349
  · exact context_13_352482_653370
  · exact context_13_352483_653376

theorem selected_cut_25802 : selected 8 ⟨653385, by decide⟩
    (prefixPartial 13 352484) = some ⟨13, 2, 0, 653385, 352484, 353, 16384⟩ := by
  decide +kernel

theorem context_13_352484_653385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352484 ⟨653385, by decide⟩ :=
  accepted_of_selected 13 352484 ⟨653385, by decide⟩ ⟨13, 2, 0, 653385, 352484, 353, 16384⟩
    (by decide) selected_cut_25802

theorem selected_cut_25803 : selected 8 ⟨653412, by decide⟩
    (prefixPartial 13 352485) = some ⟨13, 2, 0, 653412, 352485, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_352485_653412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352485 ⟨653412, by decide⟩ :=
  accepted_of_selected 13 352485 ⟨653412, by decide⟩ ⟨13, 2, 0, 653412, 352485, 2141, 16384⟩
    (by decide) selected_cut_25803

theorem selected_cut_25804 : selected 8 ⟨653435, by decide⟩
    (prefixPartial 13 352486) = some ⟨13, 2, 0, 653435, 352486, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_352486_653435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352486 ⟨653435, by decide⟩ :=
  accepted_of_selected 13 352486 ⟨653435, by decide⟩ ⟨13, 2, 0, 653435, 352486, 1709, 16384⟩
    (by decide) selected_cut_25804

theorem selected_cut_25805 : selected 8 ⟨653441, by decide⟩
    (prefixPartial 13 352487) = some ⟨13, 2, 0, 653441, 352487, 829, 16384⟩ := by
  decide +kernel

theorem context_13_352487_653441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352487 ⟨653441, by decide⟩ :=
  accepted_of_selected 13 352487 ⟨653441, by decide⟩ ⟨13, 2, 0, 653441, 352487, 829, 16384⟩
    (by decide) selected_cut_25805

theorem unmarked_context_12_88121_653442 : frontier 9 ⟨653442, by decide⟩
    (prefixCache 12 88121) (prefixPartial 12 88121) = false := by
  decide +kernel

theorem node_context_12_88121_653442 : EJMOriginalGlobalDAGData.nodes 9 ⟨653442, by decide⟩ =
    .split (coordinate 12) (![⟨653385, by decide⟩,⟨653412, by decide⟩,⟨653435, by decide⟩,⟨653441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88121_653442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88121 ⟨653442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88121
    ⟨653442, by decide⟩ (by decide) (![⟨653385, by decide⟩,⟨653412, by decide⟩,⟨653435, by decide⟩,⟨653441, by decide⟩]) unmarked_context_12_88121_653442 node_context_12_88121_653442
  intro a
  fin_cases a
  · exact context_13_352484_653385
  · exact context_13_352485_653412
  · exact context_13_352486_653435
  · exact context_13_352487_653441

theorem selected_cut_25806 : selected 8 ⟨653449, by decide⟩
    (prefixPartial 13 352488) = some ⟨13, 2, 0, 653449, 352488, 261, 16384⟩ := by
  decide +kernel

theorem context_13_352488_653449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352488 ⟨653449, by decide⟩ :=
  accepted_of_selected 13 352488 ⟨653449, by decide⟩ ⟨13, 2, 0, 653449, 352488, 261, 16384⟩
    (by decide) selected_cut_25806

theorem selected_cut_25807 : selected 8 ⟨653481, by decide⟩
    (prefixPartial 13 352489) = some ⟨13, 2, 0, 653481, 352489, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_352489_653481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352489 ⟨653481, by decide⟩ :=
  accepted_of_selected 13 352489 ⟨653481, by decide⟩ ⟨13, 2, 0, 653481, 352489, 2281, 16384⟩
    (by decide) selected_cut_25807

theorem selected_cut_25808 : selected 8 ⟨653497, by decide⟩
    (prefixPartial 13 352490) = some ⟨13, 2, 0, 653497, 352490, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_352490_653497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352490 ⟨653497, by decide⟩ :=
  accepted_of_selected 13 352490 ⟨653497, by decide⟩ ⟨13, 2, 0, 653497, 352490, 1513, 16384⟩
    (by decide) selected_cut_25808

theorem selected_cut_25809 : selected 8 ⟨653501, by decide⟩
    (prefixPartial 13 352491) = some ⟨13, 2, 0, 653501, 352491, 713, 16384⟩ := by
  decide +kernel

theorem context_13_352491_653501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352491 ⟨653501, by decide⟩ :=
  accepted_of_selected 13 352491 ⟨653501, by decide⟩ ⟨13, 2, 0, 653501, 352491, 713, 16384⟩
    (by decide) selected_cut_25809

theorem unmarked_context_12_88122_653502 : frontier 9 ⟨653502, by decide⟩
    (prefixCache 12 88122) (prefixPartial 12 88122) = false := by
  decide +kernel

theorem node_context_12_88122_653502 : EJMOriginalGlobalDAGData.nodes 9 ⟨653502, by decide⟩ =
    .split (coordinate 12) (![⟨653449, by decide⟩,⟨653481, by decide⟩,⟨653497, by decide⟩,⟨653501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88122_653502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88122 ⟨653502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88122
    ⟨653502, by decide⟩ (by decide) (![⟨653449, by decide⟩,⟨653481, by decide⟩,⟨653497, by decide⟩,⟨653501, by decide⟩]) unmarked_context_12_88122_653502 node_context_12_88122_653502
  intro a
  fin_cases a
  · exact context_13_352488_653449
  · exact context_13_352489_653481
  · exact context_13_352490_653497
  · exact context_13_352491_653501

theorem selected_cut_25810 : selected 8 ⟨653510, by decide⟩
    (prefixPartial 13 352492) = some ⟨13, 2, 0, 653510, 352492, 257, 16384⟩ := by
  decide +kernel

theorem context_13_352492_653510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352492 ⟨653510, by decide⟩ :=
  accepted_of_selected 13 352492 ⟨653510, by decide⟩ ⟨13, 2, 0, 653510, 352492, 257, 16384⟩
    (by decide) selected_cut_25810

theorem selected_cut_25811 : selected 8 ⟨653558, by decide⟩
    (prefixPartial 13 352493) = some ⟨13, 2, 0, 653558, 352493, 3037, 16384⟩ := by
  decide +kernel

theorem context_13_352493_653558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352493 ⟨653558, by decide⟩ :=
  accepted_of_selected 13 352493 ⟨653558, by decide⟩ ⟨13, 2, 0, 653558, 352493, 3037, 16384⟩
    (by decide) selected_cut_25811

theorem selected_cut_25812 : selected 8 ⟨653578, by decide⟩
    (prefixPartial 13 352494) = some ⟨13, 2, 0, 653578, 352494, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_352494_653578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352494 ⟨653578, by decide⟩ :=
  accepted_of_selected 13 352494 ⟨653578, by decide⟩ ⟨13, 2, 0, 653578, 352494, 1773, 16384⟩
    (by decide) selected_cut_25812

theorem selected_cut_25813 : selected 8 ⟨653584, by decide⟩
    (prefixPartial 13 352495) = some ⟨13, 2, 0, 653584, 352495, 805, 16384⟩ := by
  decide +kernel

theorem context_13_352495_653584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352495 ⟨653584, by decide⟩ :=
  accepted_of_selected 13 352495 ⟨653584, by decide⟩ ⟨13, 2, 0, 653584, 352495, 805, 16384⟩
    (by decide) selected_cut_25813

theorem unmarked_context_12_88123_653585 : frontier 9 ⟨653585, by decide⟩
    (prefixCache 12 88123) (prefixPartial 12 88123) = false := by
  decide +kernel

theorem node_context_12_88123_653585 : EJMOriginalGlobalDAGData.nodes 9 ⟨653585, by decide⟩ =
    .split (coordinate 12) (![⟨653510, by decide⟩,⟨653558, by decide⟩,⟨653578, by decide⟩,⟨653584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88123_653585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88123 ⟨653585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88123
    ⟨653585, by decide⟩ (by decide) (![⟨653510, by decide⟩,⟨653558, by decide⟩,⟨653578, by decide⟩,⟨653584, by decide⟩]) unmarked_context_12_88123_653585 node_context_12_88123_653585
  intro a
  fin_cases a
  · exact context_13_352492_653510
  · exact context_13_352493_653558
  · exact context_13_352494_653578
  · exact context_13_352495_653584

theorem unmarked_context_11_22030_653586 : frontier 10 ⟨653586, by decide⟩
    (prefixCache 11 22030) (prefixPartial 11 22030) = false := by
  decide +kernel

theorem node_context_11_22030_653586 : EJMOriginalGlobalDAGData.nodes 10 ⟨653586, by decide⟩ =
    .split (coordinate 11) (![⟨653377, by decide⟩,⟨653442, by decide⟩,⟨653502, by decide⟩,⟨653585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22030_653586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22030 ⟨653586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22030
    ⟨653586, by decide⟩ (by decide) (![⟨653377, by decide⟩,⟨653442, by decide⟩,⟨653502, by decide⟩,⟨653585, by decide⟩]) unmarked_context_11_22030_653586 node_context_11_22030_653586
  intro a
  fin_cases a
  · exact context_12_88120_653377
  · exact context_12_88121_653442
  · exact context_12_88122_653502
  · exact context_12_88123_653585

theorem selected_cut_25814 : selected 8 ⟨653588, by decide⟩
    (prefixPartial 13 352496) = some ⟨13, 2, 0, 653588, 352496, 125, 16384⟩ := by
  decide +kernel

theorem context_13_352496_653588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352496 ⟨653588, by decide⟩ :=
  accepted_of_selected 13 352496 ⟨653588, by decide⟩ ⟨13, 2, 0, 653588, 352496, 125, 16384⟩
    (by decide) selected_cut_25814

theorem selected_cut_25815 : selected 8 ⟨653626, by decide⟩
    (prefixPartial 13 352497) = some ⟨13, 2, 0, 653626, 352497, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_352497_653626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352497 ⟨653626, by decide⟩ :=
  accepted_of_selected 13 352497 ⟨653626, by decide⟩ ⟨13, 2, 0, 653626, 352497, 2313, 16384⟩
    (by decide) selected_cut_25815

theorem selected_cut_25816 : selected 8 ⟨653651, by decide⟩
    (prefixPartial 13 352498) = some ⟨13, 2, 0, 653651, 352498, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_352498_653651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352498 ⟨653651, by decide⟩ :=
  accepted_of_selected 13 352498 ⟨653651, by decide⟩ ⟨13, 2, 0, 653651, 352498, 1745, 16384⟩
    (by decide) selected_cut_25816

theorem selected_cut_25817 : selected 8 ⟨653656, by decide⟩
    (prefixPartial 13 352499) = some ⟨13, 2, 0, 653656, 352499, 761, 16384⟩ := by
  decide +kernel

theorem context_13_352499_653656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352499 ⟨653656, by decide⟩ :=
  accepted_of_selected 13 352499 ⟨653656, by decide⟩ ⟨13, 2, 0, 653656, 352499, 761, 16384⟩
    (by decide) selected_cut_25817

theorem unmarked_context_12_88124_653657 : frontier 9 ⟨653657, by decide⟩
    (prefixCache 12 88124) (prefixPartial 12 88124) = false := by
  decide +kernel

theorem node_context_12_88124_653657 : EJMOriginalGlobalDAGData.nodes 9 ⟨653657, by decide⟩ =
    .split (coordinate 12) (![⟨653588, by decide⟩,⟨653626, by decide⟩,⟨653651, by decide⟩,⟨653656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88124_653657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88124 ⟨653657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88124
    ⟨653657, by decide⟩ (by decide) (![⟨653588, by decide⟩,⟨653626, by decide⟩,⟨653651, by decide⟩,⟨653656, by decide⟩]) unmarked_context_12_88124_653657 node_context_12_88124_653657
  intro a
  fin_cases a
  · exact context_13_352496_653588
  · exact context_13_352497_653626
  · exact context_13_352498_653651
  · exact context_13_352499_653656

theorem selected_cut_25818 : selected 8 ⟨653660, by decide⟩
    (prefixPartial 13 352500) = some ⟨13, 2, 0, 653660, 352500, 141, 16384⟩ := by
  decide +kernel

theorem context_13_352500_653660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352500 ⟨653660, by decide⟩ :=
  accepted_of_selected 13 352500 ⟨653660, by decide⟩ ⟨13, 2, 0, 653660, 352500, 141, 16384⟩
    (by decide) selected_cut_25818

theorem selected_cut_25819 : selected 8 ⟨653689, by decide⟩
    (prefixPartial 13 352501) = some ⟨13, 2, 0, 653689, 352501, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_352501_653689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352501 ⟨653689, by decide⟩ :=
  accepted_of_selected 13 352501 ⟨653689, by decide⟩ ⟨13, 2, 0, 653689, 352501, 2221, 16384⟩
    (by decide) selected_cut_25819

theorem selected_cut_25820 : selected 8 ⟨653718, by decide⟩
    (prefixPartial 13 352502) = some ⟨13, 2, 0, 653718, 352502, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_352502_653718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352502 ⟨653718, by decide⟩ :=
  accepted_of_selected 13 352502 ⟨653718, by decide⟩ ⟨13, 2, 0, 653718, 352502, 1769, 16384⟩
    (by decide) selected_cut_25820

theorem selected_cut_25821 : selected 8 ⟨653723, by decide⟩
    (prefixPartial 13 352503) = some ⟨13, 2, 0, 653723, 352503, 801, 16384⟩ := by
  decide +kernel

theorem context_13_352503_653723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352503 ⟨653723, by decide⟩ :=
  accepted_of_selected 13 352503 ⟨653723, by decide⟩ ⟨13, 2, 0, 653723, 352503, 801, 16384⟩
    (by decide) selected_cut_25821

theorem unmarked_context_12_88125_653724 : frontier 9 ⟨653724, by decide⟩
    (prefixCache 12 88125) (prefixPartial 12 88125) = false := by
  decide +kernel

theorem node_context_12_88125_653724 : EJMOriginalGlobalDAGData.nodes 9 ⟨653724, by decide⟩ =
    .split (coordinate 12) (![⟨653660, by decide⟩,⟨653689, by decide⟩,⟨653718, by decide⟩,⟨653723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88125_653724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88125 ⟨653724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88125
    ⟨653724, by decide⟩ (by decide) (![⟨653660, by decide⟩,⟨653689, by decide⟩,⟨653718, by decide⟩,⟨653723, by decide⟩]) unmarked_context_12_88125_653724 node_context_12_88125_653724
  intro a
  fin_cases a
  · exact context_13_352500_653660
  · exact context_13_352501_653689
  · exact context_13_352502_653718
  · exact context_13_352503_653723

theorem selected_cut_25822 : selected 8 ⟨653728, by decide⟩
    (prefixPartial 13 352504) = some ⟨13, 2, 0, 653728, 352504, 93, 16384⟩ := by
  decide +kernel

theorem context_13_352504_653728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352504 ⟨653728, by decide⟩ :=
  accepted_of_selected 13 352504 ⟨653728, by decide⟩ ⟨13, 2, 0, 653728, 352504, 93, 16384⟩
    (by decide) selected_cut_25822

theorem selected_cut_25823 : selected 8 ⟨653760, by decide⟩
    (prefixPartial 13 352505) = some ⟨13, 2, 0, 653760, 352505, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_352505_653760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352505 ⟨653760, by decide⟩ :=
  accepted_of_selected 13 352505 ⟨653760, by decide⟩ ⟨13, 2, 0, 653760, 352505, 2525, 16384⟩
    (by decide) selected_cut_25823

theorem selected_cut_25824 : selected 8 ⟨653784, by decide⟩
    (prefixPartial 13 352506) = some ⟨13, 2, 0, 653784, 352506, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_352506_653784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352506 ⟨653784, by decide⟩ :=
  accepted_of_selected 13 352506 ⟨653784, by decide⟩ ⟨13, 2, 0, 653784, 352506, 1813, 16384⟩
    (by decide) selected_cut_25824

theorem selected_cut_25825 : selected 8 ⟨653789, by decide⟩
    (prefixPartial 13 352507) = some ⟨13, 2, 0, 653789, 352507, 761, 16384⟩ := by
  decide +kernel

theorem context_13_352507_653789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352507 ⟨653789, by decide⟩ :=
  accepted_of_selected 13 352507 ⟨653789, by decide⟩ ⟨13, 2, 0, 653789, 352507, 761, 16384⟩
    (by decide) selected_cut_25825

theorem unmarked_context_12_88126_653790 : frontier 9 ⟨653790, by decide⟩
    (prefixCache 12 88126) (prefixPartial 12 88126) = false := by
  decide +kernel

theorem node_context_12_88126_653790 : EJMOriginalGlobalDAGData.nodes 9 ⟨653790, by decide⟩ =
    .split (coordinate 12) (![⟨653728, by decide⟩,⟨653760, by decide⟩,⟨653784, by decide⟩,⟨653789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88126_653790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88126 ⟨653790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88126
    ⟨653790, by decide⟩ (by decide) (![⟨653728, by decide⟩,⟨653760, by decide⟩,⟨653784, by decide⟩,⟨653789, by decide⟩]) unmarked_context_12_88126_653790 node_context_12_88126_653790
  intro a
  fin_cases a
  · exact context_13_352504_653728
  · exact context_13_352505_653760
  · exact context_13_352506_653784
  · exact context_13_352507_653789

theorem selected_cut_25826 : selected 8 ⟨653793, by decide⟩
    (prefixPartial 13 352508) = some ⟨13, 2, 0, 653793, 352508, 53, 16384⟩ := by
  decide +kernel

theorem context_13_352508_653793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352508 ⟨653793, by decide⟩ :=
  accepted_of_selected 13 352508 ⟨653793, by decide⟩ ⟨13, 2, 0, 653793, 352508, 53, 16384⟩
    (by decide) selected_cut_25826

theorem selected_cut_25827 : selected 8 ⟨653848, by decide⟩
    (prefixPartial 13 352509) = some ⟨13, 2, 0, 653848, 352509, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_352509_653848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352509 ⟨653848, by decide⟩ :=
  accepted_of_selected 13 352509 ⟨653848, by decide⟩ ⟨13, 2, 0, 653848, 352509, 2809, 16384⟩
    (by decide) selected_cut_25827

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
