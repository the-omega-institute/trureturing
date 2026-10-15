/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover021
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_02114 : selected 9 ⟨69664, by decide⟩
    (prefixPartial 12 5516) = some ⟨12, 2, 0, 69664, 5516, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_5516_69664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5516 ⟨69664, by decide⟩ :=
  accepted_of_selected 12 5516 ⟨69664, by decide⟩ ⟨12, 2, 0, 69664, 5516, 1673, 65536⟩
    (by decide) selected_cut_02114

theorem selected_cut_02115 : selected 9 ⟨69723, by decide⟩
    (prefixPartial 12 5517) = some ⟨12, 2, 0, 69723, 5517, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_5517_69723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5517 ⟨69723, by decide⟩ :=
  accepted_of_selected 12 5517 ⟨69723, by decide⟩ ⟨12, 2, 0, 69723, 5517, 2417, 65536⟩
    (by decide) selected_cut_02115

theorem selected_cut_02116 : selected 9 ⟨69774, by decide⟩
    (prefixPartial 12 5518) = some ⟨12, 2, 0, 69774, 5518, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_5518_69774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5518 ⟨69774, by decide⟩ :=
  accepted_of_selected 12 5518 ⟨69774, by decide⟩ ⟨12, 2, 0, 69774, 5518, 2381, 65536⟩
    (by decide) selected_cut_02116

theorem selected_cut_02117 : selected 9 ⟨69813, by decide⟩
    (prefixPartial 12 5519) = some ⟨12, 2, 0, 69813, 5519, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_5519_69813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5519 ⟨69813, by decide⟩ :=
  accepted_of_selected 12 5519 ⟨69813, by decide⟩ ⟨12, 2, 0, 69813, 5519, 2309, 65536⟩
    (by decide) selected_cut_02117

theorem unmarked_context_11_1379_69814 : frontier 10 ⟨69814, by decide⟩
    (prefixCache 11 1379) (prefixPartial 11 1379) = false := by
  decide +kernel

theorem node_context_11_1379_69814 : EJMOriginalGlobalDAGData.nodes 10 ⟨69814, by decide⟩ =
    .split (coordinate 11) (![⟨69664, by decide⟩,⟨69723, by decide⟩,⟨69774, by decide⟩,⟨69813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1379_69814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1379 ⟨69814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1379
    ⟨69814, by decide⟩ (by decide) (![⟨69664, by decide⟩,⟨69723, by decide⟩,⟨69774, by decide⟩,⟨69813, by decide⟩]) unmarked_context_11_1379_69814 node_context_11_1379_69814
  intro a
  fin_cases a
  · exact context_12_5516_69664
  · exact context_12_5517_69723
  · exact context_12_5518_69774
  · exact context_12_5519_69813

theorem unmarked_context_10_344_69815 : frontier 11 ⟨69815, by decide⟩
    (prefixCache 10 344) (prefixPartial 10 344) = false := by
  decide +kernel

theorem node_context_10_344_69815 : EJMOriginalGlobalDAGData.nodes 11 ⟨69815, by decide⟩ =
    .split (coordinate 10) (![⟨69143, by decide⟩,⟨69367, by decide⟩,⟨69621, by decide⟩,⟨69814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_344_69815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 344 ⟨69815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 344
    ⟨69815, by decide⟩ (by decide) (![⟨69143, by decide⟩,⟨69367, by decide⟩,⟨69621, by decide⟩,⟨69814, by decide⟩]) unmarked_context_10_344_69815 node_context_10_344_69815
  intro a
  fin_cases a
  · exact context_11_1376_69143
  · exact context_11_1377_69367
  · exact context_11_1378_69621
  · exact context_11_1379_69814

theorem selected_cut_02118 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5520) = some ⟨12, 1, 0, 1738, 5520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5520_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5520 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5520 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5520, 1, 65536⟩
    (by decide) selected_cut_02118

theorem selected_cut_02119 : selected 9 ⟨69859, by decide⟩
    (prefixPartial 12 5521) = some ⟨12, 2, 0, 69859, 5521, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_5521_69859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5521 ⟨69859, by decide⟩ :=
  accepted_of_selected 12 5521 ⟨69859, by decide⟩ ⟨12, 2, 0, 69859, 5521, 1373, 65536⟩
    (by decide) selected_cut_02119

theorem selected_cut_02120 : selected 9 ⟨69933, by decide⟩
    (prefixPartial 12 5522) = some ⟨12, 2, 0, 69933, 5522, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_5522_69933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5522 ⟨69933, by decide⟩ :=
  accepted_of_selected 12 5522 ⟨69933, by decide⟩ ⟨12, 2, 0, 69933, 5522, 2041, 65536⟩
    (by decide) selected_cut_02120

theorem selected_cut_02121 : selected 9 ⟨70005, by decide⟩
    (prefixPartial 12 5523) = some ⟨12, 2, 0, 70005, 5523, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_5523_70005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5523 ⟨70005, by decide⟩ :=
  accepted_of_selected 12 5523 ⟨70005, by decide⟩ ⟨12, 2, 0, 70005, 5523, 2077, 65536⟩
    (by decide) selected_cut_02121

theorem unmarked_context_11_1380_70006 : frontier 10 ⟨70006, by decide⟩
    (prefixCache 11 1380) (prefixPartial 11 1380) = false := by
  decide +kernel

theorem node_context_11_1380_70006 : EJMOriginalGlobalDAGData.nodes 10 ⟨70006, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨69859, by decide⟩,⟨69933, by decide⟩,⟨70005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1380_70006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1380 ⟨70006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1380
    ⟨70006, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨69859, by decide⟩,⟨69933, by decide⟩,⟨70005, by decide⟩]) unmarked_context_11_1380_70006 node_context_11_1380_70006
  intro a
  fin_cases a
  · exact context_12_5520_1738
  · exact context_12_5521_69859
  · exact context_12_5522_69933
  · exact context_12_5523_70005

theorem selected_cut_02122 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5524) = some ⟨12, 1, 0, 1738, 5524, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5524_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5524 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5524 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5524, 1, 65536⟩
    (by decide) selected_cut_02122

theorem selected_cut_02123 : selected 9 ⟨70113, by decide⟩
    (prefixPartial 12 5525) = some ⟨12, 2, 0, 70113, 5525, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_5525_70113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5525 ⟨70113, by decide⟩ :=
  accepted_of_selected 12 5525 ⟨70113, by decide⟩ ⟨12, 2, 0, 70113, 5525, 2497, 65536⟩
    (by decide) selected_cut_02123

theorem selected_cut_02124 : selected 9 ⟨70212, by decide⟩
    (prefixPartial 12 5526) = some ⟨12, 2, 0, 70212, 5526, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_5526_70212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5526 ⟨70212, by decide⟩ :=
  accepted_of_selected 12 5526 ⟨70212, by decide⟩ ⟨12, 2, 0, 70212, 5526, 2145, 65536⟩
    (by decide) selected_cut_02124

theorem selected_cut_02125 : selected 9 ⟨70301, by decide⟩
    (prefixPartial 12 5527) = some ⟨12, 2, 0, 70301, 5527, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_5527_70301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5527 ⟨70301, by decide⟩ :=
  accepted_of_selected 12 5527 ⟨70301, by decide⟩ ⟨12, 2, 0, 70301, 5527, 1949, 65536⟩
    (by decide) selected_cut_02125

theorem unmarked_context_11_1381_70302 : frontier 10 ⟨70302, by decide⟩
    (prefixCache 11 1381) (prefixPartial 11 1381) = false := by
  decide +kernel

theorem node_context_11_1381_70302 : EJMOriginalGlobalDAGData.nodes 10 ⟨70302, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨70113, by decide⟩,⟨70212, by decide⟩,⟨70301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1381_70302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1381 ⟨70302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1381
    ⟨70302, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨70113, by decide⟩,⟨70212, by decide⟩,⟨70301, by decide⟩]) unmarked_context_11_1381_70302 node_context_11_1381_70302
  intro a
  fin_cases a
  · exact context_12_5524_1738
  · exact context_12_5525_70113
  · exact context_12_5526_70212
  · exact context_12_5527_70301

theorem selected_cut_02126 : selected 10 ⟨70388, by decide⟩
    (prefixPartial 11 1382) = some ⟨11, 2, 0, 70388, 1382, 3477, 262144⟩ := by
  decide +kernel

theorem context_11_1382_70388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1382 ⟨70388, by decide⟩ :=
  accepted_of_selected 11 1382 ⟨70388, by decide⟩ ⟨11, 2, 0, 70388, 1382, 3477, 262144⟩
    (by decide) selected_cut_02126

theorem selected_cut_02127 : selected 10 ⟨70461, by decide⟩
    (prefixPartial 11 1383) = some ⟨11, 2, 0, 70461, 1383, 2677, 262144⟩ := by
  decide +kernel

theorem context_11_1383_70461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1383 ⟨70461, by decide⟩ :=
  accepted_of_selected 11 1383 ⟨70461, by decide⟩ ⟨11, 2, 0, 70461, 1383, 2677, 262144⟩
    (by decide) selected_cut_02127

theorem unmarked_context_10_345_70462 : frontier 11 ⟨70462, by decide⟩
    (prefixCache 10 345) (prefixPartial 10 345) = false := by
  decide +kernel

theorem node_context_10_345_70462 : EJMOriginalGlobalDAGData.nodes 11 ⟨70462, by decide⟩ =
    .split (coordinate 10) (![⟨70006, by decide⟩,⟨70302, by decide⟩,⟨70388, by decide⟩,⟨70461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_345_70462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 345 ⟨70462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 345
    ⟨70462, by decide⟩ (by decide) (![⟨70006, by decide⟩,⟨70302, by decide⟩,⟨70388, by decide⟩,⟨70461, by decide⟩]) unmarked_context_10_345_70462 node_context_10_345_70462
  intro a
  fin_cases a
  · exact context_11_1380_70006
  · exact context_11_1381_70302
  · exact context_11_1382_70388
  · exact context_11_1383_70461

theorem selected_cut_02128 : selected 11 ⟨70582, by decide⟩
    (prefixPartial 10 346) = some ⟨10, 2, 0, 70582, 346, 3725, 1048576⟩ := by
  decide +kernel

theorem context_10_346_70582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 346 ⟨70582, by decide⟩ :=
  accepted_of_selected 10 346 ⟨70582, by decide⟩ ⟨10, 2, 0, 70582, 346, 3725, 1048576⟩
    (by decide) selected_cut_02128

theorem selected_cut_02129 : selected 11 ⟨70596, by decide⟩
    (prefixPartial 10 347) = some ⟨10, 2, 0, 70596, 347, 505, 1048576⟩ := by
  decide +kernel

theorem context_10_347_70596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 347 ⟨70596, by decide⟩ :=
  accepted_of_selected 10 347 ⟨70596, by decide⟩ ⟨10, 2, 0, 70596, 347, 505, 1048576⟩
    (by decide) selected_cut_02129

theorem unmarked_context_9_86_70597 : frontier 12 ⟨70597, by decide⟩
    (prefixCache 9 86) (prefixPartial 9 86) = false := by
  decide +kernel

theorem node_context_9_86_70597 : EJMOriginalGlobalDAGData.nodes 12 ⟨70597, by decide⟩ =
    .split (coordinate 9) (![⟨69815, by decide⟩,⟨70462, by decide⟩,⟨70582, by decide⟩,⟨70596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_86_70597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 86 ⟨70597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 86
    ⟨70597, by decide⟩ (by decide) (![⟨69815, by decide⟩,⟨70462, by decide⟩,⟨70582, by decide⟩,⟨70596, by decide⟩]) unmarked_context_9_86_70597 node_context_9_86_70597
  intro a
  fin_cases a
  · exact context_10_344_69815
  · exact context_10_345_70462
  · exact context_10_346_70582
  · exact context_10_347_70596

theorem selected_cut_02130 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 87) = some ⟨9, 1, 0, 4601, 87, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_87_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 87 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 87 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 87, 1, 4194304⟩
    (by decide) selected_cut_02130

theorem unmarked_context_8_21_70598 : frontier 13 ⟨70598, by decide⟩
    (prefixCache 8 21) (prefixPartial 8 21) = false := by
  decide +kernel

theorem node_context_8_21_70598 : EJMOriginalGlobalDAGData.nodes 13 ⟨70598, by decide⟩ =
    .split (coordinate 8) (![⟨67394, by decide⟩,⟨68984, by decide⟩,⟨70597, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_21_70598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 21 ⟨70598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 21
    ⟨70598, by decide⟩ (by decide) (![⟨67394, by decide⟩,⟨68984, by decide⟩,⟨70597, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_21_70598 node_context_8_21_70598
  intro a
  fin_cases a
  · exact context_9_84_67394
  · exact context_9_85_68984
  · exact context_9_86_70597
  · exact context_9_87_4601

theorem selected_cut_02131 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 5632) = some ⟨12, 1, 0, 34034, 5632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5632_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5632 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 5632 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 5632, 1, 65536⟩
    (by decide) selected_cut_02131

theorem selected_cut_02132 : selected 7 ⟨70624, by decide⟩
    (prefixPartial 14 90128) = some ⟨14, 2, 0, 70624, 90128, 1657, 4096⟩ := by
  decide +kernel

theorem context_14_90128_70624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90128 ⟨70624, by decide⟩ :=
  accepted_of_selected 14 90128 ⟨70624, by decide⟩ ⟨14, 2, 0, 70624, 90128, 1657, 4096⟩
    (by decide) selected_cut_02132

theorem selected_cut_02133 : selected 7 ⟨70645, by decide⟩
    (prefixPartial 14 90129) = some ⟨14, 2, 0, 70645, 90129, 1381, 4096⟩ := by
  decide +kernel

theorem context_14_90129_70645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90129 ⟨70645, by decide⟩ :=
  accepted_of_selected 14 90129 ⟨70645, by decide⟩ ⟨14, 2, 0, 70645, 90129, 1381, 4096⟩
    (by decide) selected_cut_02133

theorem selected_cut_02134 : selected 7 ⟨70665, by decide⟩
    (prefixPartial 14 90130) = some ⟨14, 2, 0, 70665, 90130, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_90130_70665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90130 ⟨70665, by decide⟩ :=
  accepted_of_selected 14 90130 ⟨70665, by decide⟩ ⟨14, 2, 0, 70665, 90130, 1169, 4096⟩
    (by decide) selected_cut_02134

theorem selected_cut_02135 : selected 7 ⟨70679, by decide⟩
    (prefixPartial 14 90131) = some ⟨14, 2, 0, 70679, 90131, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_90131_70679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90131 ⟨70679, by decide⟩ :=
  accepted_of_selected 14 90131 ⟨70679, by decide⟩ ⟨14, 2, 0, 70679, 90131, 1169, 4096⟩
    (by decide) selected_cut_02135

theorem unmarked_context_13_22532_70680 : frontier 8 ⟨70680, by decide⟩
    (prefixCache 13 22532) (prefixPartial 13 22532) = false := by
  decide +kernel

theorem node_context_13_22532_70680 : EJMOriginalGlobalDAGData.nodes 8 ⟨70680, by decide⟩ =
    .split (coordinate 13) (![⟨70624, by decide⟩,⟨70645, by decide⟩,⟨70665, by decide⟩,⟨70679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22532_70680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22532 ⟨70680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22532
    ⟨70680, by decide⟩ (by decide) (![⟨70624, by decide⟩,⟨70645, by decide⟩,⟨70665, by decide⟩,⟨70679, by decide⟩]) unmarked_context_13_22532_70680 node_context_13_22532_70680
  intro a
  fin_cases a
  · exact context_14_90128_70624
  · exact context_14_90129_70645
  · exact context_14_90130_70665
  · exact context_14_90131_70679

theorem selected_cut_02136 : selected 8 ⟨70739, by decide⟩
    (prefixPartial 13 22533) = some ⟨13, 2, 0, 70739, 22533, 3777, 16384⟩ := by
  decide +kernel

theorem context_13_22533_70739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22533 ⟨70739, by decide⟩ :=
  accepted_of_selected 13 22533 ⟨70739, by decide⟩ ⟨13, 2, 0, 70739, 22533, 3777, 16384⟩
    (by decide) selected_cut_02136

theorem selected_cut_02137 : selected 8 ⟨70767, by decide⟩
    (prefixPartial 13 22534) = some ⟨13, 2, 0, 70767, 22534, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_22534_70767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22534 ⟨70767, by decide⟩ :=
  accepted_of_selected 13 22534 ⟨70767, by decide⟩ ⟨13, 2, 0, 70767, 22534, 2333, 16384⟩
    (by decide) selected_cut_02137

theorem selected_cut_02138 : selected 8 ⟨70781, by decide⟩
    (prefixPartial 13 22535) = some ⟨13, 2, 0, 70781, 22535, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_22535_70781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22535 ⟨70781, by decide⟩ :=
  accepted_of_selected 13 22535 ⟨70781, by decide⟩ ⟨13, 2, 0, 70781, 22535, 1333, 16384⟩
    (by decide) selected_cut_02138

theorem unmarked_context_12_5633_70782 : frontier 9 ⟨70782, by decide⟩
    (prefixCache 12 5633) (prefixPartial 12 5633) = false := by
  decide +kernel

theorem node_context_12_5633_70782 : EJMOriginalGlobalDAGData.nodes 9 ⟨70782, by decide⟩ =
    .split (coordinate 12) (![⟨70680, by decide⟩,⟨70739, by decide⟩,⟨70767, by decide⟩,⟨70781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5633_70782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5633 ⟨70782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5633
    ⟨70782, by decide⟩ (by decide) (![⟨70680, by decide⟩,⟨70739, by decide⟩,⟨70767, by decide⟩,⟨70781, by decide⟩]) unmarked_context_12_5633_70782 node_context_12_5633_70782
  intro a
  fin_cases a
  · exact context_13_22532_70680
  · exact context_13_22533_70739
  · exact context_13_22534_70767
  · exact context_13_22535_70781

theorem selected_cut_02139 : selected 7 ⟨70808, by decide⟩
    (prefixPartial 14 90144) = some ⟨14, 2, 0, 70808, 90144, 1449, 4096⟩ := by
  decide +kernel

theorem context_14_90144_70808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90144 ⟨70808, by decide⟩ :=
  accepted_of_selected 14 90144 ⟨70808, by decide⟩ ⟨14, 2, 0, 70808, 90144, 1449, 4096⟩
    (by decide) selected_cut_02139

theorem selected_cut_02140 : selected 7 ⟨70825, by decide⟩
    (prefixPartial 14 90145) = some ⟨14, 2, 0, 70825, 90145, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_90145_70825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90145 ⟨70825, by decide⟩ :=
  accepted_of_selected 14 90145 ⟨70825, by decide⟩ ⟨14, 2, 0, 70825, 90145, 1193, 4096⟩
    (by decide) selected_cut_02140

theorem selected_cut_02141 : selected 7 ⟨70841, by decide⟩
    (prefixPartial 14 90146) = some ⟨14, 2, 0, 70841, 90146, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_90146_70841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90146 ⟨70841, by decide⟩ :=
  accepted_of_selected 14 90146 ⟨70841, by decide⟩ ⟨14, 2, 0, 70841, 90146, 1157, 4096⟩
    (by decide) selected_cut_02141

theorem selected_cut_02142 : selected 7 ⟨70853, by decide⟩
    (prefixPartial 14 90147) = some ⟨14, 2, 0, 70853, 90147, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_90147_70853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90147 ⟨70853, by decide⟩ :=
  accepted_of_selected 14 90147 ⟨70853, by decide⟩ ⟨14, 2, 0, 70853, 90147, 1053, 4096⟩
    (by decide) selected_cut_02142

theorem unmarked_context_13_22536_70854 : frontier 8 ⟨70854, by decide⟩
    (prefixCache 13 22536) (prefixPartial 13 22536) = false := by
  decide +kernel

theorem node_context_13_22536_70854 : EJMOriginalGlobalDAGData.nodes 8 ⟨70854, by decide⟩ =
    .split (coordinate 13) (![⟨70808, by decide⟩,⟨70825, by decide⟩,⟨70841, by decide⟩,⟨70853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22536_70854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22536 ⟨70854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22536
    ⟨70854, by decide⟩ (by decide) (![⟨70808, by decide⟩,⟨70825, by decide⟩,⟨70841, by decide⟩,⟨70853, by decide⟩]) unmarked_context_13_22536_70854 node_context_13_22536_70854
  intro a
  fin_cases a
  · exact context_14_90144_70808
  · exact context_14_90145_70825
  · exact context_14_90146_70841
  · exact context_14_90147_70853

theorem selected_cut_02143 : selected 8 ⟨70894, by decide⟩
    (prefixPartial 13 22537) = some ⟨13, 2, 0, 70894, 22537, 3377, 16384⟩ := by
  decide +kernel

theorem context_13_22537_70894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22537 ⟨70894, by decide⟩ :=
  accepted_of_selected 13 22537 ⟨70894, by decide⟩ ⟨13, 2, 0, 70894, 22537, 3377, 16384⟩
    (by decide) selected_cut_02143

theorem selected_cut_02144 : selected 8 ⟨70921, by decide⟩
    (prefixPartial 13 22538) = some ⟨13, 2, 0, 70921, 22538, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_22538_70921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22538 ⟨70921, by decide⟩ :=
  accepted_of_selected 13 22538 ⟨70921, by decide⟩ ⟨13, 2, 0, 70921, 22538, 2121, 16384⟩
    (by decide) selected_cut_02144

theorem selected_cut_02145 : selected 8 ⟨70934, by decide⟩
    (prefixPartial 13 22539) = some ⟨13, 2, 0, 70934, 22539, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_22539_70934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22539 ⟨70934, by decide⟩ :=
  accepted_of_selected 13 22539 ⟨70934, by decide⟩ ⟨13, 2, 0, 70934, 22539, 1313, 16384⟩
    (by decide) selected_cut_02145

theorem unmarked_context_12_5634_70935 : frontier 9 ⟨70935, by decide⟩
    (prefixCache 12 5634) (prefixPartial 12 5634) = false := by
  decide +kernel

theorem node_context_12_5634_70935 : EJMOriginalGlobalDAGData.nodes 9 ⟨70935, by decide⟩ =
    .split (coordinate 12) (![⟨70854, by decide⟩,⟨70894, by decide⟩,⟨70921, by decide⟩,⟨70934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5634_70935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5634 ⟨70935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5634
    ⟨70935, by decide⟩ (by decide) (![⟨70854, by decide⟩,⟨70894, by decide⟩,⟨70921, by decide⟩,⟨70934, by decide⟩]) unmarked_context_12_5634_70935 node_context_12_5634_70935
  intro a
  fin_cases a
  · exact context_13_22536_70854
  · exact context_13_22537_70894
  · exact context_13_22538_70921
  · exact context_13_22539_70934

theorem selected_cut_02146 : selected 7 ⟨70960, by decide⟩
    (prefixPartial 14 90160) = some ⟨14, 2, 0, 70960, 90160, 1749, 4096⟩ := by
  decide +kernel

theorem context_14_90160_70960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90160 ⟨70960, by decide⟩ :=
  accepted_of_selected 14 90160 ⟨70960, by decide⟩ ⟨14, 2, 0, 70960, 90160, 1749, 4096⟩
    (by decide) selected_cut_02146

theorem selected_cut_02147 : selected 7 ⟨70978, by decide⟩
    (prefixPartial 14 90161) = some ⟨14, 2, 0, 70978, 90161, 1389, 4096⟩ := by
  decide +kernel

theorem context_14_90161_70978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90161 ⟨70978, by decide⟩ :=
  accepted_of_selected 14 90161 ⟨70978, by decide⟩ ⟨14, 2, 0, 70978, 90161, 1389, 4096⟩
    (by decide) selected_cut_02147

theorem selected_cut_02148 : selected 7 ⟨70997, by decide⟩
    (prefixPartial 14 90162) = some ⟨14, 2, 0, 70997, 90162, 1325, 4096⟩ := by
  decide +kernel

theorem context_14_90162_70997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90162 ⟨70997, by decide⟩ :=
  accepted_of_selected 14 90162 ⟨70997, by decide⟩ ⟨14, 2, 0, 70997, 90162, 1325, 4096⟩
    (by decide) selected_cut_02148

theorem selected_cut_02149 : selected 7 ⟨71013, by decide⟩
    (prefixPartial 14 90163) = some ⟨14, 2, 0, 71013, 90163, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_90163_71013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90163 ⟨71013, by decide⟩ :=
  accepted_of_selected 14 90163 ⟨71013, by decide⟩ ⟨14, 2, 0, 71013, 90163, 1285, 4096⟩
    (by decide) selected_cut_02149

theorem unmarked_context_13_22540_71014 : frontier 8 ⟨71014, by decide⟩
    (prefixCache 13 22540) (prefixPartial 13 22540) = false := by
  decide +kernel

theorem node_context_13_22540_71014 : EJMOriginalGlobalDAGData.nodes 8 ⟨71014, by decide⟩ =
    .split (coordinate 13) (![⟨70960, by decide⟩,⟨70978, by decide⟩,⟨70997, by decide⟩,⟨71013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22540_71014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22540 ⟨71014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22540
    ⟨71014, by decide⟩ (by decide) (![⟨70960, by decide⟩,⟨70978, by decide⟩,⟨70997, by decide⟩,⟨71013, by decide⟩]) unmarked_context_13_22540_71014 node_context_13_22540_71014
  intro a
  fin_cases a
  · exact context_14_90160_70960
  · exact context_14_90161_70978
  · exact context_14_90162_70997
  · exact context_14_90163_71013

theorem selected_cut_02150 : selected 8 ⟨71074, by decide⟩
    (prefixPartial 13 22541) = some ⟨13, 2, 0, 71074, 22541, 3913, 16384⟩ := by
  decide +kernel

theorem context_13_22541_71074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22541 ⟨71074, by decide⟩ :=
  accepted_of_selected 13 22541 ⟨71074, by decide⟩ ⟨13, 2, 0, 71074, 22541, 3913, 16384⟩
    (by decide) selected_cut_02150

theorem selected_cut_02151 : selected 8 ⟨71099, by decide⟩
    (prefixPartial 13 22542) = some ⟨13, 2, 0, 71099, 22542, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_22542_71099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22542 ⟨71099, by decide⟩ :=
  accepted_of_selected 13 22542 ⟨71099, by decide⟩ ⟨13, 2, 0, 71099, 22542, 2433, 16384⟩
    (by decide) selected_cut_02151

theorem selected_cut_02152 : selected 8 ⟨71116, by decide⟩
    (prefixPartial 13 22543) = some ⟨13, 2, 0, 71116, 22543, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_22543_71116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22543 ⟨71116, by decide⟩ :=
  accepted_of_selected 13 22543 ⟨71116, by decide⟩ ⟨13, 2, 0, 71116, 22543, 1277, 16384⟩
    (by decide) selected_cut_02152

theorem unmarked_context_12_5635_71117 : frontier 9 ⟨71117, by decide⟩
    (prefixCache 12 5635) (prefixPartial 12 5635) = false := by
  decide +kernel

theorem node_context_12_5635_71117 : EJMOriginalGlobalDAGData.nodes 9 ⟨71117, by decide⟩ =
    .split (coordinate 12) (![⟨71014, by decide⟩,⟨71074, by decide⟩,⟨71099, by decide⟩,⟨71116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5635_71117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5635 ⟨71117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5635
    ⟨71117, by decide⟩ (by decide) (![⟨71014, by decide⟩,⟨71074, by decide⟩,⟨71099, by decide⟩,⟨71116, by decide⟩]) unmarked_context_12_5635_71117 node_context_12_5635_71117
  intro a
  fin_cases a
  · exact context_13_22540_71014
  · exact context_13_22541_71074
  · exact context_13_22542_71099
  · exact context_13_22543_71116

theorem unmarked_context_11_1408_71118 : frontier 10 ⟨71118, by decide⟩
    (prefixCache 11 1408) (prefixPartial 11 1408) = false := by
  decide +kernel

theorem node_context_11_1408_71118 : EJMOriginalGlobalDAGData.nodes 10 ⟨71118, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨70782, by decide⟩,⟨70935, by decide⟩,⟨71117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1408_71118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1408 ⟨71118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1408
    ⟨71118, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨70782, by decide⟩,⟨70935, by decide⟩,⟨71117, by decide⟩]) unmarked_context_11_1408_71118 node_context_11_1408_71118
  intro a
  fin_cases a
  · exact context_12_5632_34034
  · exact context_12_5633_70782
  · exact context_12_5634_70935
  · exact context_12_5635_71117

theorem selected_cut_02153 : selected 7 ⟨71153, by decide⟩
    (prefixPartial 14 90176) = some ⟨14, 2, 0, 71153, 90176, 2357, 4096⟩ := by
  decide +kernel

theorem context_14_90176_71153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90176 ⟨71153, by decide⟩ :=
  accepted_of_selected 14 90176 ⟨71153, by decide⟩ ⟨14, 2, 0, 71153, 90176, 2357, 4096⟩
    (by decide) selected_cut_02153

theorem selected_cut_02154 : selected 7 ⟨71174, by decide⟩
    (prefixPartial 14 90177) = some ⟨14, 2, 0, 71174, 90177, 1409, 4096⟩ := by
  decide +kernel

theorem context_14_90177_71174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90177 ⟨71174, by decide⟩ :=
  accepted_of_selected 14 90177 ⟨71174, by decide⟩ ⟨14, 2, 0, 71174, 90177, 1409, 4096⟩
    (by decide) selected_cut_02154

theorem selected_cut_02155 : selected 7 ⟨71206, by decide⟩
    (prefixPartial 14 90178) = some ⟨14, 2, 0, 71206, 90178, 1649, 4096⟩ := by
  decide +kernel

theorem context_14_90178_71206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90178 ⟨71206, by decide⟩ :=
  accepted_of_selected 14 90178 ⟨71206, by decide⟩ ⟨14, 2, 0, 71206, 90178, 1649, 4096⟩
    (by decide) selected_cut_02155

theorem selected_cut_02156 : selected 7 ⟨71230, by decide⟩
    (prefixPartial 14 90179) = some ⟨14, 2, 0, 71230, 90179, 1541, 4096⟩ := by
  decide +kernel

theorem context_14_90179_71230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90179 ⟨71230, by decide⟩ :=
  accepted_of_selected 14 90179 ⟨71230, by decide⟩ ⟨14, 2, 0, 71230, 90179, 1541, 4096⟩
    (by decide) selected_cut_02156

theorem unmarked_context_13_22544_71231 : frontier 8 ⟨71231, by decide⟩
    (prefixCache 13 22544) (prefixPartial 13 22544) = false := by
  decide +kernel

theorem node_context_13_22544_71231 : EJMOriginalGlobalDAGData.nodes 8 ⟨71231, by decide⟩ =
    .split (coordinate 13) (![⟨71153, by decide⟩,⟨71174, by decide⟩,⟨71206, by decide⟩,⟨71230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22544_71231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22544 ⟨71231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22544
    ⟨71231, by decide⟩ (by decide) (![⟨71153, by decide⟩,⟨71174, by decide⟩,⟨71206, by decide⟩,⟨71230, by decide⟩]) unmarked_context_13_22544_71231 node_context_13_22544_71231
  intro a
  fin_cases a
  · exact context_14_90176_71153
  · exact context_14_90177_71174
  · exact context_14_90178_71206
  · exact context_14_90179_71230

theorem selected_cut_02157 : selected 7 ⟨71254, by decide⟩
    (prefixPartial 14 90180) = some ⟨14, 2, 0, 71254, 90180, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_90180_71254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90180 ⟨71254, by decide⟩ :=
  accepted_of_selected 14 90180 ⟨71254, by decide⟩ ⟨14, 2, 0, 71254, 90180, 1313, 4096⟩
    (by decide) selected_cut_02157

theorem selected_cut_02158 : selected 7 ⟨71284, by decide⟩
    (prefixPartial 14 90181) = some ⟨14, 2, 0, 71284, 90181, 1609, 4096⟩ := by
  decide +kernel

theorem context_14_90181_71284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90181 ⟨71284, by decide⟩ :=
  accepted_of_selected 14 90181 ⟨71284, by decide⟩ ⟨14, 2, 0, 71284, 90181, 1609, 4096⟩
    (by decide) selected_cut_02158

theorem selected_cut_02159 : selected 7 ⟨71307, by decide⟩
    (prefixPartial 14 90182) = some ⟨14, 2, 0, 71307, 90182, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_90182_71307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90182 ⟨71307, by decide⟩ :=
  accepted_of_selected 14 90182 ⟨71307, by decide⟩ ⟨14, 2, 0, 71307, 90182, 1177, 4096⟩
    (by decide) selected_cut_02159

theorem selected_cut_02160 : selected 7 ⟨71331, by decide⟩
    (prefixPartial 14 90183) = some ⟨14, 2, 0, 71331, 90183, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_90183_71331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90183 ⟨71331, by decide⟩ :=
  accepted_of_selected 14 90183 ⟨71331, by decide⟩ ⟨14, 2, 0, 71331, 90183, 1313, 4096⟩
    (by decide) selected_cut_02160

theorem unmarked_context_13_22545_71332 : frontier 8 ⟨71332, by decide⟩
    (prefixCache 13 22545) (prefixPartial 13 22545) = false := by
  decide +kernel

theorem node_context_13_22545_71332 : EJMOriginalGlobalDAGData.nodes 8 ⟨71332, by decide⟩ =
    .split (coordinate 13) (![⟨71254, by decide⟩,⟨71284, by decide⟩,⟨71307, by decide⟩,⟨71331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22545_71332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22545 ⟨71332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22545
    ⟨71332, by decide⟩ (by decide) (![⟨71254, by decide⟩,⟨71284, by decide⟩,⟨71307, by decide⟩,⟨71331, by decide⟩]) unmarked_context_13_22545_71332 node_context_13_22545_71332
  intro a
  fin_cases a
  · exact context_14_90180_71254
  · exact context_14_90181_71284
  · exact context_14_90182_71307
  · exact context_14_90183_71331

theorem selected_cut_02161 : selected 8 ⟨71400, by decide⟩
    (prefixPartial 13 22546) = some ⟨13, 2, 0, 71400, 22546, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_22546_71400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22546 ⟨71400, by decide⟩ :=
  accepted_of_selected 13 22546 ⟨71400, by decide⟩ ⟨13, 2, 0, 71400, 22546, 3389, 16384⟩
    (by decide) selected_cut_02161

theorem selected_cut_02162 : selected 8 ⟨71447, by decide⟩
    (prefixPartial 13 22547) = some ⟨13, 2, 0, 71447, 22547, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_22547_71447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22547 ⟨71447, by decide⟩ :=
  accepted_of_selected 13 22547 ⟨71447, by decide⟩ ⟨13, 2, 0, 71447, 22547, 1753, 16384⟩
    (by decide) selected_cut_02162

theorem unmarked_context_12_5636_71448 : frontier 9 ⟨71448, by decide⟩
    (prefixCache 12 5636) (prefixPartial 12 5636) = false := by
  decide +kernel

theorem node_context_12_5636_71448 : EJMOriginalGlobalDAGData.nodes 9 ⟨71448, by decide⟩ =
    .split (coordinate 12) (![⟨71231, by decide⟩,⟨71332, by decide⟩,⟨71400, by decide⟩,⟨71447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5636_71448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5636 ⟨71448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5636
    ⟨71448, by decide⟩ (by decide) (![⟨71231, by decide⟩,⟨71332, by decide⟩,⟨71400, by decide⟩,⟨71447, by decide⟩]) unmarked_context_12_5636_71448 node_context_12_5636_71448
  intro a
  fin_cases a
  · exact context_13_22544_71231
  · exact context_13_22545_71332
  · exact context_13_22546_71400
  · exact context_13_22547_71447

theorem selected_cut_02163 : selected 7 ⟨71471, by decide⟩
    (prefixPartial 14 90192) = some ⟨14, 2, 0, 71471, 90192, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_90192_71471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90192 ⟨71471, by decide⟩ :=
  accepted_of_selected 14 90192 ⟨71471, by decide⟩ ⟨14, 2, 0, 71471, 90192, 1273, 4096⟩
    (by decide) selected_cut_02163

theorem selected_cut_02164 : selected 7 ⟨71493, by decide⟩
    (prefixPartial 14 90193) = some ⟨14, 2, 0, 71493, 90193, 1225, 4096⟩ := by
  decide +kernel

theorem context_14_90193_71493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90193 ⟨71493, by decide⟩ :=
  accepted_of_selected 14 90193 ⟨71493, by decide⟩ ⟨14, 2, 0, 71493, 90193, 1225, 4096⟩
    (by decide) selected_cut_02164

theorem selected_cut_02165 : selected 7 ⟨71512, by decide⟩
    (prefixPartial 14 90194) = some ⟨14, 2, 0, 71512, 90194, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_90194_71512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90194 ⟨71512, by decide⟩ :=
  accepted_of_selected 14 90194 ⟨71512, by decide⟩ ⟨14, 2, 0, 71512, 90194, 1289, 4096⟩
    (by decide) selected_cut_02165

theorem selected_cut_02166 : selected 7 ⟨71531, by decide⟩
    (prefixPartial 14 90195) = some ⟨14, 2, 0, 71531, 90195, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_90195_71531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90195 ⟨71531, by decide⟩ :=
  accepted_of_selected 14 90195 ⟨71531, by decide⟩ ⟨14, 2, 0, 71531, 90195, 1393, 4096⟩
    (by decide) selected_cut_02166

theorem unmarked_context_13_22548_71532 : frontier 8 ⟨71532, by decide⟩
    (prefixCache 13 22548) (prefixPartial 13 22548) = false := by
  decide +kernel

theorem node_context_13_22548_71532 : EJMOriginalGlobalDAGData.nodes 8 ⟨71532, by decide⟩ =
    .split (coordinate 13) (![⟨71471, by decide⟩,⟨71493, by decide⟩,⟨71512, by decide⟩,⟨71531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22548_71532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22548 ⟨71532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22548
    ⟨71532, by decide⟩ (by decide) (![⟨71471, by decide⟩,⟨71493, by decide⟩,⟨71512, by decide⟩,⟨71531, by decide⟩]) unmarked_context_13_22548_71532 node_context_13_22548_71532
  intro a
  fin_cases a
  · exact context_14_90192_71471
  · exact context_14_90193_71493
  · exact context_14_90194_71512
  · exact context_14_90195_71531

theorem selected_cut_02167 : selected 8 ⟨71579, by decide⟩
    (prefixPartial 13 22549) = some ⟨13, 2, 0, 71579, 22549, 3541, 16384⟩ := by
  decide +kernel

theorem context_13_22549_71579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22549 ⟨71579, by decide⟩ :=
  accepted_of_selected 13 22549 ⟨71579, by decide⟩ ⟨13, 2, 0, 71579, 22549, 3541, 16384⟩
    (by decide) selected_cut_02167

theorem selected_cut_02168 : selected 8 ⟨71611, by decide⟩
    (prefixPartial 13 22550) = some ⟨13, 2, 0, 71611, 22550, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_22550_71611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22550 ⟨71611, by decide⟩ :=
  accepted_of_selected 13 22550 ⟨71611, by decide⟩ ⟨13, 2, 0, 71611, 22550, 2373, 16384⟩
    (by decide) selected_cut_02168

theorem selected_cut_02169 : selected 8 ⟨71631, by decide⟩
    (prefixPartial 13 22551) = some ⟨13, 2, 0, 71631, 22551, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_22551_71631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22551 ⟨71631, by decide⟩ :=
  accepted_of_selected 13 22551 ⟨71631, by decide⟩ ⟨13, 2, 0, 71631, 22551, 1345, 16384⟩
    (by decide) selected_cut_02169

theorem unmarked_context_12_5637_71632 : frontier 9 ⟨71632, by decide⟩
    (prefixCache 12 5637) (prefixPartial 12 5637) = false := by
  decide +kernel

theorem node_context_12_5637_71632 : EJMOriginalGlobalDAGData.nodes 9 ⟨71632, by decide⟩ =
    .split (coordinate 12) (![⟨71532, by decide⟩,⟨71579, by decide⟩,⟨71611, by decide⟩,⟨71631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5637_71632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5637 ⟨71632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5637
    ⟨71632, by decide⟩ (by decide) (![⟨71532, by decide⟩,⟨71579, by decide⟩,⟨71611, by decide⟩,⟨71631, by decide⟩]) unmarked_context_12_5637_71632 node_context_12_5637_71632
  intro a
  fin_cases a
  · exact context_13_22548_71532
  · exact context_13_22549_71579
  · exact context_13_22550_71611
  · exact context_13_22551_71631

theorem selected_cut_02170 : selected 7 ⟨71654, by decide⟩
    (prefixPartial 14 90208) = some ⟨14, 2, 0, 71654, 90208, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_90208_71654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90208 ⟨71654, by decide⟩ :=
  accepted_of_selected 14 90208 ⟨71654, by decide⟩ ⟨14, 2, 0, 71654, 90208, 1049, 4096⟩
    (by decide) selected_cut_02170

theorem selected_cut_02171 : selected 7 ⟨71673, by decide⟩
    (prefixPartial 14 90209) = some ⟨14, 2, 0, 71673, 90209, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_90209_71673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90209 ⟨71673, by decide⟩ :=
  accepted_of_selected 14 90209 ⟨71673, by decide⟩ ⟨14, 2, 0, 71673, 90209, 1073, 4096⟩
    (by decide) selected_cut_02171

theorem selected_cut_02172 : selected 7 ⟨71692, by decide⟩
    (prefixPartial 14 90210) = some ⟨14, 2, 0, 71692, 90210, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_90210_71692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90210 ⟨71692, by decide⟩ :=
  accepted_of_selected 14 90210 ⟨71692, by decide⟩ ⟨14, 2, 0, 71692, 90210, 1253, 4096⟩
    (by decide) selected_cut_02172

theorem selected_cut_02173 : selected 7 ⟨71711, by decide⟩
    (prefixPartial 14 90211) = some ⟨14, 2, 0, 71711, 90211, 1329, 4096⟩ := by
  decide +kernel

theorem context_14_90211_71711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90211 ⟨71711, by decide⟩ :=
  accepted_of_selected 14 90211 ⟨71711, by decide⟩ ⟨14, 2, 0, 71711, 90211, 1329, 4096⟩
    (by decide) selected_cut_02173

theorem unmarked_context_13_22552_71712 : frontier 8 ⟨71712, by decide⟩
    (prefixCache 13 22552) (prefixPartial 13 22552) = false := by
  decide +kernel

theorem node_context_13_22552_71712 : EJMOriginalGlobalDAGData.nodes 8 ⟨71712, by decide⟩ =
    .split (coordinate 13) (![⟨71654, by decide⟩,⟨71673, by decide⟩,⟨71692, by decide⟩,⟨71711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22552_71712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22552 ⟨71712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22552
    ⟨71712, by decide⟩ (by decide) (![⟨71654, by decide⟩,⟨71673, by decide⟩,⟨71692, by decide⟩,⟨71711, by decide⟩]) unmarked_context_13_22552_71712 node_context_13_22552_71712
  intro a
  fin_cases a
  · exact context_14_90208_71654
  · exact context_14_90209_71673
  · exact context_14_90210_71692
  · exact context_14_90211_71711

theorem selected_cut_02174 : selected 8 ⟨71753, by decide⟩
    (prefixPartial 13 22553) = some ⟨13, 2, 0, 71753, 22553, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_22553_71753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22553 ⟨71753, by decide⟩ :=
  accepted_of_selected 13 22553 ⟨71753, by decide⟩ ⟨13, 2, 0, 71753, 22553, 3181, 16384⟩
    (by decide) selected_cut_02174

theorem selected_cut_02175 : selected 8 ⟨71778, by decide⟩
    (prefixPartial 13 22554) = some ⟨13, 2, 0, 71778, 22554, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_22554_71778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22554 ⟨71778, by decide⟩ :=
  accepted_of_selected 13 22554 ⟨71778, by decide⟩ ⟨13, 2, 0, 71778, 22554, 2133, 16384⟩
    (by decide) selected_cut_02175

theorem selected_cut_02176 : selected 8 ⟨71800, by decide⟩
    (prefixPartial 13 22555) = some ⟨13, 2, 0, 71800, 22555, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_22555_71800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22555 ⟨71800, by decide⟩ :=
  accepted_of_selected 13 22555 ⟨71800, by decide⟩ ⟨13, 2, 0, 71800, 22555, 1393, 16384⟩
    (by decide) selected_cut_02176

theorem unmarked_context_12_5638_71801 : frontier 9 ⟨71801, by decide⟩
    (prefixCache 12 5638) (prefixPartial 12 5638) = false := by
  decide +kernel

theorem node_context_12_5638_71801 : EJMOriginalGlobalDAGData.nodes 9 ⟨71801, by decide⟩ =
    .split (coordinate 12) (![⟨71712, by decide⟩,⟨71753, by decide⟩,⟨71778, by decide⟩,⟨71800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5638_71801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5638 ⟨71801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5638
    ⟨71801, by decide⟩ (by decide) (![⟨71712, by decide⟩,⟨71753, by decide⟩,⟨71778, by decide⟩,⟨71800, by decide⟩]) unmarked_context_12_5638_71801 node_context_12_5638_71801
  intro a
  fin_cases a
  · exact context_13_22552_71712
  · exact context_13_22553_71753
  · exact context_13_22554_71778
  · exact context_13_22555_71800

theorem selected_cut_02177 : selected 7 ⟨71822, by decide⟩
    (prefixPartial 14 90224) = some ⟨14, 2, 0, 71822, 90224, 1305, 4096⟩ := by
  decide +kernel

theorem context_14_90224_71822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90224 ⟨71822, by decide⟩ :=
  accepted_of_selected 14 90224 ⟨71822, by decide⟩ ⟨14, 2, 0, 71822, 90224, 1305, 4096⟩
    (by decide) selected_cut_02177

theorem selected_cut_02178 : selected 7 ⟨71847, by decide⟩
    (prefixPartial 14 90225) = some ⟨14, 2, 0, 71847, 90225, 1373, 4096⟩ := by
  decide +kernel

theorem context_14_90225_71847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90225 ⟨71847, by decide⟩ :=
  accepted_of_selected 14 90225 ⟨71847, by decide⟩ ⟨14, 2, 0, 71847, 90225, 1373, 4096⟩
    (by decide) selected_cut_02178

theorem selected_cut_02179 : selected 7 ⟨71866, by decide⟩
    (prefixPartial 14 90226) = some ⟨14, 2, 0, 71866, 90226, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_90226_71866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90226 ⟨71866, by decide⟩ :=
  accepted_of_selected 14 90226 ⟨71866, by decide⟩ ⟨14, 2, 0, 71866, 90226, 1453, 4096⟩
    (by decide) selected_cut_02179

theorem selected_cut_02180 : selected 7 ⟨71886, by decide⟩
    (prefixPartial 14 90227) = some ⟨14, 2, 0, 71886, 90227, 1601, 4096⟩ := by
  decide +kernel

theorem context_14_90227_71886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90227 ⟨71886, by decide⟩ :=
  accepted_of_selected 14 90227 ⟨71886, by decide⟩ ⟨14, 2, 0, 71886, 90227, 1601, 4096⟩
    (by decide) selected_cut_02180

theorem unmarked_context_13_22556_71887 : frontier 8 ⟨71887, by decide⟩
    (prefixCache 13 22556) (prefixPartial 13 22556) = false := by
  decide +kernel

theorem node_context_13_22556_71887 : EJMOriginalGlobalDAGData.nodes 8 ⟨71887, by decide⟩ =
    .split (coordinate 13) (![⟨71822, by decide⟩,⟨71847, by decide⟩,⟨71866, by decide⟩,⟨71886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22556_71887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22556 ⟨71887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22556
    ⟨71887, by decide⟩ (by decide) (![⟨71822, by decide⟩,⟨71847, by decide⟩,⟨71866, by decide⟩,⟨71886, by decide⟩]) unmarked_context_13_22556_71887 node_context_13_22556_71887
  intro a
  fin_cases a
  · exact context_14_90224_71822
  · exact context_14_90225_71847
  · exact context_14_90226_71866
  · exact context_14_90227_71886

theorem selected_cut_02181 : selected 8 ⟨71940, by decide⟩
    (prefixPartial 13 22557) = some ⟨13, 2, 0, 71940, 22557, 3593, 16384⟩ := by
  decide +kernel

theorem context_13_22557_71940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22557 ⟨71940, by decide⟩ :=
  accepted_of_selected 13 22557 ⟨71940, by decide⟩ ⟨13, 2, 0, 71940, 22557, 3593, 16384⟩
    (by decide) selected_cut_02181

theorem selected_cut_02182 : selected 8 ⟨71985, by decide⟩
    (prefixPartial 13 22558) = some ⟨13, 2, 0, 71985, 22558, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_22558_71985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22558 ⟨71985, by decide⟩ :=
  accepted_of_selected 13 22558 ⟨71985, by decide⟩ ⟨13, 2, 0, 71985, 22558, 2661, 16384⟩
    (by decide) selected_cut_02182

theorem selected_cut_02183 : selected 8 ⟨71998, by decide⟩
    (prefixPartial 13 22559) = some ⟨13, 2, 0, 71998, 22559, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_22559_71998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22559 ⟨71998, by decide⟩ :=
  accepted_of_selected 13 22559 ⟨71998, by decide⟩ ⟨13, 2, 0, 71998, 22559, 1321, 16384⟩
    (by decide) selected_cut_02183

theorem unmarked_context_12_5639_71999 : frontier 9 ⟨71999, by decide⟩
    (prefixCache 12 5639) (prefixPartial 12 5639) = false := by
  decide +kernel

theorem node_context_12_5639_71999 : EJMOriginalGlobalDAGData.nodes 9 ⟨71999, by decide⟩ =
    .split (coordinate 12) (![⟨71887, by decide⟩,⟨71940, by decide⟩,⟨71985, by decide⟩,⟨71998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5639_71999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5639 ⟨71999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5639
    ⟨71999, by decide⟩ (by decide) (![⟨71887, by decide⟩,⟨71940, by decide⟩,⟨71985, by decide⟩,⟨71998, by decide⟩]) unmarked_context_12_5639_71999 node_context_12_5639_71999
  intro a
  fin_cases a
  · exact context_13_22556_71887
  · exact context_13_22557_71940
  · exact context_13_22558_71985
  · exact context_13_22559_71998

theorem unmarked_context_11_1409_72000 : frontier 10 ⟨72000, by decide⟩
    (prefixCache 11 1409) (prefixPartial 11 1409) = false := by
  decide +kernel

theorem node_context_11_1409_72000 : EJMOriginalGlobalDAGData.nodes 10 ⟨72000, by decide⟩ =
    .split (coordinate 11) (![⟨71448, by decide⟩,⟨71632, by decide⟩,⟨71801, by decide⟩,⟨71999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1409_72000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1409 ⟨72000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1409
    ⟨72000, by decide⟩ (by decide) (![⟨71448, by decide⟩,⟨71632, by decide⟩,⟨71801, by decide⟩,⟨71999, by decide⟩]) unmarked_context_11_1409_72000 node_context_11_1409_72000
  intro a
  fin_cases a
  · exact context_12_5636_71448
  · exact context_12_5637_71632
  · exact context_12_5638_71801
  · exact context_12_5639_71999

theorem selected_cut_02184 : selected 8 ⟨72097, by decide⟩
    (prefixPartial 13 22560) = some ⟨13, 2, 0, 72097, 22560, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_22560_72097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22560 ⟨72097, by decide⟩ :=
  accepted_of_selected 13 22560 ⟨72097, by decide⟩ ⟨13, 2, 0, 72097, 22560, 2741, 16384⟩
    (by decide) selected_cut_02184

theorem selected_cut_02185 : selected 7 ⟨72137, by decide⟩
    (prefixPartial 14 90244) = some ⟨14, 2, 0, 72137, 90244, 1689, 4096⟩ := by
  decide +kernel

theorem context_14_90244_72137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90244 ⟨72137, by decide⟩ :=
  accepted_of_selected 14 90244 ⟨72137, by decide⟩ ⟨14, 2, 0, 72137, 90244, 1689, 4096⟩
    (by decide) selected_cut_02185

theorem selected_cut_02186 : selected 7 ⟨72191, by decide⟩
    (prefixPartial 14 90245) = some ⟨14, 2, 0, 72191, 90245, 1629, 4096⟩ := by
  decide +kernel

theorem context_14_90245_72191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90245 ⟨72191, by decide⟩ :=
  accepted_of_selected 14 90245 ⟨72191, by decide⟩ ⟨14, 2, 0, 72191, 90245, 1629, 4096⟩
    (by decide) selected_cut_02186

theorem selected_cut_02187 : selected 7 ⟨72238, by decide⟩
    (prefixPartial 14 90246) = some ⟨14, 2, 0, 72238, 90246, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_90246_72238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90246 ⟨72238, by decide⟩ :=
  accepted_of_selected 14 90246 ⟨72238, by decide⟩ ⟨14, 2, 0, 72238, 90246, 1117, 4096⟩
    (by decide) selected_cut_02187

theorem selected_cut_02188 : selected 7 ⟨72290, by decide⟩
    (prefixPartial 14 90247) = some ⟨14, 2, 0, 72290, 90247, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_90247_72290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90247 ⟨72290, by decide⟩ :=
  accepted_of_selected 14 90247 ⟨72290, by decide⟩ ⟨14, 2, 0, 72290, 90247, 1301, 4096⟩
    (by decide) selected_cut_02188

theorem unmarked_context_13_22561_72291 : frontier 8 ⟨72291, by decide⟩
    (prefixCache 13 22561) (prefixPartial 13 22561) = false := by
  decide +kernel

theorem node_context_13_22561_72291 : EJMOriginalGlobalDAGData.nodes 8 ⟨72291, by decide⟩ =
    .split (coordinate 13) (![⟨72137, by decide⟩,⟨72191, by decide⟩,⟨72238, by decide⟩,⟨72290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22561_72291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22561 ⟨72291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22561
    ⟨72291, by decide⟩ (by decide) (![⟨72137, by decide⟩,⟨72191, by decide⟩,⟨72238, by decide⟩,⟨72290, by decide⟩]) unmarked_context_13_22561_72291 node_context_13_22561_72291
  intro a
  fin_cases a
  · exact context_14_90244_72137
  · exact context_14_90245_72191
  · exact context_14_90246_72238
  · exact context_14_90247_72290

theorem selected_cut_02189 : selected 8 ⟨72292, by decide⟩
    (prefixPartial 13 22562) = some ⟨13, 1, 0, 72292, 22562, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22562_72292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22562 ⟨72292, by decide⟩ :=
  accepted_of_selected 13 22562 ⟨72292, by decide⟩ ⟨13, 1, 0, 72292, 22562, 1, 16384⟩
    (by decide) selected_cut_02189

theorem selected_cut_02190 : selected 8 ⟨72371, by decide⟩
    (prefixPartial 13 22563) = some ⟨13, 2, 0, 72371, 22563, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_22563_72371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22563 ⟨72371, by decide⟩ :=
  accepted_of_selected 13 22563 ⟨72371, by decide⟩ ⟨13, 2, 0, 72371, 22563, 1189, 16384⟩
    (by decide) selected_cut_02190

theorem unmarked_context_12_5640_72372 : frontier 9 ⟨72372, by decide⟩
    (prefixCache 12 5640) (prefixPartial 12 5640) = false := by
  decide +kernel

theorem node_context_12_5640_72372 : EJMOriginalGlobalDAGData.nodes 9 ⟨72372, by decide⟩ =
    .split (coordinate 12) (![⟨72097, by decide⟩,⟨72291, by decide⟩,⟨72292, by decide⟩,⟨72371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5640_72372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5640 ⟨72372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5640
    ⟨72372, by decide⟩ (by decide) (![⟨72097, by decide⟩,⟨72291, by decide⟩,⟨72292, by decide⟩,⟨72371, by decide⟩]) unmarked_context_12_5640_72372 node_context_12_5640_72372
  intro a
  fin_cases a
  · exact context_13_22560_72097
  · exact context_13_22561_72291
  · exact context_13_22562_72292
  · exact context_13_22563_72371

theorem selected_cut_02191 : selected 7 ⟨72387, by decide⟩
    (prefixPartial 14 90256) = some ⟨14, 2, 0, 72387, 90256, 965, 4096⟩ := by
  decide +kernel

theorem context_14_90256_72387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90256 ⟨72387, by decide⟩ :=
  accepted_of_selected 14 90256 ⟨72387, by decide⟩ ⟨14, 2, 0, 72387, 90256, 965, 4096⟩
    (by decide) selected_cut_02191

theorem selected_cut_02192 : selected 7 ⟨72409, by decide⟩
    (prefixPartial 14 90257) = some ⟨14, 2, 0, 72409, 90257, 1581, 4096⟩ := by
  decide +kernel

theorem context_14_90257_72409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90257 ⟨72409, by decide⟩ :=
  accepted_of_selected 14 90257 ⟨72409, by decide⟩ ⟨14, 2, 0, 72409, 90257, 1581, 4096⟩
    (by decide) selected_cut_02192

theorem selected_cut_02193 : selected 7 ⟨72430, by decide⟩
    (prefixPartial 14 90258) = some ⟨14, 2, 0, 72430, 90258, 1413, 4096⟩ := by
  decide +kernel

theorem context_14_90258_72430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90258 ⟨72430, by decide⟩ :=
  accepted_of_selected 14 90258 ⟨72430, by decide⟩ ⟨14, 2, 0, 72430, 90258, 1413, 4096⟩
    (by decide) selected_cut_02193

theorem selected_cut_02194 : selected 7 ⟨72450, by decide⟩
    (prefixPartial 14 90259) = some ⟨14, 2, 0, 72450, 90259, 1521, 4096⟩ := by
  decide +kernel

theorem context_14_90259_72450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90259 ⟨72450, by decide⟩ :=
  accepted_of_selected 14 90259 ⟨72450, by decide⟩ ⟨14, 2, 0, 72450, 90259, 1521, 4096⟩
    (by decide) selected_cut_02194

theorem unmarked_context_13_22564_72451 : frontier 8 ⟨72451, by decide⟩
    (prefixCache 13 22564) (prefixPartial 13 22564) = false := by
  decide +kernel

theorem node_context_13_22564_72451 : EJMOriginalGlobalDAGData.nodes 8 ⟨72451, by decide⟩ =
    .split (coordinate 13) (![⟨72387, by decide⟩,⟨72409, by decide⟩,⟨72430, by decide⟩,⟨72450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22564_72451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22564 ⟨72451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22564
    ⟨72451, by decide⟩ (by decide) (![⟨72387, by decide⟩,⟨72409, by decide⟩,⟨72430, by decide⟩,⟨72450, by decide⟩]) unmarked_context_13_22564_72451 node_context_13_22564_72451
  intro a
  fin_cases a
  · exact context_14_90256_72387
  · exact context_14_90257_72409
  · exact context_14_90258_72430
  · exact context_14_90259_72450

theorem selected_cut_02195 : selected 7 ⟨72465, by decide⟩
    (prefixPartial 14 90260) = some ⟨14, 2, 0, 72465, 90260, 965, 4096⟩ := by
  decide +kernel

theorem context_14_90260_72465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90260 ⟨72465, by decide⟩ :=
  accepted_of_selected 14 90260 ⟨72465, by decide⟩ ⟨14, 2, 0, 72465, 90260, 965, 4096⟩
    (by decide) selected_cut_02195

theorem selected_cut_02196 : selected 7 ⟨72485, by decide⟩
    (prefixPartial 14 90261) = some ⟨14, 2, 0, 72485, 90261, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_90261_72485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90261 ⟨72485, by decide⟩ :=
  accepted_of_selected 14 90261 ⟨72485, by decide⟩ ⟨14, 2, 0, 72485, 90261, 1201, 4096⟩
    (by decide) selected_cut_02196

theorem selected_cut_02197 : selected 7 ⟨72503, by decide⟩
    (prefixPartial 14 90262) = some ⟨14, 2, 0, 72503, 90262, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_90262_72503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90262 ⟨72503, by decide⟩ :=
  accepted_of_selected 14 90262 ⟨72503, by decide⟩ ⟨14, 2, 0, 72503, 90262, 1089, 4096⟩
    (by decide) selected_cut_02197

theorem selected_cut_02198 : selected 7 ⟨72519, by decide⟩
    (prefixPartial 14 90263) = some ⟨14, 2, 0, 72519, 90263, 1005, 4096⟩ := by
  decide +kernel

theorem context_14_90263_72519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90263 ⟨72519, by decide⟩ :=
  accepted_of_selected 14 90263 ⟨72519, by decide⟩ ⟨14, 2, 0, 72519, 90263, 1005, 4096⟩
    (by decide) selected_cut_02198

theorem unmarked_context_13_22565_72520 : frontier 8 ⟨72520, by decide⟩
    (prefixCache 13 22565) (prefixPartial 13 22565) = false := by
  decide +kernel

theorem node_context_13_22565_72520 : EJMOriginalGlobalDAGData.nodes 8 ⟨72520, by decide⟩ =
    .split (coordinate 13) (![⟨72465, by decide⟩,⟨72485, by decide⟩,⟨72503, by decide⟩,⟨72519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22565_72520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22565 ⟨72520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22565
    ⟨72520, by decide⟩ (by decide) (![⟨72465, by decide⟩,⟨72485, by decide⟩,⟨72503, by decide⟩,⟨72519, by decide⟩]) unmarked_context_13_22565_72520 node_context_13_22565_72520
  intro a
  fin_cases a
  · exact context_14_90260_72465
  · exact context_14_90261_72485
  · exact context_14_90262_72503
  · exact context_14_90263_72519

theorem selected_cut_02199 : selected 8 ⟨72556, by decide⟩
    (prefixPartial 13 22566) = some ⟨13, 2, 0, 72556, 22566, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_22566_72556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22566 ⟨72556, by decide⟩ :=
  accepted_of_selected 13 22566 ⟨72556, by decide⟩ ⟨13, 2, 0, 72556, 22566, 2553, 16384⟩
    (by decide) selected_cut_02199

theorem selected_cut_02200 : selected 8 ⟨72578, by decide⟩
    (prefixPartial 13 22567) = some ⟨13, 2, 0, 72578, 22567, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_22567_72578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22567 ⟨72578, by decide⟩ :=
  accepted_of_selected 13 22567 ⟨72578, by decide⟩ ⟨13, 2, 0, 72578, 22567, 1465, 16384⟩
    (by decide) selected_cut_02200

theorem unmarked_context_12_5641_72579 : frontier 9 ⟨72579, by decide⟩
    (prefixCache 12 5641) (prefixPartial 12 5641) = false := by
  decide +kernel

theorem node_context_12_5641_72579 : EJMOriginalGlobalDAGData.nodes 9 ⟨72579, by decide⟩ =
    .split (coordinate 12) (![⟨72451, by decide⟩,⟨72520, by decide⟩,⟨72556, by decide⟩,⟨72578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5641_72579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5641 ⟨72579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5641
    ⟨72579, by decide⟩ (by decide) (![⟨72451, by decide⟩,⟨72520, by decide⟩,⟨72556, by decide⟩,⟨72578, by decide⟩]) unmarked_context_12_5641_72579 node_context_12_5641_72579
  intro a
  fin_cases a
  · exact context_13_22564_72451
  · exact context_13_22565_72520
  · exact context_13_22566_72556
  · exact context_13_22567_72578

theorem selected_cut_02201 : selected 7 ⟨72597, by decide⟩
    (prefixPartial 14 90272) = some ⟨14, 2, 0, 72597, 90272, 1577, 4096⟩ := by
  decide +kernel

theorem context_14_90272_72597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90272 ⟨72597, by decide⟩ :=
  accepted_of_selected 14 90272 ⟨72597, by decide⟩ ⟨14, 2, 0, 72597, 90272, 1577, 4096⟩
    (by decide) selected_cut_02201

theorem selected_cut_02202 : selected 7 ⟨72630, by decide⟩
    (prefixPartial 14 90273) = some ⟨14, 2, 0, 72630, 90273, 2225, 4096⟩ := by
  decide +kernel

theorem context_14_90273_72630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90273 ⟨72630, by decide⟩ :=
  accepted_of_selected 14 90273 ⟨72630, by decide⟩ ⟨14, 2, 0, 72630, 90273, 2225, 4096⟩
    (by decide) selected_cut_02202

theorem selected_cut_02203 : selected 7 ⟨72668, by decide⟩
    (prefixPartial 14 90274) = some ⟨14, 2, 0, 72668, 90274, 2265, 4096⟩ := by
  decide +kernel

theorem context_14_90274_72668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90274 ⟨72668, by decide⟩ :=
  accepted_of_selected 14 90274 ⟨72668, by decide⟩ ⟨14, 2, 0, 72668, 90274, 2265, 4096⟩
    (by decide) selected_cut_02203

theorem selected_cut_02204 : selected 7 ⟨72700, by decide⟩
    (prefixPartial 14 90275) = some ⟨14, 2, 0, 72700, 90275, 2201, 4096⟩ := by
  decide +kernel

theorem context_14_90275_72700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90275 ⟨72700, by decide⟩ :=
  accepted_of_selected 14 90275 ⟨72700, by decide⟩ ⟨14, 2, 0, 72700, 90275, 2201, 4096⟩
    (by decide) selected_cut_02204

theorem unmarked_context_13_22568_72701 : frontier 8 ⟨72701, by decide⟩
    (prefixCache 13 22568) (prefixPartial 13 22568) = false := by
  decide +kernel

theorem node_context_13_22568_72701 : EJMOriginalGlobalDAGData.nodes 8 ⟨72701, by decide⟩ =
    .split (coordinate 13) (![⟨72597, by decide⟩,⟨72630, by decide⟩,⟨72668, by decide⟩,⟨72700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22568_72701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22568 ⟨72701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22568
    ⟨72701, by decide⟩ (by decide) (![⟨72597, by decide⟩,⟨72630, by decide⟩,⟨72668, by decide⟩,⟨72700, by decide⟩]) unmarked_context_13_22568_72701 node_context_13_22568_72701
  intro a
  fin_cases a
  · exact context_14_90272_72597
  · exact context_14_90273_72630
  · exact context_14_90274_72668
  · exact context_14_90275_72700

theorem selected_cut_02205 : selected 7 ⟨72719, by decide⟩
    (prefixPartial 14 90276) = some ⟨14, 2, 0, 72719, 90276, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_90276_72719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90276 ⟨72719, by decide⟩ :=
  accepted_of_selected 14 90276 ⟨72719, by decide⟩ ⟨14, 2, 0, 72719, 90276, 1253, 4096⟩
    (by decide) selected_cut_02205

theorem selected_cut_02206 : selected 7 ⟨72748, by decide⟩
    (prefixPartial 14 90277) = some ⟨14, 2, 0, 72748, 90277, 1829, 4096⟩ := by
  decide +kernel

theorem context_14_90277_72748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90277 ⟨72748, by decide⟩ :=
  accepted_of_selected 14 90277 ⟨72748, by decide⟩ ⟨14, 2, 0, 72748, 90277, 1829, 4096⟩
    (by decide) selected_cut_02206

theorem selected_cut_02207 : selected 7 ⟨72786, by decide⟩
    (prefixPartial 14 90278) = some ⟨14, 2, 0, 72786, 90278, 1825, 4096⟩ := by
  decide +kernel

theorem context_14_90278_72786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90278 ⟨72786, by decide⟩ :=
  accepted_of_selected 14 90278 ⟨72786, by decide⟩ ⟨14, 2, 0, 72786, 90278, 1825, 4096⟩
    (by decide) selected_cut_02207

theorem selected_cut_02208 : selected 7 ⟨72815, by decide⟩
    (prefixPartial 14 90279) = some ⟨14, 2, 0, 72815, 90279, 1617, 4096⟩ := by
  decide +kernel

theorem context_14_90279_72815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90279 ⟨72815, by decide⟩ :=
  accepted_of_selected 14 90279 ⟨72815, by decide⟩ ⟨14, 2, 0, 72815, 90279, 1617, 4096⟩
    (by decide) selected_cut_02208

theorem unmarked_context_13_22569_72816 : frontier 8 ⟨72816, by decide⟩
    (prefixCache 13 22569) (prefixPartial 13 22569) = false := by
  decide +kernel

theorem node_context_13_22569_72816 : EJMOriginalGlobalDAGData.nodes 8 ⟨72816, by decide⟩ =
    .split (coordinate 13) (![⟨72719, by decide⟩,⟨72748, by decide⟩,⟨72786, by decide⟩,⟨72815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22569_72816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22569 ⟨72816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22569
    ⟨72816, by decide⟩ (by decide) (![⟨72719, by decide⟩,⟨72748, by decide⟩,⟨72786, by decide⟩,⟨72815, by decide⟩]) unmarked_context_13_22569_72816 node_context_13_22569_72816
  intro a
  fin_cases a
  · exact context_14_90276_72719
  · exact context_14_90277_72748
  · exact context_14_90278_72786
  · exact context_14_90279_72815

theorem selected_cut_02209 : selected 8 ⟨72890, by decide⟩
    (prefixPartial 13 22570) = some ⟨13, 2, 0, 72890, 22570, 3925, 16384⟩ := by
  decide +kernel

theorem context_13_22570_72890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22570 ⟨72890, by decide⟩ :=
  accepted_of_selected 13 22570 ⟨72890, by decide⟩ ⟨13, 2, 0, 72890, 22570, 3925, 16384⟩
    (by decide) selected_cut_02209

theorem selected_cut_02210 : selected 8 ⟨72949, by decide⟩
    (prefixPartial 13 22571) = some ⟨13, 2, 0, 72949, 22571, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_22571_72949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22571 ⟨72949, by decide⟩ :=
  accepted_of_selected 13 22571 ⟨72949, by decide⟩ ⟨13, 2, 0, 72949, 22571, 2093, 16384⟩
    (by decide) selected_cut_02210

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
