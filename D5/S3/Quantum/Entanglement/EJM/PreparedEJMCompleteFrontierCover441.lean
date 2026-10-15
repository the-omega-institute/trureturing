/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover440
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_84444_1157226 : frontier 10 ⟨1157226, by decide⟩
    (prefixCache 11 84444) (prefixPartial 11 84444) = false := by
  decide +kernel

theorem node_context_11_84444_1157226 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157226, by decide⟩ =
    .split (coordinate 11) (![⟨1157123, by decide⟩,⟨1157149, by decide⟩,⟨1157190, by decide⟩,⟨1157225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84444_1157226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84444 ⟨1157226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84444
    ⟨1157226, by decide⟩ (by decide) (![⟨1157123, by decide⟩,⟨1157149, by decide⟩,⟨1157190, by decide⟩,⟨1157225, by decide⟩]) unmarked_context_11_84444_1157226 node_context_11_84444_1157226
  intro a
  fin_cases a
  · exact context_12_337776_1157123
  · exact context_12_337777_1157149
  · exact context_12_337778_1157190
  · exact context_12_337779_1157225

theorem selected_cut_42340 : selected 9 ⟨1157249, by decide⟩
    (prefixPartial 12 337780) = some ⟨12, 2, 0, 1157249, 337780, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_337780_1157249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337780 ⟨1157249, by decide⟩ :=
  accepted_of_selected 12 337780 ⟨1157249, by decide⟩ ⟨12, 2, 0, 1157249, 337780, 1453, 65536⟩
    (by decide) selected_cut_42340

theorem selected_cut_42341 : selected 9 ⟨410616, by decide⟩
    (prefixPartial 12 337781) = some ⟨12, 1, 0, 410616, 337781, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337781_410616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337781 ⟨410616, by decide⟩ :=
  accepted_of_selected 12 337781 ⟨410616, by decide⟩ ⟨12, 1, 0, 410616, 337781, 1, 65536⟩
    (by decide) selected_cut_42341

theorem selected_cut_42342 : selected 9 ⟨1157280, by decide⟩
    (prefixPartial 12 337782) = some ⟨12, 2, 0, 1157280, 337782, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_337782_1157280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337782 ⟨1157280, by decide⟩ :=
  accepted_of_selected 12 337782 ⟨1157280, by decide⟩ ⟨12, 2, 0, 1157280, 337782, 1577, 65536⟩
    (by decide) selected_cut_42342

theorem selected_cut_42343 : selected 9 ⟨1157304, by decide⟩
    (prefixPartial 12 337783) = some ⟨12, 2, 0, 1157304, 337783, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_337783_1157304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337783 ⟨1157304, by decide⟩ :=
  accepted_of_selected 12 337783 ⟨1157304, by decide⟩ ⟨12, 2, 0, 1157304, 337783, 1645, 65536⟩
    (by decide) selected_cut_42343

theorem unmarked_context_11_84445_1157305 : frontier 10 ⟨1157305, by decide⟩
    (prefixCache 11 84445) (prefixPartial 11 84445) = false := by
  decide +kernel

theorem node_context_11_84445_1157305 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157305, by decide⟩ =
    .split (coordinate 11) (![⟨1157249, by decide⟩,⟨410616, by decide⟩,⟨1157280, by decide⟩,⟨1157304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84445_1157305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84445 ⟨1157305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84445
    ⟨1157305, by decide⟩ (by decide) (![⟨1157249, by decide⟩,⟨410616, by decide⟩,⟨1157280, by decide⟩,⟨1157304, by decide⟩]) unmarked_context_11_84445_1157305 node_context_11_84445_1157305
  intro a
  fin_cases a
  · exact context_12_337780_1157249
  · exact context_12_337781_410616
  · exact context_12_337782_1157280
  · exact context_12_337783_1157304

theorem selected_cut_42344 : selected 9 ⟨1157327, by decide⟩
    (prefixPartial 12 337784) = some ⟨12, 2, 0, 1157327, 337784, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_337784_1157327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337784 ⟨1157327, by decide⟩ :=
  accepted_of_selected 12 337784 ⟨1157327, by decide⟩ ⟨12, 2, 0, 1157327, 337784, 1617, 65536⟩
    (by decide) selected_cut_42344

theorem selected_cut_42345 : selected 9 ⟨1157344, by decide⟩
    (prefixPartial 12 337785) = some ⟨12, 2, 0, 1157344, 337785, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_337785_1157344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337785 ⟨1157344, by decide⟩ :=
  accepted_of_selected 12 337785 ⟨1157344, by decide⟩ ⟨12, 2, 0, 1157344, 337785, 1433, 65536⟩
    (by decide) selected_cut_42345

theorem selected_cut_42346 : selected 9 ⟨1157372, by decide⟩
    (prefixPartial 12 337786) = some ⟨12, 2, 0, 1157372, 337786, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_337786_1157372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337786 ⟨1157372, by decide⟩ :=
  accepted_of_selected 12 337786 ⟨1157372, by decide⟩ ⟨12, 2, 0, 1157372, 337786, 1709, 65536⟩
    (by decide) selected_cut_42346

theorem selected_cut_42347 : selected 9 ⟨1157401, by decide⟩
    (prefixPartial 12 337787) = some ⟨12, 2, 0, 1157401, 337787, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_337787_1157401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337787 ⟨1157401, by decide⟩ :=
  accepted_of_selected 12 337787 ⟨1157401, by decide⟩ ⟨12, 2, 0, 1157401, 337787, 1677, 65536⟩
    (by decide) selected_cut_42347

theorem unmarked_context_11_84446_1157402 : frontier 10 ⟨1157402, by decide⟩
    (prefixCache 11 84446) (prefixPartial 11 84446) = false := by
  decide +kernel

theorem node_context_11_84446_1157402 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157402, by decide⟩ =
    .split (coordinate 11) (![⟨1157327, by decide⟩,⟨1157344, by decide⟩,⟨1157372, by decide⟩,⟨1157401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84446_1157402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84446 ⟨1157402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84446
    ⟨1157402, by decide⟩ (by decide) (![⟨1157327, by decide⟩,⟨1157344, by decide⟩,⟨1157372, by decide⟩,⟨1157401, by decide⟩]) unmarked_context_11_84446_1157402 node_context_11_84446_1157402
  intro a
  fin_cases a
  · exact context_12_337784_1157327
  · exact context_12_337785_1157344
  · exact context_12_337786_1157372
  · exact context_12_337787_1157401

theorem selected_cut_42348 : selected 10 ⟨1157457, by decide⟩
    (prefixPartial 11 84447) = some ⟨11, 2, 0, 1157457, 84447, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_84447_1157457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84447 ⟨1157457, by decide⟩ :=
  accepted_of_selected 11 84447 ⟨1157457, by decide⟩ ⟨11, 2, 0, 1157457, 84447, 3113, 262144⟩
    (by decide) selected_cut_42348

theorem unmarked_context_10_21111_1157458 : frontier 11 ⟨1157458, by decide⟩
    (prefixCache 10 21111) (prefixPartial 10 21111) = false := by
  decide +kernel

theorem node_context_10_21111_1157458 : EJMOriginalGlobalDAGData.nodes 11 ⟨1157458, by decide⟩ =
    .split (coordinate 10) (![⟨1157226, by decide⟩,⟨1157305, by decide⟩,⟨1157402, by decide⟩,⟨1157457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21111_1157458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21111 ⟨1157458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21111
    ⟨1157458, by decide⟩ (by decide) (![⟨1157226, by decide⟩,⟨1157305, by decide⟩,⟨1157402, by decide⟩,⟨1157457, by decide⟩]) unmarked_context_10_21111_1157458 node_context_10_21111_1157458
  intro a
  fin_cases a
  · exact context_11_84444_1157226
  · exact context_11_84445_1157305
  · exact context_11_84446_1157402
  · exact context_11_84447_1157457

theorem unmarked_context_9_5277_1157459 : frontier 12 ⟨1157459, by decide⟩
    (prefixCache 9 5277) (prefixPartial 9 5277) = false := by
  decide +kernel

theorem node_context_9_5277_1157459 : EJMOriginalGlobalDAGData.nodes 12 ⟨1157459, by decide⟩ =
    .split (coordinate 9) (![⟨1156751, by decide⟩,⟨893098, by decide⟩,⟨1157092, by decide⟩,⟨1157458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5277_1157459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5277 ⟨1157459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5277
    ⟨1157459, by decide⟩ (by decide) (![⟨1156751, by decide⟩,⟨893098, by decide⟩,⟨1157092, by decide⟩,⟨1157458, by decide⟩]) unmarked_context_9_5277_1157459 node_context_9_5277_1157459
  intro a
  fin_cases a
  · exact context_10_21108_1156751
  · exact context_10_21109_893098
  · exact context_10_21110_1157092
  · exact context_10_21111_1157458

theorem selected_cut_42349 : selected 10 ⟨1157503, by decide⟩
    (prefixPartial 11 84448) = some ⟨11, 2, 0, 1157503, 84448, 3801, 262144⟩ := by
  decide +kernel

theorem context_11_84448_1157503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84448 ⟨1157503, by decide⟩ :=
  accepted_of_selected 11 84448 ⟨1157503, by decide⟩ ⟨11, 2, 0, 1157503, 84448, 3801, 262144⟩
    (by decide) selected_cut_42349

theorem selected_cut_42350 : selected 9 ⟨1157524, by decide⟩
    (prefixPartial 12 337796) = some ⟨12, 2, 0, 1157524, 337796, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_337796_1157524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337796 ⟨1157524, by decide⟩ :=
  accepted_of_selected 12 337796 ⟨1157524, by decide⟩ ⟨12, 2, 0, 1157524, 337796, 1173, 65536⟩
    (by decide) selected_cut_42350

theorem selected_cut_42351 : selected 9 ⟨1157539, by decide⟩
    (prefixPartial 12 337797) = some ⟨12, 2, 0, 1157539, 337797, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_337797_1157539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337797 ⟨1157539, by decide⟩ :=
  accepted_of_selected 12 337797 ⟨1157539, by decide⟩ ⟨12, 2, 0, 1157539, 337797, 1097, 65536⟩
    (by decide) selected_cut_42351

theorem selected_cut_42352 : selected 9 ⟨1157554, by decide⟩
    (prefixPartial 12 337798) = some ⟨12, 2, 0, 1157554, 337798, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_337798_1157554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337798 ⟨1157554, by decide⟩ :=
  accepted_of_selected 12 337798 ⟨1157554, by decide⟩ ⟨12, 2, 0, 1157554, 337798, 1153, 65536⟩
    (by decide) selected_cut_42352

theorem selected_cut_42353 : selected 9 ⟨1157571, by decide⟩
    (prefixPartial 12 337799) = some ⟨12, 2, 0, 1157571, 337799, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_337799_1157571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337799 ⟨1157571, by decide⟩ :=
  accepted_of_selected 12 337799 ⟨1157571, by decide⟩ ⟨12, 2, 0, 1157571, 337799, 1273, 65536⟩
    (by decide) selected_cut_42353

theorem unmarked_context_11_84449_1157572 : frontier 10 ⟨1157572, by decide⟩
    (prefixCache 11 84449) (prefixPartial 11 84449) = false := by
  decide +kernel

theorem node_context_11_84449_1157572 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157572, by decide⟩ =
    .split (coordinate 11) (![⟨1157524, by decide⟩,⟨1157539, by decide⟩,⟨1157554, by decide⟩,⟨1157571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84449_1157572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84449 ⟨1157572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84449
    ⟨1157572, by decide⟩ (by decide) (![⟨1157524, by decide⟩,⟨1157539, by decide⟩,⟨1157554, by decide⟩,⟨1157571, by decide⟩]) unmarked_context_11_84449_1157572 node_context_11_84449_1157572
  intro a
  fin_cases a
  · exact context_12_337796_1157524
  · exact context_12_337797_1157539
  · exact context_12_337798_1157554
  · exact context_12_337799_1157571

theorem selected_cut_42354 : selected 10 ⟨1157623, by decide⟩
    (prefixPartial 11 84450) = some ⟨11, 2, 0, 1157623, 84450, 3813, 262144⟩ := by
  decide +kernel

theorem context_11_84450_1157623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84450 ⟨1157623, by decide⟩ :=
  accepted_of_selected 11 84450 ⟨1157623, by decide⟩ ⟨11, 2, 0, 1157623, 84450, 3813, 262144⟩
    (by decide) selected_cut_42354

theorem selected_cut_42355 : selected 10 ⟨1157661, by decide⟩
    (prefixPartial 11 84451) = some ⟨11, 2, 0, 1157661, 84451, 3141, 262144⟩ := by
  decide +kernel

theorem context_11_84451_1157661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84451 ⟨1157661, by decide⟩ :=
  accepted_of_selected 11 84451 ⟨1157661, by decide⟩ ⟨11, 2, 0, 1157661, 84451, 3141, 262144⟩
    (by decide) selected_cut_42355

theorem unmarked_context_10_21112_1157662 : frontier 11 ⟨1157662, by decide⟩
    (prefixCache 10 21112) (prefixPartial 10 21112) = false := by
  decide +kernel

theorem node_context_10_21112_1157662 : EJMOriginalGlobalDAGData.nodes 11 ⟨1157662, by decide⟩ =
    .split (coordinate 10) (![⟨1157503, by decide⟩,⟨1157572, by decide⟩,⟨1157623, by decide⟩,⟨1157661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21112_1157662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21112 ⟨1157662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21112
    ⟨1157662, by decide⟩ (by decide) (![⟨1157503, by decide⟩,⟨1157572, by decide⟩,⟨1157623, by decide⟩,⟨1157661, by decide⟩]) unmarked_context_10_21112_1157662 node_context_10_21112_1157662
  intro a
  fin_cases a
  · exact context_11_84448_1157503
  · exact context_11_84449_1157572
  · exact context_11_84450_1157623
  · exact context_11_84451_1157661

theorem selected_cut_42356 : selected 9 ⟨1157678, by decide⟩
    (prefixPartial 12 337808) = some ⟨12, 2, 0, 1157678, 337808, 997, 65536⟩ := by
  decide +kernel

theorem context_12_337808_1157678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337808 ⟨1157678, by decide⟩ :=
  accepted_of_selected 12 337808 ⟨1157678, by decide⟩ ⟨12, 2, 0, 1157678, 337808, 997, 65536⟩
    (by decide) selected_cut_42356

theorem selected_cut_42357 : selected 9 ⟨1157688, by decide⟩
    (prefixPartial 12 337809) = some ⟨12, 2, 0, 1157688, 337809, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_337809_1157688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337809 ⟨1157688, by decide⟩ :=
  accepted_of_selected 12 337809 ⟨1157688, by decide⟩ ⟨12, 2, 0, 1157688, 337809, 1013, 65536⟩
    (by decide) selected_cut_42357

theorem selected_cut_42358 : selected 9 ⟨1157704, by decide⟩
    (prefixPartial 12 337810) = some ⟨12, 2, 0, 1157704, 337810, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_337810_1157704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337810 ⟨1157704, by decide⟩ :=
  accepted_of_selected 12 337810 ⟨1157704, by decide⟩ ⟨12, 2, 0, 1157704, 337810, 1133, 65536⟩
    (by decide) selected_cut_42358

theorem selected_cut_42359 : selected 9 ⟨1157713, by decide⟩
    (prefixPartial 12 337811) = some ⟨12, 2, 0, 1157713, 337811, 969, 65536⟩ := by
  decide +kernel

theorem context_12_337811_1157713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337811 ⟨1157713, by decide⟩ :=
  accepted_of_selected 12 337811 ⟨1157713, by decide⟩ ⟨12, 2, 0, 1157713, 337811, 969, 65536⟩
    (by decide) selected_cut_42359

theorem unmarked_context_11_84452_1157714 : frontier 10 ⟨1157714, by decide⟩
    (prefixCache 11 84452) (prefixPartial 11 84452) = false := by
  decide +kernel

theorem node_context_11_84452_1157714 : EJMOriginalGlobalDAGData.nodes 10 ⟨1157714, by decide⟩ =
    .split (coordinate 11) (![⟨1157678, by decide⟩,⟨1157688, by decide⟩,⟨1157704, by decide⟩,⟨1157713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84452_1157714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84452 ⟨1157714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84452
    ⟨1157714, by decide⟩ (by decide) (![⟨1157678, by decide⟩,⟨1157688, by decide⟩,⟨1157704, by decide⟩,⟨1157713, by decide⟩]) unmarked_context_11_84452_1157714 node_context_11_84452_1157714
  intro a
  fin_cases a
  · exact context_12_337808_1157678
  · exact context_12_337809_1157688
  · exact context_12_337810_1157704
  · exact context_12_337811_1157713

theorem selected_cut_42360 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84453) = some ⟨11, 1, 0, 892405, 84453, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84453_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84453 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84453 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84453, 1, 262144⟩
    (by decide) selected_cut_42360

theorem selected_cut_42361 : selected 10 ⟨1157754, by decide⟩
    (prefixPartial 11 84454) = some ⟨11, 2, 0, 1157754, 84454, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_84454_1157754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84454 ⟨1157754, by decide⟩ :=
  accepted_of_selected 11 84454 ⟨1157754, by decide⟩ ⟨11, 2, 0, 1157754, 84454, 3025, 262144⟩
    (by decide) selected_cut_42361

theorem selected_cut_42362 : selected 10 ⟨1157778, by decide⟩
    (prefixPartial 11 84455) = some ⟨11, 2, 0, 1157778, 84455, 2533, 262144⟩ := by
  decide +kernel

theorem context_11_84455_1157778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84455 ⟨1157778, by decide⟩ :=
  accepted_of_selected 11 84455 ⟨1157778, by decide⟩ ⟨11, 2, 0, 1157778, 84455, 2533, 262144⟩
    (by decide) selected_cut_42362

theorem unmarked_context_10_21113_1157779 : frontier 11 ⟨1157779, by decide⟩
    (prefixCache 10 21113) (prefixPartial 10 21113) = false := by
  decide +kernel

theorem node_context_10_21113_1157779 : EJMOriginalGlobalDAGData.nodes 11 ⟨1157779, by decide⟩ =
    .split (coordinate 10) (![⟨1157714, by decide⟩,⟨892405, by decide⟩,⟨1157754, by decide⟩,⟨1157778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21113_1157779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21113 ⟨1157779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21113
    ⟨1157779, by decide⟩ (by decide) (![⟨1157714, by decide⟩,⟨892405, by decide⟩,⟨1157754, by decide⟩,⟨1157778, by decide⟩]) unmarked_context_10_21113_1157779 node_context_10_21113_1157779
  intro a
  fin_cases a
  · exact context_11_84452_1157714
  · exact context_11_84453_892405
  · exact context_11_84454_1157754
  · exact context_11_84455_1157778

theorem selected_cut_42363 : selected 10 ⟨1157803, by decide⟩
    (prefixPartial 11 84456) = some ⟨11, 2, 0, 1157803, 84456, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_84456_1157803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84456 ⟨1157803, by decide⟩ :=
  accepted_of_selected 11 84456 ⟨1157803, by decide⟩ ⟨11, 2, 0, 1157803, 84456, 2413, 262144⟩
    (by decide) selected_cut_42363

theorem selected_cut_42364 : selected 10 ⟨1157830, by decide⟩
    (prefixPartial 11 84457) = some ⟨11, 2, 0, 1157830, 84457, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_84457_1157830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84457 ⟨1157830, by decide⟩ :=
  accepted_of_selected 11 84457 ⟨1157830, by decide⟩ ⟨11, 2, 0, 1157830, 84457, 2329, 262144⟩
    (by decide) selected_cut_42364

theorem selected_cut_42365 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84458) = some ⟨11, 1, 0, 1109453, 84458, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84458_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84458 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84458 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84458, 1, 262144⟩
    (by decide) selected_cut_42365

theorem selected_cut_42366 : selected 10 ⟨1157844, by decide⟩
    (prefixPartial 11 84459) = some ⟨11, 2, 0, 1157844, 84459, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_84459_1157844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84459 ⟨1157844, by decide⟩ :=
  accepted_of_selected 11 84459 ⟨1157844, by decide⟩ ⟨11, 2, 0, 1157844, 84459, 1373, 262144⟩
    (by decide) selected_cut_42366

theorem unmarked_context_10_21114_1157845 : frontier 11 ⟨1157845, by decide⟩
    (prefixCache 10 21114) (prefixPartial 10 21114) = false := by
  decide +kernel

theorem node_context_10_21114_1157845 : EJMOriginalGlobalDAGData.nodes 11 ⟨1157845, by decide⟩ =
    .split (coordinate 10) (![⟨1157803, by decide⟩,⟨1157830, by decide⟩,⟨1109453, by decide⟩,⟨1157844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21114_1157845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21114 ⟨1157845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21114
    ⟨1157845, by decide⟩ (by decide) (![⟨1157803, by decide⟩,⟨1157830, by decide⟩,⟨1109453, by decide⟩,⟨1157844, by decide⟩]) unmarked_context_10_21114_1157845 node_context_10_21114_1157845
  intro a
  fin_cases a
  · exact context_11_84456_1157803
  · exact context_11_84457_1157830
  · exact context_11_84458_1109453
  · exact context_11_84459_1157844

theorem selected_cut_42367 : selected 10 ⟨1157891, by decide⟩
    (prefixPartial 11 84460) = some ⟨11, 2, 0, 1157891, 84460, 3301, 262144⟩ := by
  decide +kernel

theorem context_11_84460_1157891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84460 ⟨1157891, by decide⟩ :=
  accepted_of_selected 11 84460 ⟨1157891, by decide⟩ ⟨11, 2, 0, 1157891, 84460, 3301, 262144⟩
    (by decide) selected_cut_42367

theorem selected_cut_42368 : selected 10 ⟨1157930, by decide⟩
    (prefixPartial 11 84461) = some ⟨11, 2, 0, 1157930, 84461, 2877, 262144⟩ := by
  decide +kernel

theorem context_11_84461_1157930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84461 ⟨1157930, by decide⟩ :=
  accepted_of_selected 11 84461 ⟨1157930, by decide⟩ ⟨11, 2, 0, 1157930, 84461, 2877, 262144⟩
    (by decide) selected_cut_42368

theorem selected_cut_42369 : selected 10 ⟨1157958, by decide⟩
    (prefixPartial 11 84462) = some ⟨11, 2, 0, 1157958, 84462, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_84462_1157958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84462 ⟨1157958, by decide⟩ :=
  accepted_of_selected 11 84462 ⟨1157958, by decide⟩ ⟨11, 2, 0, 1157958, 84462, 2041, 262144⟩
    (by decide) selected_cut_42369

theorem selected_cut_42370 : selected 10 ⟨1157987, by decide⟩
    (prefixPartial 11 84463) = some ⟨11, 2, 0, 1157987, 84463, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_84463_1157987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84463 ⟨1157987, by decide⟩ :=
  accepted_of_selected 11 84463 ⟨1157987, by decide⟩ ⟨11, 2, 0, 1157987, 84463, 1381, 262144⟩
    (by decide) selected_cut_42370

theorem unmarked_context_10_21115_1157988 : frontier 11 ⟨1157988, by decide⟩
    (prefixCache 10 21115) (prefixPartial 10 21115) = false := by
  decide +kernel

theorem node_context_10_21115_1157988 : EJMOriginalGlobalDAGData.nodes 11 ⟨1157988, by decide⟩ =
    .split (coordinate 10) (![⟨1157891, by decide⟩,⟨1157930, by decide⟩,⟨1157958, by decide⟩,⟨1157987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21115_1157988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21115 ⟨1157988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21115
    ⟨1157988, by decide⟩ (by decide) (![⟨1157891, by decide⟩,⟨1157930, by decide⟩,⟨1157958, by decide⟩,⟨1157987, by decide⟩]) unmarked_context_10_21115_1157988 node_context_10_21115_1157988
  intro a
  fin_cases a
  · exact context_11_84460_1157891
  · exact context_11_84461_1157930
  · exact context_11_84462_1157958
  · exact context_11_84463_1157987

theorem unmarked_context_9_5278_1157989 : frontier 12 ⟨1157989, by decide⟩
    (prefixCache 9 5278) (prefixPartial 9 5278) = false := by
  decide +kernel

theorem node_context_9_5278_1157989 : EJMOriginalGlobalDAGData.nodes 12 ⟨1157989, by decide⟩ =
    .split (coordinate 9) (![⟨1157662, by decide⟩,⟨1157779, by decide⟩,⟨1157845, by decide⟩,⟨1157988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5278_1157989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5278 ⟨1157989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5278
    ⟨1157989, by decide⟩ (by decide) (![⟨1157662, by decide⟩,⟨1157779, by decide⟩,⟨1157845, by decide⟩,⟨1157988, by decide⟩]) unmarked_context_9_5278_1157989 node_context_9_5278_1157989
  intro a
  fin_cases a
  · exact context_10_21112_1157662
  · exact context_10_21113_1157779
  · exact context_10_21114_1157845
  · exact context_10_21115_1157988

theorem selected_cut_42371 : selected 10 ⟨1158002, by decide⟩
    (prefixPartial 11 84464) = some ⟨11, 2, 0, 1158002, 84464, 945, 262144⟩ := by
  decide +kernel

theorem context_11_84464_1158002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84464 ⟨1158002, by decide⟩ :=
  accepted_of_selected 11 84464 ⟨1158002, by decide⟩ ⟨11, 2, 0, 1158002, 84464, 945, 262144⟩
    (by decide) selected_cut_42371

theorem selected_cut_42372 : selected 10 ⟨1158023, by decide⟩
    (prefixPartial 11 84465) = some ⟨11, 2, 0, 1158023, 84465, 1617, 262144⟩ := by
  decide +kernel

theorem context_11_84465_1158023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84465 ⟨1158023, by decide⟩ :=
  accepted_of_selected 11 84465 ⟨1158023, by decide⟩ ⟨11, 2, 0, 1158023, 84465, 1617, 262144⟩
    (by decide) selected_cut_42372

theorem selected_cut_42373 : selected 10 ⟨1158044, by decide⟩
    (prefixPartial 11 84466) = some ⟨11, 2, 0, 1158044, 84466, 1577, 262144⟩ := by
  decide +kernel

theorem context_11_84466_1158044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84466 ⟨1158044, by decide⟩ :=
  accepted_of_selected 11 84466 ⟨1158044, by decide⟩ ⟨11, 2, 0, 1158044, 84466, 1577, 262144⟩
    (by decide) selected_cut_42373

theorem selected_cut_42374 : selected 10 ⟨1158063, by decide⟩
    (prefixPartial 11 84467) = some ⟨11, 2, 0, 1158063, 84467, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_84467_1158063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84467 ⟨1158063, by decide⟩ :=
  accepted_of_selected 11 84467 ⟨1158063, by decide⟩ ⟨11, 2, 0, 1158063, 84467, 1149, 262144⟩
    (by decide) selected_cut_42374

theorem unmarked_context_10_21116_1158064 : frontier 11 ⟨1158064, by decide⟩
    (prefixCache 10 21116) (prefixPartial 10 21116) = false := by
  decide +kernel

theorem node_context_10_21116_1158064 : EJMOriginalGlobalDAGData.nodes 11 ⟨1158064, by decide⟩ =
    .split (coordinate 10) (![⟨1158002, by decide⟩,⟨1158023, by decide⟩,⟨1158044, by decide⟩,⟨1158063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21116_1158064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21116 ⟨1158064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21116
    ⟨1158064, by decide⟩ (by decide) (![⟨1158002, by decide⟩,⟨1158023, by decide⟩,⟨1158044, by decide⟩,⟨1158063, by decide⟩]) unmarked_context_10_21116_1158064 node_context_10_21116_1158064
  intro a
  fin_cases a
  · exact context_11_84464_1158002
  · exact context_11_84465_1158023
  · exact context_11_84466_1158044
  · exact context_11_84467_1158063

theorem selected_cut_42375 : selected 11 ⟨1158098, by decide⟩
    (prefixPartial 10 21117) = some ⟨10, 2, 0, 1158098, 21117, 3045, 1048576⟩ := by
  decide +kernel

theorem context_10_21117_1158098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21117 ⟨1158098, by decide⟩ :=
  accepted_of_selected 10 21117 ⟨1158098, by decide⟩ ⟨10, 2, 0, 1158098, 21117, 3045, 1048576⟩
    (by decide) selected_cut_42375

theorem selected_cut_42376 : selected 11 ⟨1158152, by decide⟩
    (prefixPartial 10 21118) = some ⟨10, 2, 0, 1158152, 21118, 2381, 1048576⟩ := by
  decide +kernel

theorem context_10_21118_1158152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21118 ⟨1158152, by decide⟩ :=
  accepted_of_selected 10 21118 ⟨1158152, by decide⟩ ⟨10, 2, 0, 1158152, 21118, 2381, 1048576⟩
    (by decide) selected_cut_42376

theorem selected_cut_42377 : selected 11 ⟨1158168, by decide⟩
    (prefixPartial 10 21119) = some ⟨10, 2, 0, 1158168, 21119, 409, 1048576⟩ := by
  decide +kernel

theorem context_10_21119_1158168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21119 ⟨1158168, by decide⟩ :=
  accepted_of_selected 10 21119 ⟨1158168, by decide⟩ ⟨10, 2, 0, 1158168, 21119, 409, 1048576⟩
    (by decide) selected_cut_42377

theorem unmarked_context_9_5279_1158169 : frontier 12 ⟨1158169, by decide⟩
    (prefixCache 9 5279) (prefixPartial 9 5279) = false := by
  decide +kernel

theorem node_context_9_5279_1158169 : EJMOriginalGlobalDAGData.nodes 12 ⟨1158169, by decide⟩ =
    .split (coordinate 9) (![⟨1158064, by decide⟩,⟨1158098, by decide⟩,⟨1158152, by decide⟩,⟨1158168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5279_1158169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5279 ⟨1158169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5279
    ⟨1158169, by decide⟩ (by decide) (![⟨1158064, by decide⟩,⟨1158098, by decide⟩,⟨1158152, by decide⟩,⟨1158168, by decide⟩]) unmarked_context_9_5279_1158169 node_context_9_5279_1158169
  intro a
  fin_cases a
  · exact context_10_21116_1158064
  · exact context_10_21117_1158098
  · exact context_10_21118_1158152
  · exact context_10_21119_1158168

theorem unmarked_context_8_1319_1158170 : frontier 13 ⟨1158170, by decide⟩
    (prefixCache 8 1319) (prefixPartial 8 1319) = false := by
  decide +kernel

theorem node_context_8_1319_1158170 : EJMOriginalGlobalDAGData.nodes 13 ⟨1158170, by decide⟩ =
    .split (coordinate 8) (![⟨1156296, by decide⟩,⟨1157459, by decide⟩,⟨1157989, by decide⟩,⟨1158169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1319_1158170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1319 ⟨1158170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1319
    ⟨1158170, by decide⟩ (by decide) (![⟨1156296, by decide⟩,⟨1157459, by decide⟩,⟨1157989, by decide⟩,⟨1158169, by decide⟩]) unmarked_context_8_1319_1158170 node_context_8_1319_1158170
  intro a
  fin_cases a
  · exact context_9_5276_1156296
  · exact context_9_5277_1157459
  · exact context_9_5278_1157989
  · exact context_9_5279_1158169

theorem unmarked_context_7_329_1158171 : frontier 14 ⟨1158171, by decide⟩
    (prefixCache 7 329) (prefixPartial 7 329) = false := by
  decide +kernel

theorem node_context_7_329_1158171 : EJMOriginalGlobalDAGData.nodes 14 ⟨1158171, by decide⟩ =
    .split (coordinate 7) (![⟨1148565, by decide⟩,⟨1151539, by decide⟩,⟨1154749, by decide⟩,⟨1158170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_329_1158171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 329 ⟨1158171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 329
    ⟨1158171, by decide⟩ (by decide) (![⟨1148565, by decide⟩,⟨1151539, by decide⟩,⟨1154749, by decide⟩,⟨1158170, by decide⟩]) unmarked_context_7_329_1158171 node_context_7_329_1158171
  intro a
  fin_cases a
  · exact context_8_1316_1148565
  · exact context_8_1317_1151539
  · exact context_8_1318_1154749
  · exact context_8_1319_1158170

theorem selected_cut_42378 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84480) = some ⟨11, 1, 0, 434745, 84480, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84480_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84480 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84480 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84480, 1, 262144⟩
    (by decide) selected_cut_42378

theorem selected_cut_42379 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337924) = some ⟨12, 1, 0, 448748, 337924, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337924_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337924 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337924 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337924, 1, 65536⟩
    (by decide) selected_cut_42379

theorem selected_cut_42380 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 337925) = some ⟨12, 1, 0, 34034, 337925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337925_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337925 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 337925 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 337925, 1, 65536⟩
    (by decide) selected_cut_42380

theorem selected_cut_42381 : selected 9 ⟨1158217, by decide⟩
    (prefixPartial 12 337926) = some ⟨12, 2, 0, 1158217, 337926, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_337926_1158217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337926 ⟨1158217, by decide⟩ :=
  accepted_of_selected 12 337926 ⟨1158217, by decide⟩ ⟨12, 2, 0, 1158217, 337926, 2829, 65536⟩
    (by decide) selected_cut_42381

theorem selected_cut_42382 : selected 9 ⟨1158263, by decide⟩
    (prefixPartial 12 337927) = some ⟨12, 2, 0, 1158263, 337927, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_337927_1158263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337927 ⟨1158263, by decide⟩ :=
  accepted_of_selected 12 337927 ⟨1158263, by decide⟩ ⟨12, 2, 0, 1158263, 337927, 2917, 65536⟩
    (by decide) selected_cut_42382

theorem unmarked_context_11_84481_1158264 : frontier 10 ⟨1158264, by decide⟩
    (prefixCache 11 84481) (prefixPartial 11 84481) = false := by
  decide +kernel

theorem node_context_11_84481_1158264 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158264, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1158217, by decide⟩,⟨1158263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84481_1158264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84481 ⟨1158264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84481
    ⟨1158264, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1158217, by decide⟩,⟨1158263, by decide⟩]) unmarked_context_11_84481_1158264 node_context_11_84481_1158264
  intro a
  fin_cases a
  · exact context_12_337924_448748
  · exact context_12_337925_34034
  · exact context_12_337926_1158217
  · exact context_12_337927_1158263

theorem selected_cut_42383 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337928) = some ⟨12, 1, 0, 448748, 337928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337928_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337928 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337928 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337928, 1, 65536⟩
    (by decide) selected_cut_42383

theorem selected_cut_42384 : selected 9 ⟨1158313, by decide⟩
    (prefixPartial 12 337929) = some ⟨12, 2, 0, 1158313, 337929, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_337929_1158313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337929 ⟨1158313, by decide⟩ :=
  accepted_of_selected 12 337929 ⟨1158313, by decide⟩ ⟨12, 2, 0, 1158313, 337929, 2909, 65536⟩
    (by decide) selected_cut_42384

theorem selected_cut_42385 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 337930) = some ⟨12, 1, 0, 188189, 337930, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337930_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337930 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 337930 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 337930, 1, 65536⟩
    (by decide) selected_cut_42385

theorem selected_cut_42386 : selected 9 ⟨1158351, by decide⟩
    (prefixPartial 12 337931) = some ⟨12, 2, 0, 1158351, 337931, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_337931_1158351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337931 ⟨1158351, by decide⟩ :=
  accepted_of_selected 12 337931 ⟨1158351, by decide⟩ ⟨12, 2, 0, 1158351, 337931, 2697, 65536⟩
    (by decide) selected_cut_42386

theorem unmarked_context_11_84482_1158352 : frontier 10 ⟨1158352, by decide⟩
    (prefixCache 11 84482) (prefixPartial 11 84482) = false := by
  decide +kernel

theorem node_context_11_84482_1158352 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158352, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1158313, by decide⟩,⟨188189, by decide⟩,⟨1158351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84482_1158352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84482 ⟨1158352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84482
    ⟨1158352, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1158313, by decide⟩,⟨188189, by decide⟩,⟨1158351, by decide⟩]) unmarked_context_11_84482_1158352 node_context_11_84482_1158352
  intro a
  fin_cases a
  · exact context_12_337928_448748
  · exact context_12_337929_1158313
  · exact context_12_337930_188189
  · exact context_12_337931_1158351

theorem selected_cut_42387 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337932) = some ⟨12, 1, 0, 448748, 337932, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337932_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337932 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337932 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337932, 1, 65536⟩
    (by decide) selected_cut_42387

theorem selected_cut_42388 : selected 9 ⟨1158395, by decide⟩
    (prefixPartial 12 337933) = some ⟨12, 2, 0, 1158395, 337933, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_337933_1158395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337933 ⟨1158395, by decide⟩ :=
  accepted_of_selected 12 337933 ⟨1158395, by decide⟩ ⟨12, 2, 0, 1158395, 337933, 3001, 65536⟩
    (by decide) selected_cut_42388

theorem selected_cut_42389 : selected 9 ⟨1158437, by decide⟩
    (prefixPartial 12 337934) = some ⟨12, 2, 0, 1158437, 337934, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_337934_1158437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337934 ⟨1158437, by decide⟩ :=
  accepted_of_selected 12 337934 ⟨1158437, by decide⟩ ⟨12, 2, 0, 1158437, 337934, 2821, 65536⟩
    (by decide) selected_cut_42389

theorem selected_cut_42390 : selected 9 ⟨1158469, by decide⟩
    (prefixPartial 12 337935) = some ⟨12, 2, 0, 1158469, 337935, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_337935_1158469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337935 ⟨1158469, by decide⟩ :=
  accepted_of_selected 12 337935 ⟨1158469, by decide⟩ ⟨12, 2, 0, 1158469, 337935, 2657, 65536⟩
    (by decide) selected_cut_42390

theorem unmarked_context_11_84483_1158470 : frontier 10 ⟨1158470, by decide⟩
    (prefixCache 11 84483) (prefixPartial 11 84483) = false := by
  decide +kernel

theorem node_context_11_84483_1158470 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158470, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1158395, by decide⟩,⟨1158437, by decide⟩,⟨1158469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84483_1158470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84483 ⟨1158470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84483
    ⟨1158470, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1158395, by decide⟩,⟨1158437, by decide⟩,⟨1158469, by decide⟩]) unmarked_context_11_84483_1158470 node_context_11_84483_1158470
  intro a
  fin_cases a
  · exact context_12_337932_448748
  · exact context_12_337933_1158395
  · exact context_12_337934_1158437
  · exact context_12_337935_1158469

theorem unmarked_context_10_21120_1158471 : frontier 11 ⟨1158471, by decide⟩
    (prefixCache 10 21120) (prefixPartial 10 21120) = false := by
  decide +kernel

theorem node_context_10_21120_1158471 : EJMOriginalGlobalDAGData.nodes 11 ⟨1158471, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1158264, by decide⟩,⟨1158352, by decide⟩,⟨1158470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21120_1158471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21120 ⟨1158471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21120
    ⟨1158471, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1158264, by decide⟩,⟨1158352, by decide⟩,⟨1158470, by decide⟩]) unmarked_context_10_21120_1158471 node_context_10_21120_1158471
  intro a
  fin_cases a
  · exact context_11_84480_434745
  · exact context_11_84481_1158264
  · exact context_11_84482_1158352
  · exact context_11_84483_1158470

theorem selected_cut_42391 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337936) = some ⟨12, 1, 0, 1108174, 337936, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337936_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337936 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337936 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337936, 1, 65536⟩
    (by decide) selected_cut_42391

theorem selected_cut_42392 : selected 9 ⟨1158518, by decide⟩
    (prefixPartial 12 337937) = some ⟨12, 2, 0, 1158518, 337937, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_337937_1158518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337937 ⟨1158518, by decide⟩ :=
  accepted_of_selected 12 337937 ⟨1158518, by decide⟩ ⟨12, 2, 0, 1158518, 337937, 2889, 65536⟩
    (by decide) selected_cut_42392

theorem selected_cut_42393 : selected 9 ⟨1158567, by decide⟩
    (prefixPartial 12 337938) = some ⟨12, 2, 0, 1158567, 337938, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_337938_1158567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337938 ⟨1158567, by decide⟩ :=
  accepted_of_selected 12 337938 ⟨1158567, by decide⟩ ⟨12, 2, 0, 1158567, 337938, 2885, 65536⟩
    (by decide) selected_cut_42393

theorem selected_cut_42394 : selected 9 ⟨1158611, by decide⟩
    (prefixPartial 12 337939) = some ⟨12, 2, 0, 1158611, 337939, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_337939_1158611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337939 ⟨1158611, by decide⟩ :=
  accepted_of_selected 12 337939 ⟨1158611, by decide⟩ ⟨12, 2, 0, 1158611, 337939, 2797, 65536⟩
    (by decide) selected_cut_42394

theorem unmarked_context_11_84484_1158612 : frontier 10 ⟨1158612, by decide⟩
    (prefixCache 11 84484) (prefixPartial 11 84484) = false := by
  decide +kernel

theorem node_context_11_84484_1158612 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158612, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1158518, by decide⟩,⟨1158567, by decide⟩,⟨1158611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84484_1158612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84484 ⟨1158612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84484
    ⟨1158612, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1158518, by decide⟩,⟨1158567, by decide⟩,⟨1158611, by decide⟩]) unmarked_context_11_84484_1158612 node_context_11_84484_1158612
  intro a
  fin_cases a
  · exact context_12_337936_1108174
  · exact context_12_337937_1158518
  · exact context_12_337938_1158567
  · exact context_12_337939_1158611

theorem selected_cut_42395 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337940) = some ⟨12, 1, 0, 1108174, 337940, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337940_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337940 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337940 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337940, 1, 65536⟩
    (by decide) selected_cut_42395

theorem selected_cut_42396 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 337941) = some ⟨12, 1, 0, 1118965, 337941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337941_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337941 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 337941 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 337941, 1, 65536⟩
    (by decide) selected_cut_42396

theorem selected_cut_42397 : selected 9 ⟨1158660, by decide⟩
    (prefixPartial 12 337942) = some ⟨12, 2, 0, 1158660, 337942, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_337942_1158660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337942 ⟨1158660, by decide⟩ :=
  accepted_of_selected 12 337942 ⟨1158660, by decide⟩ ⟨12, 2, 0, 1158660, 337942, 3133, 65536⟩
    (by decide) selected_cut_42397

theorem selected_cut_42398 : selected 9 ⟨1158713, by decide⟩
    (prefixPartial 12 337943) = some ⟨12, 2, 0, 1158713, 337943, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_337943_1158713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337943 ⟨1158713, by decide⟩ :=
  accepted_of_selected 12 337943 ⟨1158713, by decide⟩ ⟨12, 2, 0, 1158713, 337943, 3137, 65536⟩
    (by decide) selected_cut_42398

theorem unmarked_context_11_84485_1158714 : frontier 10 ⟨1158714, by decide⟩
    (prefixCache 11 84485) (prefixPartial 11 84485) = false := by
  decide +kernel

theorem node_context_11_84485_1158714 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158714, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1158660, by decide⟩,⟨1158713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84485_1158714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84485 ⟨1158714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84485
    ⟨1158714, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1158660, by decide⟩,⟨1158713, by decide⟩]) unmarked_context_11_84485_1158714 node_context_11_84485_1158714
  intro a
  fin_cases a
  · exact context_12_337940_1108174
  · exact context_12_337941_1118965
  · exact context_12_337942_1158660
  · exact context_12_337943_1158713

theorem selected_cut_42399 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337944) = some ⟨12, 1, 0, 1108174, 337944, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337944_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337944 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337944 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337944, 1, 65536⟩
    (by decide) selected_cut_42399

theorem selected_cut_42400 : selected 9 ⟨1158763, by decide⟩
    (prefixPartial 12 337945) = some ⟨12, 2, 0, 1158763, 337945, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_337945_1158763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337945 ⟨1158763, by decide⟩ :=
  accepted_of_selected 12 337945 ⟨1158763, by decide⟩ ⟨12, 2, 0, 1158763, 337945, 2817, 65536⟩
    (by decide) selected_cut_42400

theorem selected_cut_42401 : selected 9 ⟨1158796, by decide⟩
    (prefixPartial 12 337946) = some ⟨12, 2, 0, 1158796, 337946, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_337946_1158796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337946 ⟨1158796, by decide⟩ :=
  accepted_of_selected 12 337946 ⟨1158796, by decide⟩ ⟨12, 2, 0, 1158796, 337946, 2605, 65536⟩
    (by decide) selected_cut_42401

theorem selected_cut_42402 : selected 9 ⟨1158833, by decide⟩
    (prefixPartial 12 337947) = some ⟨12, 2, 0, 1158833, 337947, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_337947_1158833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337947 ⟨1158833, by decide⟩ :=
  accepted_of_selected 12 337947 ⟨1158833, by decide⟩ ⟨12, 2, 0, 1158833, 337947, 2677, 65536⟩
    (by decide) selected_cut_42402

theorem unmarked_context_11_84486_1158834 : frontier 10 ⟨1158834, by decide⟩
    (prefixCache 11 84486) (prefixPartial 11 84486) = false := by
  decide +kernel

theorem node_context_11_84486_1158834 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158834, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1158763, by decide⟩,⟨1158796, by decide⟩,⟨1158833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84486_1158834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84486 ⟨1158834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84486
    ⟨1158834, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1158763, by decide⟩,⟨1158796, by decide⟩,⟨1158833, by decide⟩]) unmarked_context_11_84486_1158834 node_context_11_84486_1158834
  intro a
  fin_cases a
  · exact context_12_337944_1108174
  · exact context_12_337945_1158763
  · exact context_12_337946_1158796
  · exact context_12_337947_1158833

theorem selected_cut_42403 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337948) = some ⟨12, 1, 0, 1108174, 337948, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337948_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337948 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337948 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337948, 1, 65536⟩
    (by decide) selected_cut_42403

theorem selected_cut_42404 : selected 9 ⟨1158877, by decide⟩
    (prefixPartial 12 337949) = some ⟨12, 2, 0, 1158877, 337949, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_337949_1158877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337949 ⟨1158877, by decide⟩ :=
  accepted_of_selected 12 337949 ⟨1158877, by decide⟩ ⟨12, 2, 0, 1158877, 337949, 2869, 65536⟩
    (by decide) selected_cut_42404

theorem selected_cut_42405 : selected 9 ⟨1158920, by decide⟩
    (prefixPartial 12 337950) = some ⟨12, 2, 0, 1158920, 337950, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_337950_1158920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337950 ⟨1158920, by decide⟩ :=
  accepted_of_selected 12 337950 ⟨1158920, by decide⟩ ⟨12, 2, 0, 1158920, 337950, 2837, 65536⟩
    (by decide) selected_cut_42405

theorem selected_cut_42406 : selected 9 ⟨1158952, by decide⟩
    (prefixPartial 12 337951) = some ⟨12, 2, 0, 1158952, 337951, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_337951_1158952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337951 ⟨1158952, by decide⟩ :=
  accepted_of_selected 12 337951 ⟨1158952, by decide⟩ ⟨12, 2, 0, 1158952, 337951, 2693, 65536⟩
    (by decide) selected_cut_42406

theorem unmarked_context_11_84487_1158953 : frontier 10 ⟨1158953, by decide⟩
    (prefixCache 11 84487) (prefixPartial 11 84487) = false := by
  decide +kernel

theorem node_context_11_84487_1158953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1158953, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1158877, by decide⟩,⟨1158920, by decide⟩,⟨1158952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84487_1158953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84487 ⟨1158953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84487
    ⟨1158953, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1158877, by decide⟩,⟨1158920, by decide⟩,⟨1158952, by decide⟩]) unmarked_context_11_84487_1158953 node_context_11_84487_1158953
  intro a
  fin_cases a
  · exact context_12_337948_1108174
  · exact context_12_337949_1158877
  · exact context_12_337950_1158920
  · exact context_12_337951_1158952

theorem unmarked_context_10_21121_1158954 : frontier 11 ⟨1158954, by decide⟩
    (prefixCache 10 21121) (prefixPartial 10 21121) = false := by
  decide +kernel

theorem node_context_10_21121_1158954 : EJMOriginalGlobalDAGData.nodes 11 ⟨1158954, by decide⟩ =
    .split (coordinate 10) (![⟨1158612, by decide⟩,⟨1158714, by decide⟩,⟨1158834, by decide⟩,⟨1158953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21121_1158954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21121 ⟨1158954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21121
    ⟨1158954, by decide⟩ (by decide) (![⟨1158612, by decide⟩,⟨1158714, by decide⟩,⟨1158834, by decide⟩,⟨1158953, by decide⟩]) unmarked_context_10_21121_1158954 node_context_10_21121_1158954
  intro a
  fin_cases a
  · exact context_11_84484_1158612
  · exact context_11_84485_1158714
  · exact context_11_84486_1158834
  · exact context_11_84487_1158953

theorem selected_cut_42407 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337952) = some ⟨12, 1, 0, 1108174, 337952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337952_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337952 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337952 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337952, 1, 65536⟩
    (by decide) selected_cut_42407

theorem selected_cut_42408 : selected 9 ⟨1158994, by decide⟩
    (prefixPartial 12 337953) = some ⟨12, 2, 0, 1158994, 337953, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_337953_1158994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337953 ⟨1158994, by decide⟩ :=
  accepted_of_selected 12 337953 ⟨1158994, by decide⟩ ⟨12, 2, 0, 1158994, 337953, 2541, 65536⟩
    (by decide) selected_cut_42408

theorem selected_cut_42409 : selected 9 ⟨1159033, by decide⟩
    (prefixPartial 12 337954) = some ⟨12, 2, 0, 1159033, 337954, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_337954_1159033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337954 ⟨1159033, by decide⟩ :=
  accepted_of_selected 12 337954 ⟨1159033, by decide⟩ ⟨12, 2, 0, 1159033, 337954, 2457, 65536⟩
    (by decide) selected_cut_42409

theorem selected_cut_42410 : selected 9 ⟨1159077, by decide⟩
    (prefixPartial 12 337955) = some ⟨12, 2, 0, 1159077, 337955, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_337955_1159077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337955 ⟨1159077, by decide⟩ :=
  accepted_of_selected 12 337955 ⟨1159077, by decide⟩ ⟨12, 2, 0, 1159077, 337955, 2425, 65536⟩
    (by decide) selected_cut_42410

theorem unmarked_context_11_84488_1159078 : frontier 10 ⟨1159078, by decide⟩
    (prefixCache 11 84488) (prefixPartial 11 84488) = false := by
  decide +kernel

theorem node_context_11_84488_1159078 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159078, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1158994, by decide⟩,⟨1159033, by decide⟩,⟨1159077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84488_1159078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84488 ⟨1159078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84488
    ⟨1159078, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1158994, by decide⟩,⟨1159033, by decide⟩,⟨1159077, by decide⟩]) unmarked_context_11_84488_1159078 node_context_11_84488_1159078
  intro a
  fin_cases a
  · exact context_12_337952_1108174
  · exact context_12_337953_1158994
  · exact context_12_337954_1159033
  · exact context_12_337955_1159077

theorem selected_cut_42411 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337956) = some ⟨12, 1, 0, 1108174, 337956, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337956_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337956 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337956 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337956, 1, 65536⟩
    (by decide) selected_cut_42411

theorem selected_cut_42412 : selected 9 ⟨1159129, by decide⟩
    (prefixPartial 12 337957) = some ⟨12, 2, 0, 1159129, 337957, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_337957_1159129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337957 ⟨1159129, by decide⟩ :=
  accepted_of_selected 12 337957 ⟨1159129, by decide⟩ ⟨12, 2, 0, 1159129, 337957, 2817, 65536⟩
    (by decide) selected_cut_42412

theorem selected_cut_42413 : selected 9 ⟨1159178, by decide⟩
    (prefixPartial 12 337958) = some ⟨12, 2, 0, 1159178, 337958, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_337958_1159178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337958 ⟨1159178, by decide⟩ :=
  accepted_of_selected 12 337958 ⟨1159178, by decide⟩ ⟨12, 2, 0, 1159178, 337958, 2889, 65536⟩
    (by decide) selected_cut_42413

theorem selected_cut_42414 : selected 9 ⟨1159234, by decide⟩
    (prefixPartial 12 337959) = some ⟨12, 2, 0, 1159234, 337959, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_337959_1159234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337959 ⟨1159234, by decide⟩ :=
  accepted_of_selected 12 337959 ⟨1159234, by decide⟩ ⟨12, 2, 0, 1159234, 337959, 2917, 65536⟩
    (by decide) selected_cut_42414

theorem unmarked_context_11_84489_1159235 : frontier 10 ⟨1159235, by decide⟩
    (prefixCache 11 84489) (prefixPartial 11 84489) = false := by
  decide +kernel

theorem node_context_11_84489_1159235 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159235, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1159129, by decide⟩,⟨1159178, by decide⟩,⟨1159234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84489_1159235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84489 ⟨1159235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84489
    ⟨1159235, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1159129, by decide⟩,⟨1159178, by decide⟩,⟨1159234, by decide⟩]) unmarked_context_11_84489_1159235 node_context_11_84489_1159235
  intro a
  fin_cases a
  · exact context_12_337956_1108174
  · exact context_12_337957_1159129
  · exact context_12_337958_1159178
  · exact context_12_337959_1159234

theorem selected_cut_42415 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 84490) = some ⟨11, 1, 0, 900587, 84490, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84490_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84490 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 84490 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 84490, 1, 262144⟩
    (by decide) selected_cut_42415

theorem selected_cut_42416 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337964) = some ⟨12, 1, 0, 1108174, 337964, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337964_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337964 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337964 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337964, 1, 65536⟩
    (by decide) selected_cut_42416

theorem selected_cut_42417 : selected 9 ⟨1159279, by decide⟩
    (prefixPartial 12 337965) = some ⟨12, 2, 0, 1159279, 337965, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_337965_1159279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337965 ⟨1159279, by decide⟩ :=
  accepted_of_selected 12 337965 ⟨1159279, by decide⟩ ⟨12, 2, 0, 1159279, 337965, 2673, 65536⟩
    (by decide) selected_cut_42417

theorem selected_cut_42418 : selected 9 ⟨1159323, by decide⟩
    (prefixPartial 12 337966) = some ⟨12, 2, 0, 1159323, 337966, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_337966_1159323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337966 ⟨1159323, by decide⟩ :=
  accepted_of_selected 12 337966 ⟨1159323, by decide⟩ ⟨12, 2, 0, 1159323, 337966, 2613, 65536⟩
    (by decide) selected_cut_42418

theorem selected_cut_42419 : selected 9 ⟨1159368, by decide⟩
    (prefixPartial 12 337967) = some ⟨12, 2, 0, 1159368, 337967, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_337967_1159368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337967 ⟨1159368, by decide⟩ :=
  accepted_of_selected 12 337967 ⟨1159368, by decide⟩ ⟨12, 2, 0, 1159368, 337967, 2517, 65536⟩
    (by decide) selected_cut_42419

theorem unmarked_context_11_84491_1159369 : frontier 10 ⟨1159369, by decide⟩
    (prefixCache 11 84491) (prefixPartial 11 84491) = false := by
  decide +kernel

theorem node_context_11_84491_1159369 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159369, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1159279, by decide⟩,⟨1159323, by decide⟩,⟨1159368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84491_1159369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84491 ⟨1159369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84491
    ⟨1159369, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1159279, by decide⟩,⟨1159323, by decide⟩,⟨1159368, by decide⟩]) unmarked_context_11_84491_1159369 node_context_11_84491_1159369
  intro a
  fin_cases a
  · exact context_12_337964_1108174
  · exact context_12_337965_1159279
  · exact context_12_337966_1159323
  · exact context_12_337967_1159368

theorem unmarked_context_10_21122_1159370 : frontier 11 ⟨1159370, by decide⟩
    (prefixCache 10 21122) (prefixPartial 10 21122) = false := by
  decide +kernel

theorem node_context_10_21122_1159370 : EJMOriginalGlobalDAGData.nodes 11 ⟨1159370, by decide⟩ =
    .split (coordinate 10) (![⟨1159078, by decide⟩,⟨1159235, by decide⟩,⟨900587, by decide⟩,⟨1159369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21122_1159370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21122 ⟨1159370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21122
    ⟨1159370, by decide⟩ (by decide) (![⟨1159078, by decide⟩,⟨1159235, by decide⟩,⟨900587, by decide⟩,⟨1159369, by decide⟩]) unmarked_context_10_21122_1159370 node_context_10_21122_1159370
  intro a
  fin_cases a
  · exact context_11_84488_1159078
  · exact context_11_84489_1159235
  · exact context_11_84490_900587
  · exact context_11_84491_1159369

theorem selected_cut_42420 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337968) = some ⟨12, 1, 0, 1108174, 337968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337968_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337968 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337968 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337968, 1, 65536⟩
    (by decide) selected_cut_42420

theorem selected_cut_42421 : selected 9 ⟨1159404, by decide⟩
    (prefixPartial 12 337969) = some ⟨12, 2, 0, 1159404, 337969, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_337969_1159404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337969 ⟨1159404, by decide⟩ :=
  accepted_of_selected 12 337969 ⟨1159404, by decide⟩ ⟨12, 2, 0, 1159404, 337969, 2549, 65536⟩
    (by decide) selected_cut_42421

theorem selected_cut_42422 : selected 9 ⟨1159448, by decide⟩
    (prefixPartial 12 337970) = some ⟨12, 2, 0, 1159448, 337970, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_337970_1159448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337970 ⟨1159448, by decide⟩ :=
  accepted_of_selected 12 337970 ⟨1159448, by decide⟩ ⟨12, 2, 0, 1159448, 337970, 2613, 65536⟩
    (by decide) selected_cut_42422

theorem selected_cut_42423 : selected 9 ⟨1159496, by decide⟩
    (prefixPartial 12 337971) = some ⟨12, 2, 0, 1159496, 337971, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_337971_1159496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337971 ⟨1159496, by decide⟩ :=
  accepted_of_selected 12 337971 ⟨1159496, by decide⟩ ⟨12, 2, 0, 1159496, 337971, 2745, 65536⟩
    (by decide) selected_cut_42423

theorem unmarked_context_11_84492_1159497 : frontier 10 ⟨1159497, by decide⟩
    (prefixCache 11 84492) (prefixPartial 11 84492) = false := by
  decide +kernel

theorem node_context_11_84492_1159497 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159497, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1159404, by decide⟩,⟨1159448, by decide⟩,⟨1159496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84492_1159497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84492 ⟨1159497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84492
    ⟨1159497, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1159404, by decide⟩,⟨1159448, by decide⟩,⟨1159496, by decide⟩]) unmarked_context_11_84492_1159497 node_context_11_84492_1159497
  intro a
  fin_cases a
  · exact context_12_337968_1108174
  · exact context_12_337969_1159404
  · exact context_12_337970_1159448
  · exact context_12_337971_1159496

theorem selected_cut_42424 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337972) = some ⟨12, 1, 0, 1108174, 337972, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337972_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337972 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337972 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337972, 1, 65536⟩
    (by decide) selected_cut_42424

theorem selected_cut_42425 : selected 9 ⟨1159533, by decide⟩
    (prefixPartial 12 337973) = some ⟨12, 2, 0, 1159533, 337973, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_337973_1159533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337973 ⟨1159533, by decide⟩ :=
  accepted_of_selected 12 337973 ⟨1159533, by decide⟩ ⟨12, 2, 0, 1159533, 337973, 2597, 65536⟩
    (by decide) selected_cut_42425

theorem selected_cut_42426 : selected 9 ⟨1159584, by decide⟩
    (prefixPartial 12 337974) = some ⟨12, 2, 0, 1159584, 337974, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_337974_1159584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337974 ⟨1159584, by decide⟩ :=
  accepted_of_selected 12 337974 ⟨1159584, by decide⟩ ⟨12, 2, 0, 1159584, 337974, 2877, 65536⟩
    (by decide) selected_cut_42426

theorem selected_cut_42427 : selected 9 ⟨1159638, by decide⟩
    (prefixPartial 12 337975) = some ⟨12, 2, 0, 1159638, 337975, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_337975_1159638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337975 ⟨1159638, by decide⟩ :=
  accepted_of_selected 12 337975 ⟨1159638, by decide⟩ ⟨12, 2, 0, 1159638, 337975, 3085, 65536⟩
    (by decide) selected_cut_42427

theorem unmarked_context_11_84493_1159639 : frontier 10 ⟨1159639, by decide⟩
    (prefixCache 11 84493) (prefixPartial 11 84493) = false := by
  decide +kernel

theorem node_context_11_84493_1159639 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159639, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1159533, by decide⟩,⟨1159584, by decide⟩,⟨1159638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84493_1159639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84493 ⟨1159639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84493
    ⟨1159639, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1159533, by decide⟩,⟨1159584, by decide⟩,⟨1159638, by decide⟩]) unmarked_context_11_84493_1159639 node_context_11_84493_1159639
  intro a
  fin_cases a
  · exact context_12_337972_1108174
  · exact context_12_337973_1159533
  · exact context_12_337974_1159584
  · exact context_12_337975_1159638

theorem selected_cut_42428 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337976) = some ⟨12, 1, 0, 1108174, 337976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337976_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337976 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337976 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337976, 1, 65536⟩
    (by decide) selected_cut_42428

theorem selected_cut_42429 : selected 9 ⟨1159669, by decide⟩
    (prefixPartial 12 337977) = some ⟨12, 2, 0, 1159669, 337977, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_337977_1159669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337977 ⟨1159669, by decide⟩ :=
  accepted_of_selected 12 337977 ⟨1159669, by decide⟩ ⟨12, 2, 0, 1159669, 337977, 2309, 65536⟩
    (by decide) selected_cut_42429

theorem selected_cut_42430 : selected 9 ⟨1159702, by decide⟩
    (prefixPartial 12 337978) = some ⟨12, 2, 0, 1159702, 337978, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_337978_1159702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337978 ⟨1159702, by decide⟩ :=
  accepted_of_selected 12 337978 ⟨1159702, by decide⟩ ⟨12, 2, 0, 1159702, 337978, 2321, 65536⟩
    (by decide) selected_cut_42430

theorem selected_cut_42431 : selected 9 ⟨1159749, by decide⟩
    (prefixPartial 12 337979) = some ⟨12, 2, 0, 1159749, 337979, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_337979_1159749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337979 ⟨1159749, by decide⟩ :=
  accepted_of_selected 12 337979 ⟨1159749, by decide⟩ ⟨12, 2, 0, 1159749, 337979, 2553, 65536⟩
    (by decide) selected_cut_42431

theorem unmarked_context_11_84494_1159750 : frontier 10 ⟨1159750, by decide⟩
    (prefixCache 11 84494) (prefixPartial 11 84494) = false := by
  decide +kernel

theorem node_context_11_84494_1159750 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159750, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1159669, by decide⟩,⟨1159702, by decide⟩,⟨1159749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84494_1159750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84494 ⟨1159750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84494
    ⟨1159750, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1159669, by decide⟩,⟨1159702, by decide⟩,⟨1159749, by decide⟩]) unmarked_context_11_84494_1159750 node_context_11_84494_1159750
  intro a
  fin_cases a
  · exact context_12_337976_1108174
  · exact context_12_337977_1159669
  · exact context_12_337978_1159702
  · exact context_12_337979_1159749

theorem selected_cut_42432 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337980) = some ⟨12, 1, 0, 1108174, 337980, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337980_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337980 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337980 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337980, 1, 65536⟩
    (by decide) selected_cut_42432

theorem selected_cut_42433 : selected 9 ⟨1159781, by decide⟩
    (prefixPartial 12 337981) = some ⟨12, 2, 0, 1159781, 337981, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_337981_1159781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337981 ⟨1159781, by decide⟩ :=
  accepted_of_selected 12 337981 ⟨1159781, by decide⟩ ⟨12, 2, 0, 1159781, 337981, 2309, 65536⟩
    (by decide) selected_cut_42433

theorem selected_cut_42434 : selected 9 ⟨1159813, by decide⟩
    (prefixPartial 12 337982) = some ⟨12, 2, 0, 1159813, 337982, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_337982_1159813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337982 ⟨1159813, by decide⟩ :=
  accepted_of_selected 12 337982 ⟨1159813, by decide⟩ ⟨12, 2, 0, 1159813, 337982, 2381, 65536⟩
    (by decide) selected_cut_42434

theorem selected_cut_42435 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 337983) = some ⟨12, 1, 0, 1120582, 337983, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337983_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337983 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 337983 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 337983, 1, 65536⟩
    (by decide) selected_cut_42435

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
