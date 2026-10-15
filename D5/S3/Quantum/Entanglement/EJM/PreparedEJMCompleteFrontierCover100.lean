/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover099
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_7_22_265057 : frontier 14 ⟨265057, by decide⟩
    (prefixCache 7 22) (prefixPartial 7 22) = false := by
  decide +kernel

theorem node_context_7_22_265057 : EJMOriginalGlobalDAGData.nodes 14 ⟨265057, by decide⟩ =
    .split (coordinate 7) (![⟨225090, by decide⟩,⟨235681, by decide⟩,⟨249816, by decide⟩,⟨265056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_22_265057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 22 ⟨265057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 22
    ⟨265057, by decide⟩ (by decide) (![⟨225090, by decide⟩,⟨235681, by decide⟩,⟨249816, by decide⟩,⟨265056, by decide⟩]) unmarked_context_7_22_265057 node_context_7_22_265057
  intro a
  fin_cases a
  · exact context_8_88_225090
  · exact context_8_89_235681
  · exact context_8_90_249816
  · exact context_8_91_265056

theorem selected_cut_09602 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 23) = some ⟨7, 1, 0, 34032, 23, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_23_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 23 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 23 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 23, 1, 67108864⟩
    (by decide) selected_cut_09602

theorem unmarked_context_6_5_265058 : frontier 15 ⟨265058, by decide⟩
    (prefixCache 6 5) (prefixPartial 6 5) = false := by
  decide +kernel

theorem node_context_6_5_265058 : EJMOriginalGlobalDAGData.nodes 15 ⟨265058, by decide⟩ =
    .split (coordinate 6) (![⟨188835, by decide⟩,⟨212791, by decide⟩,⟨265057, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_5_265058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 5 ⟨265058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 5
    ⟨265058, by decide⟩ (by decide) (![⟨188835, by decide⟩,⟨212791, by decide⟩,⟨265057, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_5_265058 node_context_6_5_265058
  intro a
  fin_cases a
  · exact context_7_20_188835
  · exact context_7_21_212791
  · exact context_7_22_265057
  · exact context_7_23_34032

theorem selected_cut_09603 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 6144) = some ⟨11, 1, 0, 167448, 6144, 1, 262144⟩ := by
  decide +kernel

theorem context_11_6144_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6144 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 6144 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 6144, 1, 262144⟩
    (by decide) selected_cut_09603

theorem selected_cut_09604 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 24580) = some ⟨12, 1, 0, 34034, 24580, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24580_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24580 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 24580 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 24580, 1, 65536⟩
    (by decide) selected_cut_09604

theorem selected_cut_09605 : selected 8 ⟨265098, by decide⟩
    (prefixPartial 13 98324) = some ⟨13, 2, 0, 265098, 98324, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_98324_265098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98324 ⟨265098, by decide⟩ :=
  accepted_of_selected 13 98324 ⟨265098, by decide⟩ ⟨13, 2, 0, 265098, 98324, 1945, 16384⟩
    (by decide) selected_cut_09605

theorem selected_cut_09606 : selected 8 ⟨265128, by decide⟩
    (prefixPartial 13 98325) = some ⟨13, 2, 0, 265128, 98325, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_98325_265128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98325 ⟨265128, by decide⟩ :=
  accepted_of_selected 13 98325 ⟨265128, by decide⟩ ⟨13, 2, 0, 265128, 98325, 2577, 16384⟩
    (by decide) selected_cut_09606

theorem selected_cut_09607 : selected 8 ⟨265146, by decide⟩
    (prefixPartial 13 98326) = some ⟨13, 2, 0, 265146, 98326, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_98326_265146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98326 ⟨265146, by decide⟩ :=
  accepted_of_selected 13 98326 ⟨265146, by decide⟩ ⟨13, 2, 0, 265146, 98326, 1801, 16384⟩
    (by decide) selected_cut_09607

theorem selected_cut_09608 : selected 8 ⟨265153, by decide⟩
    (prefixPartial 13 98327) = some ⟨13, 2, 0, 265153, 98327, 753, 16384⟩ := by
  decide +kernel

theorem context_13_98327_265153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98327 ⟨265153, by decide⟩ :=
  accepted_of_selected 13 98327 ⟨265153, by decide⟩ ⟨13, 2, 0, 265153, 98327, 753, 16384⟩
    (by decide) selected_cut_09608

theorem unmarked_context_12_24581_265154 : frontier 9 ⟨265154, by decide⟩
    (prefixCache 12 24581) (prefixPartial 12 24581) = false := by
  decide +kernel

theorem node_context_12_24581_265154 : EJMOriginalGlobalDAGData.nodes 9 ⟨265154, by decide⟩ =
    .split (coordinate 12) (![⟨265098, by decide⟩,⟨265128, by decide⟩,⟨265146, by decide⟩,⟨265153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24581_265154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24581 ⟨265154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24581
    ⟨265154, by decide⟩ (by decide) (![⟨265098, by decide⟩,⟨265128, by decide⟩,⟨265146, by decide⟩,⟨265153, by decide⟩]) unmarked_context_12_24581_265154 node_context_12_24581_265154
  intro a
  fin_cases a
  · exact context_13_98324_265098
  · exact context_13_98325_265128
  · exact context_13_98326_265146
  · exact context_13_98327_265153

theorem selected_cut_09609 : selected 8 ⟨265187, by decide⟩
    (prefixPartial 13 98328) = some ⟨13, 2, 0, 265187, 98328, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_98328_265187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98328 ⟨265187, by decide⟩ :=
  accepted_of_selected 13 98328 ⟨265187, by decide⟩ ⟨13, 2, 0, 265187, 98328, 1949, 16384⟩
    (by decide) selected_cut_09609

theorem selected_cut_09610 : selected 8 ⟨265214, by decide⟩
    (prefixPartial 13 98329) = some ⟨13, 2, 0, 265214, 98329, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_98329_265214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98329 ⟨265214, by decide⟩ :=
  accepted_of_selected 13 98329 ⟨265214, by decide⟩ ⟨13, 2, 0, 265214, 98329, 2933, 16384⟩
    (by decide) selected_cut_09610

theorem selected_cut_09611 : selected 8 ⟨265234, by decide⟩
    (prefixPartial 13 98330) = some ⟨13, 2, 0, 265234, 98330, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_98330_265234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98330 ⟨265234, by decide⟩ :=
  accepted_of_selected 13 98330 ⟨265234, by decide⟩ ⟨13, 2, 0, 265234, 98330, 1877, 16384⟩
    (by decide) selected_cut_09611

theorem selected_cut_09612 : selected 8 ⟨265243, by decide⟩
    (prefixPartial 13 98331) = some ⟨13, 2, 0, 265243, 98331, 893, 16384⟩ := by
  decide +kernel

theorem context_13_98331_265243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98331 ⟨265243, by decide⟩ :=
  accepted_of_selected 13 98331 ⟨265243, by decide⟩ ⟨13, 2, 0, 265243, 98331, 893, 16384⟩
    (by decide) selected_cut_09612

theorem unmarked_context_12_24582_265244 : frontier 9 ⟨265244, by decide⟩
    (prefixCache 12 24582) (prefixPartial 12 24582) = false := by
  decide +kernel

theorem node_context_12_24582_265244 : EJMOriginalGlobalDAGData.nodes 9 ⟨265244, by decide⟩ =
    .split (coordinate 12) (![⟨265187, by decide⟩,⟨265214, by decide⟩,⟨265234, by decide⟩,⟨265243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24582_265244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24582 ⟨265244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24582
    ⟨265244, by decide⟩ (by decide) (![⟨265187, by decide⟩,⟨265214, by decide⟩,⟨265234, by decide⟩,⟨265243, by decide⟩]) unmarked_context_12_24582_265244 node_context_12_24582_265244
  intro a
  fin_cases a
  · exact context_13_98328_265187
  · exact context_13_98329_265214
  · exact context_13_98330_265234
  · exact context_13_98331_265243

theorem selected_cut_09613 : selected 8 ⟨265283, by decide⟩
    (prefixPartial 13 98332) = some ⟨13, 2, 0, 265283, 98332, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_98332_265283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98332 ⟨265283, by decide⟩ :=
  accepted_of_selected 13 98332 ⟨265283, by decide⟩ ⟨13, 2, 0, 265283, 98332, 2345, 16384⟩
    (by decide) selected_cut_09613

theorem selected_cut_09614 : selected 8 ⟨265310, by decide⟩
    (prefixPartial 13 98333) = some ⟨13, 2, 0, 265310, 98333, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_98333_265310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98333 ⟨265310, by decide⟩ :=
  accepted_of_selected 13 98333 ⟨265310, by decide⟩ ⟨13, 2, 0, 265310, 98333, 3025, 16384⟩
    (by decide) selected_cut_09614

theorem selected_cut_09615 : selected 8 ⟨265332, by decide⟩
    (prefixPartial 13 98334) = some ⟨13, 2, 0, 265332, 98334, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_98334_265332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98334 ⟨265332, by decide⟩ :=
  accepted_of_selected 13 98334 ⟨265332, by decide⟩ ⟨13, 2, 0, 265332, 98334, 1901, 16384⟩
    (by decide) selected_cut_09615

theorem selected_cut_09616 : selected 8 ⟨265343, by decide⟩
    (prefixPartial 13 98335) = some ⟨13, 2, 0, 265343, 98335, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_98335_265343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98335 ⟨265343, by decide⟩ :=
  accepted_of_selected 13 98335 ⟨265343, by decide⟩ ⟨13, 2, 0, 265343, 98335, 1013, 16384⟩
    (by decide) selected_cut_09616

theorem unmarked_context_12_24583_265344 : frontier 9 ⟨265344, by decide⟩
    (prefixCache 12 24583) (prefixPartial 12 24583) = false := by
  decide +kernel

theorem node_context_12_24583_265344 : EJMOriginalGlobalDAGData.nodes 9 ⟨265344, by decide⟩ =
    .split (coordinate 12) (![⟨265283, by decide⟩,⟨265310, by decide⟩,⟨265332, by decide⟩,⟨265343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24583_265344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24583 ⟨265344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24583
    ⟨265344, by decide⟩ (by decide) (![⟨265283, by decide⟩,⟨265310, by decide⟩,⟨265332, by decide⟩,⟨265343, by decide⟩]) unmarked_context_12_24583_265344 node_context_12_24583_265344
  intro a
  fin_cases a
  · exact context_13_98332_265283
  · exact context_13_98333_265310
  · exact context_13_98334_265332
  · exact context_13_98335_265343

theorem unmarked_context_11_6145_265345 : frontier 10 ⟨265345, by decide⟩
    (prefixCache 11 6145) (prefixPartial 11 6145) = false := by
  decide +kernel

theorem node_context_11_6145_265345 : EJMOriginalGlobalDAGData.nodes 10 ⟨265345, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨265154, by decide⟩,⟨265244, by decide⟩,⟨265344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6145_265345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6145 ⟨265345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6145
    ⟨265345, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨265154, by decide⟩,⟨265244, by decide⟩,⟨265344, by decide⟩]) unmarked_context_11_6145_265345 node_context_11_6145_265345
  intro a
  fin_cases a
  · exact context_12_24580_34034
  · exact context_12_24581_265154
  · exact context_12_24582_265244
  · exact context_12_24583_265344

theorem selected_cut_09617 : selected 8 ⟨265383, by decide⟩
    (prefixPartial 13 98336) = some ⟨13, 2, 0, 265383, 98336, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_98336_265383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98336 ⟨265383, by decide⟩ :=
  accepted_of_selected 13 98336 ⟨265383, by decide⟩ ⟨13, 2, 0, 265383, 98336, 1533, 16384⟩
    (by decide) selected_cut_09617

theorem selected_cut_09618 : selected 8 ⟨265413, by decide⟩
    (prefixPartial 13 98337) = some ⟨13, 2, 0, 265413, 98337, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_98337_265413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98337 ⟨265413, by decide⟩ :=
  accepted_of_selected 13 98337 ⟨265413, by decide⟩ ⟨13, 2, 0, 265413, 98337, 2601, 16384⟩
    (by decide) selected_cut_09618

theorem selected_cut_09619 : selected 8 ⟨265433, by decide⟩
    (prefixPartial 13 98338) = some ⟨13, 2, 0, 265433, 98338, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_98338_265433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98338 ⟨265433, by decide⟩ :=
  accepted_of_selected 13 98338 ⟨265433, by decide⟩ ⟨13, 2, 0, 265433, 98338, 1661, 16384⟩
    (by decide) selected_cut_09619

theorem selected_cut_09620 : selected 8 ⟨265439, by decide⟩
    (prefixPartial 13 98339) = some ⟨13, 2, 0, 265439, 98339, 741, 16384⟩ := by
  decide +kernel

theorem context_13_98339_265439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98339 ⟨265439, by decide⟩ :=
  accepted_of_selected 13 98339 ⟨265439, by decide⟩ ⟨13, 2, 0, 265439, 98339, 741, 16384⟩
    (by decide) selected_cut_09620

theorem unmarked_context_12_24584_265440 : frontier 9 ⟨265440, by decide⟩
    (prefixCache 12 24584) (prefixPartial 12 24584) = false := by
  decide +kernel

theorem node_context_12_24584_265440 : EJMOriginalGlobalDAGData.nodes 9 ⟨265440, by decide⟩ =
    .split (coordinate 12) (![⟨265383, by decide⟩,⟨265413, by decide⟩,⟨265433, by decide⟩,⟨265439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24584_265440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24584 ⟨265440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24584
    ⟨265440, by decide⟩ (by decide) (![⟨265383, by decide⟩,⟨265413, by decide⟩,⟨265433, by decide⟩,⟨265439, by decide⟩]) unmarked_context_12_24584_265440 node_context_12_24584_265440
  intro a
  fin_cases a
  · exact context_13_98336_265383
  · exact context_13_98337_265413
  · exact context_13_98338_265433
  · exact context_13_98339_265439

theorem selected_cut_09621 : selected 8 ⟨265478, by decide⟩
    (prefixPartial 13 98340) = some ⟨13, 2, 0, 265478, 98340, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_98340_265478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98340 ⟨265478, by decide⟩ :=
  accepted_of_selected 13 98340 ⟨265478, by decide⟩ ⟨13, 2, 0, 265478, 98340, 1757, 16384⟩
    (by decide) selected_cut_09621

theorem selected_cut_09622 : selected 8 ⟨265516, by decide⟩
    (prefixPartial 13 98341) = some ⟨13, 2, 0, 265516, 98341, 3093, 16384⟩ := by
  decide +kernel

theorem context_13_98341_265516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98341 ⟨265516, by decide⟩ :=
  accepted_of_selected 13 98341 ⟨265516, by decide⟩ ⟨13, 2, 0, 265516, 98341, 3093, 16384⟩
    (by decide) selected_cut_09622

theorem selected_cut_09623 : selected 8 ⟨265534, by decide⟩
    (prefixPartial 13 98342) = some ⟨13, 2, 0, 265534, 98342, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_98342_265534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98342 ⟨265534, by decide⟩ :=
  accepted_of_selected 13 98342 ⟨265534, by decide⟩ ⟨13, 2, 0, 265534, 98342, 1753, 16384⟩
    (by decide) selected_cut_09623

theorem selected_cut_09624 : selected 8 ⟨265544, by decide⟩
    (prefixPartial 13 98343) = some ⟨13, 2, 0, 265544, 98343, 805, 16384⟩ := by
  decide +kernel

theorem context_13_98343_265544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98343 ⟨265544, by decide⟩ :=
  accepted_of_selected 13 98343 ⟨265544, by decide⟩ ⟨13, 2, 0, 265544, 98343, 805, 16384⟩
    (by decide) selected_cut_09624

theorem unmarked_context_12_24585_265545 : frontier 9 ⟨265545, by decide⟩
    (prefixCache 12 24585) (prefixPartial 12 24585) = false := by
  decide +kernel

theorem node_context_12_24585_265545 : EJMOriginalGlobalDAGData.nodes 9 ⟨265545, by decide⟩ =
    .split (coordinate 12) (![⟨265478, by decide⟩,⟨265516, by decide⟩,⟨265534, by decide⟩,⟨265544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24585_265545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24585 ⟨265545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24585
    ⟨265545, by decide⟩ (by decide) (![⟨265478, by decide⟩,⟨265516, by decide⟩,⟨265534, by decide⟩,⟨265544, by decide⟩]) unmarked_context_12_24585_265545 node_context_12_24585_265545
  intro a
  fin_cases a
  · exact context_13_98340_265478
  · exact context_13_98341_265516
  · exact context_13_98342_265534
  · exact context_13_98343_265544

theorem selected_cut_09625 : selected 8 ⟨265578, by decide⟩
    (prefixPartial 13 98344) = some ⟨13, 2, 0, 265578, 98344, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_98344_265578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98344 ⟨265578, by decide⟩ :=
  accepted_of_selected 13 98344 ⟨265578, by decide⟩ ⟨13, 2, 0, 265578, 98344, 1597, 16384⟩
    (by decide) selected_cut_09625

theorem selected_cut_09626 : selected 8 ⟨265615, by decide⟩
    (prefixPartial 13 98345) = some ⟨13, 2, 0, 265615, 98345, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_98345_265615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98345 ⟨265615, by decide⟩ :=
  accepted_of_selected 13 98345 ⟨265615, by decide⟩ ⟨13, 2, 0, 265615, 98345, 3073, 16384⟩
    (by decide) selected_cut_09626

theorem selected_cut_09627 : selected 8 ⟨265636, by decide⟩
    (prefixPartial 13 98346) = some ⟨13, 2, 0, 265636, 98346, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_98346_265636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98346 ⟨265636, by decide⟩ :=
  accepted_of_selected 13 98346 ⟨265636, by decide⟩ ⟨13, 2, 0, 265636, 98346, 1645, 16384⟩
    (by decide) selected_cut_09627

theorem selected_cut_09628 : selected 8 ⟨265646, by decide⟩
    (prefixPartial 13 98347) = some ⟨13, 2, 0, 265646, 98347, 909, 16384⟩ := by
  decide +kernel

theorem context_13_98347_265646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98347 ⟨265646, by decide⟩ :=
  accepted_of_selected 13 98347 ⟨265646, by decide⟩ ⟨13, 2, 0, 265646, 98347, 909, 16384⟩
    (by decide) selected_cut_09628

theorem unmarked_context_12_24586_265647 : frontier 9 ⟨265647, by decide⟩
    (prefixCache 12 24586) (prefixPartial 12 24586) = false := by
  decide +kernel

theorem node_context_12_24586_265647 : EJMOriginalGlobalDAGData.nodes 9 ⟨265647, by decide⟩ =
    .split (coordinate 12) (![⟨265578, by decide⟩,⟨265615, by decide⟩,⟨265636, by decide⟩,⟨265646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24586_265647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24586 ⟨265647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24586
    ⟨265647, by decide⟩ (by decide) (![⟨265578, by decide⟩,⟨265615, by decide⟩,⟨265636, by decide⟩,⟨265646, by decide⟩]) unmarked_context_12_24586_265647 node_context_12_24586_265647
  intro a
  fin_cases a
  · exact context_13_98344_265578
  · exact context_13_98345_265615
  · exact context_13_98346_265636
  · exact context_13_98347_265646

theorem selected_cut_09629 : selected 8 ⟨265683, by decide⟩
    (prefixPartial 13 98348) = some ⟨13, 2, 0, 265683, 98348, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_98348_265683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98348 ⟨265683, by decide⟩ :=
  accepted_of_selected 13 98348 ⟨265683, by decide⟩ ⟨13, 2, 0, 265683, 98348, 2013, 16384⟩
    (by decide) selected_cut_09629

theorem selected_cut_09630 : selected 8 ⟨265718, by decide⟩
    (prefixPartial 13 98349) = some ⟨13, 2, 0, 265718, 98349, 3257, 16384⟩ := by
  decide +kernel

theorem context_13_98349_265718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98349 ⟨265718, by decide⟩ :=
  accepted_of_selected 13 98349 ⟨265718, by decide⟩ ⟨13, 2, 0, 265718, 98349, 3257, 16384⟩
    (by decide) selected_cut_09630

theorem selected_cut_09631 : selected 8 ⟨265740, by decide⟩
    (prefixPartial 13 98350) = some ⟨13, 2, 0, 265740, 98350, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_98350_265740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98350 ⟨265740, by decide⟩ :=
  accepted_of_selected 13 98350 ⟨265740, by decide⟩ ⟨13, 2, 0, 265740, 98350, 1801, 16384⟩
    (by decide) selected_cut_09631

theorem selected_cut_09632 : selected 8 ⟨265748, by decide⟩
    (prefixPartial 13 98351) = some ⟨13, 2, 0, 265748, 98351, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_98351_265748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98351 ⟨265748, by decide⟩ :=
  accepted_of_selected 13 98351 ⟨265748, by decide⟩ ⟨13, 2, 0, 265748, 98351, 1025, 16384⟩
    (by decide) selected_cut_09632

theorem unmarked_context_12_24587_265749 : frontier 9 ⟨265749, by decide⟩
    (prefixCache 12 24587) (prefixPartial 12 24587) = false := by
  decide +kernel

theorem node_context_12_24587_265749 : EJMOriginalGlobalDAGData.nodes 9 ⟨265749, by decide⟩ =
    .split (coordinate 12) (![⟨265683, by decide⟩,⟨265718, by decide⟩,⟨265740, by decide⟩,⟨265748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24587_265749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24587 ⟨265749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24587
    ⟨265749, by decide⟩ (by decide) (![⟨265683, by decide⟩,⟨265718, by decide⟩,⟨265740, by decide⟩,⟨265748, by decide⟩]) unmarked_context_12_24587_265749 node_context_12_24587_265749
  intro a
  fin_cases a
  · exact context_13_98348_265683
  · exact context_13_98349_265718
  · exact context_13_98350_265740
  · exact context_13_98351_265748

theorem unmarked_context_11_6146_265750 : frontier 10 ⟨265750, by decide⟩
    (prefixCache 11 6146) (prefixPartial 11 6146) = false := by
  decide +kernel

theorem node_context_11_6146_265750 : EJMOriginalGlobalDAGData.nodes 10 ⟨265750, by decide⟩ =
    .split (coordinate 11) (![⟨265440, by decide⟩,⟨265545, by decide⟩,⟨265647, by decide⟩,⟨265749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6146_265750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6146 ⟨265750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6146
    ⟨265750, by decide⟩ (by decide) (![⟨265440, by decide⟩,⟨265545, by decide⟩,⟨265647, by decide⟩,⟨265749, by decide⟩]) unmarked_context_11_6146_265750 node_context_11_6146_265750
  intro a
  fin_cases a
  · exact context_12_24584_265440
  · exact context_12_24585_265545
  · exact context_12_24586_265647
  · exact context_12_24587_265749

theorem selected_cut_09633 : selected 9 ⟨265884, by decide⟩
    (prefixPartial 12 24588) = some ⟨12, 2, 0, 265884, 24588, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_24588_265884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24588 ⟨265884, by decide⟩ :=
  accepted_of_selected 12 24588 ⟨265884, by decide⟩ ⟨12, 2, 0, 265884, 24588, 2981, 65536⟩
    (by decide) selected_cut_09633

theorem selected_cut_09634 : selected 8 ⟨265910, by decide⟩
    (prefixPartial 13 98356) = some ⟨13, 2, 0, 265910, 98356, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_98356_265910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98356 ⟨265910, by decide⟩ :=
  accepted_of_selected 13 98356 ⟨265910, by decide⟩ ⟨13, 2, 0, 265910, 98356, 1601, 16384⟩
    (by decide) selected_cut_09634

theorem selected_cut_09635 : selected 8 ⟨265939, by decide⟩
    (prefixPartial 13 98357) = some ⟨13, 2, 0, 265939, 98357, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_98357_265939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98357 ⟨265939, by decide⟩ :=
  accepted_of_selected 13 98357 ⟨265939, by decide⟩ ⟨13, 2, 0, 265939, 98357, 3109, 16384⟩
    (by decide) selected_cut_09635

theorem selected_cut_09636 : selected 8 ⟨265962, by decide⟩
    (prefixPartial 13 98358) = some ⟨13, 2, 0, 265962, 98358, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_98358_265962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98358 ⟨265962, by decide⟩ :=
  accepted_of_selected 13 98358 ⟨265962, by decide⟩ ⟨13, 2, 0, 265962, 98358, 1813, 16384⟩
    (by decide) selected_cut_09636

theorem selected_cut_09637 : selected 8 ⟨265971, by decide⟩
    (prefixPartial 13 98359) = some ⟨13, 2, 0, 265971, 98359, 781, 16384⟩ := by
  decide +kernel

theorem context_13_98359_265971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98359 ⟨265971, by decide⟩ :=
  accepted_of_selected 13 98359 ⟨265971, by decide⟩ ⟨13, 2, 0, 265971, 98359, 781, 16384⟩
    (by decide) selected_cut_09637

theorem unmarked_context_12_24589_265972 : frontier 9 ⟨265972, by decide⟩
    (prefixCache 12 24589) (prefixPartial 12 24589) = false := by
  decide +kernel

theorem node_context_12_24589_265972 : EJMOriginalGlobalDAGData.nodes 9 ⟨265972, by decide⟩ =
    .split (coordinate 12) (![⟨265910, by decide⟩,⟨265939, by decide⟩,⟨265962, by decide⟩,⟨265971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24589_265972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24589 ⟨265972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24589
    ⟨265972, by decide⟩ (by decide) (![⟨265910, by decide⟩,⟨265939, by decide⟩,⟨265962, by decide⟩,⟨265971, by decide⟩]) unmarked_context_12_24589_265972 node_context_12_24589_265972
  intro a
  fin_cases a
  · exact context_13_98356_265910
  · exact context_13_98357_265939
  · exact context_13_98358_265962
  · exact context_13_98359_265971

theorem selected_cut_09638 : selected 8 ⟨265997, by decide⟩
    (prefixPartial 13 98360) = some ⟨13, 2, 0, 265997, 98360, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_98360_265997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98360 ⟨265997, by decide⟩ :=
  accepted_of_selected 13 98360 ⟨265997, by decide⟩ ⟨13, 2, 0, 265997, 98360, 1553, 16384⟩
    (by decide) selected_cut_09638

theorem selected_cut_09639 : selected 8 ⟨266034, by decide⟩
    (prefixPartial 13 98361) = some ⟨13, 2, 0, 266034, 98361, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_98361_266034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98361 ⟨266034, by decide⟩ :=
  accepted_of_selected 13 98361 ⟨266034, by decide⟩ ⟨13, 2, 0, 266034, 98361, 3181, 16384⟩
    (by decide) selected_cut_09639

theorem selected_cut_09640 : selected 8 ⟨266060, by decide⟩
    (prefixPartial 13 98362) = some ⟨13, 2, 0, 266060, 98362, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_98362_266060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98362 ⟨266060, by decide⟩ :=
  accepted_of_selected 13 98362 ⟨266060, by decide⟩ ⟨13, 2, 0, 266060, 98362, 1865, 16384⟩
    (by decide) selected_cut_09640

theorem selected_cut_09641 : selected 8 ⟨266068, by decide⟩
    (prefixPartial 13 98363) = some ⟨13, 2, 0, 266068, 98363, 837, 16384⟩ := by
  decide +kernel

theorem context_13_98363_266068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98363 ⟨266068, by decide⟩ :=
  accepted_of_selected 13 98363 ⟨266068, by decide⟩ ⟨13, 2, 0, 266068, 98363, 837, 16384⟩
    (by decide) selected_cut_09641

theorem unmarked_context_12_24590_266069 : frontier 9 ⟨266069, by decide⟩
    (prefixCache 12 24590) (prefixPartial 12 24590) = false := by
  decide +kernel

theorem node_context_12_24590_266069 : EJMOriginalGlobalDAGData.nodes 9 ⟨266069, by decide⟩ =
    .split (coordinate 12) (![⟨265997, by decide⟩,⟨266034, by decide⟩,⟨266060, by decide⟩,⟨266068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24590_266069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24590 ⟨266069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24590
    ⟨266069, by decide⟩ (by decide) (![⟨265997, by decide⟩,⟨266034, by decide⟩,⟨266060, by decide⟩,⟨266068, by decide⟩]) unmarked_context_12_24590_266069 node_context_12_24590_266069
  intro a
  fin_cases a
  · exact context_13_98360_265997
  · exact context_13_98361_266034
  · exact context_13_98362_266060
  · exact context_13_98363_266068

theorem selected_cut_09642 : selected 8 ⟨266101, by decide⟩
    (prefixPartial 13 98364) = some ⟨13, 2, 0, 266101, 98364, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_98364_266101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98364 ⟨266101, by decide⟩ :=
  accepted_of_selected 13 98364 ⟨266101, by decide⟩ ⟨13, 2, 0, 266101, 98364, 1725, 16384⟩
    (by decide) selected_cut_09642

theorem selected_cut_09643 : selected 8 ⟨266138, by decide⟩
    (prefixPartial 13 98365) = some ⟨13, 2, 0, 266138, 98365, 3129, 16384⟩ := by
  decide +kernel

theorem context_13_98365_266138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98365 ⟨266138, by decide⟩ :=
  accepted_of_selected 13 98365 ⟨266138, by decide⟩ ⟨13, 2, 0, 266138, 98365, 3129, 16384⟩
    (by decide) selected_cut_09643

theorem selected_cut_09644 : selected 8 ⟨266160, by decide⟩
    (prefixPartial 13 98366) = some ⟨13, 2, 0, 266160, 98366, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_98366_266160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98366 ⟨266160, by decide⟩ :=
  accepted_of_selected 13 98366 ⟨266160, by decide⟩ ⟨13, 2, 0, 266160, 98366, 1873, 16384⟩
    (by decide) selected_cut_09644

theorem selected_cut_09645 : selected 8 ⟨266166, by decide⟩
    (prefixPartial 13 98367) = some ⟨13, 2, 0, 266166, 98367, 941, 16384⟩ := by
  decide +kernel

theorem context_13_98367_266166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98367 ⟨266166, by decide⟩ :=
  accepted_of_selected 13 98367 ⟨266166, by decide⟩ ⟨13, 2, 0, 266166, 98367, 941, 16384⟩
    (by decide) selected_cut_09645

theorem unmarked_context_12_24591_266167 : frontier 9 ⟨266167, by decide⟩
    (prefixCache 12 24591) (prefixPartial 12 24591) = false := by
  decide +kernel

theorem node_context_12_24591_266167 : EJMOriginalGlobalDAGData.nodes 9 ⟨266167, by decide⟩ =
    .split (coordinate 12) (![⟨266101, by decide⟩,⟨266138, by decide⟩,⟨266160, by decide⟩,⟨266166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24591_266167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24591 ⟨266167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24591
    ⟨266167, by decide⟩ (by decide) (![⟨266101, by decide⟩,⟨266138, by decide⟩,⟨266160, by decide⟩,⟨266166, by decide⟩]) unmarked_context_12_24591_266167 node_context_12_24591_266167
  intro a
  fin_cases a
  · exact context_13_98364_266101
  · exact context_13_98365_266138
  · exact context_13_98366_266160
  · exact context_13_98367_266166

theorem unmarked_context_11_6147_266168 : frontier 10 ⟨266168, by decide⟩
    (prefixCache 11 6147) (prefixPartial 11 6147) = false := by
  decide +kernel

theorem node_context_11_6147_266168 : EJMOriginalGlobalDAGData.nodes 10 ⟨266168, by decide⟩ =
    .split (coordinate 11) (![⟨265884, by decide⟩,⟨265972, by decide⟩,⟨266069, by decide⟩,⟨266167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6147_266168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6147 ⟨266168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6147
    ⟨266168, by decide⟩ (by decide) (![⟨265884, by decide⟩,⟨265972, by decide⟩,⟨266069, by decide⟩,⟨266167, by decide⟩]) unmarked_context_11_6147_266168 node_context_11_6147_266168
  intro a
  fin_cases a
  · exact context_12_24588_265884
  · exact context_12_24589_265972
  · exact context_12_24590_266069
  · exact context_12_24591_266167

theorem unmarked_context_10_1536_266169 : frontier 11 ⟨266169, by decide⟩
    (prefixCache 10 1536) (prefixPartial 10 1536) = false := by
  decide +kernel

theorem node_context_10_1536_266169 : EJMOriginalGlobalDAGData.nodes 11 ⟨266169, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨265345, by decide⟩,⟨265750, by decide⟩,⟨266168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1536_266169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1536 ⟨266169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1536
    ⟨266169, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨265345, by decide⟩,⟨265750, by decide⟩,⟨266168, by decide⟩]) unmarked_context_10_1536_266169 node_context_10_1536_266169
  intro a
  fin_cases a
  · exact context_11_6144_167448
  · exact context_11_6145_265345
  · exact context_11_6146_265750
  · exact context_11_6147_266168

theorem selected_cut_09646 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 24592) = some ⟨12, 1, 0, 266170, 24592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24592_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24592 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 24592 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 24592, 1, 65536⟩
    (by decide) selected_cut_09646

theorem selected_cut_09647 : selected 9 ⟨266216, by decide⟩
    (prefixPartial 12 24593) = some ⟨12, 2, 0, 266216, 24593, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_24593_266216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24593 ⟨266216, by decide⟩ :=
  accepted_of_selected 12 24593 ⟨266216, by decide⟩ ⟨12, 2, 0, 266216, 24593, 2957, 65536⟩
    (by decide) selected_cut_09647

theorem selected_cut_09648 : selected 9 ⟨266261, by decide⟩
    (prefixPartial 12 24594) = some ⟨12, 2, 0, 266261, 24594, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_24594_266261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24594 ⟨266261, by decide⟩ :=
  accepted_of_selected 12 24594 ⟨266261, by decide⟩ ⟨12, 2, 0, 266261, 24594, 3053, 65536⟩
    (by decide) selected_cut_09648

theorem selected_cut_09649 : selected 9 ⟨266307, by decide⟩
    (prefixPartial 12 24595) = some ⟨12, 2, 0, 266307, 24595, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_24595_266307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24595 ⟨266307, by decide⟩ :=
  accepted_of_selected 12 24595 ⟨266307, by decide⟩ ⟨12, 2, 0, 266307, 24595, 3237, 65536⟩
    (by decide) selected_cut_09649

theorem unmarked_context_11_6148_266308 : frontier 10 ⟨266308, by decide⟩
    (prefixCache 11 6148) (prefixPartial 11 6148) = false := by
  decide +kernel

theorem node_context_11_6148_266308 : EJMOriginalGlobalDAGData.nodes 10 ⟨266308, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨266216, by decide⟩,⟨266261, by decide⟩,⟨266307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6148_266308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6148 ⟨266308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6148
    ⟨266308, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨266216, by decide⟩,⟨266261, by decide⟩,⟨266307, by decide⟩]) unmarked_context_11_6148_266308 node_context_11_6148_266308
  intro a
  fin_cases a
  · exact context_12_24592_266170
  · exact context_12_24593_266216
  · exact context_12_24594_266261
  · exact context_12_24595_266307

theorem selected_cut_09650 : selected 9 ⟨266363, by decide⟩
    (prefixPartial 12 24596) = some ⟨12, 2, 0, 266363, 24596, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_24596_266363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24596 ⟨266363, by decide⟩ :=
  accepted_of_selected 12 24596 ⟨266363, by decide⟩ ⟨12, 2, 0, 266363, 24596, 3561, 65536⟩
    (by decide) selected_cut_09650

theorem selected_cut_09651 : selected 9 ⟨266421, by decide⟩
    (prefixPartial 12 24597) = some ⟨12, 2, 0, 266421, 24597, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_24597_266421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24597 ⟨266421, by decide⟩ :=
  accepted_of_selected 12 24597 ⟨266421, by decide⟩ ⟨12, 2, 0, 266421, 24597, 4001, 65536⟩
    (by decide) selected_cut_09651

theorem selected_cut_09652 : selected 8 ⟨266436, by decide⟩
    (prefixPartial 13 98392) = some ⟨13, 2, 0, 266436, 98392, 857, 16384⟩ := by
  decide +kernel

theorem context_13_98392_266436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98392 ⟨266436, by decide⟩ :=
  accepted_of_selected 13 98392 ⟨266436, by decide⟩ ⟨13, 2, 0, 266436, 98392, 857, 16384⟩
    (by decide) selected_cut_09652

theorem selected_cut_09653 : selected 8 ⟨266461, by decide⟩
    (prefixPartial 13 98393) = some ⟨13, 2, 0, 266461, 98393, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_98393_266461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98393 ⟨266461, by decide⟩ :=
  accepted_of_selected 13 98393 ⟨266461, by decide⟩ ⟨13, 2, 0, 266461, 98393, 1565, 16384⟩
    (by decide) selected_cut_09653

theorem selected_cut_09654 : selected 8 ⟨266478, by decide⟩
    (prefixPartial 13 98394) = some ⟨13, 2, 0, 266478, 98394, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_98394_266478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98394 ⟨266478, by decide⟩ :=
  accepted_of_selected 13 98394 ⟨266478, by decide⟩ ⟨13, 2, 0, 266478, 98394, 1109, 16384⟩
    (by decide) selected_cut_09654

theorem selected_cut_09655 : selected 8 ⟨266485, by decide⟩
    (prefixPartial 13 98395) = some ⟨13, 2, 0, 266485, 98395, 745, 16384⟩ := by
  decide +kernel

theorem context_13_98395_266485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98395 ⟨266485, by decide⟩ :=
  accepted_of_selected 13 98395 ⟨266485, by decide⟩ ⟨13, 2, 0, 266485, 98395, 745, 16384⟩
    (by decide) selected_cut_09655

theorem unmarked_context_12_24598_266486 : frontier 9 ⟨266486, by decide⟩
    (prefixCache 12 24598) (prefixPartial 12 24598) = false := by
  decide +kernel

theorem node_context_12_24598_266486 : EJMOriginalGlobalDAGData.nodes 9 ⟨266486, by decide⟩ =
    .split (coordinate 12) (![⟨266436, by decide⟩,⟨266461, by decide⟩,⟨266478, by decide⟩,⟨266485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24598_266486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24598 ⟨266486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24598
    ⟨266486, by decide⟩ (by decide) (![⟨266436, by decide⟩,⟨266461, by decide⟩,⟨266478, by decide⟩,⟨266485, by decide⟩]) unmarked_context_12_24598_266486 node_context_12_24598_266486
  intro a
  fin_cases a
  · exact context_13_98392_266436
  · exact context_13_98393_266461
  · exact context_13_98394_266478
  · exact context_13_98395_266485

theorem selected_cut_09656 : selected 8 ⟨266503, by decide⟩
    (prefixPartial 13 98396) = some ⟨13, 2, 0, 266503, 98396, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_98396_266503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98396 ⟨266503, by decide⟩ :=
  accepted_of_selected 13 98396 ⟨266503, by decide⟩ ⟨13, 2, 0, 266503, 98396, 1045, 16384⟩
    (by decide) selected_cut_09656

theorem selected_cut_09657 : selected 8 ⟨266526, by decide⟩
    (prefixPartial 13 98397) = some ⟨13, 2, 0, 266526, 98397, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_98397_266526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98397 ⟨266526, by decide⟩ :=
  accepted_of_selected 13 98397 ⟨266526, by decide⟩ ⟨13, 2, 0, 266526, 98397, 1601, 16384⟩
    (by decide) selected_cut_09657

theorem selected_cut_09658 : selected 8 ⟨266545, by decide⟩
    (prefixPartial 13 98398) = some ⟨13, 2, 0, 266545, 98398, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_98398_266545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98398 ⟨266545, by decide⟩ :=
  accepted_of_selected 13 98398 ⟨266545, by decide⟩ ⟨13, 2, 0, 266545, 98398, 1249, 16384⟩
    (by decide) selected_cut_09658

theorem selected_cut_09659 : selected 8 ⟨266553, by decide⟩
    (prefixPartial 13 98399) = some ⟨13, 2, 0, 266553, 98399, 765, 16384⟩ := by
  decide +kernel

theorem context_13_98399_266553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98399 ⟨266553, by decide⟩ :=
  accepted_of_selected 13 98399 ⟨266553, by decide⟩ ⟨13, 2, 0, 266553, 98399, 765, 16384⟩
    (by decide) selected_cut_09659

theorem unmarked_context_12_24599_266554 : frontier 9 ⟨266554, by decide⟩
    (prefixCache 12 24599) (prefixPartial 12 24599) = false := by
  decide +kernel

theorem node_context_12_24599_266554 : EJMOriginalGlobalDAGData.nodes 9 ⟨266554, by decide⟩ =
    .split (coordinate 12) (![⟨266503, by decide⟩,⟨266526, by decide⟩,⟨266545, by decide⟩,⟨266553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24599_266554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24599 ⟨266554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24599
    ⟨266554, by decide⟩ (by decide) (![⟨266503, by decide⟩,⟨266526, by decide⟩,⟨266545, by decide⟩,⟨266553, by decide⟩]) unmarked_context_12_24599_266554 node_context_12_24599_266554
  intro a
  fin_cases a
  · exact context_13_98396_266503
  · exact context_13_98397_266526
  · exact context_13_98398_266545
  · exact context_13_98399_266553

theorem unmarked_context_11_6149_266555 : frontier 10 ⟨266555, by decide⟩
    (prefixCache 11 6149) (prefixPartial 11 6149) = false := by
  decide +kernel

theorem node_context_11_6149_266555 : EJMOriginalGlobalDAGData.nodes 10 ⟨266555, by decide⟩ =
    .split (coordinate 11) (![⟨266363, by decide⟩,⟨266421, by decide⟩,⟨266486, by decide⟩,⟨266554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6149_266555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6149 ⟨266555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6149
    ⟨266555, by decide⟩ (by decide) (![⟨266363, by decide⟩,⟨266421, by decide⟩,⟨266486, by decide⟩,⟨266554, by decide⟩]) unmarked_context_11_6149_266555 node_context_11_6149_266555
  intro a
  fin_cases a
  · exact context_12_24596_266363
  · exact context_12_24597_266421
  · exact context_12_24598_266486
  · exact context_12_24599_266554

theorem selected_cut_09660 : selected 9 ⟨266615, by decide⟩
    (prefixPartial 12 24600) = some ⟨12, 2, 0, 266615, 24600, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_24600_266615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24600 ⟨266615, by decide⟩ :=
  accepted_of_selected 12 24600 ⟨266615, by decide⟩ ⟨12, 2, 0, 266615, 24600, 3713, 65536⟩
    (by decide) selected_cut_09660

theorem selected_cut_09661 : selected 8 ⟨266633, by decide⟩
    (prefixPartial 13 98404) = some ⟨13, 2, 0, 266633, 98404, 833, 16384⟩ := by
  decide +kernel

theorem context_13_98404_266633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98404 ⟨266633, by decide⟩ :=
  accepted_of_selected 13 98404 ⟨266633, by decide⟩ ⟨13, 2, 0, 266633, 98404, 833, 16384⟩
    (by decide) selected_cut_09661

theorem selected_cut_09662 : selected 8 ⟨266659, by decide⟩
    (prefixPartial 13 98405) = some ⟨13, 2, 0, 266659, 98405, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_98405_266659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98405 ⟨266659, by decide⟩ :=
  accepted_of_selected 13 98405 ⟨266659, by decide⟩ ⟨13, 2, 0, 266659, 98405, 1537, 16384⟩
    (by decide) selected_cut_09662

theorem selected_cut_09663 : selected 8 ⟨266676, by decide⟩
    (prefixPartial 13 98406) = some ⟨13, 2, 0, 266676, 98406, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_98406_266676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98406 ⟨266676, by decide⟩ :=
  accepted_of_selected 13 98406 ⟨266676, by decide⟩ ⟨13, 2, 0, 266676, 98406, 1201, 16384⟩
    (by decide) selected_cut_09663

theorem selected_cut_09664 : selected 8 ⟨266680, by decide⟩
    (prefixPartial 13 98407) = some ⟨13, 2, 0, 266680, 98407, 689, 16384⟩ := by
  decide +kernel

theorem context_13_98407_266680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98407 ⟨266680, by decide⟩ :=
  accepted_of_selected 13 98407 ⟨266680, by decide⟩ ⟨13, 2, 0, 266680, 98407, 689, 16384⟩
    (by decide) selected_cut_09664

theorem unmarked_context_12_24601_266681 : frontier 9 ⟨266681, by decide⟩
    (prefixCache 12 24601) (prefixPartial 12 24601) = false := by
  decide +kernel

theorem node_context_12_24601_266681 : EJMOriginalGlobalDAGData.nodes 9 ⟨266681, by decide⟩ =
    .split (coordinate 12) (![⟨266633, by decide⟩,⟨266659, by decide⟩,⟨266676, by decide⟩,⟨266680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24601_266681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24601 ⟨266681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24601
    ⟨266681, by decide⟩ (by decide) (![⟨266633, by decide⟩,⟨266659, by decide⟩,⟨266676, by decide⟩,⟨266680, by decide⟩]) unmarked_context_12_24601_266681 node_context_12_24601_266681
  intro a
  fin_cases a
  · exact context_13_98404_266633
  · exact context_13_98405_266659
  · exact context_13_98406_266676
  · exact context_13_98407_266680

theorem selected_cut_09665 : selected 9 ⟨266734, by decide⟩
    (prefixPartial 12 24602) = some ⟨12, 2, 0, 266734, 24602, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_24602_266734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24602 ⟨266734, by decide⟩ :=
  accepted_of_selected 12 24602 ⟨266734, by decide⟩ ⟨12, 2, 0, 266734, 24602, 4013, 65536⟩
    (by decide) selected_cut_09665

theorem selected_cut_09666 : selected 8 ⟨266750, by decide⟩
    (prefixPartial 13 98412) = some ⟨13, 2, 0, 266750, 98412, 949, 16384⟩ := by
  decide +kernel

theorem context_13_98412_266750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98412 ⟨266750, by decide⟩ :=
  accepted_of_selected 13 98412 ⟨266750, by decide⟩ ⟨13, 2, 0, 266750, 98412, 949, 16384⟩
    (by decide) selected_cut_09666

theorem selected_cut_09667 : selected 8 ⟨266777, by decide⟩
    (prefixPartial 13 98413) = some ⟨13, 2, 0, 266777, 98413, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_98413_266777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98413 ⟨266777, by decide⟩ :=
  accepted_of_selected 13 98413 ⟨266777, by decide⟩ ⟨13, 2, 0, 266777, 98413, 1593, 16384⟩
    (by decide) selected_cut_09667

theorem selected_cut_09668 : selected 8 ⟨266791, by decide⟩
    (prefixPartial 13 98414) = some ⟨13, 2, 0, 266791, 98414, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_98414_266791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98414 ⟨266791, by decide⟩ :=
  accepted_of_selected 13 98414 ⟨266791, by decide⟩ ⟨13, 2, 0, 266791, 98414, 1205, 16384⟩
    (by decide) selected_cut_09668

theorem selected_cut_09669 : selected 8 ⟨266798, by decide⟩
    (prefixPartial 13 98415) = some ⟨13, 2, 0, 266798, 98415, 757, 16384⟩ := by
  decide +kernel

theorem context_13_98415_266798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98415 ⟨266798, by decide⟩ :=
  accepted_of_selected 13 98415 ⟨266798, by decide⟩ ⟨13, 2, 0, 266798, 98415, 757, 16384⟩
    (by decide) selected_cut_09669

theorem unmarked_context_12_24603_266799 : frontier 9 ⟨266799, by decide⟩
    (prefixCache 12 24603) (prefixPartial 12 24603) = false := by
  decide +kernel

theorem node_context_12_24603_266799 : EJMOriginalGlobalDAGData.nodes 9 ⟨266799, by decide⟩ =
    .split (coordinate 12) (![⟨266750, by decide⟩,⟨266777, by decide⟩,⟨266791, by decide⟩,⟨266798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24603_266799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24603 ⟨266799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24603
    ⟨266799, by decide⟩ (by decide) (![⟨266750, by decide⟩,⟨266777, by decide⟩,⟨266791, by decide⟩,⟨266798, by decide⟩]) unmarked_context_12_24603_266799 node_context_12_24603_266799
  intro a
  fin_cases a
  · exact context_13_98412_266750
  · exact context_13_98413_266777
  · exact context_13_98414_266791
  · exact context_13_98415_266798

theorem unmarked_context_11_6150_266800 : frontier 10 ⟨266800, by decide⟩
    (prefixCache 11 6150) (prefixPartial 11 6150) = false := by
  decide +kernel

theorem node_context_11_6150_266800 : EJMOriginalGlobalDAGData.nodes 10 ⟨266800, by decide⟩ =
    .split (coordinate 11) (![⟨266615, by decide⟩,⟨266681, by decide⟩,⟨266734, by decide⟩,⟨266799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6150_266800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6150 ⟨266800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6150
    ⟨266800, by decide⟩ (by decide) (![⟨266615, by decide⟩,⟨266681, by decide⟩,⟨266734, by decide⟩,⟨266799, by decide⟩]) unmarked_context_11_6150_266800 node_context_11_6150_266800
  intro a
  fin_cases a
  · exact context_12_24600_266615
  · exact context_12_24601_266681
  · exact context_12_24602_266734
  · exact context_12_24603_266799

theorem selected_cut_09670 : selected 9 ⟨266843, by decide⟩
    (prefixPartial 12 24604) = some ⟨12, 2, 0, 266843, 24604, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_24604_266843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24604 ⟨266843, by decide⟩ :=
  accepted_of_selected 12 24604 ⟨266843, by decide⟩ ⟨12, 2, 0, 266843, 24604, 3365, 65536⟩
    (by decide) selected_cut_09670

theorem selected_cut_09671 : selected 8 ⟨266858, by decide⟩
    (prefixPartial 13 98420) = some ⟨13, 2, 0, 266858, 98420, 881, 16384⟩ := by
  decide +kernel

theorem context_13_98420_266858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98420 ⟨266858, by decide⟩ :=
  accepted_of_selected 13 98420 ⟨266858, by decide⟩ ⟨13, 2, 0, 266858, 98420, 881, 16384⟩
    (by decide) selected_cut_09671

theorem selected_cut_09672 : selected 8 ⟨266881, by decide⟩
    (prefixPartial 13 98421) = some ⟨13, 2, 0, 266881, 98421, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_98421_266881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98421 ⟨266881, by decide⟩ :=
  accepted_of_selected 13 98421 ⟨266881, by decide⟩ ⟨13, 2, 0, 266881, 98421, 1545, 16384⟩
    (by decide) selected_cut_09672

theorem selected_cut_09673 : selected 8 ⟨266897, by decide⟩
    (prefixPartial 13 98422) = some ⟨13, 2, 0, 266897, 98422, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_98422_266897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98422 ⟨266897, by decide⟩ :=
  accepted_of_selected 13 98422 ⟨266897, by decide⟩ ⟨13, 2, 0, 266897, 98422, 1205, 16384⟩
    (by decide) selected_cut_09673

theorem selected_cut_09674 : selected 8 ⟨266904, by decide⟩
    (prefixPartial 13 98423) = some ⟨13, 2, 0, 266904, 98423, 641, 16384⟩ := by
  decide +kernel

theorem context_13_98423_266904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98423 ⟨266904, by decide⟩ :=
  accepted_of_selected 13 98423 ⟨266904, by decide⟩ ⟨13, 2, 0, 266904, 98423, 641, 16384⟩
    (by decide) selected_cut_09674

theorem unmarked_context_12_24605_266905 : frontier 9 ⟨266905, by decide⟩
    (prefixCache 12 24605) (prefixPartial 12 24605) = false := by
  decide +kernel

theorem node_context_12_24605_266905 : EJMOriginalGlobalDAGData.nodes 9 ⟨266905, by decide⟩ =
    .split (coordinate 12) (![⟨266858, by decide⟩,⟨266881, by decide⟩,⟨266897, by decide⟩,⟨266904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24605_266905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24605 ⟨266905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24605
    ⟨266905, by decide⟩ (by decide) (![⟨266858, by decide⟩,⟨266881, by decide⟩,⟨266897, by decide⟩,⟨266904, by decide⟩]) unmarked_context_12_24605_266905 node_context_12_24605_266905
  intro a
  fin_cases a
  · exact context_13_98420_266858
  · exact context_13_98421_266881
  · exact context_13_98422_266897
  · exact context_13_98423_266904

theorem selected_cut_09675 : selected 8 ⟨266917, by decide⟩
    (prefixPartial 13 98424) = some ⟨13, 2, 0, 266917, 98424, 849, 16384⟩ := by
  decide +kernel

theorem context_13_98424_266917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98424 ⟨266917, by decide⟩ :=
  accepted_of_selected 13 98424 ⟨266917, by decide⟩ ⟨13, 2, 0, 266917, 98424, 849, 16384⟩
    (by decide) selected_cut_09675

theorem selected_cut_09676 : selected 8 ⟨266939, by decide⟩
    (prefixPartial 13 98425) = some ⟨13, 2, 0, 266939, 98425, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_98425_266939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98425 ⟨266939, by decide⟩ :=
  accepted_of_selected 13 98425 ⟨266939, by decide⟩ ⟨13, 2, 0, 266939, 98425, 1609, 16384⟩
    (by decide) selected_cut_09676

theorem selected_cut_09677 : selected 8 ⟨266953, by decide⟩
    (prefixPartial 13 98426) = some ⟨13, 2, 0, 266953, 98426, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_98426_266953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98426 ⟨266953, by decide⟩ :=
  accepted_of_selected 13 98426 ⟨266953, by decide⟩ ⟨13, 2, 0, 266953, 98426, 1101, 16384⟩
    (by decide) selected_cut_09677

theorem selected_cut_09678 : selected 8 ⟨266960, by decide⟩
    (prefixPartial 13 98427) = some ⟨13, 2, 0, 266960, 98427, 673, 16384⟩ := by
  decide +kernel

theorem context_13_98427_266960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98427 ⟨266960, by decide⟩ :=
  accepted_of_selected 13 98427 ⟨266960, by decide⟩ ⟨13, 2, 0, 266960, 98427, 673, 16384⟩
    (by decide) selected_cut_09678

theorem unmarked_context_12_24606_266961 : frontier 9 ⟨266961, by decide⟩
    (prefixCache 12 24606) (prefixPartial 12 24606) = false := by
  decide +kernel

theorem node_context_12_24606_266961 : EJMOriginalGlobalDAGData.nodes 9 ⟨266961, by decide⟩ =
    .split (coordinate 12) (![⟨266917, by decide⟩,⟨266939, by decide⟩,⟨266953, by decide⟩,⟨266960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24606_266961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24606 ⟨266961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24606
    ⟨266961, by decide⟩ (by decide) (![⟨266917, by decide⟩,⟨266939, by decide⟩,⟨266953, by decide⟩,⟨266960, by decide⟩]) unmarked_context_12_24606_266961 node_context_12_24606_266961
  intro a
  fin_cases a
  · exact context_13_98424_266917
  · exact context_13_98425_266939
  · exact context_13_98426_266953
  · exact context_13_98427_266960

theorem selected_cut_09679 : selected 8 ⟨266974, by decide⟩
    (prefixPartial 13 98428) = some ⟨13, 2, 0, 266974, 98428, 901, 16384⟩ := by
  decide +kernel

theorem context_13_98428_266974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98428 ⟨266974, by decide⟩ :=
  accepted_of_selected 13 98428 ⟨266974, by decide⟩ ⟨13, 2, 0, 266974, 98428, 901, 16384⟩
    (by decide) selected_cut_09679

theorem selected_cut_09680 : selected 8 ⟨266995, by decide⟩
    (prefixPartial 13 98429) = some ⟨13, 2, 0, 266995, 98429, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_98429_266995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98429 ⟨266995, by decide⟩ :=
  accepted_of_selected 13 98429 ⟨266995, by decide⟩ ⟨13, 2, 0, 266995, 98429, 1501, 16384⟩
    (by decide) selected_cut_09680

theorem selected_cut_09681 : selected 8 ⟨267010, by decide⟩
    (prefixPartial 13 98430) = some ⟨13, 2, 0, 267010, 98430, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_98430_267010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98430 ⟨267010, by decide⟩ :=
  accepted_of_selected 13 98430 ⟨267010, by decide⟩ ⟨13, 2, 0, 267010, 98430, 1137, 16384⟩
    (by decide) selected_cut_09681

theorem selected_cut_09682 : selected 8 ⟨267017, by decide⟩
    (prefixPartial 13 98431) = some ⟨13, 2, 0, 267017, 98431, 681, 16384⟩ := by
  decide +kernel

theorem context_13_98431_267017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98431 ⟨267017, by decide⟩ :=
  accepted_of_selected 13 98431 ⟨267017, by decide⟩ ⟨13, 2, 0, 267017, 98431, 681, 16384⟩
    (by decide) selected_cut_09682

theorem unmarked_context_12_24607_267018 : frontier 9 ⟨267018, by decide⟩
    (prefixCache 12 24607) (prefixPartial 12 24607) = false := by
  decide +kernel

theorem node_context_12_24607_267018 : EJMOriginalGlobalDAGData.nodes 9 ⟨267018, by decide⟩ =
    .split (coordinate 12) (![⟨266974, by decide⟩,⟨266995, by decide⟩,⟨267010, by decide⟩,⟨267017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24607_267018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24607 ⟨267018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24607
    ⟨267018, by decide⟩ (by decide) (![⟨266974, by decide⟩,⟨266995, by decide⟩,⟨267010, by decide⟩,⟨267017, by decide⟩]) unmarked_context_12_24607_267018 node_context_12_24607_267018
  intro a
  fin_cases a
  · exact context_13_98428_266974
  · exact context_13_98429_266995
  · exact context_13_98430_267010
  · exact context_13_98431_267017

theorem unmarked_context_11_6151_267019 : frontier 10 ⟨267019, by decide⟩
    (prefixCache 11 6151) (prefixPartial 11 6151) = false := by
  decide +kernel

theorem node_context_11_6151_267019 : EJMOriginalGlobalDAGData.nodes 10 ⟨267019, by decide⟩ =
    .split (coordinate 11) (![⟨266843, by decide⟩,⟨266905, by decide⟩,⟨266961, by decide⟩,⟨267018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6151_267019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6151 ⟨267019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6151
    ⟨267019, by decide⟩ (by decide) (![⟨266843, by decide⟩,⟨266905, by decide⟩,⟨266961, by decide⟩,⟨267018, by decide⟩]) unmarked_context_11_6151_267019 node_context_11_6151_267019
  intro a
  fin_cases a
  · exact context_12_24604_266843
  · exact context_12_24605_266905
  · exact context_12_24606_266961
  · exact context_12_24607_267018

theorem unmarked_context_10_1537_267020 : frontier 11 ⟨267020, by decide⟩
    (prefixCache 10 1537) (prefixPartial 10 1537) = false := by
  decide +kernel

theorem node_context_10_1537_267020 : EJMOriginalGlobalDAGData.nodes 11 ⟨267020, by decide⟩ =
    .split (coordinate 10) (![⟨266308, by decide⟩,⟨266555, by decide⟩,⟨266800, by decide⟩,⟨267019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1537_267020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1537 ⟨267020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1537
    ⟨267020, by decide⟩ (by decide) (![⟨266308, by decide⟩,⟨266555, by decide⟩,⟨266800, by decide⟩,⟨267019, by decide⟩]) unmarked_context_10_1537_267020 node_context_10_1537_267020
  intro a
  fin_cases a
  · exact context_11_6148_266308
  · exact context_11_6149_266555
  · exact context_11_6150_266800
  · exact context_11_6151_267019

theorem selected_cut_09683 : selected 9 ⟨267104, by decide⟩
    (prefixPartial 12 24608) = some ⟨12, 2, 0, 267104, 24608, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_24608_267104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24608 ⟨267104, by decide⟩ :=
  accepted_of_selected 12 24608 ⟨267104, by decide⟩ ⟨12, 2, 0, 267104, 24608, 3029, 65536⟩
    (by decide) selected_cut_09683

theorem selected_cut_09684 : selected 9 ⟨267141, by decide⟩
    (prefixPartial 12 24609) = some ⟨12, 2, 0, 267141, 24609, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_24609_267141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24609 ⟨267141, by decide⟩ :=
  accepted_of_selected 12 24609 ⟨267141, by decide⟩ ⟨12, 2, 0, 267141, 24609, 2713, 65536⟩
    (by decide) selected_cut_09684

theorem selected_cut_09685 : selected 9 ⟨267181, by decide⟩
    (prefixPartial 12 24610) = some ⟨12, 2, 0, 267181, 24610, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_24610_267181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24610 ⟨267181, by decide⟩ :=
  accepted_of_selected 12 24610 ⟨267181, by decide⟩ ⟨12, 2, 0, 267181, 24610, 2813, 65536⟩
    (by decide) selected_cut_09685

theorem selected_cut_09686 : selected 9 ⟨267220, by decide⟩
    (prefixPartial 12 24611) = some ⟨12, 2, 0, 267220, 24611, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_24611_267220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24611 ⟨267220, by decide⟩ :=
  accepted_of_selected 12 24611 ⟨267220, by decide⟩ ⟨12, 2, 0, 267220, 24611, 2821, 65536⟩
    (by decide) selected_cut_09686

theorem unmarked_context_11_6152_267221 : frontier 10 ⟨267221, by decide⟩
    (prefixCache 11 6152) (prefixPartial 11 6152) = false := by
  decide +kernel

theorem node_context_11_6152_267221 : EJMOriginalGlobalDAGData.nodes 10 ⟨267221, by decide⟩ =
    .split (coordinate 11) (![⟨267104, by decide⟩,⟨267141, by decide⟩,⟨267181, by decide⟩,⟨267220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6152_267221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6152 ⟨267221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6152
    ⟨267221, by decide⟩ (by decide) (![⟨267104, by decide⟩,⟨267141, by decide⟩,⟨267181, by decide⟩,⟨267220, by decide⟩]) unmarked_context_11_6152_267221 node_context_11_6152_267221
  intro a
  fin_cases a
  · exact context_12_24608_267104
  · exact context_12_24609_267141
  · exact context_12_24610_267181
  · exact context_12_24611_267220

theorem selected_cut_09687 : selected 9 ⟨267268, by decide⟩
    (prefixPartial 12 24612) = some ⟨12, 2, 0, 267268, 24612, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_24612_267268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24612 ⟨267268, by decide⟩ :=
  accepted_of_selected 12 24612 ⟨267268, by decide⟩ ⟨12, 2, 0, 267268, 24612, 3289, 65536⟩
    (by decide) selected_cut_09687

theorem selected_cut_09688 : selected 9 ⟨267314, by decide⟩
    (prefixPartial 12 24613) = some ⟨12, 2, 0, 267314, 24613, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_24613_267314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24613 ⟨267314, by decide⟩ :=
  accepted_of_selected 12 24613 ⟨267314, by decide⟩ ⟨12, 2, 0, 267314, 24613, 3545, 65536⟩
    (by decide) selected_cut_09688

theorem selected_cut_09689 : selected 9 ⟨267370, by decide⟩
    (prefixPartial 12 24614) = some ⟨12, 2, 0, 267370, 24614, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_24614_267370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24614 ⟨267370, by decide⟩ :=
  accepted_of_selected 12 24614 ⟨267370, by decide⟩ ⟨12, 2, 0, 267370, 24614, 3965, 65536⟩
    (by decide) selected_cut_09689

theorem selected_cut_09690 : selected 9 ⟨267427, by decide⟩
    (prefixPartial 12 24615) = some ⟨12, 2, 0, 267427, 24615, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_24615_267427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24615 ⟨267427, by decide⟩ :=
  accepted_of_selected 12 24615 ⟨267427, by decide⟩ ⟨12, 2, 0, 267427, 24615, 4065, 65536⟩
    (by decide) selected_cut_09690

theorem unmarked_context_11_6153_267428 : frontier 10 ⟨267428, by decide⟩
    (prefixCache 11 6153) (prefixPartial 11 6153) = false := by
  decide +kernel

theorem node_context_11_6153_267428 : EJMOriginalGlobalDAGData.nodes 10 ⟨267428, by decide⟩ =
    .split (coordinate 11) (![⟨267268, by decide⟩,⟨267314, by decide⟩,⟨267370, by decide⟩,⟨267427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6153_267428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6153 ⟨267428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6153
    ⟨267428, by decide⟩ (by decide) (![⟨267268, by decide⟩,⟨267314, by decide⟩,⟨267370, by decide⟩,⟨267427, by decide⟩]) unmarked_context_11_6153_267428 node_context_11_6153_267428
  intro a
  fin_cases a
  · exact context_12_24612_267268
  · exact context_12_24613_267314
  · exact context_12_24614_267370
  · exact context_12_24615_267427

theorem selected_cut_09691 : selected 9 ⟨267475, by decide⟩
    (prefixPartial 12 24616) = some ⟨12, 2, 0, 267475, 24616, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_24616_267475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24616 ⟨267475, by decide⟩ :=
  accepted_of_selected 12 24616 ⟨267475, by decide⟩ ⟨12, 2, 0, 267475, 24616, 3381, 65536⟩
    (by decide) selected_cut_09691

theorem selected_cut_09692 : selected 9 ⟨267525, by decide⟩
    (prefixPartial 12 24617) = some ⟨12, 2, 0, 267525, 24617, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_24617_267525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24617 ⟨267525, by decide⟩ :=
  accepted_of_selected 12 24617 ⟨267525, by decide⟩ ⟨12, 2, 0, 267525, 24617, 3777, 65536⟩
    (by decide) selected_cut_09692

theorem selected_cut_09693 : selected 9 ⟨267574, by decide⟩
    (prefixPartial 12 24618) = some ⟨12, 2, 0, 267574, 24618, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_24618_267574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24618 ⟨267574, by decide⟩ :=
  accepted_of_selected 12 24618 ⟨267574, by decide⟩ ⟨12, 2, 0, 267574, 24618, 3565, 65536⟩
    (by decide) selected_cut_09693

theorem selected_cut_09694 : selected 9 ⟨267622, by decide⟩
    (prefixPartial 12 24619) = some ⟨12, 2, 0, 267622, 24619, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_24619_267622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24619 ⟨267622, by decide⟩ :=
  accepted_of_selected 12 24619 ⟨267622, by decide⟩ ⟨12, 2, 0, 267622, 24619, 3809, 65536⟩
    (by decide) selected_cut_09694

theorem unmarked_context_11_6154_267623 : frontier 10 ⟨267623, by decide⟩
    (prefixCache 11 6154) (prefixPartial 11 6154) = false := by
  decide +kernel

theorem node_context_11_6154_267623 : EJMOriginalGlobalDAGData.nodes 10 ⟨267623, by decide⟩ =
    .split (coordinate 11) (![⟨267475, by decide⟩,⟨267525, by decide⟩,⟨267574, by decide⟩,⟨267622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6154_267623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6154 ⟨267623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6154
    ⟨267623, by decide⟩ (by decide) (![⟨267475, by decide⟩,⟨267525, by decide⟩,⟨267574, by decide⟩,⟨267622, by decide⟩]) unmarked_context_11_6154_267623 node_context_11_6154_267623
  intro a
  fin_cases a
  · exact context_12_24616_267475
  · exact context_12_24617_267525
  · exact context_12_24618_267574
  · exact context_12_24619_267622

theorem selected_cut_09695 : selected 9 ⟨267665, by decide⟩
    (prefixPartial 12 24620) = some ⟨12, 2, 0, 267665, 24620, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_24620_267665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24620 ⟨267665, by decide⟩ :=
  accepted_of_selected 12 24620 ⟨267665, by decide⟩ ⟨12, 2, 0, 267665, 24620, 3293, 65536⟩
    (by decide) selected_cut_09695

theorem selected_cut_09696 : selected 9 ⟨267719, by decide⟩
    (prefixPartial 12 24621) = some ⟨12, 2, 0, 267719, 24621, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_24621_267719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24621 ⟨267719, by decide⟩ :=
  accepted_of_selected 12 24621 ⟨267719, by decide⟩ ⟨12, 2, 0, 267719, 24621, 4045, 65536⟩
    (by decide) selected_cut_09696

theorem selected_cut_09697 : selected 9 ⟨267772, by decide⟩
    (prefixPartial 12 24622) = some ⟨12, 2, 0, 267772, 24622, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_24622_267772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24622 ⟨267772, by decide⟩ :=
  accepted_of_selected 12 24622 ⟨267772, by decide⟩ ⟨12, 2, 0, 267772, 24622, 4085, 65536⟩
    (by decide) selected_cut_09697

theorem selected_cut_09698 : selected 9 ⟨267817, by decide⟩
    (prefixPartial 12 24623) = some ⟨12, 2, 0, 267817, 24623, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_24623_267817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24623 ⟨267817, by decide⟩ :=
  accepted_of_selected 12 24623 ⟨267817, by decide⟩ ⟨12, 2, 0, 267817, 24623, 3729, 65536⟩
    (by decide) selected_cut_09698

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
