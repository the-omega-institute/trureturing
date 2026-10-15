/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover121
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_1613_313208 : frontier 11 ⟨313208, by decide⟩
    (prefixCache 10 1613) (prefixPartial 10 1613) = false := by
  decide +kernel

theorem node_context_10_1613_313208 : EJMOriginalGlobalDAGData.nodes 11 ⟨313208, by decide⟩ =
    .split (coordinate 10) (![⟨313136, by decide⟩,⟨313166, by decide⟩,⟨313189, by decide⟩,⟨313207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1613_313208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1613 ⟨313208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1613
    ⟨313208, by decide⟩ (by decide) (![⟨313136, by decide⟩,⟨313166, by decide⟩,⟨313189, by decide⟩,⟨313207, by decide⟩]) unmarked_context_10_1613_313208 node_context_10_1613_313208
  intro a
  fin_cases a
  · exact context_11_6452_313136
  · exact context_11_6453_313166
  · exact context_11_6454_313189
  · exact context_11_6455_313207

theorem selected_cut_11715 : selected 10 ⟨313228, by decide⟩
    (prefixPartial 11 6456) = some ⟨11, 2, 0, 313228, 6456, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_6456_313228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6456 ⟨313228, by decide⟩ :=
  accepted_of_selected 11 6456 ⟨313228, by decide⟩ ⟨11, 2, 0, 313228, 6456, 1677, 262144⟩
    (by decide) selected_cut_11715

theorem selected_cut_11716 : selected 10 ⟨313241, by decide⟩
    (prefixPartial 11 6457) = some ⟨11, 2, 0, 313241, 6457, 1185, 262144⟩ := by
  decide +kernel

theorem context_11_6457_313241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6457 ⟨313241, by decide⟩ :=
  accepted_of_selected 11 6457 ⟨313241, by decide⟩ ⟨11, 2, 0, 313241, 6457, 1185, 262144⟩
    (by decide) selected_cut_11716

theorem selected_cut_11717 : selected 10 ⟨313256, by decide⟩
    (prefixPartial 11 6458) = some ⟨11, 2, 0, 313256, 6458, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_6458_313256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6458 ⟨313256, by decide⟩ :=
  accepted_of_selected 11 6458 ⟨313256, by decide⟩ ⟨11, 2, 0, 313256, 6458, 1069, 262144⟩
    (by decide) selected_cut_11717

theorem selected_cut_11718 : selected 10 ⟨313273, by decide⟩
    (prefixPartial 11 6459) = some ⟨11, 2, 0, 313273, 6459, 861, 262144⟩ := by
  decide +kernel

theorem context_11_6459_313273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6459 ⟨313273, by decide⟩ :=
  accepted_of_selected 11 6459 ⟨313273, by decide⟩ ⟨11, 2, 0, 313273, 6459, 861, 262144⟩
    (by decide) selected_cut_11718

theorem unmarked_context_10_1614_313274 : frontier 11 ⟨313274, by decide⟩
    (prefixCache 10 1614) (prefixPartial 10 1614) = false := by
  decide +kernel

theorem node_context_10_1614_313274 : EJMOriginalGlobalDAGData.nodes 11 ⟨313274, by decide⟩ =
    .split (coordinate 10) (![⟨313228, by decide⟩,⟨313241, by decide⟩,⟨313256, by decide⟩,⟨313273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1614_313274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1614 ⟨313274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1614
    ⟨313274, by decide⟩ (by decide) (![⟨313228, by decide⟩,⟨313241, by decide⟩,⟨313256, by decide⟩,⟨313273, by decide⟩]) unmarked_context_10_1614_313274 node_context_10_1614_313274
  intro a
  fin_cases a
  · exact context_11_6456_313228
  · exact context_11_6457_313241
  · exact context_11_6458_313256
  · exact context_11_6459_313273

theorem selected_cut_11719 : selected 11 ⟨313301, by decide⟩
    (prefixPartial 10 1615) = some ⟨10, 2, 0, 313301, 1615, 1633, 1048576⟩ := by
  decide +kernel

theorem context_10_1615_313301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1615 ⟨313301, by decide⟩ :=
  accepted_of_selected 10 1615 ⟨313301, by decide⟩ ⟨10, 2, 0, 313301, 1615, 1633, 1048576⟩
    (by decide) selected_cut_11719

theorem unmarked_context_9_403_313302 : frontier 12 ⟨313302, by decide⟩
    (prefixCache 9 403) (prefixPartial 9 403) = false := by
  decide +kernel

theorem node_context_9_403_313302 : EJMOriginalGlobalDAGData.nodes 12 ⟨313302, by decide⟩ =
    .split (coordinate 9) (![⟨313105, by decide⟩,⟨313208, by decide⟩,⟨313274, by decide⟩,⟨313301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_403_313302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 403 ⟨313302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 403
    ⟨313302, by decide⟩ (by decide) (![⟨313105, by decide⟩,⟨313208, by decide⟩,⟨313274, by decide⟩,⟨313301, by decide⟩]) unmarked_context_9_403_313302 node_context_9_403_313302
  intro a
  fin_cases a
  · exact context_10_1612_313105
  · exact context_10_1613_313208
  · exact context_10_1614_313274
  · exact context_10_1615_313301

theorem unmarked_context_8_100_313303 : frontier 13 ⟨313303, by decide⟩
    (prefixCache 8 100) (prefixPartial 8 100) = false := by
  decide +kernel

theorem node_context_8_100_313303 : EJMOriginalGlobalDAGData.nodes 13 ⟨313303, by decide⟩ =
    .split (coordinate 8) (![⟨307380, by decide⟩,⟨311259, by decide⟩,⟨312926, by decide⟩,⟨313302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_100_313303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 100 ⟨313303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 100
    ⟨313303, by decide⟩ (by decide) (![⟨307380, by decide⟩,⟨311259, by decide⟩,⟨312926, by decide⟩,⟨313302, by decide⟩]) unmarked_context_8_100_313303 node_context_8_100_313303
  intro a
  fin_cases a
  · exact context_9_400_307380
  · exact context_9_401_311259
  · exact context_9_402_312926
  · exact context_9_403_313302

theorem selected_cut_11720 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 25856) = some ⟨12, 1, 0, 34034, 25856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25856_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25856 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 25856 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 25856, 1, 65536⟩
    (by decide) selected_cut_11720

theorem selected_cut_11721 : selected 9 ⟨301653, by decide⟩
    (prefixPartial 12 25857) = some ⟨12, 1, 0, 301653, 25857, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25857_301653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25857 ⟨301653, by decide⟩ :=
  accepted_of_selected 12 25857 ⟨301653, by decide⟩ ⟨12, 1, 0, 301653, 25857, 1, 65536⟩
    (by decide) selected_cut_11721

theorem selected_cut_11722 : selected 7 ⟨313331, by decide⟩
    (prefixPartial 14 413728) = some ⟨14, 2, 0, 313331, 413728, 873, 4096⟩ := by
  decide +kernel

theorem context_14_413728_313331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413728 ⟨313331, by decide⟩ :=
  accepted_of_selected 14 413728 ⟨313331, by decide⟩ ⟨14, 2, 0, 313331, 413728, 873, 4096⟩
    (by decide) selected_cut_11722

theorem selected_cut_11723 : selected 7 ⟨313348, by decide⟩
    (prefixPartial 14 413729) = some ⟨14, 2, 0, 313348, 413729, 969, 4096⟩ := by
  decide +kernel

theorem context_14_413729_313348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413729 ⟨313348, by decide⟩ :=
  accepted_of_selected 14 413729 ⟨313348, by decide⟩ ⟨14, 2, 0, 313348, 413729, 969, 4096⟩
    (by decide) selected_cut_11723

theorem selected_cut_11724 : selected 7 ⟨313381, by decide⟩
    (prefixPartial 14 413730) = some ⟨14, 2, 0, 313381, 413730, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_413730_313381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413730 ⟨313381, by decide⟩ :=
  accepted_of_selected 14 413730 ⟨313381, by decide⟩ ⟨14, 2, 0, 313381, 413730, 1237, 4096⟩
    (by decide) selected_cut_11724

theorem selected_cut_11725 : selected 7 ⟨313406, by decide⟩
    (prefixPartial 14 413731) = some ⟨14, 2, 0, 313406, 413731, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_413731_313406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413731 ⟨313406, by decide⟩ :=
  accepted_of_selected 14 413731 ⟨313406, by decide⟩ ⟨14, 2, 0, 313406, 413731, 1081, 4096⟩
    (by decide) selected_cut_11725

theorem unmarked_context_13_103432_313407 : frontier 8 ⟨313407, by decide⟩
    (prefixCache 13 103432) (prefixPartial 13 103432) = false := by
  decide +kernel

theorem node_context_13_103432_313407 : EJMOriginalGlobalDAGData.nodes 8 ⟨313407, by decide⟩ =
    .split (coordinate 13) (![⟨313331, by decide⟩,⟨313348, by decide⟩,⟨313381, by decide⟩,⟨313406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103432_313407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103432 ⟨313407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103432
    ⟨313407, by decide⟩ (by decide) (![⟨313331, by decide⟩,⟨313348, by decide⟩,⟨313381, by decide⟩,⟨313406, by decide⟩]) unmarked_context_13_103432_313407 node_context_13_103432_313407
  intro a
  fin_cases a
  · exact context_14_413728_313331
  · exact context_14_413729_313348
  · exact context_14_413730_313381
  · exact context_14_413731_313406

theorem selected_cut_11726 : selected 8 ⟨313477, by decide⟩
    (prefixPartial 13 103433) = some ⟨13, 2, 0, 313477, 103433, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_103433_313477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103433 ⟨313477, by decide⟩ :=
  accepted_of_selected 13 103433 ⟨313477, by decide⟩ ⟨13, 2, 0, 313477, 103433, 2077, 16384⟩
    (by decide) selected_cut_11726

theorem selected_cut_11727 : selected 8 ⟨313511, by decide⟩
    (prefixPartial 13 103434) = some ⟨13, 2, 0, 313511, 103434, 817, 16384⟩ := by
  decide +kernel

theorem context_13_103434_313511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103434 ⟨313511, by decide⟩ :=
  accepted_of_selected 13 103434 ⟨313511, by decide⟩ ⟨13, 2, 0, 313511, 103434, 817, 16384⟩
    (by decide) selected_cut_11727

theorem selected_cut_11728 : selected 8 ⟨313521, by decide⟩
    (prefixPartial 13 103435) = some ⟨13, 2, 0, 313521, 103435, 161, 16384⟩ := by
  decide +kernel

theorem context_13_103435_313521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103435 ⟨313521, by decide⟩ :=
  accepted_of_selected 13 103435 ⟨313521, by decide⟩ ⟨13, 2, 0, 313521, 103435, 161, 16384⟩
    (by decide) selected_cut_11728

theorem unmarked_context_12_25858_313522 : frontier 9 ⟨313522, by decide⟩
    (prefixCache 12 25858) (prefixPartial 12 25858) = false := by
  decide +kernel

theorem node_context_12_25858_313522 : EJMOriginalGlobalDAGData.nodes 9 ⟨313522, by decide⟩ =
    .split (coordinate 12) (![⟨313407, by decide⟩,⟨313477, by decide⟩,⟨313511, by decide⟩,⟨313521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25858_313522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25858 ⟨313522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25858
    ⟨313522, by decide⟩ (by decide) (![⟨313407, by decide⟩,⟨313477, by decide⟩,⟨313511, by decide⟩,⟨313521, by decide⟩]) unmarked_context_12_25858_313522 node_context_12_25858_313522
  intro a
  fin_cases a
  · exact context_13_103432_313407
  · exact context_13_103433_313477
  · exact context_13_103434_313511
  · exact context_13_103435_313521

theorem selected_cut_11729 : selected 7 ⟨313554, by decide⟩
    (prefixPartial 14 413744) = some ⟨14, 2, 0, 313554, 413744, 909, 4096⟩ := by
  decide +kernel

theorem context_14_413744_313554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413744 ⟨313554, by decide⟩ :=
  accepted_of_selected 14 413744 ⟨313554, by decide⟩ ⟨14, 2, 0, 313554, 413744, 909, 4096⟩
    (by decide) selected_cut_11729

theorem selected_cut_11730 : selected 7 ⟨313573, by decide⟩
    (prefixPartial 14 413745) = some ⟨14, 2, 0, 313573, 413745, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_413745_313573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413745 ⟨313573, by decide⟩ :=
  accepted_of_selected 14 413745 ⟨313573, by decide⟩ ⟨14, 2, 0, 313573, 413745, 1113, 4096⟩
    (by decide) selected_cut_11730

theorem selected_cut_11731 : selected 7 ⟨313601, by decide⟩
    (prefixPartial 14 413746) = some ⟨14, 2, 0, 313601, 413746, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_413746_313601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413746 ⟨313601, by decide⟩ :=
  accepted_of_selected 14 413746 ⟨313601, by decide⟩ ⟨14, 2, 0, 313601, 413746, 1177, 4096⟩
    (by decide) selected_cut_11731

theorem selected_cut_11732 : selected 7 ⟨313631, by decide⟩
    (prefixPartial 14 413747) = some ⟨14, 2, 0, 313631, 413747, 1233, 4096⟩ := by
  decide +kernel

theorem context_14_413747_313631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413747 ⟨313631, by decide⟩ :=
  accepted_of_selected 14 413747 ⟨313631, by decide⟩ ⟨14, 2, 0, 313631, 413747, 1233, 4096⟩
    (by decide) selected_cut_11732

theorem unmarked_context_13_103436_313632 : frontier 8 ⟨313632, by decide⟩
    (prefixCache 13 103436) (prefixPartial 13 103436) = false := by
  decide +kernel

theorem node_context_13_103436_313632 : EJMOriginalGlobalDAGData.nodes 8 ⟨313632, by decide⟩ =
    .split (coordinate 13) (![⟨313554, by decide⟩,⟨313573, by decide⟩,⟨313601, by decide⟩,⟨313631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103436_313632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103436 ⟨313632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103436
    ⟨313632, by decide⟩ (by decide) (![⟨313554, by decide⟩,⟨313573, by decide⟩,⟨313601, by decide⟩,⟨313631, by decide⟩]) unmarked_context_13_103436_313632 node_context_13_103436_313632
  intro a
  fin_cases a
  · exact context_14_413744_313554
  · exact context_14_413745_313573
  · exact context_14_413746_313601
  · exact context_14_413747_313631

theorem selected_cut_11733 : selected 8 ⟨313704, by decide⟩
    (prefixPartial 13 103437) = some ⟨13, 2, 0, 313704, 103437, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_103437_313704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103437 ⟨313704, by decide⟩ :=
  accepted_of_selected 13 103437 ⟨313704, by decide⟩ ⟨13, 2, 0, 313704, 103437, 2097, 16384⟩
    (by decide) selected_cut_11733

theorem selected_cut_11734 : selected 8 ⟨313745, by decide⟩
    (prefixPartial 13 103438) = some ⟨13, 2, 0, 313745, 103438, 885, 16384⟩ := by
  decide +kernel

theorem context_13_103438_313745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103438 ⟨313745, by decide⟩ :=
  accepted_of_selected 13 103438 ⟨313745, by decide⟩ ⟨13, 2, 0, 313745, 103438, 885, 16384⟩
    (by decide) selected_cut_11734

theorem selected_cut_11735 : selected 8 ⟨313759, by decide⟩
    (prefixPartial 13 103439) = some ⟨13, 2, 0, 313759, 103439, 177, 16384⟩ := by
  decide +kernel

theorem context_13_103439_313759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103439 ⟨313759, by decide⟩ :=
  accepted_of_selected 13 103439 ⟨313759, by decide⟩ ⟨13, 2, 0, 313759, 103439, 177, 16384⟩
    (by decide) selected_cut_11735

theorem unmarked_context_12_25859_313760 : frontier 9 ⟨313760, by decide⟩
    (prefixCache 12 25859) (prefixPartial 12 25859) = false := by
  decide +kernel

theorem node_context_12_25859_313760 : EJMOriginalGlobalDAGData.nodes 9 ⟨313760, by decide⟩ =
    .split (coordinate 12) (![⟨313632, by decide⟩,⟨313704, by decide⟩,⟨313745, by decide⟩,⟨313759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25859_313760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25859 ⟨313760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25859
    ⟨313760, by decide⟩ (by decide) (![⟨313632, by decide⟩,⟨313704, by decide⟩,⟨313745, by decide⟩,⟨313759, by decide⟩]) unmarked_context_12_25859_313760 node_context_12_25859_313760
  intro a
  fin_cases a
  · exact context_13_103436_313632
  · exact context_13_103437_313704
  · exact context_13_103438_313745
  · exact context_13_103439_313759

theorem unmarked_context_11_6464_313761 : frontier 10 ⟨313761, by decide⟩
    (prefixCache 11 6464) (prefixPartial 11 6464) = false := by
  decide +kernel

theorem node_context_11_6464_313761 : EJMOriginalGlobalDAGData.nodes 10 ⟨313761, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨313522, by decide⟩,⟨313760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6464_313761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6464 ⟨313761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6464
    ⟨313761, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨313522, by decide⟩,⟨313760, by decide⟩]) unmarked_context_11_6464_313761 node_context_11_6464_313761
  intro a
  fin_cases a
  · exact context_12_25856_34034
  · exact context_12_25857_301653
  · exact context_12_25858_313522
  · exact context_12_25859_313760

theorem selected_cut_11736 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 25860) = some ⟨12, 1, 0, 34034, 25860, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25860_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25860 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 25860 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 25860, 1, 65536⟩
    (by decide) selected_cut_11736

theorem selected_cut_11737 : selected 7 ⟨313822, by decide⟩
    (prefixPartial 14 413776) = some ⟨14, 2, 0, 313822, 413776, 2353, 4096⟩ := by
  decide +kernel

theorem context_14_413776_313822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413776 ⟨313822, by decide⟩ :=
  accepted_of_selected 14 413776 ⟨313822, by decide⟩ ⟨14, 2, 0, 313822, 413776, 2353, 4096⟩
    (by decide) selected_cut_11737

theorem selected_cut_11738 : selected 7 ⟨313836, by decide⟩
    (prefixPartial 14 413777) = some ⟨14, 2, 0, 313836, 413777, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_413777_313836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413777 ⟨313836, by decide⟩ :=
  accepted_of_selected 14 413777 ⟨313836, by decide⟩ ⟨14, 2, 0, 313836, 413777, 1241, 4096⟩
    (by decide) selected_cut_11738

theorem selected_cut_11739 : selected 7 ⟨313855, by decide⟩
    (prefixPartial 14 413778) = some ⟨14, 2, 0, 313855, 413778, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_413778_313855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413778 ⟨313855, by decide⟩ :=
  accepted_of_selected 14 413778 ⟨313855, by decide⟩ ⟨14, 2, 0, 313855, 413778, 1301, 4096⟩
    (by decide) selected_cut_11739

theorem selected_cut_11740 : selected 7 ⟨313881, by decide⟩
    (prefixPartial 14 413779) = some ⟨14, 2, 0, 313881, 413779, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_413779_313881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413779 ⟨313881, by decide⟩ :=
  accepted_of_selected 14 413779 ⟨313881, by decide⟩ ⟨14, 2, 0, 313881, 413779, 1457, 4096⟩
    (by decide) selected_cut_11740

theorem unmarked_context_13_103444_313882 : frontier 8 ⟨313882, by decide⟩
    (prefixCache 13 103444) (prefixPartial 13 103444) = false := by
  decide +kernel

theorem node_context_13_103444_313882 : EJMOriginalGlobalDAGData.nodes 8 ⟨313882, by decide⟩ =
    .split (coordinate 13) (![⟨313822, by decide⟩,⟨313836, by decide⟩,⟨313855, by decide⟩,⟨313881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103444_313882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103444 ⟨313882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103444
    ⟨313882, by decide⟩ (by decide) (![⟨313822, by decide⟩,⟨313836, by decide⟩,⟨313855, by decide⟩,⟨313881, by decide⟩]) unmarked_context_13_103444_313882 node_context_13_103444_313882
  intro a
  fin_cases a
  · exact context_14_413776_313822
  · exact context_14_413777_313836
  · exact context_14_413778_313855
  · exact context_14_413779_313881

theorem selected_cut_11741 : selected 7 ⟨313926, by decide⟩
    (prefixPartial 14 413780) = some ⟨14, 2, 0, 313926, 413780, 1593, 4096⟩ := by
  decide +kernel

theorem context_14_413780_313926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413780 ⟨313926, by decide⟩ :=
  accepted_of_selected 14 413780 ⟨313926, by decide⟩ ⟨14, 2, 0, 313926, 413780, 1593, 4096⟩
    (by decide) selected_cut_11741

theorem selected_cut_11742 : selected 7 ⟨313944, by decide⟩
    (prefixPartial 14 413781) = some ⟨14, 2, 0, 313944, 413781, 677, 4096⟩ := by
  decide +kernel

theorem context_14_413781_313944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413781 ⟨313944, by decide⟩ :=
  accepted_of_selected 14 413781 ⟨313944, by decide⟩ ⟨14, 2, 0, 313944, 413781, 677, 4096⟩
    (by decide) selected_cut_11742

theorem selected_cut_11743 : selected 7 ⟨313993, by decide⟩
    (prefixPartial 14 413782) = some ⟨14, 2, 0, 313993, 413782, 1801, 4096⟩ := by
  decide +kernel

theorem context_14_413782_313993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413782 ⟨313993, by decide⟩ :=
  accepted_of_selected 14 413782 ⟨313993, by decide⟩ ⟨14, 2, 0, 313993, 413782, 1801, 4096⟩
    (by decide) selected_cut_11743

theorem selected_cut_11744 : selected 7 ⟨314033, by decide⟩
    (prefixPartial 14 413783) = some ⟨14, 2, 0, 314033, 413783, 1713, 4096⟩ := by
  decide +kernel

theorem context_14_413783_314033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413783 ⟨314033, by decide⟩ :=
  accepted_of_selected 14 413783 ⟨314033, by decide⟩ ⟨14, 2, 0, 314033, 413783, 1713, 4096⟩
    (by decide) selected_cut_11744

theorem unmarked_context_13_103445_314034 : frontier 8 ⟨314034, by decide⟩
    (prefixCache 13 103445) (prefixPartial 13 103445) = false := by
  decide +kernel

theorem node_context_13_103445_314034 : EJMOriginalGlobalDAGData.nodes 8 ⟨314034, by decide⟩ =
    .split (coordinate 13) (![⟨313926, by decide⟩,⟨313944, by decide⟩,⟨313993, by decide⟩,⟨314033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103445_314034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103445 ⟨314034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103445
    ⟨314034, by decide⟩ (by decide) (![⟨313926, by decide⟩,⟨313944, by decide⟩,⟨313993, by decide⟩,⟨314033, by decide⟩]) unmarked_context_13_103445_314034 node_context_13_103445_314034
  intro a
  fin_cases a
  · exact context_14_413780_313926
  · exact context_14_413781_313944
  · exact context_14_413782_313993
  · exact context_14_413783_314033

theorem selected_cut_11745 : selected 8 ⟨314145, by decide⟩
    (prefixPartial 13 103446) = some ⟨13, 2, 0, 314145, 103446, 3621, 16384⟩ := by
  decide +kernel

theorem context_13_103446_314145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103446 ⟨314145, by decide⟩ :=
  accepted_of_selected 13 103446 ⟨314145, by decide⟩ ⟨13, 2, 0, 314145, 103446, 3621, 16384⟩
    (by decide) selected_cut_11745

theorem selected_cut_11746 : selected 8 ⟨314182, by decide⟩
    (prefixPartial 13 103447) = some ⟨13, 2, 0, 314182, 103447, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_103447_314182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103447 ⟨314182, by decide⟩ :=
  accepted_of_selected 13 103447 ⟨314182, by decide⟩ ⟨13, 2, 0, 314182, 103447, 1561, 16384⟩
    (by decide) selected_cut_11746

theorem unmarked_context_12_25861_314183 : frontier 9 ⟨314183, by decide⟩
    (prefixCache 12 25861) (prefixPartial 12 25861) = false := by
  decide +kernel

theorem node_context_12_25861_314183 : EJMOriginalGlobalDAGData.nodes 9 ⟨314183, by decide⟩ =
    .split (coordinate 12) (![⟨313882, by decide⟩,⟨314034, by decide⟩,⟨314145, by decide⟩,⟨314182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25861_314183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25861 ⟨314183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25861
    ⟨314183, by decide⟩ (by decide) (![⟨313882, by decide⟩,⟨314034, by decide⟩,⟨314145, by decide⟩,⟨314182, by decide⟩]) unmarked_context_12_25861_314183 node_context_12_25861_314183
  intro a
  fin_cases a
  · exact context_13_103444_313882
  · exact context_13_103445_314034
  · exact context_13_103446_314145
  · exact context_13_103447_314182

theorem selected_cut_11747 : selected 8 ⟨314239, by decide⟩
    (prefixPartial 13 103448) = some ⟨13, 2, 0, 314239, 103448, 4001, 16384⟩ := by
  decide +kernel

theorem context_13_103448_314239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103448 ⟨314239, by decide⟩ :=
  accepted_of_selected 13 103448 ⟨314239, by decide⟩ ⟨13, 2, 0, 314239, 103448, 4001, 16384⟩
    (by decide) selected_cut_11747

theorem selected_cut_11748 : selected 8 ⟨314292, by decide⟩
    (prefixPartial 13 103449) = some ⟨13, 2, 0, 314292, 103449, 3293, 16384⟩ := by
  decide +kernel

theorem context_13_103449_314292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103449 ⟨314292, by decide⟩ :=
  accepted_of_selected 13 103449 ⟨314292, by decide⟩ ⟨13, 2, 0, 314292, 103449, 3293, 16384⟩
    (by decide) selected_cut_11748

theorem selected_cut_11749 : selected 8 ⟨314332, by decide⟩
    (prefixPartial 13 103450) = some ⟨13, 2, 0, 314332, 103450, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_103450_314332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103450 ⟨314332, by decide⟩ :=
  accepted_of_selected 13 103450 ⟨314332, by decide⟩ ⟨13, 2, 0, 314332, 103450, 2649, 16384⟩
    (by decide) selected_cut_11749

theorem selected_cut_11750 : selected 8 ⟨314347, by decide⟩
    (prefixPartial 13 103451) = some ⟨13, 2, 0, 314347, 103451, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_103451_314347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103451 ⟨314347, by decide⟩ :=
  accepted_of_selected 13 103451 ⟨314347, by decide⟩ ⟨13, 2, 0, 314347, 103451, 1301, 16384⟩
    (by decide) selected_cut_11750

theorem unmarked_context_12_25862_314348 : frontier 9 ⟨314348, by decide⟩
    (prefixCache 12 25862) (prefixPartial 12 25862) = false := by
  decide +kernel

theorem node_context_12_25862_314348 : EJMOriginalGlobalDAGData.nodes 9 ⟨314348, by decide⟩ =
    .split (coordinate 12) (![⟨314239, by decide⟩,⟨314292, by decide⟩,⟨314332, by decide⟩,⟨314347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25862_314348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25862 ⟨314348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25862
    ⟨314348, by decide⟩ (by decide) (![⟨314239, by decide⟩,⟨314292, by decide⟩,⟨314332, by decide⟩,⟨314347, by decide⟩]) unmarked_context_12_25862_314348 node_context_12_25862_314348
  intro a
  fin_cases a
  · exact context_13_103448_314239
  · exact context_13_103449_314292
  · exact context_13_103450_314332
  · exact context_13_103451_314347

theorem selected_cut_11751 : selected 7 ⟨314366, by decide⟩
    (prefixPartial 14 413808) = some ⟨14, 2, 0, 314366, 413808, 881, 4096⟩ := by
  decide +kernel

theorem context_14_413808_314366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413808 ⟨314366, by decide⟩ :=
  accepted_of_selected 14 413808 ⟨314366, by decide⟩ ⟨14, 2, 0, 314366, 413808, 881, 4096⟩
    (by decide) selected_cut_11751

theorem selected_cut_11752 : selected 7 ⟨314379, by decide⟩
    (prefixPartial 14 413809) = some ⟨14, 2, 0, 314379, 413809, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_413809_314379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413809 ⟨314379, by decide⟩ :=
  accepted_of_selected 14 413809 ⟨314379, by decide⟩ ⟨14, 2, 0, 314379, 413809, 1009, 4096⟩
    (by decide) selected_cut_11752

theorem selected_cut_11753 : selected 7 ⟨314393, by decide⟩
    (prefixPartial 14 413810) = some ⟨14, 2, 0, 314393, 413810, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_413810_314393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413810 ⟨314393, by decide⟩ :=
  accepted_of_selected 14 413810 ⟨314393, by decide⟩ ⟨14, 2, 0, 314393, 413810, 1089, 4096⟩
    (by decide) selected_cut_11753

theorem selected_cut_11754 : selected 7 ⟨314407, by decide⟩
    (prefixPartial 14 413811) = some ⟨14, 2, 0, 314407, 413811, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_413811_314407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413811 ⟨314407, by decide⟩ :=
  accepted_of_selected 14 413811 ⟨314407, by decide⟩ ⟨14, 2, 0, 314407, 413811, 1153, 4096⟩
    (by decide) selected_cut_11754

theorem unmarked_context_13_103452_314408 : frontier 8 ⟨314408, by decide⟩
    (prefixCache 13 103452) (prefixPartial 13 103452) = false := by
  decide +kernel

theorem node_context_13_103452_314408 : EJMOriginalGlobalDAGData.nodes 8 ⟨314408, by decide⟩ =
    .split (coordinate 13) (![⟨314366, by decide⟩,⟨314379, by decide⟩,⟨314393, by decide⟩,⟨314407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103452_314408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103452 ⟨314408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103452
    ⟨314408, by decide⟩ (by decide) (![⟨314366, by decide⟩,⟨314379, by decide⟩,⟨314393, by decide⟩,⟨314407, by decide⟩]) unmarked_context_13_103452_314408 node_context_13_103452_314408
  intro a
  fin_cases a
  · exact context_14_413808_314366
  · exact context_14_413809_314379
  · exact context_14_413810_314393
  · exact context_14_413811_314407

theorem selected_cut_11755 : selected 8 ⟨314464, by decide⟩
    (prefixPartial 13 103453) = some ⟨13, 2, 0, 314464, 103453, 3681, 16384⟩ := by
  decide +kernel

theorem context_13_103453_314464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103453 ⟨314464, by decide⟩ :=
  accepted_of_selected 13 103453 ⟨314464, by decide⟩ ⟨13, 2, 0, 314464, 103453, 3681, 16384⟩
    (by decide) selected_cut_11755

theorem selected_cut_11756 : selected 8 ⟨314508, by decide⟩
    (prefixPartial 13 103454) = some ⟨13, 2, 0, 314508, 103454, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_103454_314508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103454 ⟨314508, by decide⟩ :=
  accepted_of_selected 13 103454 ⟨314508, by decide⟩ ⟨13, 2, 0, 314508, 103454, 2773, 16384⟩
    (by decide) selected_cut_11756

theorem selected_cut_11757 : selected 8 ⟨314524, by decide⟩
    (prefixPartial 13 103455) = some ⟨13, 2, 0, 314524, 103455, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_103455_314524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103455 ⟨314524, by decide⟩ :=
  accepted_of_selected 13 103455 ⟨314524, by decide⟩ ⟨13, 2, 0, 314524, 103455, 1281, 16384⟩
    (by decide) selected_cut_11757

theorem unmarked_context_12_25863_314525 : frontier 9 ⟨314525, by decide⟩
    (prefixCache 12 25863) (prefixPartial 12 25863) = false := by
  decide +kernel

theorem node_context_12_25863_314525 : EJMOriginalGlobalDAGData.nodes 9 ⟨314525, by decide⟩ =
    .split (coordinate 12) (![⟨314408, by decide⟩,⟨314464, by decide⟩,⟨314508, by decide⟩,⟨314524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25863_314525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25863 ⟨314525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25863
    ⟨314525, by decide⟩ (by decide) (![⟨314408, by decide⟩,⟨314464, by decide⟩,⟨314508, by decide⟩,⟨314524, by decide⟩]) unmarked_context_12_25863_314525 node_context_12_25863_314525
  intro a
  fin_cases a
  · exact context_13_103452_314408
  · exact context_13_103453_314464
  · exact context_13_103454_314508
  · exact context_13_103455_314524

theorem unmarked_context_11_6465_314526 : frontier 10 ⟨314526, by decide⟩
    (prefixCache 11 6465) (prefixPartial 11 6465) = false := by
  decide +kernel

theorem node_context_11_6465_314526 : EJMOriginalGlobalDAGData.nodes 10 ⟨314526, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨314183, by decide⟩,⟨314348, by decide⟩,⟨314525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6465_314526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6465 ⟨314526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6465
    ⟨314526, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨314183, by decide⟩,⟨314348, by decide⟩,⟨314525, by decide⟩]) unmarked_context_11_6465_314526 node_context_11_6465_314526
  intro a
  fin_cases a
  · exact context_12_25860_34034
  · exact context_12_25861_314183
  · exact context_12_25862_314348
  · exact context_12_25863_314525

theorem selected_cut_11758 : selected 8 ⟨314589, by decide⟩
    (prefixPartial 13 103456) = some ⟨13, 2, 0, 314589, 103456, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_103456_314589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103456 ⟨314589, by decide⟩ :=
  accepted_of_selected 13 103456 ⟨314589, by decide⟩ ⟨13, 2, 0, 314589, 103456, 3317, 16384⟩
    (by decide) selected_cut_11758

theorem selected_cut_11759 : selected 8 ⟨314664, by decide⟩
    (prefixPartial 13 103457) = some ⟨13, 2, 0, 314664, 103457, 4053, 16384⟩ := by
  decide +kernel

theorem context_13_103457_314664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103457 ⟨314664, by decide⟩ :=
  accepted_of_selected 13 103457 ⟨314664, by decide⟩ ⟨13, 2, 0, 314664, 103457, 4053, 16384⟩
    (by decide) selected_cut_11759

theorem selected_cut_11760 : selected 8 ⟨314710, by decide⟩
    (prefixPartial 13 103458) = some ⟨13, 2, 0, 314710, 103458, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_103458_314710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103458 ⟨314710, by decide⟩ :=
  accepted_of_selected 13 103458 ⟨314710, by decide⟩ ⟨13, 2, 0, 314710, 103458, 2605, 16384⟩
    (by decide) selected_cut_11760

theorem selected_cut_11761 : selected 8 ⟨314727, by decide⟩
    (prefixPartial 13 103459) = some ⟨13, 2, 0, 314727, 103459, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_103459_314727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103459 ⟨314727, by decide⟩ :=
  accepted_of_selected 13 103459 ⟨314727, by decide⟩ ⟨13, 2, 0, 314727, 103459, 1289, 16384⟩
    (by decide) selected_cut_11761

theorem unmarked_context_12_25864_314728 : frontier 9 ⟨314728, by decide⟩
    (prefixCache 12 25864) (prefixPartial 12 25864) = false := by
  decide +kernel

theorem node_context_12_25864_314728 : EJMOriginalGlobalDAGData.nodes 9 ⟨314728, by decide⟩ =
    .split (coordinate 12) (![⟨314589, by decide⟩,⟨314664, by decide⟩,⟨314710, by decide⟩,⟨314727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25864_314728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25864 ⟨314728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25864
    ⟨314728, by decide⟩ (by decide) (![⟨314589, by decide⟩,⟨314664, by decide⟩,⟨314710, by decide⟩,⟨314727, by decide⟩]) unmarked_context_12_25864_314728 node_context_12_25864_314728
  intro a
  fin_cases a
  · exact context_13_103456_314589
  · exact context_13_103457_314664
  · exact context_13_103458_314710
  · exact context_13_103459_314727

theorem selected_cut_11762 : selected 7 ⟨314758, by decide⟩
    (prefixPartial 14 413840) = some ⟨14, 2, 0, 314758, 413840, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_413840_314758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413840 ⟨314758, by decide⟩ :=
  accepted_of_selected 14 413840 ⟨314758, by decide⟩ ⟨14, 2, 0, 314758, 413840, 1137, 4096⟩
    (by decide) selected_cut_11762

theorem selected_cut_11763 : selected 7 ⟨314767, by decide⟩
    (prefixPartial 14 413841) = some ⟨14, 2, 0, 314767, 413841, 857, 4096⟩ := by
  decide +kernel

theorem context_14_413841_314767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413841 ⟨314767, by decide⟩ :=
  accepted_of_selected 14 413841 ⟨314767, by decide⟩ ⟨14, 2, 0, 314767, 413841, 857, 4096⟩
    (by decide) selected_cut_11763

theorem selected_cut_11764 : selected 7 ⟨314780, by decide⟩
    (prefixPartial 14 413842) = some ⟨14, 2, 0, 314780, 413842, 921, 4096⟩ := by
  decide +kernel

theorem context_14_413842_314780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413842 ⟨314780, by decide⟩ :=
  accepted_of_selected 14 413842 ⟨314780, by decide⟩ ⟨14, 2, 0, 314780, 413842, 921, 4096⟩
    (by decide) selected_cut_11764

theorem selected_cut_11765 : selected 7 ⟨314799, by decide⟩
    (prefixPartial 14 413843) = some ⟨14, 2, 0, 314799, 413843, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_413843_314799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413843 ⟨314799, by decide⟩ :=
  accepted_of_selected 14 413843 ⟨314799, by decide⟩ ⟨14, 2, 0, 314799, 413843, 1185, 4096⟩
    (by decide) selected_cut_11765

theorem unmarked_context_13_103460_314800 : frontier 8 ⟨314800, by decide⟩
    (prefixCache 13 103460) (prefixPartial 13 103460) = false := by
  decide +kernel

theorem node_context_13_103460_314800 : EJMOriginalGlobalDAGData.nodes 8 ⟨314800, by decide⟩ =
    .split (coordinate 13) (![⟨314758, by decide⟩,⟨314767, by decide⟩,⟨314780, by decide⟩,⟨314799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103460_314800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103460 ⟨314800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103460
    ⟨314800, by decide⟩ (by decide) (![⟨314758, by decide⟩,⟨314767, by decide⟩,⟨314780, by decide⟩,⟨314799, by decide⟩]) unmarked_context_13_103460_314800 node_context_13_103460_314800
  intro a
  fin_cases a
  · exact context_14_413840_314758
  · exact context_14_413841_314767
  · exact context_14_413842_314780
  · exact context_14_413843_314799

theorem selected_cut_11766 : selected 8 ⟨314858, by decide⟩
    (prefixPartial 13 103461) = some ⟨13, 2, 0, 314858, 103461, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_103461_314858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103461 ⟨314858, by decide⟩ :=
  accepted_of_selected 13 103461 ⟨314858, by decide⟩ ⟨13, 2, 0, 314858, 103461, 3421, 16384⟩
    (by decide) selected_cut_11766

theorem selected_cut_11767 : selected 8 ⟨314877, by decide⟩
    (prefixPartial 13 103462) = some ⟨13, 2, 0, 314877, 103462, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_103462_314877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103462 ⟨314877, by decide⟩ :=
  accepted_of_selected 13 103462 ⟨314877, by decide⟩ ⟨13, 2, 0, 314877, 103462, 2497, 16384⟩
    (by decide) selected_cut_11767

theorem selected_cut_11768 : selected 8 ⟨314887, by decide⟩
    (prefixPartial 13 103463) = some ⟨13, 2, 0, 314887, 103463, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_103463_314887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103463 ⟨314887, by decide⟩ :=
  accepted_of_selected 13 103463 ⟨314887, by decide⟩ ⟨13, 2, 0, 314887, 103463, 1237, 16384⟩
    (by decide) selected_cut_11768

theorem unmarked_context_12_25865_314888 : frontier 9 ⟨314888, by decide⟩
    (prefixCache 12 25865) (prefixPartial 12 25865) = false := by
  decide +kernel

theorem node_context_12_25865_314888 : EJMOriginalGlobalDAGData.nodes 9 ⟨314888, by decide⟩ =
    .split (coordinate 12) (![⟨314800, by decide⟩,⟨314858, by decide⟩,⟨314877, by decide⟩,⟨314887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25865_314888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25865 ⟨314888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25865
    ⟨314888, by decide⟩ (by decide) (![⟨314800, by decide⟩,⟨314858, by decide⟩,⟨314877, by decide⟩,⟨314887, by decide⟩]) unmarked_context_12_25865_314888 node_context_12_25865_314888
  intro a
  fin_cases a
  · exact context_13_103460_314800
  · exact context_13_103461_314858
  · exact context_13_103462_314877
  · exact context_13_103463_314887

theorem selected_cut_11769 : selected 7 ⟨314905, by decide⟩
    (prefixPartial 14 413856) = some ⟨14, 2, 0, 314905, 413856, 845, 4096⟩ := by
  decide +kernel

theorem context_14_413856_314905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413856 ⟨314905, by decide⟩ :=
  accepted_of_selected 14 413856 ⟨314905, by decide⟩ ⟨14, 2, 0, 314905, 413856, 845, 4096⟩
    (by decide) selected_cut_11769

theorem selected_cut_11770 : selected 7 ⟨314916, by decide⟩
    (prefixPartial 14 413857) = some ⟨14, 2, 0, 314916, 413857, 909, 4096⟩ := by
  decide +kernel

theorem context_14_413857_314916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413857 ⟨314916, by decide⟩ :=
  accepted_of_selected 14 413857 ⟨314916, by decide⟩ ⟨14, 2, 0, 314916, 413857, 909, 4096⟩
    (by decide) selected_cut_11770

theorem selected_cut_11771 : selected 7 ⟨314934, by decide⟩
    (prefixPartial 14 413858) = some ⟨14, 2, 0, 314934, 413858, 1109, 4096⟩ := by
  decide +kernel

theorem context_14_413858_314934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413858 ⟨314934, by decide⟩ :=
  accepted_of_selected 14 413858 ⟨314934, by decide⟩ ⟨14, 2, 0, 314934, 413858, 1109, 4096⟩
    (by decide) selected_cut_11771

theorem selected_cut_11772 : selected 7 ⟨314952, by decide⟩
    (prefixPartial 14 413859) = some ⟨14, 2, 0, 314952, 413859, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_413859_314952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413859 ⟨314952, by decide⟩ :=
  accepted_of_selected 14 413859 ⟨314952, by decide⟩ ⟨14, 2, 0, 314952, 413859, 1293, 4096⟩
    (by decide) selected_cut_11772

theorem unmarked_context_13_103464_314953 : frontier 8 ⟨314953, by decide⟩
    (prefixCache 13 103464) (prefixPartial 13 103464) = false := by
  decide +kernel

theorem node_context_13_103464_314953 : EJMOriginalGlobalDAGData.nodes 8 ⟨314953, by decide⟩ =
    .split (coordinate 13) (![⟨314905, by decide⟩,⟨314916, by decide⟩,⟨314934, by decide⟩,⟨314952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103464_314953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103464 ⟨314953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103464
    ⟨314953, by decide⟩ (by decide) (![⟨314905, by decide⟩,⟨314916, by decide⟩,⟨314934, by decide⟩,⟨314952, by decide⟩]) unmarked_context_13_103464_314953 node_context_13_103464_314953
  intro a
  fin_cases a
  · exact context_14_413856_314905
  · exact context_14_413857_314916
  · exact context_14_413858_314934
  · exact context_14_413859_314952

theorem selected_cut_11773 : selected 8 ⟨315008, by decide⟩
    (prefixPartial 13 103465) = some ⟨13, 2, 0, 315008, 103465, 3677, 16384⟩ := by
  decide +kernel

theorem context_13_103465_315008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103465 ⟨315008, by decide⟩ :=
  accepted_of_selected 13 103465 ⟨315008, by decide⟩ ⟨13, 2, 0, 315008, 103465, 3677, 16384⟩
    (by decide) selected_cut_11773

theorem selected_cut_11774 : selected 8 ⟨315051, by decide⟩
    (prefixPartial 13 103466) = some ⟨13, 2, 0, 315051, 103466, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_103466_315051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103466 ⟨315051, by decide⟩ :=
  accepted_of_selected 13 103466 ⟨315051, by decide⟩ ⟨13, 2, 0, 315051, 103466, 2709, 16384⟩
    (by decide) selected_cut_11774

theorem selected_cut_11775 : selected 8 ⟨315070, by decide⟩
    (prefixPartial 13 103467) = some ⟨13, 2, 0, 315070, 103467, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_103467_315070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103467 ⟨315070, by decide⟩ :=
  accepted_of_selected 13 103467 ⟨315070, by decide⟩ ⟨13, 2, 0, 315070, 103467, 1385, 16384⟩
    (by decide) selected_cut_11775

theorem unmarked_context_12_25866_315071 : frontier 9 ⟨315071, by decide⟩
    (prefixCache 12 25866) (prefixPartial 12 25866) = false := by
  decide +kernel

theorem node_context_12_25866_315071 : EJMOriginalGlobalDAGData.nodes 9 ⟨315071, by decide⟩ =
    .split (coordinate 12) (![⟨314953, by decide⟩,⟨315008, by decide⟩,⟨315051, by decide⟩,⟨315070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25866_315071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25866 ⟨315071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25866
    ⟨315071, by decide⟩ (by decide) (![⟨314953, by decide⟩,⟨315008, by decide⟩,⟨315051, by decide⟩,⟨315070, by decide⟩]) unmarked_context_12_25866_315071 node_context_12_25866_315071
  intro a
  fin_cases a
  · exact context_13_103464_314953
  · exact context_13_103465_315008
  · exact context_13_103466_315051
  · exact context_13_103467_315070

theorem selected_cut_11776 : selected 7 ⟨315086, by decide⟩
    (prefixPartial 14 413872) = some ⟨14, 2, 0, 315086, 413872, 853, 4096⟩ := by
  decide +kernel

theorem context_14_413872_315086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413872 ⟨315086, by decide⟩ :=
  accepted_of_selected 14 413872 ⟨315086, by decide⟩ ⟨14, 2, 0, 315086, 413872, 853, 4096⟩
    (by decide) selected_cut_11776

theorem selected_cut_11777 : selected 7 ⟨315102, by decide⟩
    (prefixPartial 14 413873) = some ⟨14, 2, 0, 315102, 413873, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_413873_315102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413873 ⟨315102, by decide⟩ :=
  accepted_of_selected 14 413873 ⟨315102, by decide⟩ ⟨14, 2, 0, 315102, 413873, 1121, 4096⟩
    (by decide) selected_cut_11777

theorem selected_cut_11778 : selected 7 ⟨315118, by decide⟩
    (prefixPartial 14 413874) = some ⟨14, 2, 0, 315118, 413874, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_413874_315118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413874 ⟨315118, by decide⟩ :=
  accepted_of_selected 14 413874 ⟨315118, by decide⟩ ⟨14, 2, 0, 315118, 413874, 1193, 4096⟩
    (by decide) selected_cut_11778

theorem selected_cut_11779 : selected 7 ⟨315145, by decide⟩
    (prefixPartial 14 413875) = some ⟨14, 2, 0, 315145, 413875, 1509, 4096⟩ := by
  decide +kernel

theorem context_14_413875_315145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413875 ⟨315145, by decide⟩ :=
  accepted_of_selected 14 413875 ⟨315145, by decide⟩ ⟨14, 2, 0, 315145, 413875, 1509, 4096⟩
    (by decide) selected_cut_11779

theorem unmarked_context_13_103468_315146 : frontier 8 ⟨315146, by decide⟩
    (prefixCache 13 103468) (prefixPartial 13 103468) = false := by
  decide +kernel

theorem node_context_13_103468_315146 : EJMOriginalGlobalDAGData.nodes 8 ⟨315146, by decide⟩ =
    .split (coordinate 13) (![⟨315086, by decide⟩,⟨315102, by decide⟩,⟨315118, by decide⟩,⟨315145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103468_315146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103468 ⟨315146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103468
    ⟨315146, by decide⟩ (by decide) (![⟨315086, by decide⟩,⟨315102, by decide⟩,⟨315118, by decide⟩,⟨315145, by decide⟩]) unmarked_context_13_103468_315146 node_context_13_103468_315146
  intro a
  fin_cases a
  · exact context_14_413872_315086
  · exact context_14_413873_315102
  · exact context_14_413874_315118
  · exact context_14_413875_315145

theorem selected_cut_11780 : selected 7 ⟨315176, by decide⟩
    (prefixPartial 14 413876) = some ⟨14, 2, 0, 315176, 413876, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_413876_315176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413876 ⟨315176, by decide⟩ :=
  accepted_of_selected 14 413876 ⟨315176, by decide⟩ ⟨14, 2, 0, 315176, 413876, 1357, 4096⟩
    (by decide) selected_cut_11780

theorem selected_cut_11781 : selected 7 ⟨315181, by decide⟩
    (prefixPartial 14 413877) = some ⟨14, 2, 0, 315181, 413877, 497, 4096⟩ := by
  decide +kernel

theorem context_14_413877_315181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413877 ⟨315181, by decide⟩ :=
  accepted_of_selected 14 413877 ⟨315181, by decide⟩ ⟨14, 2, 0, 315181, 413877, 497, 4096⟩
    (by decide) selected_cut_11781

theorem selected_cut_11782 : selected 7 ⟨315207, by decide⟩
    (prefixPartial 14 413878) = some ⟨14, 2, 0, 315207, 413878, 1377, 4096⟩ := by
  decide +kernel

theorem context_14_413878_315207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413878 ⟨315207, by decide⟩ :=
  accepted_of_selected 14 413878 ⟨315207, by decide⟩ ⟨14, 2, 0, 315207, 413878, 1377, 4096⟩
    (by decide) selected_cut_11782

theorem selected_cut_11783 : selected 7 ⟨315230, by decide⟩
    (prefixPartial 14 413879) = some ⟨14, 2, 0, 315230, 413879, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_413879_315230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 413879 ⟨315230, by decide⟩ :=
  accepted_of_selected 14 413879 ⟨315230, by decide⟩ ⟨14, 2, 0, 315230, 413879, 1297, 4096⟩
    (by decide) selected_cut_11783

theorem unmarked_context_13_103469_315231 : frontier 8 ⟨315231, by decide⟩
    (prefixCache 13 103469) (prefixPartial 13 103469) = false := by
  decide +kernel

theorem node_context_13_103469_315231 : EJMOriginalGlobalDAGData.nodes 8 ⟨315231, by decide⟩ =
    .split (coordinate 13) (![⟨315176, by decide⟩,⟨315181, by decide⟩,⟨315207, by decide⟩,⟨315230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_103469_315231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103469 ⟨315231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 103469
    ⟨315231, by decide⟩ (by decide) (![⟨315176, by decide⟩,⟨315181, by decide⟩,⟨315207, by decide⟩,⟨315230, by decide⟩]) unmarked_context_13_103469_315231 node_context_13_103469_315231
  intro a
  fin_cases a
  · exact context_14_413876_315176
  · exact context_14_413877_315181
  · exact context_14_413878_315207
  · exact context_14_413879_315230

theorem selected_cut_11784 : selected 8 ⟨315273, by decide⟩
    (prefixPartial 13 103470) = some ⟨13, 2, 0, 315273, 103470, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_103470_315273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103470 ⟨315273, by decide⟩ :=
  accepted_of_selected 13 103470 ⟨315273, by decide⟩ ⟨13, 2, 0, 315273, 103470, 2817, 16384⟩
    (by decide) selected_cut_11784

theorem selected_cut_11785 : selected 8 ⟨315286, by decide⟩
    (prefixPartial 13 103471) = some ⟨13, 2, 0, 315286, 103471, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_103471_315286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103471 ⟨315286, by decide⟩ :=
  accepted_of_selected 13 103471 ⟨315286, by decide⟩ ⟨13, 2, 0, 315286, 103471, 1337, 16384⟩
    (by decide) selected_cut_11785

theorem unmarked_context_12_25867_315287 : frontier 9 ⟨315287, by decide⟩
    (prefixCache 12 25867) (prefixPartial 12 25867) = false := by
  decide +kernel

theorem node_context_12_25867_315287 : EJMOriginalGlobalDAGData.nodes 9 ⟨315287, by decide⟩ =
    .split (coordinate 12) (![⟨315146, by decide⟩,⟨315231, by decide⟩,⟨315273, by decide⟩,⟨315286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25867_315287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25867 ⟨315287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25867
    ⟨315287, by decide⟩ (by decide) (![⟨315146, by decide⟩,⟨315231, by decide⟩,⟨315273, by decide⟩,⟨315286, by decide⟩]) unmarked_context_12_25867_315287 node_context_12_25867_315287
  intro a
  fin_cases a
  · exact context_13_103468_315146
  · exact context_13_103469_315231
  · exact context_13_103470_315273
  · exact context_13_103471_315286

theorem unmarked_context_11_6466_315288 : frontier 10 ⟨315288, by decide⟩
    (prefixCache 11 6466) (prefixPartial 11 6466) = false := by
  decide +kernel

theorem node_context_11_6466_315288 : EJMOriginalGlobalDAGData.nodes 10 ⟨315288, by decide⟩ =
    .split (coordinate 11) (![⟨314728, by decide⟩,⟨314888, by decide⟩,⟨315071, by decide⟩,⟨315287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6466_315288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6466 ⟨315288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6466
    ⟨315288, by decide⟩ (by decide) (![⟨314728, by decide⟩,⟨314888, by decide⟩,⟨315071, by decide⟩,⟨315287, by decide⟩]) unmarked_context_11_6466_315288 node_context_11_6466_315288
  intro a
  fin_cases a
  · exact context_12_25864_314728
  · exact context_12_25865_314888
  · exact context_12_25866_315071
  · exact context_12_25867_315287

theorem selected_cut_11786 : selected 8 ⟨315307, by decide⟩
    (prefixPartial 13 103472) = some ⟨13, 2, 0, 315307, 103472, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_103472_315307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103472 ⟨315307, by decide⟩ :=
  accepted_of_selected 13 103472 ⟨315307, by decide⟩ ⟨13, 2, 0, 315307, 103472, 1061, 16384⟩
    (by decide) selected_cut_11786

theorem selected_cut_11787 : selected 8 ⟨315364, by decide⟩
    (prefixPartial 13 103473) = some ⟨13, 2, 0, 315364, 103473, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_103473_315364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103473 ⟨315364, by decide⟩ :=
  accepted_of_selected 13 103473 ⟨315364, by decide⟩ ⟨13, 2, 0, 315364, 103473, 1965, 16384⟩
    (by decide) selected_cut_11787

theorem selected_cut_11788 : selected 8 ⟨315414, by decide⟩
    (prefixPartial 13 103474) = some ⟨13, 2, 0, 315414, 103474, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_103474_315414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103474 ⟨315414, by decide⟩ :=
  accepted_of_selected 13 103474 ⟨315414, by decide⟩ ⟨13, 2, 0, 315414, 103474, 2073, 16384⟩
    (by decide) selected_cut_11788

theorem selected_cut_11789 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 103475) = some ⟨13, 1, 0, 265883, 103475, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103475_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103475 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 103475 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 103475, 1, 16384⟩
    (by decide) selected_cut_11789

theorem unmarked_context_12_25868_315415 : frontier 9 ⟨315415, by decide⟩
    (prefixCache 12 25868) (prefixPartial 12 25868) = false := by
  decide +kernel

theorem node_context_12_25868_315415 : EJMOriginalGlobalDAGData.nodes 9 ⟨315415, by decide⟩ =
    .split (coordinate 12) (![⟨315307, by decide⟩,⟨315364, by decide⟩,⟨315414, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25868_315415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25868 ⟨315415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25868
    ⟨315415, by decide⟩ (by decide) (![⟨315307, by decide⟩,⟨315364, by decide⟩,⟨315414, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_25868_315415 node_context_12_25868_315415
  intro a
  fin_cases a
  · exact context_13_103472_315307
  · exact context_13_103473_315364
  · exact context_13_103474_315414
  · exact context_13_103475_265883

theorem selected_cut_11790 : selected 8 ⟨315470, by decide⟩
    (prefixPartial 13 103476) = some ⟨13, 2, 0, 315470, 103476, 3577, 16384⟩ := by
  decide +kernel

theorem context_13_103476_315470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103476 ⟨315470, by decide⟩ :=
  accepted_of_selected 13 103476 ⟨315470, by decide⟩ ⟨13, 2, 0, 315470, 103476, 3577, 16384⟩
    (by decide) selected_cut_11790

theorem selected_cut_11791 : selected 8 ⟨315527, by decide⟩
    (prefixPartial 13 103477) = some ⟨13, 2, 0, 315527, 103477, 3405, 16384⟩ := by
  decide +kernel

theorem context_13_103477_315527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103477 ⟨315527, by decide⟩ :=
  accepted_of_selected 13 103477 ⟨315527, by decide⟩ ⟨13, 2, 0, 315527, 103477, 3405, 16384⟩
    (by decide) selected_cut_11791

theorem selected_cut_11792 : selected 8 ⟨315554, by decide⟩
    (prefixPartial 13 103478) = some ⟨13, 2, 0, 315554, 103478, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_103478_315554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103478 ⟨315554, by decide⟩ :=
  accepted_of_selected 13 103478 ⟨315554, by decide⟩ ⟨13, 2, 0, 315554, 103478, 2493, 16384⟩
    (by decide) selected_cut_11792

theorem selected_cut_11793 : selected 8 ⟨315560, by decide⟩
    (prefixPartial 13 103479) = some ⟨13, 2, 0, 315560, 103479, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_103479_315560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103479 ⟨315560, by decide⟩ :=
  accepted_of_selected 13 103479 ⟨315560, by decide⟩ ⟨13, 2, 0, 315560, 103479, 1157, 16384⟩
    (by decide) selected_cut_11793

theorem unmarked_context_12_25869_315561 : frontier 9 ⟨315561, by decide⟩
    (prefixCache 12 25869) (prefixPartial 12 25869) = false := by
  decide +kernel

theorem node_context_12_25869_315561 : EJMOriginalGlobalDAGData.nodes 9 ⟨315561, by decide⟩ =
    .split (coordinate 12) (![⟨315470, by decide⟩,⟨315527, by decide⟩,⟨315554, by decide⟩,⟨315560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25869_315561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25869 ⟨315561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25869
    ⟨315561, by decide⟩ (by decide) (![⟨315470, by decide⟩,⟨315527, by decide⟩,⟨315554, by decide⟩,⟨315560, by decide⟩]) unmarked_context_12_25869_315561 node_context_12_25869_315561
  intro a
  fin_cases a
  · exact context_13_103476_315470
  · exact context_13_103477_315527
  · exact context_13_103478_315554
  · exact context_13_103479_315560

theorem selected_cut_11794 : selected 8 ⟨315617, by decide⟩
    (prefixPartial 13 103480) = some ⟨13, 2, 0, 315617, 103480, 3765, 16384⟩ := by
  decide +kernel

theorem context_13_103480_315617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103480 ⟨315617, by decide⟩ :=
  accepted_of_selected 13 103480 ⟨315617, by decide⟩ ⟨13, 2, 0, 315617, 103480, 3765, 16384⟩
    (by decide) selected_cut_11794

theorem selected_cut_11795 : selected 8 ⟨315672, by decide⟩
    (prefixPartial 13 103481) = some ⟨13, 2, 0, 315672, 103481, 3665, 16384⟩ := by
  decide +kernel

theorem context_13_103481_315672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103481 ⟨315672, by decide⟩ :=
  accepted_of_selected 13 103481 ⟨315672, by decide⟩ ⟨13, 2, 0, 315672, 103481, 3665, 16384⟩
    (by decide) selected_cut_11795

theorem selected_cut_11796 : selected 8 ⟨315714, by decide⟩
    (prefixPartial 13 103482) = some ⟨13, 2, 0, 315714, 103482, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_103482_315714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103482 ⟨315714, by decide⟩ :=
  accepted_of_selected 13 103482 ⟨315714, by decide⟩ ⟨13, 2, 0, 315714, 103482, 2513, 16384⟩
    (by decide) selected_cut_11796

theorem selected_cut_11797 : selected 8 ⟨315729, by decide⟩
    (prefixPartial 13 103483) = some ⟨13, 2, 0, 315729, 103483, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_103483_315729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103483 ⟨315729, by decide⟩ :=
  accepted_of_selected 13 103483 ⟨315729, by decide⟩ ⟨13, 2, 0, 315729, 103483, 1281, 16384⟩
    (by decide) selected_cut_11797

theorem unmarked_context_12_25870_315730 : frontier 9 ⟨315730, by decide⟩
    (prefixCache 12 25870) (prefixPartial 12 25870) = false := by
  decide +kernel

theorem node_context_12_25870_315730 : EJMOriginalGlobalDAGData.nodes 9 ⟨315730, by decide⟩ =
    .split (coordinate 12) (![⟨315617, by decide⟩,⟨315672, by decide⟩,⟨315714, by decide⟩,⟨315729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25870_315730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25870 ⟨315730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25870
    ⟨315730, by decide⟩ (by decide) (![⟨315617, by decide⟩,⟨315672, by decide⟩,⟨315714, by decide⟩,⟨315729, by decide⟩]) unmarked_context_12_25870_315730 node_context_12_25870_315730
  intro a
  fin_cases a
  · exact context_13_103480_315617
  · exact context_13_103481_315672
  · exact context_13_103482_315714
  · exact context_13_103483_315729

theorem selected_cut_11798 : selected 8 ⟨315784, by decide⟩
    (prefixPartial 13 103484) = some ⟨13, 2, 0, 315784, 103484, 3877, 16384⟩ := by
  decide +kernel

theorem context_13_103484_315784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103484 ⟨315784, by decide⟩ :=
  accepted_of_selected 13 103484 ⟨315784, by decide⟩ ⟨13, 2, 0, 315784, 103484, 3877, 16384⟩
    (by decide) selected_cut_11798

theorem selected_cut_11799 : selected 8 ⟨315834, by decide⟩
    (prefixPartial 13 103485) = some ⟨13, 2, 0, 315834, 103485, 3721, 16384⟩ := by
  decide +kernel

theorem context_13_103485_315834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103485 ⟨315834, by decide⟩ :=
  accepted_of_selected 13 103485 ⟨315834, by decide⟩ ⟨13, 2, 0, 315834, 103485, 3721, 16384⟩
    (by decide) selected_cut_11799

theorem selected_cut_11800 : selected 8 ⟨315875, by decide⟩
    (prefixPartial 13 103486) = some ⟨13, 2, 0, 315875, 103486, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_103486_315875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103486 ⟨315875, by decide⟩ :=
  accepted_of_selected 13 103486 ⟨315875, by decide⟩ ⟨13, 2, 0, 315875, 103486, 2649, 16384⟩
    (by decide) selected_cut_11800

theorem selected_cut_11801 : selected 8 ⟨315882, by decide⟩
    (prefixPartial 13 103487) = some ⟨13, 2, 0, 315882, 103487, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_103487_315882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103487 ⟨315882, by decide⟩ :=
  accepted_of_selected 13 103487 ⟨315882, by decide⟩ ⟨13, 2, 0, 315882, 103487, 1265, 16384⟩
    (by decide) selected_cut_11801

theorem unmarked_context_12_25871_315883 : frontier 9 ⟨315883, by decide⟩
    (prefixCache 12 25871) (prefixPartial 12 25871) = false := by
  decide +kernel

theorem node_context_12_25871_315883 : EJMOriginalGlobalDAGData.nodes 9 ⟨315883, by decide⟩ =
    .split (coordinate 12) (![⟨315784, by decide⟩,⟨315834, by decide⟩,⟨315875, by decide⟩,⟨315882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25871_315883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25871 ⟨315883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25871
    ⟨315883, by decide⟩ (by decide) (![⟨315784, by decide⟩,⟨315834, by decide⟩,⟨315875, by decide⟩,⟨315882, by decide⟩]) unmarked_context_12_25871_315883 node_context_12_25871_315883
  intro a
  fin_cases a
  · exact context_13_103484_315784
  · exact context_13_103485_315834
  · exact context_13_103486_315875
  · exact context_13_103487_315882

theorem unmarked_context_11_6467_315884 : frontier 10 ⟨315884, by decide⟩
    (prefixCache 11 6467) (prefixPartial 11 6467) = false := by
  decide +kernel

theorem node_context_11_6467_315884 : EJMOriginalGlobalDAGData.nodes 10 ⟨315884, by decide⟩ =
    .split (coordinate 11) (![⟨315415, by decide⟩,⟨315561, by decide⟩,⟨315730, by decide⟩,⟨315883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6467_315884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6467 ⟨315884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6467
    ⟨315884, by decide⟩ (by decide) (![⟨315415, by decide⟩,⟨315561, by decide⟩,⟨315730, by decide⟩,⟨315883, by decide⟩]) unmarked_context_11_6467_315884 node_context_11_6467_315884
  intro a
  fin_cases a
  · exact context_12_25868_315415
  · exact context_12_25869_315561
  · exact context_12_25870_315730
  · exact context_12_25871_315883

theorem unmarked_context_10_1616_315885 : frontier 11 ⟨315885, by decide⟩
    (prefixCache 10 1616) (prefixPartial 10 1616) = false := by
  decide +kernel

theorem node_context_10_1616_315885 : EJMOriginalGlobalDAGData.nodes 11 ⟨315885, by decide⟩ =
    .split (coordinate 10) (![⟨313761, by decide⟩,⟨314526, by decide⟩,⟨315288, by decide⟩,⟨315884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1616_315885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1616 ⟨315885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1616
    ⟨315885, by decide⟩ (by decide) (![⟨313761, by decide⟩,⟨314526, by decide⟩,⟨315288, by decide⟩,⟨315884, by decide⟩]) unmarked_context_10_1616_315885 node_context_10_1616_315885
  intro a
  fin_cases a
  · exact context_11_6464_313761
  · exact context_11_6465_314526
  · exact context_11_6466_315288
  · exact context_11_6467_315884

theorem selected_cut_11802 : selected 8 ⟨315902, by decide⟩
    (prefixPartial 13 103488) = some ⟨13, 2, 0, 315902, 103488, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_103488_315902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103488 ⟨315902, by decide⟩ :=
  accepted_of_selected 13 103488 ⟨315902, by decide⟩ ⟨13, 2, 0, 315902, 103488, 1361, 16384⟩
    (by decide) selected_cut_11802

theorem selected_cut_11803 : selected 8 ⟨315920, by decide⟩
    (prefixPartial 13 103489) = some ⟨13, 2, 0, 315920, 103489, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_103489_315920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103489 ⟨315920, by decide⟩ :=
  accepted_of_selected 13 103489 ⟨315920, by decide⟩ ⟨13, 2, 0, 315920, 103489, 1501, 16384⟩
    (by decide) selected_cut_11803

theorem selected_cut_11804 : selected 8 ⟨315938, by decide⟩
    (prefixPartial 13 103490) = some ⟨13, 2, 0, 315938, 103490, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_103490_315938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103490 ⟨315938, by decide⟩ :=
  accepted_of_selected 13 103490 ⟨315938, by decide⟩ ⟨13, 2, 0, 315938, 103490, 1105, 16384⟩
    (by decide) selected_cut_11804

theorem selected_cut_11805 : selected 8 ⟨315943, by decide⟩
    (prefixPartial 13 103491) = some ⟨13, 2, 0, 315943, 103491, 697, 16384⟩ := by
  decide +kernel

theorem context_13_103491_315943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103491 ⟨315943, by decide⟩ :=
  accepted_of_selected 13 103491 ⟨315943, by decide⟩ ⟨13, 2, 0, 315943, 103491, 697, 16384⟩
    (by decide) selected_cut_11805

theorem unmarked_context_12_25872_315944 : frontier 9 ⟨315944, by decide⟩
    (prefixCache 12 25872) (prefixPartial 12 25872) = false := by
  decide +kernel

theorem node_context_12_25872_315944 : EJMOriginalGlobalDAGData.nodes 9 ⟨315944, by decide⟩ =
    .split (coordinate 12) (![⟨315902, by decide⟩,⟨315920, by decide⟩,⟨315938, by decide⟩,⟨315943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25872_315944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25872 ⟨315944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25872
    ⟨315944, by decide⟩ (by decide) (![⟨315902, by decide⟩,⟨315920, by decide⟩,⟨315938, by decide⟩,⟨315943, by decide⟩]) unmarked_context_12_25872_315944 node_context_12_25872_315944
  intro a
  fin_cases a
  · exact context_13_103488_315902
  · exact context_13_103489_315920
  · exact context_13_103490_315938
  · exact context_13_103491_315943

theorem selected_cut_11806 : selected 8 ⟨315969, by decide⟩
    (prefixPartial 13 103492) = some ⟨13, 2, 0, 315969, 103492, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_103492_315969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103492 ⟨315969, by decide⟩ :=
  accepted_of_selected 13 103492 ⟨315969, by decide⟩ ⟨13, 2, 0, 315969, 103492, 1745, 16384⟩
    (by decide) selected_cut_11806

theorem selected_cut_11807 : selected 8 ⟨315988, by decide⟩
    (prefixPartial 13 103493) = some ⟨13, 2, 0, 315988, 103493, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_103493_315988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103493 ⟨315988, by decide⟩ :=
  accepted_of_selected 13 103493 ⟨315988, by decide⟩ ⟨13, 2, 0, 315988, 103493, 1189, 16384⟩
    (by decide) selected_cut_11807

theorem selected_cut_11808 : selected 8 ⟨316010, by decide⟩
    (prefixPartial 13 103494) = some ⟨13, 2, 0, 316010, 103494, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_103494_316010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103494 ⟨316010, by decide⟩ :=
  accepted_of_selected 13 103494 ⟨316010, by decide⟩ ⟨13, 2, 0, 316010, 103494, 1397, 16384⟩
    (by decide) selected_cut_11808

theorem selected_cut_11809 : selected 8 ⟨316014, by decide⟩
    (prefixPartial 13 103495) = some ⟨13, 2, 0, 316014, 103495, 741, 16384⟩ := by
  decide +kernel

theorem context_13_103495_316014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103495 ⟨316014, by decide⟩ :=
  accepted_of_selected 13 103495 ⟨316014, by decide⟩ ⟨13, 2, 0, 316014, 103495, 741, 16384⟩
    (by decide) selected_cut_11809

theorem unmarked_context_12_25873_316015 : frontier 9 ⟨316015, by decide⟩
    (prefixCache 12 25873) (prefixPartial 12 25873) = false := by
  decide +kernel

theorem node_context_12_25873_316015 : EJMOriginalGlobalDAGData.nodes 9 ⟨316015, by decide⟩ =
    .split (coordinate 12) (![⟨315969, by decide⟩,⟨315988, by decide⟩,⟨316010, by decide⟩,⟨316014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25873_316015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25873 ⟨316015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25873
    ⟨316015, by decide⟩ (by decide) (![⟨315969, by decide⟩,⟨315988, by decide⟩,⟨316010, by decide⟩,⟨316014, by decide⟩]) unmarked_context_12_25873_316015 node_context_12_25873_316015
  intro a
  fin_cases a
  · exact context_13_103492_315969
  · exact context_13_103493_315988
  · exact context_13_103494_316010
  · exact context_13_103495_316014

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
