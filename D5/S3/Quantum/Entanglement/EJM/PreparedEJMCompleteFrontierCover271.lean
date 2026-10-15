/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover270
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26019 : selected 8 ⟨658263, by decide⟩
    (prefixPartial 13 354327) = some ⟨13, 2, 0, 658263, 354327, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_354327_658263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354327 ⟨658263, by decide⟩ :=
  accepted_of_selected 13 354327 ⟨658263, by decide⟩ ⟨13, 2, 0, 658263, 354327, 1197, 16384⟩
    (by decide) selected_cut_26019

theorem unmarked_context_12_88581_658264 : frontier 9 ⟨658264, by decide⟩
    (prefixCache 12 88581) (prefixPartial 12 88581) = false := by
  decide +kernel

theorem node_context_12_88581_658264 : EJMOriginalGlobalDAGData.nodes 9 ⟨658264, by decide⟩ =
    .split (coordinate 12) (![⟨658119, by decide⟩,⟨658204, by decide⟩,⟨658224, by decide⟩,⟨658263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88581_658264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88581 ⟨658264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88581
    ⟨658264, by decide⟩ (by decide) (![⟨658119, by decide⟩,⟨658204, by decide⟩,⟨658224, by decide⟩,⟨658263, by decide⟩]) unmarked_context_12_88581_658264 node_context_12_88581_658264
  intro a
  fin_cases a
  · exact context_13_354324_658119
  · exact context_13_354325_658204
  · exact context_13_354326_658224
  · exact context_13_354327_658263

theorem selected_cut_26020 : selected 8 ⟨658356, by decide⟩
    (prefixPartial 13 354328) = some ⟨13, 2, 0, 658356, 354328, 3841, 16384⟩ := by
  decide +kernel

theorem context_13_354328_658356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354328 ⟨658356, by decide⟩ :=
  accepted_of_selected 13 354328 ⟨658356, by decide⟩ ⟨13, 2, 0, 658356, 354328, 3841, 16384⟩
    (by decide) selected_cut_26020

theorem selected_cut_26021 : selected 8 ⟨658418, by decide⟩
    (prefixPartial 13 354329) = some ⟨13, 2, 0, 658418, 354329, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_354329_658418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354329 ⟨658418, by decide⟩ :=
  accepted_of_selected 13 354329 ⟨658418, by decide⟩ ⟨13, 2, 0, 658418, 354329, 2865, 16384⟩
    (by decide) selected_cut_26021

theorem selected_cut_26022 : selected 8 ⟨658450, by decide⟩
    (prefixPartial 13 354330) = some ⟨13, 2, 0, 658450, 354330, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_354330_658450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354330 ⟨658450, by decide⟩ :=
  accepted_of_selected 13 354330 ⟨658450, by decide⟩ ⟨13, 2, 0, 658450, 354330, 1661, 16384⟩
    (by decide) selected_cut_26022

theorem selected_cut_26023 : selected 8 ⟨658484, by decide⟩
    (prefixPartial 13 354331) = some ⟨13, 2, 0, 658484, 354331, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_354331_658484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354331 ⟨658484, by decide⟩ :=
  accepted_of_selected 13 354331 ⟨658484, by decide⟩ ⟨13, 2, 0, 658484, 354331, 1277, 16384⟩
    (by decide) selected_cut_26023

theorem unmarked_context_12_88582_658485 : frontier 9 ⟨658485, by decide⟩
    (prefixCache 12 88582) (prefixPartial 12 88582) = false := by
  decide +kernel

theorem node_context_12_88582_658485 : EJMOriginalGlobalDAGData.nodes 9 ⟨658485, by decide⟩ =
    .split (coordinate 12) (![⟨658356, by decide⟩,⟨658418, by decide⟩,⟨658450, by decide⟩,⟨658484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88582_658485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88582 ⟨658485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88582
    ⟨658485, by decide⟩ (by decide) (![⟨658356, by decide⟩,⟨658418, by decide⟩,⟨658450, by decide⟩,⟨658484, by decide⟩]) unmarked_context_12_88582_658485 node_context_12_88582_658485
  intro a
  fin_cases a
  · exact context_13_354328_658356
  · exact context_13_354329_658418
  · exact context_13_354330_658450
  · exact context_13_354331_658484

theorem selected_cut_26024 : selected 7 ⟨658505, by decide⟩
    (prefixPartial 14 1417328) = some ⟨14, 2, 0, 658505, 1417328, 805, 4096⟩ := by
  decide +kernel

theorem context_14_1417328_658505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1417328 ⟨658505, by decide⟩ :=
  accepted_of_selected 14 1417328 ⟨658505, by decide⟩ ⟨14, 2, 0, 658505, 1417328, 805, 4096⟩
    (by decide) selected_cut_26024

theorem selected_cut_26025 : selected 7 ⟨658545, by decide⟩
    (prefixPartial 14 1417329) = some ⟨14, 2, 0, 658545, 1417329, 1465, 4096⟩ := by
  decide +kernel

theorem context_14_1417329_658545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1417329 ⟨658545, by decide⟩ :=
  accepted_of_selected 14 1417329 ⟨658545, by decide⟩ ⟨14, 2, 0, 658545, 1417329, 1465, 4096⟩
    (by decide) selected_cut_26025

theorem selected_cut_26026 : selected 7 ⟨658556, by decide⟩
    (prefixPartial 14 1417330) = some ⟨14, 2, 0, 658556, 1417330, 773, 4096⟩ := by
  decide +kernel

theorem context_14_1417330_658556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1417330 ⟨658556, by decide⟩ :=
  accepted_of_selected 14 1417330 ⟨658556, by decide⟩ ⟨14, 2, 0, 658556, 1417330, 773, 4096⟩
    (by decide) selected_cut_26026

theorem selected_cut_26027 : selected 7 ⟨658580, by decide⟩
    (prefixPartial 14 1417331) = some ⟨14, 2, 0, 658580, 1417331, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_1417331_658580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1417331 ⟨658580, by decide⟩ :=
  accepted_of_selected 14 1417331 ⟨658580, by decide⟩ ⟨14, 2, 0, 658580, 1417331, 1301, 4096⟩
    (by decide) selected_cut_26027

theorem unmarked_context_13_354332_658581 : frontier 8 ⟨658581, by decide⟩
    (prefixCache 13 354332) (prefixPartial 13 354332) = false := by
  decide +kernel

theorem node_context_13_354332_658581 : EJMOriginalGlobalDAGData.nodes 8 ⟨658581, by decide⟩ =
    .split (coordinate 13) (![⟨658505, by decide⟩,⟨658545, by decide⟩,⟨658556, by decide⟩,⟨658580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_354332_658581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354332 ⟨658581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 354332
    ⟨658581, by decide⟩ (by decide) (![⟨658505, by decide⟩,⟨658545, by decide⟩,⟨658556, by decide⟩,⟨658580, by decide⟩]) unmarked_context_13_354332_658581 node_context_13_354332_658581
  intro a
  fin_cases a
  · exact context_14_1417328_658505
  · exact context_14_1417329_658545
  · exact context_14_1417330_658556
  · exact context_14_1417331_658580

theorem selected_cut_26028 : selected 8 ⟨658666, by decide⟩
    (prefixPartial 13 354333) = some ⟨13, 2, 0, 658666, 354333, 3305, 16384⟩ := by
  decide +kernel

theorem context_13_354333_658666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354333 ⟨658666, by decide⟩ :=
  accepted_of_selected 13 354333 ⟨658666, by decide⟩ ⟨13, 2, 0, 658666, 354333, 3305, 16384⟩
    (by decide) selected_cut_26028

theorem selected_cut_26029 : selected 8 ⟨658693, by decide⟩
    (prefixPartial 13 354334) = some ⟨13, 2, 0, 658693, 354334, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_354334_658693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354334 ⟨658693, by decide⟩ :=
  accepted_of_selected 13 354334 ⟨658693, by decide⟩ ⟨13, 2, 0, 658693, 354334, 1717, 16384⟩
    (by decide) selected_cut_26029

theorem selected_cut_26030 : selected 8 ⟨658722, by decide⟩
    (prefixPartial 13 354335) = some ⟨13, 2, 0, 658722, 354335, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_354335_658722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354335 ⟨658722, by decide⟩ :=
  accepted_of_selected 13 354335 ⟨658722, by decide⟩ ⟨13, 2, 0, 658722, 354335, 1297, 16384⟩
    (by decide) selected_cut_26030

theorem unmarked_context_12_88583_658723 : frontier 9 ⟨658723, by decide⟩
    (prefixCache 12 88583) (prefixPartial 12 88583) = false := by
  decide +kernel

theorem node_context_12_88583_658723 : EJMOriginalGlobalDAGData.nodes 9 ⟨658723, by decide⟩ =
    .split (coordinate 12) (![⟨658581, by decide⟩,⟨658666, by decide⟩,⟨658693, by decide⟩,⟨658722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88583_658723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88583 ⟨658723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88583
    ⟨658723, by decide⟩ (by decide) (![⟨658581, by decide⟩,⟨658666, by decide⟩,⟨658693, by decide⟩,⟨658722, by decide⟩]) unmarked_context_12_88583_658723 node_context_12_88583_658723
  intro a
  fin_cases a
  · exact context_13_354332_658581
  · exact context_13_354333_658666
  · exact context_13_354334_658693
  · exact context_13_354335_658722

theorem unmarked_context_11_22145_658724 : frontier 10 ⟨658724, by decide⟩
    (prefixCache 11 22145) (prefixPartial 11 22145) = false := by
  decide +kernel

theorem node_context_11_22145_658724 : EJMOriginalGlobalDAGData.nodes 10 ⟨658724, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨658264, by decide⟩,⟨658485, by decide⟩,⟨658723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22145_658724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22145 ⟨658724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22145
    ⟨658724, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨658264, by decide⟩,⟨658485, by decide⟩,⟨658723, by decide⟩]) unmarked_context_11_22145_658724 node_context_11_22145_658724
  intro a
  fin_cases a
  · exact context_12_88580_448748
  · exact context_12_88581_658264
  · exact context_12_88582_658485
  · exact context_12_88583_658723

theorem selected_cut_26031 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88584) = some ⟨12, 1, 0, 448748, 88584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88584_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88584 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88584 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88584, 1, 65536⟩
    (by decide) selected_cut_26031

theorem selected_cut_26032 : selected 8 ⟨658784, by decide⟩
    (prefixPartial 13 354340) = some ⟨13, 2, 0, 658784, 354340, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_354340_658784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354340 ⟨658784, by decide⟩ :=
  accepted_of_selected 13 354340 ⟨658784, by decide⟩ ⟨13, 2, 0, 658784, 354340, 3193, 16384⟩
    (by decide) selected_cut_26032

theorem selected_cut_26033 : selected 8 ⟨658822, by decide⟩
    (prefixPartial 13 354341) = some ⟨13, 2, 0, 658822, 354341, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_354341_658822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354341 ⟨658822, by decide⟩ :=
  accepted_of_selected 13 354341 ⟨658822, by decide⟩ ⟨13, 2, 0, 658822, 354341, 2245, 16384⟩
    (by decide) selected_cut_26033

theorem selected_cut_26034 : selected 8 ⟨658847, by decide⟩
    (prefixPartial 13 354342) = some ⟨13, 2, 0, 658847, 354342, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_354342_658847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354342 ⟨658847, by decide⟩ :=
  accepted_of_selected 13 354342 ⟨658847, by decide⟩ ⟨13, 2, 0, 658847, 354342, 1621, 16384⟩
    (by decide) selected_cut_26034

theorem selected_cut_26035 : selected 8 ⟨658868, by decide⟩
    (prefixPartial 13 354343) = some ⟨13, 2, 0, 658868, 354343, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_354343_658868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354343 ⟨658868, by decide⟩ :=
  accepted_of_selected 13 354343 ⟨658868, by decide⟩ ⟨13, 2, 0, 658868, 354343, 1117, 16384⟩
    (by decide) selected_cut_26035

theorem unmarked_context_12_88585_658869 : frontier 9 ⟨658869, by decide⟩
    (prefixCache 12 88585) (prefixPartial 12 88585) = false := by
  decide +kernel

theorem node_context_12_88585_658869 : EJMOriginalGlobalDAGData.nodes 9 ⟨658869, by decide⟩ =
    .split (coordinate 12) (![⟨658784, by decide⟩,⟨658822, by decide⟩,⟨658847, by decide⟩,⟨658868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88585_658869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88585 ⟨658869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88585
    ⟨658869, by decide⟩ (by decide) (![⟨658784, by decide⟩,⟨658822, by decide⟩,⟨658847, by decide⟩,⟨658868, by decide⟩]) unmarked_context_12_88585_658869 node_context_12_88585_658869
  intro a
  fin_cases a
  · exact context_13_354340_658784
  · exact context_13_354341_658822
  · exact context_13_354342_658847
  · exact context_13_354343_658868

theorem selected_cut_26036 : selected 9 ⟨48867, by decide⟩
    (prefixPartial 12 88586) = some ⟨12, 1, 0, 48867, 88586, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88586_48867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88586 ⟨48867, by decide⟩ :=
  accepted_of_selected 12 88586 ⟨48867, by decide⟩ ⟨12, 1, 0, 48867, 88586, 1, 65536⟩
    (by decide) selected_cut_26036

theorem selected_cut_26037 : selected 8 ⟨658951, by decide⟩
    (prefixPartial 13 354348) = some ⟨13, 2, 0, 658951, 354348, 3881, 16384⟩ := by
  decide +kernel

theorem context_13_354348_658951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354348 ⟨658951, by decide⟩ :=
  accepted_of_selected 13 354348 ⟨658951, by decide⟩ ⟨13, 2, 0, 658951, 354348, 3881, 16384⟩
    (by decide) selected_cut_26037

theorem selected_cut_26038 : selected 8 ⟨659032, by decide⟩
    (prefixPartial 13 354349) = some ⟨13, 2, 0, 659032, 354349, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_354349_659032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354349 ⟨659032, by decide⟩ :=
  accepted_of_selected 13 354349 ⟨659032, by decide⟩ ⟨13, 2, 0, 659032, 354349, 3317, 16384⟩
    (by decide) selected_cut_26038

theorem selected_cut_26039 : selected 8 ⟨659060, by decide⟩
    (prefixPartial 13 354350) = some ⟨13, 2, 0, 659060, 354350, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_354350_659060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354350 ⟨659060, by decide⟩ :=
  accepted_of_selected 13 354350 ⟨659060, by decide⟩ ⟨13, 2, 0, 659060, 354350, 1797, 16384⟩
    (by decide) selected_cut_26039

theorem selected_cut_26040 : selected 8 ⟨659074, by decide⟩
    (prefixPartial 13 354351) = some ⟨13, 2, 0, 659074, 354351, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_354351_659074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354351 ⟨659074, by decide⟩ :=
  accepted_of_selected 13 354351 ⟨659074, by decide⟩ ⟨13, 2, 0, 659074, 354351, 1153, 16384⟩
    (by decide) selected_cut_26040

theorem unmarked_context_12_88587_659075 : frontier 9 ⟨659075, by decide⟩
    (prefixCache 12 88587) (prefixPartial 12 88587) = false := by
  decide +kernel

theorem node_context_12_88587_659075 : EJMOriginalGlobalDAGData.nodes 9 ⟨659075, by decide⟩ =
    .split (coordinate 12) (![⟨658951, by decide⟩,⟨659032, by decide⟩,⟨659060, by decide⟩,⟨659074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88587_659075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88587 ⟨659075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88587
    ⟨659075, by decide⟩ (by decide) (![⟨658951, by decide⟩,⟨659032, by decide⟩,⟨659060, by decide⟩,⟨659074, by decide⟩]) unmarked_context_12_88587_659075 node_context_12_88587_659075
  intro a
  fin_cases a
  · exact context_13_354348_658951
  · exact context_13_354349_659032
  · exact context_13_354350_659060
  · exact context_13_354351_659074

theorem unmarked_context_11_22146_659076 : frontier 10 ⟨659076, by decide⟩
    (prefixCache 11 22146) (prefixPartial 11 22146) = false := by
  decide +kernel

theorem node_context_11_22146_659076 : EJMOriginalGlobalDAGData.nodes 10 ⟨659076, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨658869, by decide⟩,⟨48867, by decide⟩,⟨659075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22146_659076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22146 ⟨659076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22146
    ⟨659076, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨658869, by decide⟩,⟨48867, by decide⟩,⟨659075, by decide⟩]) unmarked_context_11_22146_659076 node_context_11_22146_659076
  intro a
  fin_cases a
  · exact context_12_88584_448748
  · exact context_12_88585_658869
  · exact context_12_88586_48867
  · exact context_12_88587_659075

theorem selected_cut_26041 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88588) = some ⟨12, 1, 0, 448748, 88588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88588_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88588 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88588 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88588, 1, 65536⟩
    (by decide) selected_cut_26041

theorem selected_cut_26042 : selected 8 ⟨659133, by decide⟩
    (prefixPartial 13 354356) = some ⟨13, 2, 0, 659133, 354356, 3565, 16384⟩ := by
  decide +kernel

theorem context_13_354356_659133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354356 ⟨659133, by decide⟩ :=
  accepted_of_selected 13 354356 ⟨659133, by decide⟩ ⟨13, 2, 0, 659133, 354356, 3565, 16384⟩
    (by decide) selected_cut_26042

theorem selected_cut_26043 : selected 8 ⟨659189, by decide⟩
    (prefixPartial 13 354357) = some ⟨13, 2, 0, 659189, 354357, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_354357_659189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354357 ⟨659189, by decide⟩ :=
  accepted_of_selected 13 354357 ⟨659189, by decide⟩ ⟨13, 2, 0, 659189, 354357, 2753, 16384⟩
    (by decide) selected_cut_26043

theorem selected_cut_26044 : selected 8 ⟨659208, by decide⟩
    (prefixPartial 13 354358) = some ⟨13, 2, 0, 659208, 354358, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_354358_659208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354358 ⟨659208, by decide⟩ :=
  accepted_of_selected 13 354358 ⟨659208, by decide⟩ ⟨13, 2, 0, 659208, 354358, 1749, 16384⟩
    (by decide) selected_cut_26044

theorem selected_cut_26045 : selected 8 ⟨659238, by decide⟩
    (prefixPartial 13 354359) = some ⟨13, 2, 0, 659238, 354359, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_354359_659238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354359 ⟨659238, by decide⟩ :=
  accepted_of_selected 13 354359 ⟨659238, by decide⟩ ⟨13, 2, 0, 659238, 354359, 1281, 16384⟩
    (by decide) selected_cut_26045

theorem unmarked_context_12_88589_659239 : frontier 9 ⟨659239, by decide⟩
    (prefixCache 12 88589) (prefixPartial 12 88589) = false := by
  decide +kernel

theorem node_context_12_88589_659239 : EJMOriginalGlobalDAGData.nodes 9 ⟨659239, by decide⟩ =
    .split (coordinate 12) (![⟨659133, by decide⟩,⟨659189, by decide⟩,⟨659208, by decide⟩,⟨659238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88589_659239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88589 ⟨659239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88589
    ⟨659239, by decide⟩ (by decide) (![⟨659133, by decide⟩,⟨659189, by decide⟩,⟨659208, by decide⟩,⟨659238, by decide⟩]) unmarked_context_12_88589_659239 node_context_12_88589_659239
  intro a
  fin_cases a
  · exact context_13_354356_659133
  · exact context_13_354357_659189
  · exact context_13_354358_659208
  · exact context_13_354359_659238

theorem selected_cut_26046 : selected 8 ⟨659307, by decide⟩
    (prefixPartial 13 354360) = some ⟨13, 2, 0, 659307, 354360, 3793, 16384⟩ := by
  decide +kernel

theorem context_13_354360_659307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354360 ⟨659307, by decide⟩ :=
  accepted_of_selected 13 354360 ⟨659307, by decide⟩ ⟨13, 2, 0, 659307, 354360, 3793, 16384⟩
    (by decide) selected_cut_26046

theorem selected_cut_26047 : selected 8 ⟨659383, by decide⟩
    (prefixPartial 13 354361) = some ⟨13, 2, 0, 659383, 354361, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_354361_659383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354361 ⟨659383, by decide⟩ :=
  accepted_of_selected 13 354361 ⟨659383, by decide⟩ ⟨13, 2, 0, 659383, 354361, 3357, 16384⟩
    (by decide) selected_cut_26047

theorem selected_cut_26048 : selected 8 ⟨659424, by decide⟩
    (prefixPartial 13 354362) = some ⟨13, 2, 0, 659424, 354362, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_354362_659424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354362 ⟨659424, by decide⟩ :=
  accepted_of_selected 13 354362 ⟨659424, by decide⟩ ⟨13, 2, 0, 659424, 354362, 2033, 16384⟩
    (by decide) selected_cut_26048

theorem selected_cut_26049 : selected 8 ⟨659444, by decide⟩
    (prefixPartial 13 354363) = some ⟨13, 2, 0, 659444, 354363, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_354363_659444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354363 ⟨659444, by decide⟩ :=
  accepted_of_selected 13 354363 ⟨659444, by decide⟩ ⟨13, 2, 0, 659444, 354363, 1305, 16384⟩
    (by decide) selected_cut_26049

theorem unmarked_context_12_88590_659445 : frontier 9 ⟨659445, by decide⟩
    (prefixCache 12 88590) (prefixPartial 12 88590) = false := by
  decide +kernel

theorem node_context_12_88590_659445 : EJMOriginalGlobalDAGData.nodes 9 ⟨659445, by decide⟩ =
    .split (coordinate 12) (![⟨659307, by decide⟩,⟨659383, by decide⟩,⟨659424, by decide⟩,⟨659444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88590_659445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88590 ⟨659445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88590
    ⟨659445, by decide⟩ (by decide) (![⟨659307, by decide⟩,⟨659383, by decide⟩,⟨659424, by decide⟩,⟨659444, by decide⟩]) unmarked_context_12_88590_659445 node_context_12_88590_659445
  intro a
  fin_cases a
  · exact context_13_354360_659307
  · exact context_13_354361_659383
  · exact context_13_354362_659424
  · exact context_13_354363_659444

theorem selected_cut_26050 : selected 8 ⟨659517, by decide⟩
    (prefixPartial 13 354364) = some ⟨13, 2, 0, 659517, 354364, 3961, 16384⟩ := by
  decide +kernel

theorem context_13_354364_659517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354364 ⟨659517, by decide⟩ :=
  accepted_of_selected 13 354364 ⟨659517, by decide⟩ ⟨13, 2, 0, 659517, 354364, 3961, 16384⟩
    (by decide) selected_cut_26050

theorem selected_cut_26051 : selected 8 ⟨659600, by decide⟩
    (prefixPartial 13 354365) = some ⟨13, 2, 0, 659600, 354365, 3649, 16384⟩ := by
  decide +kernel

theorem context_13_354365_659600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354365 ⟨659600, by decide⟩ :=
  accepted_of_selected 13 354365 ⟨659600, by decide⟩ ⟨13, 2, 0, 659600, 354365, 3649, 16384⟩
    (by decide) selected_cut_26051

theorem selected_cut_26052 : selected 8 ⟨659625, by decide⟩
    (prefixPartial 13 354366) = some ⟨13, 2, 0, 659625, 354366, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_354366_659625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354366 ⟨659625, by decide⟩ :=
  accepted_of_selected 13 354366 ⟨659625, by decide⟩ ⟨13, 2, 0, 659625, 354366, 2029, 16384⟩
    (by decide) selected_cut_26052

theorem selected_cut_26053 : selected 8 ⟨659645, by decide⟩
    (prefixPartial 13 354367) = some ⟨13, 2, 0, 659645, 354367, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_354367_659645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354367 ⟨659645, by decide⟩ :=
  accepted_of_selected 13 354367 ⟨659645, by decide⟩ ⟨13, 2, 0, 659645, 354367, 1321, 16384⟩
    (by decide) selected_cut_26053

theorem unmarked_context_12_88591_659646 : frontier 9 ⟨659646, by decide⟩
    (prefixCache 12 88591) (prefixPartial 12 88591) = false := by
  decide +kernel

theorem node_context_12_88591_659646 : EJMOriginalGlobalDAGData.nodes 9 ⟨659646, by decide⟩ =
    .split (coordinate 12) (![⟨659517, by decide⟩,⟨659600, by decide⟩,⟨659625, by decide⟩,⟨659645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88591_659646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88591 ⟨659646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88591
    ⟨659646, by decide⟩ (by decide) (![⟨659517, by decide⟩,⟨659600, by decide⟩,⟨659625, by decide⟩,⟨659645, by decide⟩]) unmarked_context_12_88591_659646 node_context_12_88591_659646
  intro a
  fin_cases a
  · exact context_13_354364_659517
  · exact context_13_354365_659600
  · exact context_13_354366_659625
  · exact context_13_354367_659645

theorem unmarked_context_11_22147_659647 : frontier 10 ⟨659647, by decide⟩
    (prefixCache 11 22147) (prefixPartial 11 22147) = false := by
  decide +kernel

theorem node_context_11_22147_659647 : EJMOriginalGlobalDAGData.nodes 10 ⟨659647, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨659239, by decide⟩,⟨659445, by decide⟩,⟨659646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22147_659647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22147 ⟨659647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22147
    ⟨659647, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨659239, by decide⟩,⟨659445, by decide⟩,⟨659646, by decide⟩]) unmarked_context_11_22147_659647 node_context_11_22147_659647
  intro a
  fin_cases a
  · exact context_12_88588_448748
  · exact context_12_88589_659239
  · exact context_12_88590_659445
  · exact context_12_88591_659646

theorem unmarked_context_10_5536_659648 : frontier 11 ⟨659648, by decide⟩
    (prefixCache 10 5536) (prefixPartial 10 5536) = false := by
  decide +kernel

theorem node_context_10_5536_659648 : EJMOriginalGlobalDAGData.nodes 11 ⟨659648, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨658724, by decide⟩,⟨659076, by decide⟩,⟨659647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5536_659648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5536 ⟨659648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5536
    ⟨659648, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨658724, by decide⟩,⟨659076, by decide⟩,⟨659647, by decide⟩]) unmarked_context_10_5536_659648 node_context_10_5536_659648
  intro a
  fin_cases a
  · exact context_11_22144_434745
  · exact context_11_22145_658724
  · exact context_11_22146_659076
  · exact context_11_22147_659647

theorem selected_cut_26054 : selected 8 ⟨659687, by decide⟩
    (prefixPartial 13 354368) = some ⟨13, 2, 0, 659687, 354368, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_354368_659687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354368 ⟨659687, by decide⟩ :=
  accepted_of_selected 13 354368 ⟨659687, by decide⟩ ⟨13, 2, 0, 659687, 354368, 2357, 16384⟩
    (by decide) selected_cut_26054

theorem selected_cut_26055 : selected 8 ⟨659722, by decide⟩
    (prefixPartial 13 354369) = some ⟨13, 2, 0, 659722, 354369, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_354369_659722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354369 ⟨659722, by decide⟩ :=
  accepted_of_selected 13 354369 ⟨659722, by decide⟩ ⟨13, 2, 0, 659722, 354369, 1837, 16384⟩
    (by decide) selected_cut_26055

theorem selected_cut_26056 : selected 8 ⟨659743, by decide⟩
    (prefixPartial 13 354370) = some ⟨13, 2, 0, 659743, 354370, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_354370_659743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354370 ⟨659743, by decide⟩ :=
  accepted_of_selected 13 354370 ⟨659743, by decide⟩ ⟨13, 2, 0, 659743, 354370, 1405, 16384⟩
    (by decide) selected_cut_26056

theorem selected_cut_26057 : selected 8 ⟨659760, by decide⟩
    (prefixPartial 13 354371) = some ⟨13, 2, 0, 659760, 354371, 841, 16384⟩ := by
  decide +kernel

theorem context_13_354371_659760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354371 ⟨659760, by decide⟩ :=
  accepted_of_selected 13 354371 ⟨659760, by decide⟩ ⟨13, 2, 0, 659760, 354371, 841, 16384⟩
    (by decide) selected_cut_26057

theorem unmarked_context_12_88592_659761 : frontier 9 ⟨659761, by decide⟩
    (prefixCache 12 88592) (prefixPartial 12 88592) = false := by
  decide +kernel

theorem node_context_12_88592_659761 : EJMOriginalGlobalDAGData.nodes 9 ⟨659761, by decide⟩ =
    .split (coordinate 12) (![⟨659687, by decide⟩,⟨659722, by decide⟩,⟨659743, by decide⟩,⟨659760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88592_659761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88592 ⟨659761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88592
    ⟨659761, by decide⟩ (by decide) (![⟨659687, by decide⟩,⟨659722, by decide⟩,⟨659743, by decide⟩,⟨659760, by decide⟩]) unmarked_context_12_88592_659761 node_context_12_88592_659761
  intro a
  fin_cases a
  · exact context_13_354368_659687
  · exact context_13_354369_659722
  · exact context_13_354370_659743
  · exact context_13_354371_659760

theorem selected_cut_26058 : selected 8 ⟨659800, by decide⟩
    (prefixPartial 13 354372) = some ⟨13, 2, 0, 659800, 354372, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_354372_659800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354372 ⟨659800, by decide⟩ :=
  accepted_of_selected 13 354372 ⟨659800, by decide⟩ ⟨13, 2, 0, 659800, 354372, 2465, 16384⟩
    (by decide) selected_cut_26058

theorem selected_cut_26059 : selected 8 ⟨659829, by decide⟩
    (prefixPartial 13 354373) = some ⟨13, 2, 0, 659829, 354373, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_354373_659829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354373 ⟨659829, by decide⟩ :=
  accepted_of_selected 13 354373 ⟨659829, by decide⟩ ⟨13, 2, 0, 659829, 354373, 1817, 16384⟩
    (by decide) selected_cut_26059

theorem selected_cut_26060 : selected 8 ⟨659844, by decide⟩
    (prefixPartial 13 354374) = some ⟨13, 2, 0, 659844, 354374, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_354374_659844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354374 ⟨659844, by decide⟩ :=
  accepted_of_selected 13 354374 ⟨659844, by decide⟩ ⟨13, 2, 0, 659844, 354374, 1377, 16384⟩
    (by decide) selected_cut_26060

theorem selected_cut_26061 : selected 8 ⟨659855, by decide⟩
    (prefixPartial 13 354375) = some ⟨13, 2, 0, 659855, 354375, 957, 16384⟩ := by
  decide +kernel

theorem context_13_354375_659855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354375 ⟨659855, by decide⟩ :=
  accepted_of_selected 13 354375 ⟨659855, by decide⟩ ⟨13, 2, 0, 659855, 354375, 957, 16384⟩
    (by decide) selected_cut_26061

theorem unmarked_context_12_88593_659856 : frontier 9 ⟨659856, by decide⟩
    (prefixCache 12 88593) (prefixPartial 12 88593) = false := by
  decide +kernel

theorem node_context_12_88593_659856 : EJMOriginalGlobalDAGData.nodes 9 ⟨659856, by decide⟩ =
    .split (coordinate 12) (![⟨659800, by decide⟩,⟨659829, by decide⟩,⟨659844, by decide⟩,⟨659855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88593_659856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88593 ⟨659856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88593
    ⟨659856, by decide⟩ (by decide) (![⟨659800, by decide⟩,⟨659829, by decide⟩,⟨659844, by decide⟩,⟨659855, by decide⟩]) unmarked_context_12_88593_659856 node_context_12_88593_659856
  intro a
  fin_cases a
  · exact context_13_354372_659800
  · exact context_13_354373_659829
  · exact context_13_354374_659844
  · exact context_13_354375_659855

theorem selected_cut_26062 : selected 8 ⟨659894, by decide⟩
    (prefixPartial 13 354376) = some ⟨13, 2, 0, 659894, 354376, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_354376_659894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354376 ⟨659894, by decide⟩ :=
  accepted_of_selected 13 354376 ⟨659894, by decide⟩ ⟨13, 2, 0, 659894, 354376, 2681, 16384⟩
    (by decide) selected_cut_26062

theorem selected_cut_26063 : selected 8 ⟨659920, by decide⟩
    (prefixPartial 13 354377) = some ⟨13, 2, 0, 659920, 354377, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_354377_659920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354377 ⟨659920, by decide⟩ :=
  accepted_of_selected 13 354377 ⟨659920, by decide⟩ ⟨13, 2, 0, 659920, 354377, 2069, 16384⟩
    (by decide) selected_cut_26063

theorem selected_cut_26064 : selected 8 ⟨659940, by decide⟩
    (prefixPartial 13 354378) = some ⟨13, 2, 0, 659940, 354378, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_354378_659940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354378 ⟨659940, by decide⟩ :=
  accepted_of_selected 13 354378 ⟨659940, by decide⟩ ⟨13, 2, 0, 659940, 354378, 1509, 16384⟩
    (by decide) selected_cut_26064

theorem selected_cut_26065 : selected 8 ⟨659957, by decide⟩
    (prefixPartial 13 354379) = some ⟨13, 2, 0, 659957, 354379, 953, 16384⟩ := by
  decide +kernel

theorem context_13_354379_659957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354379 ⟨659957, by decide⟩ :=
  accepted_of_selected 13 354379 ⟨659957, by decide⟩ ⟨13, 2, 0, 659957, 354379, 953, 16384⟩
    (by decide) selected_cut_26065

theorem unmarked_context_12_88594_659958 : frontier 9 ⟨659958, by decide⟩
    (prefixCache 12 88594) (prefixPartial 12 88594) = false := by
  decide +kernel

theorem node_context_12_88594_659958 : EJMOriginalGlobalDAGData.nodes 9 ⟨659958, by decide⟩ =
    .split (coordinate 12) (![⟨659894, by decide⟩,⟨659920, by decide⟩,⟨659940, by decide⟩,⟨659957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88594_659958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88594 ⟨659958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88594
    ⟨659958, by decide⟩ (by decide) (![⟨659894, by decide⟩,⟨659920, by decide⟩,⟨659940, by decide⟩,⟨659957, by decide⟩]) unmarked_context_12_88594_659958 node_context_12_88594_659958
  intro a
  fin_cases a
  · exact context_13_354376_659894
  · exact context_13_354377_659920
  · exact context_13_354378_659940
  · exact context_13_354379_659957

theorem selected_cut_26066 : selected 8 ⟨660010, by decide⟩
    (prefixPartial 13 354380) = some ⟨13, 2, 0, 660010, 354380, 3017, 16384⟩ := by
  decide +kernel

theorem context_13_354380_660010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354380 ⟨660010, by decide⟩ :=
  accepted_of_selected 13 354380 ⟨660010, by decide⟩ ⟨13, 2, 0, 660010, 354380, 3017, 16384⟩
    (by decide) selected_cut_26066

theorem selected_cut_26067 : selected 8 ⟨660054, by decide⟩
    (prefixPartial 13 354381) = some ⟨13, 2, 0, 660054, 354381, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_354381_660054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354381 ⟨660054, by decide⟩ :=
  accepted_of_selected 13 354381 ⟨660054, by decide⟩ ⟨13, 2, 0, 660054, 354381, 2261, 16384⟩
    (by decide) selected_cut_26067

theorem selected_cut_26068 : selected 8 ⟨660072, by decide⟩
    (prefixPartial 13 354382) = some ⟨13, 2, 0, 660072, 354382, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_354382_660072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354382 ⟨660072, by decide⟩ :=
  accepted_of_selected 13 354382 ⟨660072, by decide⟩ ⟨13, 2, 0, 660072, 354382, 1653, 16384⟩
    (by decide) selected_cut_26068

theorem selected_cut_26069 : selected 8 ⟨660085, by decide⟩
    (prefixPartial 13 354383) = some ⟨13, 2, 0, 660085, 354383, 961, 16384⟩ := by
  decide +kernel

theorem context_13_354383_660085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354383 ⟨660085, by decide⟩ :=
  accepted_of_selected 13 354383 ⟨660085, by decide⟩ ⟨13, 2, 0, 660085, 354383, 961, 16384⟩
    (by decide) selected_cut_26069

theorem unmarked_context_12_88595_660086 : frontier 9 ⟨660086, by decide⟩
    (prefixCache 12 88595) (prefixPartial 12 88595) = false := by
  decide +kernel

theorem node_context_12_88595_660086 : EJMOriginalGlobalDAGData.nodes 9 ⟨660086, by decide⟩ =
    .split (coordinate 12) (![⟨660010, by decide⟩,⟨660054, by decide⟩,⟨660072, by decide⟩,⟨660085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88595_660086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88595 ⟨660086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88595
    ⟨660086, by decide⟩ (by decide) (![⟨660010, by decide⟩,⟨660054, by decide⟩,⟨660072, by decide⟩,⟨660085, by decide⟩]) unmarked_context_12_88595_660086 node_context_12_88595_660086
  intro a
  fin_cases a
  · exact context_13_354380_660010
  · exact context_13_354381_660054
  · exact context_13_354382_660072
  · exact context_13_354383_660085

theorem unmarked_context_11_22148_660087 : frontier 10 ⟨660087, by decide⟩
    (prefixCache 11 22148) (prefixPartial 11 22148) = false := by
  decide +kernel

theorem node_context_11_22148_660087 : EJMOriginalGlobalDAGData.nodes 10 ⟨660087, by decide⟩ =
    .split (coordinate 11) (![⟨659761, by decide⟩,⟨659856, by decide⟩,⟨659958, by decide⟩,⟨660086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22148_660087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22148 ⟨660087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22148
    ⟨660087, by decide⟩ (by decide) (![⟨659761, by decide⟩,⟨659856, by decide⟩,⟨659958, by decide⟩,⟨660086, by decide⟩]) unmarked_context_11_22148_660087 node_context_11_22148_660087
  intro a
  fin_cases a
  · exact context_12_88592_659761
  · exact context_12_88593_659856
  · exact context_12_88594_659958
  · exact context_12_88595_660086

theorem selected_cut_26070 : selected 8 ⟨660120, by decide⟩
    (prefixPartial 13 354384) = some ⟨13, 2, 0, 660120, 354384, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_354384_660120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354384 ⟨660120, by decide⟩ :=
  accepted_of_selected 13 354384 ⟨660120, by decide⟩ ⟨13, 2, 0, 660120, 354384, 1973, 16384⟩
    (by decide) selected_cut_26070

theorem selected_cut_26071 : selected 8 ⟨660163, by decide⟩
    (prefixPartial 13 354385) = some ⟨13, 2, 0, 660163, 354385, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_354385_660163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354385 ⟨660163, by decide⟩ :=
  accepted_of_selected 13 354385 ⟨660163, by decide⟩ ⟨13, 2, 0, 660163, 354385, 2309, 16384⟩
    (by decide) selected_cut_26071

theorem selected_cut_26072 : selected 8 ⟨660178, by decide⟩
    (prefixPartial 13 354386) = some ⟨13, 2, 0, 660178, 354386, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_354386_660178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354386 ⟨660178, by decide⟩ :=
  accepted_of_selected 13 354386 ⟨660178, by decide⟩ ⟨13, 2, 0, 660178, 354386, 1253, 16384⟩
    (by decide) selected_cut_26072

theorem selected_cut_26073 : selected 8 ⟨660192, by decide⟩
    (prefixPartial 13 354387) = some ⟨13, 2, 0, 660192, 354387, 985, 16384⟩ := by
  decide +kernel

theorem context_13_354387_660192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354387 ⟨660192, by decide⟩ :=
  accepted_of_selected 13 354387 ⟨660192, by decide⟩ ⟨13, 2, 0, 660192, 354387, 985, 16384⟩
    (by decide) selected_cut_26073

theorem unmarked_context_12_88596_660193 : frontier 9 ⟨660193, by decide⟩
    (prefixCache 12 88596) (prefixPartial 12 88596) = false := by
  decide +kernel

theorem node_context_12_88596_660193 : EJMOriginalGlobalDAGData.nodes 9 ⟨660193, by decide⟩ =
    .split (coordinate 12) (![⟨660120, by decide⟩,⟨660163, by decide⟩,⟨660178, by decide⟩,⟨660192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88596_660193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88596 ⟨660193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88596
    ⟨660193, by decide⟩ (by decide) (![⟨660120, by decide⟩,⟨660163, by decide⟩,⟨660178, by decide⟩,⟨660192, by decide⟩]) unmarked_context_12_88596_660193 node_context_12_88596_660193
  intro a
  fin_cases a
  · exact context_13_354384_660120
  · exact context_13_354385_660163
  · exact context_13_354386_660178
  · exact context_13_354387_660192

theorem selected_cut_26074 : selected 8 ⟨660220, by decide⟩
    (prefixPartial 13 354388) = some ⟨13, 2, 0, 660220, 354388, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_354388_660220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354388 ⟨660220, by decide⟩ :=
  accepted_of_selected 13 354388 ⟨660220, by decide⟩ ⟨13, 2, 0, 660220, 354388, 2037, 16384⟩
    (by decide) selected_cut_26074

theorem selected_cut_26075 : selected 8 ⟨660243, by decide⟩
    (prefixPartial 13 354389) = some ⟨13, 2, 0, 660243, 354389, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_354389_660243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354389 ⟨660243, by decide⟩ :=
  accepted_of_selected 13 354389 ⟨660243, by decide⟩ ⟨13, 2, 0, 660243, 354389, 1805, 16384⟩
    (by decide) selected_cut_26075

theorem selected_cut_26076 : selected 8 ⟨660262, by decide⟩
    (prefixPartial 13 354390) = some ⟨13, 2, 0, 660262, 354390, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_354390_660262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354390 ⟨660262, by decide⟩ :=
  accepted_of_selected 13 354390 ⟨660262, by decide⟩ ⟨13, 2, 0, 660262, 354390, 1049, 16384⟩
    (by decide) selected_cut_26076

theorem selected_cut_26077 : selected 8 ⟨660272, by decide⟩
    (prefixPartial 13 354391) = some ⟨13, 2, 0, 660272, 354391, 917, 16384⟩ := by
  decide +kernel

theorem context_13_354391_660272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354391 ⟨660272, by decide⟩ :=
  accepted_of_selected 13 354391 ⟨660272, by decide⟩ ⟨13, 2, 0, 660272, 354391, 917, 16384⟩
    (by decide) selected_cut_26077

theorem unmarked_context_12_88597_660273 : frontier 9 ⟨660273, by decide⟩
    (prefixCache 12 88597) (prefixPartial 12 88597) = false := by
  decide +kernel

theorem node_context_12_88597_660273 : EJMOriginalGlobalDAGData.nodes 9 ⟨660273, by decide⟩ =
    .split (coordinate 12) (![⟨660220, by decide⟩,⟨660243, by decide⟩,⟨660262, by decide⟩,⟨660272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88597_660273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88597 ⟨660273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88597
    ⟨660273, by decide⟩ (by decide) (![⟨660220, by decide⟩,⟨660243, by decide⟩,⟨660262, by decide⟩,⟨660272, by decide⟩]) unmarked_context_12_88597_660273 node_context_12_88597_660273
  intro a
  fin_cases a
  · exact context_13_354388_660220
  · exact context_13_354389_660243
  · exact context_13_354390_660262
  · exact context_13_354391_660272

theorem selected_cut_26078 : selected 8 ⟨660302, by decide⟩
    (prefixPartial 13 354392) = some ⟨13, 2, 0, 660302, 354392, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_354392_660302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354392 ⟨660302, by decide⟩ :=
  accepted_of_selected 13 354392 ⟨660302, by decide⟩ ⟨13, 2, 0, 660302, 354392, 2097, 16384⟩
    (by decide) selected_cut_26078

theorem selected_cut_26079 : selected 8 ⟨660342, by decide⟩
    (prefixPartial 13 354393) = some ⟨13, 2, 0, 660342, 354393, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_354393_660342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354393 ⟨660342, by decide⟩ :=
  accepted_of_selected 13 354393 ⟨660342, by decide⟩ ⟨13, 2, 0, 660342, 354393, 2193, 16384⟩
    (by decide) selected_cut_26079

theorem selected_cut_26080 : selected 8 ⟨660360, by decide⟩
    (prefixPartial 13 354394) = some ⟨13, 2, 0, 660360, 354394, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_354394_660360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354394 ⟨660360, by decide⟩ :=
  accepted_of_selected 13 354394 ⟨660360, by decide⟩ ⟨13, 2, 0, 660360, 354394, 1269, 16384⟩
    (by decide) selected_cut_26080

theorem selected_cut_26081 : selected 8 ⟨660373, by decide⟩
    (prefixPartial 13 354395) = some ⟨13, 2, 0, 660373, 354395, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_354395_660373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354395 ⟨660373, by decide⟩ :=
  accepted_of_selected 13 354395 ⟨660373, by decide⟩ ⟨13, 2, 0, 660373, 354395, 1025, 16384⟩
    (by decide) selected_cut_26081

theorem unmarked_context_12_88598_660374 : frontier 9 ⟨660374, by decide⟩
    (prefixCache 12 88598) (prefixPartial 12 88598) = false := by
  decide +kernel

theorem node_context_12_88598_660374 : EJMOriginalGlobalDAGData.nodes 9 ⟨660374, by decide⟩ =
    .split (coordinate 12) (![⟨660302, by decide⟩,⟨660342, by decide⟩,⟨660360, by decide⟩,⟨660373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88598_660374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88598 ⟨660374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88598
    ⟨660374, by decide⟩ (by decide) (![⟨660302, by decide⟩,⟨660342, by decide⟩,⟨660360, by decide⟩,⟨660373, by decide⟩]) unmarked_context_12_88598_660374 node_context_12_88598_660374
  intro a
  fin_cases a
  · exact context_13_354392_660302
  · exact context_13_354393_660342
  · exact context_13_354394_660360
  · exact context_13_354395_660373

theorem selected_cut_26082 : selected 8 ⟨660412, by decide⟩
    (prefixPartial 13 354396) = some ⟨13, 2, 0, 660412, 354396, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_354396_660412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354396 ⟨660412, by decide⟩ :=
  accepted_of_selected 13 354396 ⟨660412, by decide⟩ ⟨13, 2, 0, 660412, 354396, 2277, 16384⟩
    (by decide) selected_cut_26082

theorem selected_cut_26083 : selected 8 ⟨660460, by decide⟩
    (prefixPartial 13 354397) = some ⟨13, 2, 0, 660460, 354397, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_354397_660460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354397 ⟨660460, by decide⟩ :=
  accepted_of_selected 13 354397 ⟨660460, by decide⟩ ⟨13, 2, 0, 660460, 354397, 2357, 16384⟩
    (by decide) selected_cut_26083

theorem selected_cut_26084 : selected 8 ⟨660475, by decide⟩
    (prefixPartial 13 354398) = some ⟨13, 2, 0, 660475, 354398, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_354398_660475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354398 ⟨660475, by decide⟩ :=
  accepted_of_selected 13 354398 ⟨660475, by decide⟩ ⟨13, 2, 0, 660475, 354398, 1313, 16384⟩
    (by decide) selected_cut_26084

theorem selected_cut_26085 : selected 8 ⟨660486, by decide⟩
    (prefixPartial 13 354399) = some ⟨13, 2, 0, 660486, 354399, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_354399_660486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354399 ⟨660486, by decide⟩ :=
  accepted_of_selected 13 354399 ⟨660486, by decide⟩ ⟨13, 2, 0, 660486, 354399, 1025, 16384⟩
    (by decide) selected_cut_26085

theorem unmarked_context_12_88599_660487 : frontier 9 ⟨660487, by decide⟩
    (prefixCache 12 88599) (prefixPartial 12 88599) = false := by
  decide +kernel

theorem node_context_12_88599_660487 : EJMOriginalGlobalDAGData.nodes 9 ⟨660487, by decide⟩ =
    .split (coordinate 12) (![⟨660412, by decide⟩,⟨660460, by decide⟩,⟨660475, by decide⟩,⟨660486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88599_660487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88599 ⟨660487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88599
    ⟨660487, by decide⟩ (by decide) (![⟨660412, by decide⟩,⟨660460, by decide⟩,⟨660475, by decide⟩,⟨660486, by decide⟩]) unmarked_context_12_88599_660487 node_context_12_88599_660487
  intro a
  fin_cases a
  · exact context_13_354396_660412
  · exact context_13_354397_660460
  · exact context_13_354398_660475
  · exact context_13_354399_660486

theorem unmarked_context_11_22149_660488 : frontier 10 ⟨660488, by decide⟩
    (prefixCache 11 22149) (prefixPartial 11 22149) = false := by
  decide +kernel

theorem node_context_11_22149_660488 : EJMOriginalGlobalDAGData.nodes 10 ⟨660488, by decide⟩ =
    .split (coordinate 11) (![⟨660193, by decide⟩,⟨660273, by decide⟩,⟨660374, by decide⟩,⟨660487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22149_660488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22149 ⟨660488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22149
    ⟨660488, by decide⟩ (by decide) (![⟨660193, by decide⟩,⟨660273, by decide⟩,⟨660374, by decide⟩,⟨660487, by decide⟩]) unmarked_context_11_22149_660488 node_context_11_22149_660488
  intro a
  fin_cases a
  · exact context_12_88596_660193
  · exact context_12_88597_660273
  · exact context_12_88598_660374
  · exact context_12_88599_660487

theorem selected_cut_26086 : selected 8 ⟨660511, by decide⟩
    (prefixPartial 13 354400) = some ⟨13, 2, 0, 660511, 354400, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_354400_660511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354400 ⟨660511, by decide⟩ :=
  accepted_of_selected 13 354400 ⟨660511, by decide⟩ ⟨13, 2, 0, 660511, 354400, 1605, 16384⟩
    (by decide) selected_cut_26086

theorem selected_cut_26087 : selected 8 ⟨660538, by decide⟩
    (prefixPartial 13 354401) = some ⟨13, 2, 0, 660538, 354401, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_354401_660538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354401 ⟨660538, by decide⟩ :=
  accepted_of_selected 13 354401 ⟨660538, by decide⟩ ⟨13, 2, 0, 660538, 354401, 1741, 16384⟩
    (by decide) selected_cut_26087

theorem selected_cut_26088 : selected 8 ⟨660558, by decide⟩
    (prefixPartial 13 354402) = some ⟨13, 2, 0, 660558, 354402, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_354402_660558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354402 ⟨660558, by decide⟩ :=
  accepted_of_selected 13 354402 ⟨660558, by decide⟩ ⟨13, 2, 0, 660558, 354402, 1545, 16384⟩
    (by decide) selected_cut_26088

theorem selected_cut_26089 : selected 8 ⟨660565, by decide⟩
    (prefixPartial 13 354403) = some ⟨13, 2, 0, 660565, 354403, 901, 16384⟩ := by
  decide +kernel

theorem context_13_354403_660565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354403 ⟨660565, by decide⟩ :=
  accepted_of_selected 13 354403 ⟨660565, by decide⟩ ⟨13, 2, 0, 660565, 354403, 901, 16384⟩
    (by decide) selected_cut_26089

theorem unmarked_context_12_88600_660566 : frontier 9 ⟨660566, by decide⟩
    (prefixCache 12 88600) (prefixPartial 12 88600) = false := by
  decide +kernel

theorem node_context_12_88600_660566 : EJMOriginalGlobalDAGData.nodes 9 ⟨660566, by decide⟩ =
    .split (coordinate 12) (![⟨660511, by decide⟩,⟨660538, by decide⟩,⟨660558, by decide⟩,⟨660565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88600_660566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88600 ⟨660566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88600
    ⟨660566, by decide⟩ (by decide) (![⟨660511, by decide⟩,⟨660538, by decide⟩,⟨660558, by decide⟩,⟨660565, by decide⟩]) unmarked_context_12_88600_660566 node_context_12_88600_660566
  intro a
  fin_cases a
  · exact context_13_354400_660511
  · exact context_13_354401_660538
  · exact context_13_354402_660558
  · exact context_13_354403_660565

theorem selected_cut_26090 : selected 8 ⟨660589, by decide⟩
    (prefixPartial 13 354404) = some ⟨13, 2, 0, 660589, 354404, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_354404_660589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354404 ⟨660589, by decide⟩ :=
  accepted_of_selected 13 354404 ⟨660589, by decide⟩ ⟨13, 2, 0, 660589, 354404, 1633, 16384⟩
    (by decide) selected_cut_26090

theorem selected_cut_26091 : selected 8 ⟨660606, by decide⟩
    (prefixPartial 13 354405) = some ⟨13, 2, 0, 660606, 354405, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_354405_660606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354405 ⟨660606, by decide⟩ :=
  accepted_of_selected 13 354405 ⟨660606, by decide⟩ ⟨13, 2, 0, 660606, 354405, 1389, 16384⟩
    (by decide) selected_cut_26091

theorem selected_cut_26092 : selected 8 ⟨660625, by decide⟩
    (prefixPartial 13 354406) = some ⟨13, 2, 0, 660625, 354406, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_354406_660625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354406 ⟨660625, by decide⟩ :=
  accepted_of_selected 13 354406 ⟨660625, by decide⟩ ⟨13, 2, 0, 660625, 354406, 1369, 16384⟩
    (by decide) selected_cut_26092

theorem selected_cut_26093 : selected 8 ⟨660634, by decide⟩
    (prefixPartial 13 354407) = some ⟨13, 2, 0, 660634, 354407, 937, 16384⟩ := by
  decide +kernel

theorem context_13_354407_660634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354407 ⟨660634, by decide⟩ :=
  accepted_of_selected 13 354407 ⟨660634, by decide⟩ ⟨13, 2, 0, 660634, 354407, 937, 16384⟩
    (by decide) selected_cut_26093

theorem unmarked_context_12_88601_660635 : frontier 9 ⟨660635, by decide⟩
    (prefixCache 12 88601) (prefixPartial 12 88601) = false := by
  decide +kernel

theorem node_context_12_88601_660635 : EJMOriginalGlobalDAGData.nodes 9 ⟨660635, by decide⟩ =
    .split (coordinate 12) (![⟨660589, by decide⟩,⟨660606, by decide⟩,⟨660625, by decide⟩,⟨660634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88601_660635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88601 ⟨660635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88601
    ⟨660635, by decide⟩ (by decide) (![⟨660589, by decide⟩,⟨660606, by decide⟩,⟨660625, by decide⟩,⟨660634, by decide⟩]) unmarked_context_12_88601_660635 node_context_12_88601_660635
  intro a
  fin_cases a
  · exact context_13_354404_660589
  · exact context_13_354405_660606
  · exact context_13_354406_660625
  · exact context_13_354407_660634

theorem selected_cut_26094 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 88602) = some ⟨12, 1, 0, 660636, 88602, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88602_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88602 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 88602 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 88602, 1, 65536⟩
    (by decide) selected_cut_26094

theorem selected_cut_26095 : selected 8 ⟨660671, by decide⟩
    (prefixPartial 13 354412) = some ⟨13, 2, 0, 660671, 354412, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_354412_660671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354412 ⟨660671, by decide⟩ :=
  accepted_of_selected 13 354412 ⟨660671, by decide⟩ ⟨13, 2, 0, 660671, 354412, 2021, 16384⟩
    (by decide) selected_cut_26095

theorem selected_cut_26096 : selected 8 ⟨660713, by decide⟩
    (prefixPartial 13 354413) = some ⟨13, 2, 0, 660713, 354413, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_354413_660713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354413 ⟨660713, by decide⟩ :=
  accepted_of_selected 13 354413 ⟨660713, by decide⟩ ⟨13, 2, 0, 660713, 354413, 2201, 16384⟩
    (by decide) selected_cut_26096

theorem selected_cut_26097 : selected 8 ⟨660728, by decide⟩
    (prefixPartial 13 354414) = some ⟨13, 2, 0, 660728, 354414, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_354414_660728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354414 ⟨660728, by decide⟩ :=
  accepted_of_selected 13 354414 ⟨660728, by decide⟩ ⟨13, 2, 0, 660728, 354414, 1561, 16384⟩
    (by decide) selected_cut_26097

theorem selected_cut_26098 : selected 8 ⟨660739, by decide⟩
    (prefixPartial 13 354415) = some ⟨13, 2, 0, 660739, 354415, 937, 16384⟩ := by
  decide +kernel

theorem context_13_354415_660739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354415 ⟨660739, by decide⟩ :=
  accepted_of_selected 13 354415 ⟨660739, by decide⟩ ⟨13, 2, 0, 660739, 354415, 937, 16384⟩
    (by decide) selected_cut_26098

theorem unmarked_context_12_88603_660740 : frontier 9 ⟨660740, by decide⟩
    (prefixCache 12 88603) (prefixPartial 12 88603) = false := by
  decide +kernel

theorem node_context_12_88603_660740 : EJMOriginalGlobalDAGData.nodes 9 ⟨660740, by decide⟩ =
    .split (coordinate 12) (![⟨660671, by decide⟩,⟨660713, by decide⟩,⟨660728, by decide⟩,⟨660739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88603_660740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88603 ⟨660740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88603
    ⟨660740, by decide⟩ (by decide) (![⟨660671, by decide⟩,⟨660713, by decide⟩,⟨660728, by decide⟩,⟨660739, by decide⟩]) unmarked_context_12_88603_660740 node_context_12_88603_660740
  intro a
  fin_cases a
  · exact context_13_354412_660671
  · exact context_13_354413_660713
  · exact context_13_354414_660728
  · exact context_13_354415_660739

theorem unmarked_context_11_22150_660741 : frontier 10 ⟨660741, by decide⟩
    (prefixCache 11 22150) (prefixPartial 11 22150) = false := by
  decide +kernel

theorem node_context_11_22150_660741 : EJMOriginalGlobalDAGData.nodes 10 ⟨660741, by decide⟩ =
    .split (coordinate 11) (![⟨660566, by decide⟩,⟨660635, by decide⟩,⟨660636, by decide⟩,⟨660740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22150_660741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22150 ⟨660741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22150
    ⟨660741, by decide⟩ (by decide) (![⟨660566, by decide⟩,⟨660635, by decide⟩,⟨660636, by decide⟩,⟨660740, by decide⟩]) unmarked_context_11_22150_660741 node_context_11_22150_660741
  intro a
  fin_cases a
  · exact context_12_88600_660566
  · exact context_12_88601_660635
  · exact context_12_88602_660636
  · exact context_12_88603_660740

theorem selected_cut_26099 : selected 8 ⟨660771, by decide⟩
    (prefixPartial 13 354416) = some ⟨13, 2, 0, 660771, 354416, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_354416_660771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354416 ⟨660771, by decide⟩ :=
  accepted_of_selected 13 354416 ⟨660771, by decide⟩ ⟨13, 2, 0, 660771, 354416, 1657, 16384⟩
    (by decide) selected_cut_26099

theorem selected_cut_26100 : selected 8 ⟨660809, by decide⟩
    (prefixPartial 13 354417) = some ⟨13, 2, 0, 660809, 354417, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_354417_660809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354417 ⟨660809, by decide⟩ :=
  accepted_of_selected 13 354417 ⟨660809, by decide⟩ ⟨13, 2, 0, 660809, 354417, 2205, 16384⟩
    (by decide) selected_cut_26100

theorem selected_cut_26101 : selected 8 ⟨660836, by decide⟩
    (prefixPartial 13 354418) = some ⟨13, 2, 0, 660836, 354418, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_354418_660836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354418 ⟨660836, by decide⟩ :=
  accepted_of_selected 13 354418 ⟨660836, by decide⟩ ⟨13, 2, 0, 660836, 354418, 1745, 16384⟩
    (by decide) selected_cut_26101

theorem selected_cut_26102 : selected 8 ⟨660847, by decide⟩
    (prefixPartial 13 354419) = some ⟨13, 2, 0, 660847, 354419, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_354419_660847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354419 ⟨660847, by decide⟩ :=
  accepted_of_selected 13 354419 ⟨660847, by decide⟩ ⟨13, 2, 0, 660847, 354419, 1013, 16384⟩
    (by decide) selected_cut_26102

theorem unmarked_context_12_88604_660848 : frontier 9 ⟨660848, by decide⟩
    (prefixCache 12 88604) (prefixPartial 12 88604) = false := by
  decide +kernel

theorem node_context_12_88604_660848 : EJMOriginalGlobalDAGData.nodes 9 ⟨660848, by decide⟩ =
    .split (coordinate 12) (![⟨660771, by decide⟩,⟨660809, by decide⟩,⟨660836, by decide⟩,⟨660847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88604_660848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88604 ⟨660848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88604
    ⟨660848, by decide⟩ (by decide) (![⟨660771, by decide⟩,⟨660809, by decide⟩,⟨660836, by decide⟩,⟨660847, by decide⟩]) unmarked_context_12_88604_660848 node_context_12_88604_660848
  intro a
  fin_cases a
  · exact context_13_354416_660771
  · exact context_13_354417_660809
  · exact context_13_354418_660836
  · exact context_13_354419_660847

theorem selected_cut_26103 : selected 8 ⟨660872, by decide⟩
    (prefixPartial 13 354420) = some ⟨13, 2, 0, 660872, 354420, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_354420_660872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354420 ⟨660872, by decide⟩ :=
  accepted_of_selected 13 354420 ⟨660872, by decide⟩ ⟨13, 2, 0, 660872, 354420, 1697, 16384⟩
    (by decide) selected_cut_26103

theorem selected_cut_26104 : selected 8 ⟨660901, by decide⟩
    (prefixPartial 13 354421) = some ⟨13, 2, 0, 660901, 354421, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_354421_660901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354421 ⟨660901, by decide⟩ :=
  accepted_of_selected 13 354421 ⟨660901, by decide⟩ ⟨13, 2, 0, 660901, 354421, 1821, 16384⟩
    (by decide) selected_cut_26104

theorem selected_cut_26105 : selected 8 ⟨660922, by decide⟩
    (prefixPartial 13 354422) = some ⟨13, 2, 0, 660922, 354422, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_354422_660922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354422 ⟨660922, by decide⟩ :=
  accepted_of_selected 13 354422 ⟨660922, by decide⟩ ⟨13, 2, 0, 660922, 354422, 1461, 16384⟩
    (by decide) selected_cut_26105

theorem selected_cut_26106 : selected 8 ⟨660932, by decide⟩
    (prefixPartial 13 354423) = some ⟨13, 2, 0, 660932, 354423, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_354423_660932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354423 ⟨660932, by decide⟩ :=
  accepted_of_selected 13 354423 ⟨660932, by decide⟩ ⟨13, 2, 0, 660932, 354423, 1021, 16384⟩
    (by decide) selected_cut_26106

theorem unmarked_context_12_88605_660933 : frontier 9 ⟨660933, by decide⟩
    (prefixCache 12 88605) (prefixPartial 12 88605) = false := by
  decide +kernel

theorem node_context_12_88605_660933 : EJMOriginalGlobalDAGData.nodes 9 ⟨660933, by decide⟩ =
    .split (coordinate 12) (![⟨660872, by decide⟩,⟨660901, by decide⟩,⟨660922, by decide⟩,⟨660932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88605_660933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88605 ⟨660933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88605
    ⟨660933, by decide⟩ (by decide) (![⟨660872, by decide⟩,⟨660901, by decide⟩,⟨660922, by decide⟩,⟨660932, by decide⟩]) unmarked_context_12_88605_660933 node_context_12_88605_660933
  intro a
  fin_cases a
  · exact context_13_354420_660872
  · exact context_13_354421_660901
  · exact context_13_354422_660922
  · exact context_13_354423_660932

theorem selected_cut_26107 : selected 8 ⟨660965, by decide⟩
    (prefixPartial 13 354424) = some ⟨13, 2, 0, 660965, 354424, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_354424_660965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354424 ⟨660965, by decide⟩ :=
  accepted_of_selected 13 354424 ⟨660965, by decide⟩ ⟨13, 2, 0, 660965, 354424, 1793, 16384⟩
    (by decide) selected_cut_26107

theorem selected_cut_26108 : selected 8 ⟨661003, by decide⟩
    (prefixPartial 13 354425) = some ⟨13, 2, 0, 661003, 354425, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_354425_661003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354425 ⟨661003, by decide⟩ :=
  accepted_of_selected 13 354425 ⟨661003, by decide⟩ ⟨13, 2, 0, 661003, 354425, 2329, 16384⟩
    (by decide) selected_cut_26108

theorem selected_cut_26109 : selected 8 ⟨661029, by decide⟩
    (prefixPartial 13 354426) = some ⟨13, 2, 0, 661029, 354426, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_354426_661029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354426 ⟨661029, by decide⟩ :=
  accepted_of_selected 13 354426 ⟨661029, by decide⟩ ⟨13, 2, 0, 661029, 354426, 1713, 16384⟩
    (by decide) selected_cut_26109

theorem selected_cut_26110 : selected 8 ⟨661043, by decide⟩
    (prefixPartial 13 354427) = some ⟨13, 2, 0, 661043, 354427, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_354427_661043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354427 ⟨661043, by decide⟩ :=
  accepted_of_selected 13 354427 ⟨661043, by decide⟩ ⟨13, 2, 0, 661043, 354427, 1045, 16384⟩
    (by decide) selected_cut_26110

theorem unmarked_context_12_88606_661044 : frontier 9 ⟨661044, by decide⟩
    (prefixCache 12 88606) (prefixPartial 12 88606) = false := by
  decide +kernel

theorem node_context_12_88606_661044 : EJMOriginalGlobalDAGData.nodes 9 ⟨661044, by decide⟩ =
    .split (coordinate 12) (![⟨660965, by decide⟩,⟨661003, by decide⟩,⟨661029, by decide⟩,⟨661043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88606_661044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88606 ⟨661044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88606
    ⟨661044, by decide⟩ (by decide) (![⟨660965, by decide⟩,⟨661003, by decide⟩,⟨661029, by decide⟩,⟨661043, by decide⟩]) unmarked_context_12_88606_661044 node_context_12_88606_661044
  intro a
  fin_cases a
  · exact context_13_354424_660965
  · exact context_13_354425_661003
  · exact context_13_354426_661029
  · exact context_13_354427_661043

theorem selected_cut_26111 : selected 8 ⟨661070, by decide⟩
    (prefixPartial 13 354428) = some ⟨13, 2, 0, 661070, 354428, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_354428_661070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354428 ⟨661070, by decide⟩ :=
  accepted_of_selected 13 354428 ⟨661070, by decide⟩ ⟨13, 2, 0, 661070, 354428, 1861, 16384⟩
    (by decide) selected_cut_26111

theorem selected_cut_26112 : selected 8 ⟨661115, by decide⟩
    (prefixPartial 13 354429) = some ⟨13, 2, 0, 661115, 354429, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_354429_661115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354429 ⟨661115, by decide⟩ :=
  accepted_of_selected 13 354429 ⟨661115, by decide⟩ ⟨13, 2, 0, 661115, 354429, 2473, 16384⟩
    (by decide) selected_cut_26112

theorem selected_cut_26113 : selected 8 ⟨661135, by decide⟩
    (prefixPartial 13 354430) = some ⟨13, 2, 0, 661135, 354430, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_354430_661135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354430 ⟨661135, by decide⟩ :=
  accepted_of_selected 13 354430 ⟨661135, by decide⟩ ⟨13, 2, 0, 661135, 354430, 1793, 16384⟩
    (by decide) selected_cut_26113

theorem selected_cut_26114 : selected 8 ⟨661147, by decide⟩
    (prefixPartial 13 354431) = some ⟨13, 2, 0, 661147, 354431, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_354431_661147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354431 ⟨661147, by decide⟩ :=
  accepted_of_selected 13 354431 ⟨661147, by decide⟩ ⟨13, 2, 0, 661147, 354431, 1073, 16384⟩
    (by decide) selected_cut_26114

theorem unmarked_context_12_88607_661148 : frontier 9 ⟨661148, by decide⟩
    (prefixCache 12 88607) (prefixPartial 12 88607) = false := by
  decide +kernel

theorem node_context_12_88607_661148 : EJMOriginalGlobalDAGData.nodes 9 ⟨661148, by decide⟩ =
    .split (coordinate 12) (![⟨661070, by decide⟩,⟨661115, by decide⟩,⟨661135, by decide⟩,⟨661147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88607_661148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88607 ⟨661148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88607
    ⟨661148, by decide⟩ (by decide) (![⟨661070, by decide⟩,⟨661115, by decide⟩,⟨661135, by decide⟩,⟨661147, by decide⟩]) unmarked_context_12_88607_661148 node_context_12_88607_661148
  intro a
  fin_cases a
  · exact context_13_354428_661070
  · exact context_13_354429_661115
  · exact context_13_354430_661135
  · exact context_13_354431_661147

theorem unmarked_context_11_22151_661149 : frontier 10 ⟨661149, by decide⟩
    (prefixCache 11 22151) (prefixPartial 11 22151) = false := by
  decide +kernel

theorem node_context_11_22151_661149 : EJMOriginalGlobalDAGData.nodes 10 ⟨661149, by decide⟩ =
    .split (coordinate 11) (![⟨660848, by decide⟩,⟨660933, by decide⟩,⟨661044, by decide⟩,⟨661148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22151_661149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22151 ⟨661149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22151
    ⟨661149, by decide⟩ (by decide) (![⟨660848, by decide⟩,⟨660933, by decide⟩,⟨661044, by decide⟩,⟨661148, by decide⟩]) unmarked_context_11_22151_661149 node_context_11_22151_661149
  intro a
  fin_cases a
  · exact context_12_88604_660848
  · exact context_12_88605_660933
  · exact context_12_88606_661044
  · exact context_12_88607_661148

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
