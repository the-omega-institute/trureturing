/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover246
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_23715 : selected 8 ⟨599252, by decide⟩
    (prefixPartial 13 306441) = some ⟨13, 2, 0, 599252, 306441, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_306441_599252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306441 ⟨599252, by decide⟩ :=
  accepted_of_selected 13 306441 ⟨599252, by decide⟩ ⟨13, 2, 0, 599252, 306441, 2477, 16384⟩
    (by decide) selected_cut_23715

theorem selected_cut_23716 : selected 8 ⟨599272, by decide⟩
    (prefixPartial 13 306442) = some ⟨13, 2, 0, 599272, 306442, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_306442_599272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306442 ⟨599272, by decide⟩ :=
  accepted_of_selected 13 306442 ⟨599272, by decide⟩ ⟨13, 2, 0, 599272, 306442, 1405, 16384⟩
    (by decide) selected_cut_23716

theorem selected_cut_23717 : selected 8 ⟨599278, by decide⟩
    (prefixPartial 13 306443) = some ⟨13, 2, 0, 599278, 306443, 705, 16384⟩ := by
  decide +kernel

theorem context_13_306443_599278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306443 ⟨599278, by decide⟩ :=
  accepted_of_selected 13 306443 ⟨599278, by decide⟩ ⟨13, 2, 0, 599278, 306443, 705, 16384⟩
    (by decide) selected_cut_23717

theorem unmarked_context_12_76610_599279 : frontier 9 ⟨599279, by decide⟩
    (prefixCache 12 76610) (prefixPartial 12 76610) = false := by
  decide +kernel

theorem node_context_12_76610_599279 : EJMOriginalGlobalDAGData.nodes 9 ⟨599279, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599252, by decide⟩,⟨599272, by decide⟩,⟨599278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76610_599279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76610 ⟨599279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76610
    ⟨599279, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599252, by decide⟩,⟨599272, by decide⟩,⟨599278, by decide⟩]) unmarked_context_12_76610_599279 node_context_12_76610_599279
  intro a
  fin_cases a
  · exact context_13_306440_3444
  · exact context_13_306441_599252
  · exact context_13_306442_599272
  · exact context_13_306443_599278

theorem selected_cut_23718 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306444) = some ⟨13, 1, 0, 3444, 306444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306444, 1, 16384⟩
    (by decide) selected_cut_23718

theorem selected_cut_23719 : selected 8 ⟨599305, by decide⟩
    (prefixPartial 13 306445) = some ⟨13, 2, 0, 599305, 306445, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_306445_599305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306445 ⟨599305, by decide⟩ :=
  accepted_of_selected 13 306445 ⟨599305, by decide⟩ ⟨13, 2, 0, 599305, 306445, 2345, 16384⟩
    (by decide) selected_cut_23719

theorem selected_cut_23720 : selected 8 ⟨599321, by decide⟩
    (prefixPartial 13 306446) = some ⟨13, 2, 0, 599321, 306446, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_306446_599321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306446 ⟨599321, by decide⟩ :=
  accepted_of_selected 13 306446 ⟨599321, by decide⟩ ⟨13, 2, 0, 599321, 306446, 1277, 16384⟩
    (by decide) selected_cut_23720

theorem selected_cut_23721 : selected 8 ⟨599327, by decide⟩
    (prefixPartial 13 306447) = some ⟨13, 2, 0, 599327, 306447, 653, 16384⟩ := by
  decide +kernel

theorem context_13_306447_599327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306447 ⟨599327, by decide⟩ :=
  accepted_of_selected 13 306447 ⟨599327, by decide⟩ ⟨13, 2, 0, 599327, 306447, 653, 16384⟩
    (by decide) selected_cut_23721

theorem unmarked_context_12_76611_599328 : frontier 9 ⟨599328, by decide⟩
    (prefixCache 12 76611) (prefixPartial 12 76611) = false := by
  decide +kernel

theorem node_context_12_76611_599328 : EJMOriginalGlobalDAGData.nodes 9 ⟨599328, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599305, by decide⟩,⟨599321, by decide⟩,⟨599327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76611_599328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76611 ⟨599328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76611
    ⟨599328, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599305, by decide⟩,⟨599321, by decide⟩,⟨599327, by decide⟩]) unmarked_context_12_76611_599328 node_context_12_76611_599328
  intro a
  fin_cases a
  · exact context_13_306444_3444
  · exact context_13_306445_599305
  · exact context_13_306446_599321
  · exact context_13_306447_599327

theorem unmarked_context_11_19152_599329 : frontier 10 ⟨599329, by decide⟩
    (prefixCache 11 19152) (prefixPartial 11 19152) = false := by
  decide +kernel

theorem node_context_11_19152_599329 : EJMOriginalGlobalDAGData.nodes 10 ⟨599329, by decide⟩ =
    .split (coordinate 11) (![⟨599183, by decide⟩,⟨599224, by decide⟩,⟨599279, by decide⟩,⟨599328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19152_599329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19152 ⟨599329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19152
    ⟨599329, by decide⟩ (by decide) (![⟨599183, by decide⟩,⟨599224, by decide⟩,⟨599279, by decide⟩,⟨599328, by decide⟩]) unmarked_context_11_19152_599329 node_context_11_19152_599329
  intro a
  fin_cases a
  · exact context_12_76608_599183
  · exact context_12_76609_599224
  · exact context_12_76610_599279
  · exact context_12_76611_599328

theorem selected_cut_23722 : selected 9 ⟨599370, by decide⟩
    (prefixPartial 12 76612) = some ⟨12, 2, 0, 599370, 76612, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_76612_599370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76612 ⟨599370, by decide⟩ :=
  accepted_of_selected 12 76612 ⟨599370, by decide⟩ ⟨12, 2, 0, 599370, 76612, 3757, 65536⟩
    (by decide) selected_cut_23722

theorem selected_cut_23723 : selected 9 ⟨599407, by decide⟩
    (prefixPartial 12 76613) = some ⟨12, 2, 0, 599407, 76613, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_76613_599407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76613 ⟨599407, by decide⟩ :=
  accepted_of_selected 12 76613 ⟨599407, by decide⟩ ⟨12, 2, 0, 599407, 76613, 3409, 65536⟩
    (by decide) selected_cut_23723

theorem selected_cut_23724 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306456) = some ⟨13, 1, 0, 3444, 306456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306456, 1, 16384⟩
    (by decide) selected_cut_23724

theorem selected_cut_23725 : selected 8 ⟨599433, by decide⟩
    (prefixPartial 13 306457) = some ⟨13, 2, 0, 599433, 306457, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_306457_599433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306457 ⟨599433, by decide⟩ :=
  accepted_of_selected 13 306457 ⟨599433, by decide⟩ ⟨13, 2, 0, 599433, 306457, 2129, 16384⟩
    (by decide) selected_cut_23725

theorem selected_cut_23726 : selected 8 ⟨599451, by decide⟩
    (prefixPartial 13 306458) = some ⟨13, 2, 0, 599451, 306458, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_306458_599451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306458 ⟨599451, by decide⟩ :=
  accepted_of_selected 13 306458 ⟨599451, by decide⟩ ⟨13, 2, 0, 599451, 306458, 1453, 16384⟩
    (by decide) selected_cut_23726

theorem selected_cut_23727 : selected 8 ⟨599456, by decide⟩
    (prefixPartial 13 306459) = some ⟨13, 2, 0, 599456, 306459, 749, 16384⟩ := by
  decide +kernel

theorem context_13_306459_599456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306459 ⟨599456, by decide⟩ :=
  accepted_of_selected 13 306459 ⟨599456, by decide⟩ ⟨13, 2, 0, 599456, 306459, 749, 16384⟩
    (by decide) selected_cut_23727

theorem unmarked_context_12_76614_599457 : frontier 9 ⟨599457, by decide⟩
    (prefixCache 12 76614) (prefixPartial 12 76614) = false := by
  decide +kernel

theorem node_context_12_76614_599457 : EJMOriginalGlobalDAGData.nodes 9 ⟨599457, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599433, by decide⟩,⟨599451, by decide⟩,⟨599456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76614_599457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76614 ⟨599457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76614
    ⟨599457, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599433, by decide⟩,⟨599451, by decide⟩,⟨599456, by decide⟩]) unmarked_context_12_76614_599457 node_context_12_76614_599457
  intro a
  fin_cases a
  · exact context_13_306456_3444
  · exact context_13_306457_599433
  · exact context_13_306458_599451
  · exact context_13_306459_599456

theorem selected_cut_23728 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306460) = some ⟨13, 1, 0, 3444, 306460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306460, 1, 16384⟩
    (by decide) selected_cut_23728

theorem selected_cut_23729 : selected 8 ⟨599485, by decide⟩
    (prefixPartial 13 306461) = some ⟨13, 2, 0, 599485, 306461, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_306461_599485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306461 ⟨599485, by decide⟩ :=
  accepted_of_selected 13 306461 ⟨599485, by decide⟩ ⟨13, 2, 0, 599485, 306461, 1957, 16384⟩
    (by decide) selected_cut_23729

theorem selected_cut_23730 : selected 8 ⟨599507, by decide⟩
    (prefixPartial 13 306462) = some ⟨13, 2, 0, 599507, 306462, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_306462_599507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306462 ⟨599507, by decide⟩ :=
  accepted_of_selected 13 306462 ⟨599507, by decide⟩ ⟨13, 2, 0, 599507, 306462, 1489, 16384⟩
    (by decide) selected_cut_23730

theorem selected_cut_23731 : selected 8 ⟨599514, by decide⟩
    (prefixPartial 13 306463) = some ⟨13, 2, 0, 599514, 306463, 729, 16384⟩ := by
  decide +kernel

theorem context_13_306463_599514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306463 ⟨599514, by decide⟩ :=
  accepted_of_selected 13 306463 ⟨599514, by decide⟩ ⟨13, 2, 0, 599514, 306463, 729, 16384⟩
    (by decide) selected_cut_23731

theorem unmarked_context_12_76615_599515 : frontier 9 ⟨599515, by decide⟩
    (prefixCache 12 76615) (prefixPartial 12 76615) = false := by
  decide +kernel

theorem node_context_12_76615_599515 : EJMOriginalGlobalDAGData.nodes 9 ⟨599515, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599485, by decide⟩,⟨599507, by decide⟩,⟨599514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76615_599515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76615 ⟨599515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76615
    ⟨599515, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599485, by decide⟩,⟨599507, by decide⟩,⟨599514, by decide⟩]) unmarked_context_12_76615_599515 node_context_12_76615_599515
  intro a
  fin_cases a
  · exact context_13_306460_3444
  · exact context_13_306461_599485
  · exact context_13_306462_599507
  · exact context_13_306463_599514

theorem unmarked_context_11_19153_599516 : frontier 10 ⟨599516, by decide⟩
    (prefixCache 11 19153) (prefixPartial 11 19153) = false := by
  decide +kernel

theorem node_context_11_19153_599516 : EJMOriginalGlobalDAGData.nodes 10 ⟨599516, by decide⟩ =
    .split (coordinate 11) (![⟨599370, by decide⟩,⟨599407, by decide⟩,⟨599457, by decide⟩,⟨599515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19153_599516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19153 ⟨599516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19153
    ⟨599516, by decide⟩ (by decide) (![⟨599370, by decide⟩,⟨599407, by decide⟩,⟨599457, by decide⟩,⟨599515, by decide⟩]) unmarked_context_11_19153_599516 node_context_11_19153_599516
  intro a
  fin_cases a
  · exact context_12_76612_599370
  · exact context_12_76613_599407
  · exact context_12_76614_599457
  · exact context_12_76615_599515

theorem selected_cut_23732 : selected 9 ⟨599556, by decide⟩
    (prefixPartial 12 76616) = some ⟨12, 2, 0, 599556, 76616, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_76616_599556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76616 ⟨599556, by decide⟩ :=
  accepted_of_selected 12 76616 ⟨599556, by decide⟩ ⟨12, 2, 0, 599556, 76616, 3529, 65536⟩
    (by decide) selected_cut_23732

theorem selected_cut_23733 : selected 9 ⟨599593, by decide⟩
    (prefixPartial 12 76617) = some ⟨12, 2, 0, 599593, 76617, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_76617_599593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76617 ⟨599593, by decide⟩ :=
  accepted_of_selected 12 76617 ⟨599593, by decide⟩ ⟨12, 2, 0, 599593, 76617, 3397, 65536⟩
    (by decide) selected_cut_23733

theorem selected_cut_23734 : selected 9 ⟨599641, by decide⟩
    (prefixPartial 12 76618) = some ⟨12, 2, 0, 599641, 76618, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_76618_599641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76618 ⟨599641, by decide⟩ :=
  accepted_of_selected 12 76618 ⟨599641, by decide⟩ ⟨12, 2, 0, 599641, 76618, 3873, 65536⟩
    (by decide) selected_cut_23734

theorem selected_cut_23735 : selected 9 ⟨599692, by decide⟩
    (prefixPartial 12 76619) = some ⟨12, 2, 0, 599692, 76619, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_76619_599692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76619 ⟨599692, by decide⟩ :=
  accepted_of_selected 12 76619 ⟨599692, by decide⟩ ⟨12, 2, 0, 599692, 76619, 3981, 65536⟩
    (by decide) selected_cut_23735

theorem unmarked_context_11_19154_599693 : frontier 10 ⟨599693, by decide⟩
    (prefixCache 11 19154) (prefixPartial 11 19154) = false := by
  decide +kernel

theorem node_context_11_19154_599693 : EJMOriginalGlobalDAGData.nodes 10 ⟨599693, by decide⟩ =
    .split (coordinate 11) (![⟨599556, by decide⟩,⟨599593, by decide⟩,⟨599641, by decide⟩,⟨599692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19154_599693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19154 ⟨599693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19154
    ⟨599693, by decide⟩ (by decide) (![⟨599556, by decide⟩,⟨599593, by decide⟩,⟨599641, by decide⟩,⟨599692, by decide⟩]) unmarked_context_11_19154_599693 node_context_11_19154_599693
  intro a
  fin_cases a
  · exact context_12_76616_599556
  · exact context_12_76617_599593
  · exact context_12_76618_599641
  · exact context_12_76619_599692

theorem selected_cut_23736 : selected 9 ⟨599728, by decide⟩
    (prefixPartial 12 76620) = some ⟨12, 2, 0, 599728, 76620, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_76620_599728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76620 ⟨599728, by decide⟩ :=
  accepted_of_selected 12 76620 ⟨599728, by decide⟩ ⟨12, 2, 0, 599728, 76620, 3333, 65536⟩
    (by decide) selected_cut_23736

theorem selected_cut_23737 : selected 9 ⟨599769, by decide⟩
    (prefixPartial 12 76621) = some ⟨12, 2, 0, 599769, 76621, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_76621_599769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76621 ⟨599769, by decide⟩ :=
  accepted_of_selected 12 76621 ⟨599769, by decide⟩ ⟨12, 2, 0, 599769, 76621, 3285, 65536⟩
    (by decide) selected_cut_23737

theorem selected_cut_23738 : selected 9 ⟨599817, by decide⟩
    (prefixPartial 12 76622) = some ⟨12, 2, 0, 599817, 76622, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_76622_599817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76622 ⟨599817, by decide⟩ :=
  accepted_of_selected 12 76622 ⟨599817, by decide⟩ ⟨12, 2, 0, 599817, 76622, 3797, 65536⟩
    (by decide) selected_cut_23738

theorem selected_cut_23739 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306492) = some ⟨13, 1, 0, 3444, 306492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306492, 1, 16384⟩
    (by decide) selected_cut_23739

theorem selected_cut_23740 : selected 8 ⟨599861, by decide⟩
    (prefixPartial 13 306493) = some ⟨13, 2, 0, 599861, 306493, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_306493_599861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306493 ⟨599861, by decide⟩ :=
  accepted_of_selected 13 306493 ⟨599861, by decide⟩ ⟨13, 2, 0, 599861, 306493, 3009, 16384⟩
    (by decide) selected_cut_23740

theorem selected_cut_23741 : selected 8 ⟨599883, by decide⟩
    (prefixPartial 13 306494) = some ⟨13, 2, 0, 599883, 306494, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_306494_599883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306494 ⟨599883, by decide⟩ :=
  accepted_of_selected 13 306494 ⟨599883, by decide⟩ ⟨13, 2, 0, 599883, 306494, 2197, 16384⟩
    (by decide) selected_cut_23741

theorem selected_cut_23742 : selected 8 ⟨599895, by decide⟩
    (prefixPartial 13 306495) = some ⟨13, 2, 0, 599895, 306495, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_306495_599895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306495 ⟨599895, by decide⟩ :=
  accepted_of_selected 13 306495 ⟨599895, by decide⟩ ⟨13, 2, 0, 599895, 306495, 1133, 16384⟩
    (by decide) selected_cut_23742

theorem unmarked_context_12_76623_599896 : frontier 9 ⟨599896, by decide⟩
    (prefixCache 12 76623) (prefixPartial 12 76623) = false := by
  decide +kernel

theorem node_context_12_76623_599896 : EJMOriginalGlobalDAGData.nodes 9 ⟨599896, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599861, by decide⟩,⟨599883, by decide⟩,⟨599895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76623_599896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76623 ⟨599896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76623
    ⟨599896, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599861, by decide⟩,⟨599883, by decide⟩,⟨599895, by decide⟩]) unmarked_context_12_76623_599896 node_context_12_76623_599896
  intro a
  fin_cases a
  · exact context_13_306492_3444
  · exact context_13_306493_599861
  · exact context_13_306494_599883
  · exact context_13_306495_599895

theorem unmarked_context_11_19155_599897 : frontier 10 ⟨599897, by decide⟩
    (prefixCache 11 19155) (prefixPartial 11 19155) = false := by
  decide +kernel

theorem node_context_11_19155_599897 : EJMOriginalGlobalDAGData.nodes 10 ⟨599897, by decide⟩ =
    .split (coordinate 11) (![⟨599728, by decide⟩,⟨599769, by decide⟩,⟨599817, by decide⟩,⟨599896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19155_599897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19155 ⟨599897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19155
    ⟨599897, by decide⟩ (by decide) (![⟨599728, by decide⟩,⟨599769, by decide⟩,⟨599817, by decide⟩,⟨599896, by decide⟩]) unmarked_context_11_19155_599897 node_context_11_19155_599897
  intro a
  fin_cases a
  · exact context_12_76620_599728
  · exact context_12_76621_599769
  · exact context_12_76622_599817
  · exact context_12_76623_599896

theorem unmarked_context_10_4788_599898 : frontier 11 ⟨599898, by decide⟩
    (prefixCache 10 4788) (prefixPartial 10 4788) = false := by
  decide +kernel

theorem node_context_10_4788_599898 : EJMOriginalGlobalDAGData.nodes 11 ⟨599898, by decide⟩ =
    .split (coordinate 10) (![⟨599329, by decide⟩,⟨599516, by decide⟩,⟨599693, by decide⟩,⟨599897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4788_599898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4788 ⟨599898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4788
    ⟨599898, by decide⟩ (by decide) (![⟨599329, by decide⟩,⟨599516, by decide⟩,⟨599693, by decide⟩,⟨599897, by decide⟩]) unmarked_context_10_4788_599898 node_context_10_4788_599898
  intro a
  fin_cases a
  · exact context_11_19152_599329
  · exact context_11_19153_599516
  · exact context_11_19154_599693
  · exact context_11_19155_599897

theorem selected_cut_23743 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306496) = some ⟨13, 1, 0, 3444, 306496, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306496_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306496 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306496 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306496, 1, 16384⟩
    (by decide) selected_cut_23743

theorem selected_cut_23744 : selected 8 ⟨599924, by decide⟩
    (prefixPartial 13 306497) = some ⟨13, 2, 0, 599924, 306497, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_306497_599924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306497 ⟨599924, by decide⟩ :=
  accepted_of_selected 13 306497 ⟨599924, by decide⟩ ⟨13, 2, 0, 599924, 306497, 1869, 16384⟩
    (by decide) selected_cut_23744

theorem selected_cut_23745 : selected 8 ⟨599944, by decide⟩
    (prefixPartial 13 306498) = some ⟨13, 2, 0, 599944, 306498, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_306498_599944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306498 ⟨599944, by decide⟩ :=
  accepted_of_selected 13 306498 ⟨599944, by decide⟩ ⟨13, 2, 0, 599944, 306498, 1593, 16384⟩
    (by decide) selected_cut_23745

theorem selected_cut_23746 : selected 8 ⟨599953, by decide⟩
    (prefixPartial 13 306499) = some ⟨13, 2, 0, 599953, 306499, 893, 16384⟩ := by
  decide +kernel

theorem context_13_306499_599953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306499 ⟨599953, by decide⟩ :=
  accepted_of_selected 13 306499 ⟨599953, by decide⟩ ⟨13, 2, 0, 599953, 306499, 893, 16384⟩
    (by decide) selected_cut_23746

theorem unmarked_context_12_76624_599954 : frontier 9 ⟨599954, by decide⟩
    (prefixCache 12 76624) (prefixPartial 12 76624) = false := by
  decide +kernel

theorem node_context_12_76624_599954 : EJMOriginalGlobalDAGData.nodes 9 ⟨599954, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599924, by decide⟩,⟨599944, by decide⟩,⟨599953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76624_599954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76624 ⟨599954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76624
    ⟨599954, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599924, by decide⟩,⟨599944, by decide⟩,⟨599953, by decide⟩]) unmarked_context_12_76624_599954 node_context_12_76624_599954
  intro a
  fin_cases a
  · exact context_13_306496_3444
  · exact context_13_306497_599924
  · exact context_13_306498_599944
  · exact context_13_306499_599953

theorem selected_cut_23747 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306500) = some ⟨13, 1, 0, 3444, 306500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306500, 1, 16384⟩
    (by decide) selected_cut_23747

theorem selected_cut_23748 : selected 8 ⟨599985, by decide⟩
    (prefixPartial 13 306501) = some ⟨13, 2, 0, 599985, 306501, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_306501_599985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306501 ⟨599985, by decide⟩ :=
  accepted_of_selected 13 306501 ⟨599985, by decide⟩ ⟨13, 2, 0, 599985, 306501, 1873, 16384⟩
    (by decide) selected_cut_23748

theorem selected_cut_23749 : selected 8 ⟨600006, by decide⟩
    (prefixPartial 13 306502) = some ⟨13, 2, 0, 600006, 306502, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_306502_600006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306502 ⟨600006, by decide⟩ :=
  accepted_of_selected 13 306502 ⟨600006, by decide⟩ ⟨13, 2, 0, 600006, 306502, 1713, 16384⟩
    (by decide) selected_cut_23749

theorem selected_cut_23750 : selected 8 ⟨600013, by decide⟩
    (prefixPartial 13 306503) = some ⟨13, 2, 0, 600013, 306503, 793, 16384⟩ := by
  decide +kernel

theorem context_13_306503_600013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306503 ⟨600013, by decide⟩ :=
  accepted_of_selected 13 306503 ⟨600013, by decide⟩ ⟨13, 2, 0, 600013, 306503, 793, 16384⟩
    (by decide) selected_cut_23750

theorem unmarked_context_12_76625_600014 : frontier 9 ⟨600014, by decide⟩
    (prefixCache 12 76625) (prefixPartial 12 76625) = false := by
  decide +kernel

theorem node_context_12_76625_600014 : EJMOriginalGlobalDAGData.nodes 9 ⟨600014, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨599985, by decide⟩,⟨600006, by decide⟩,⟨600013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76625_600014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76625 ⟨600014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76625
    ⟨600014, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨599985, by decide⟩,⟨600006, by decide⟩,⟨600013, by decide⟩]) unmarked_context_12_76625_600014 node_context_12_76625_600014
  intro a
  fin_cases a
  · exact context_13_306500_3444
  · exact context_13_306501_599985
  · exact context_13_306502_600006
  · exact context_13_306503_600013

theorem selected_cut_23751 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306504) = some ⟨13, 1, 0, 3444, 306504, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306504_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306504 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306504 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306504, 1, 16384⟩
    (by decide) selected_cut_23751

theorem selected_cut_23752 : selected 8 ⟨600051, by decide⟩
    (prefixPartial 13 306505) = some ⟨13, 2, 0, 600051, 306505, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_306505_600051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306505 ⟨600051, by decide⟩ :=
  accepted_of_selected 13 306505 ⟨600051, by decide⟩ ⟨13, 2, 0, 600051, 306505, 2325, 16384⟩
    (by decide) selected_cut_23752

theorem selected_cut_23753 : selected 8 ⟨600075, by decide⟩
    (prefixPartial 13 306506) = some ⟨13, 2, 0, 600075, 306506, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_306506_600075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306506 ⟨600075, by decide⟩ :=
  accepted_of_selected 13 306506 ⟨600075, by decide⟩ ⟨13, 2, 0, 600075, 306506, 1977, 16384⟩
    (by decide) selected_cut_23753

theorem selected_cut_23754 : selected 8 ⟨600085, by decide⟩
    (prefixPartial 13 306507) = some ⟨13, 2, 0, 600085, 306507, 829, 16384⟩ := by
  decide +kernel

theorem context_13_306507_600085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306507 ⟨600085, by decide⟩ :=
  accepted_of_selected 13 306507 ⟨600085, by decide⟩ ⟨13, 2, 0, 600085, 306507, 829, 16384⟩
    (by decide) selected_cut_23754

theorem unmarked_context_12_76626_600086 : frontier 9 ⟨600086, by decide⟩
    (prefixCache 12 76626) (prefixPartial 12 76626) = false := by
  decide +kernel

theorem node_context_12_76626_600086 : EJMOriginalGlobalDAGData.nodes 9 ⟨600086, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600051, by decide⟩,⟨600075, by decide⟩,⟨600085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76626_600086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76626 ⟨600086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76626
    ⟨600086, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600051, by decide⟩,⟨600075, by decide⟩,⟨600085, by decide⟩]) unmarked_context_12_76626_600086 node_context_12_76626_600086
  intro a
  fin_cases a
  · exact context_13_306504_3444
  · exact context_13_306505_600051
  · exact context_13_306506_600075
  · exact context_13_306507_600085

theorem selected_cut_23755 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306508) = some ⟨13, 1, 0, 3444, 306508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306508, 1, 16384⟩
    (by decide) selected_cut_23755

theorem selected_cut_23756 : selected 8 ⟨600110, by decide⟩
    (prefixPartial 13 306509) = some ⟨13, 2, 0, 600110, 306509, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_306509_600110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306509 ⟨600110, by decide⟩ :=
  accepted_of_selected 13 306509 ⟨600110, by decide⟩ ⟨13, 2, 0, 600110, 306509, 2069, 16384⟩
    (by decide) selected_cut_23756

theorem selected_cut_23757 : selected 8 ⟨600131, by decide⟩
    (prefixPartial 13 306510) = some ⟨13, 2, 0, 600131, 306510, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_306510_600131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306510 ⟨600131, by decide⟩ :=
  accepted_of_selected 13 306510 ⟨600131, by decide⟩ ⟨13, 2, 0, 600131, 306510, 1877, 16384⟩
    (by decide) selected_cut_23757

theorem selected_cut_23758 : selected 8 ⟨600136, by decide⟩
    (prefixPartial 13 306511) = some ⟨13, 2, 0, 600136, 306511, 705, 16384⟩ := by
  decide +kernel

theorem context_13_306511_600136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306511 ⟨600136, by decide⟩ :=
  accepted_of_selected 13 306511 ⟨600136, by decide⟩ ⟨13, 2, 0, 600136, 306511, 705, 16384⟩
    (by decide) selected_cut_23758

theorem unmarked_context_12_76627_600137 : frontier 9 ⟨600137, by decide⟩
    (prefixCache 12 76627) (prefixPartial 12 76627) = false := by
  decide +kernel

theorem node_context_12_76627_600137 : EJMOriginalGlobalDAGData.nodes 9 ⟨600137, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600110, by decide⟩,⟨600131, by decide⟩,⟨600136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76627_600137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76627 ⟨600137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76627
    ⟨600137, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600110, by decide⟩,⟨600131, by decide⟩,⟨600136, by decide⟩]) unmarked_context_12_76627_600137 node_context_12_76627_600137
  intro a
  fin_cases a
  · exact context_13_306508_3444
  · exact context_13_306509_600110
  · exact context_13_306510_600131
  · exact context_13_306511_600136

theorem unmarked_context_11_19156_600138 : frontier 10 ⟨600138, by decide⟩
    (prefixCache 11 19156) (prefixPartial 11 19156) = false := by
  decide +kernel

theorem node_context_11_19156_600138 : EJMOriginalGlobalDAGData.nodes 10 ⟨600138, by decide⟩ =
    .split (coordinate 11) (![⟨599954, by decide⟩,⟨600014, by decide⟩,⟨600086, by decide⟩,⟨600137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19156_600138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19156 ⟨600138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19156
    ⟨600138, by decide⟩ (by decide) (![⟨599954, by decide⟩,⟨600014, by decide⟩,⟨600086, by decide⟩,⟨600137, by decide⟩]) unmarked_context_11_19156_600138 node_context_11_19156_600138
  intro a
  fin_cases a
  · exact context_12_76624_599954
  · exact context_12_76625_600014
  · exact context_12_76626_600086
  · exact context_12_76627_600137

theorem selected_cut_23759 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306512) = some ⟨13, 1, 0, 3444, 306512, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306512_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306512 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306512 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306512, 1, 16384⟩
    (by decide) selected_cut_23759

theorem selected_cut_23760 : selected 8 ⟨600165, by decide⟩
    (prefixPartial 13 306513) = some ⟨13, 2, 0, 600165, 306513, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_306513_600165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306513 ⟨600165, by decide⟩ :=
  accepted_of_selected 13 306513 ⟨600165, by decide⟩ ⟨13, 2, 0, 600165, 306513, 1685, 16384⟩
    (by decide) selected_cut_23760

theorem selected_cut_23761 : selected 8 ⟨600188, by decide⟩
    (prefixPartial 13 306514) = some ⟨13, 2, 0, 600188, 306514, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_306514_600188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306514 ⟨600188, by decide⟩ :=
  accepted_of_selected 13 306514 ⟨600188, by decide⟩ ⟨13, 2, 0, 600188, 306514, 1685, 16384⟩
    (by decide) selected_cut_23761

theorem selected_cut_23762 : selected 8 ⟨600201, by decide⟩
    (prefixPartial 13 306515) = some ⟨13, 2, 0, 600201, 306515, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_306515_600201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306515 ⟨600201, by decide⟩ :=
  accepted_of_selected 13 306515 ⟨600201, by decide⟩ ⟨13, 2, 0, 600201, 306515, 1049, 16384⟩
    (by decide) selected_cut_23762

theorem unmarked_context_12_76628_600202 : frontier 9 ⟨600202, by decide⟩
    (prefixCache 12 76628) (prefixPartial 12 76628) = false := by
  decide +kernel

theorem node_context_12_76628_600202 : EJMOriginalGlobalDAGData.nodes 9 ⟨600202, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600165, by decide⟩,⟨600188, by decide⟩,⟨600201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76628_600202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76628 ⟨600202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76628
    ⟨600202, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600165, by decide⟩,⟨600188, by decide⟩,⟨600201, by decide⟩]) unmarked_context_12_76628_600202 node_context_12_76628_600202
  intro a
  fin_cases a
  · exact context_13_306512_3444
  · exact context_13_306513_600165
  · exact context_13_306514_600188
  · exact context_13_306515_600201

theorem selected_cut_23763 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306516) = some ⟨13, 1, 0, 3444, 306516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306516, 1, 16384⟩
    (by decide) selected_cut_23763

theorem selected_cut_23764 : selected 8 ⟨600224, by decide⟩
    (prefixPartial 13 306517) = some ⟨13, 2, 0, 600224, 306517, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_306517_600224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306517 ⟨600224, by decide⟩ :=
  accepted_of_selected 13 306517 ⟨600224, by decide⟩ ⟨13, 2, 0, 600224, 306517, 1537, 16384⟩
    (by decide) selected_cut_23764

theorem selected_cut_23765 : selected 8 ⟨600239, by decide⟩
    (prefixPartial 13 306518) = some ⟨13, 2, 0, 600239, 306518, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_306518_600239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306518 ⟨600239, by decide⟩ :=
  accepted_of_selected 13 306518 ⟨600239, by decide⟩ ⟨13, 2, 0, 600239, 306518, 1693, 16384⟩
    (by decide) selected_cut_23765

theorem selected_cut_23766 : selected 8 ⟨600245, by decide⟩
    (prefixPartial 13 306519) = some ⟨13, 2, 0, 600245, 306519, 869, 16384⟩ := by
  decide +kernel

theorem context_13_306519_600245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306519 ⟨600245, by decide⟩ :=
  accepted_of_selected 13 306519 ⟨600245, by decide⟩ ⟨13, 2, 0, 600245, 306519, 869, 16384⟩
    (by decide) selected_cut_23766

theorem unmarked_context_12_76629_600246 : frontier 9 ⟨600246, by decide⟩
    (prefixCache 12 76629) (prefixPartial 12 76629) = false := by
  decide +kernel

theorem node_context_12_76629_600246 : EJMOriginalGlobalDAGData.nodes 9 ⟨600246, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600224, by decide⟩,⟨600239, by decide⟩,⟨600245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76629_600246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76629 ⟨600246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76629
    ⟨600246, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600224, by decide⟩,⟨600239, by decide⟩,⟨600245, by decide⟩]) unmarked_context_12_76629_600246 node_context_12_76629_600246
  intro a
  fin_cases a
  · exact context_13_306516_3444
  · exact context_13_306517_600224
  · exact context_13_306518_600239
  · exact context_13_306519_600245

theorem selected_cut_23767 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306520) = some ⟨13, 1, 0, 3444, 306520, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306520_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306520 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306520 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306520, 1, 16384⟩
    (by decide) selected_cut_23767

theorem selected_cut_23768 : selected 8 ⟨600272, by decide⟩
    (prefixPartial 13 306521) = some ⟨13, 2, 0, 600272, 306521, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_306521_600272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306521 ⟨600272, by decide⟩ :=
  accepted_of_selected 13 306521 ⟨600272, by decide⟩ ⟨13, 2, 0, 600272, 306521, 2005, 16384⟩
    (by decide) selected_cut_23768

theorem selected_cut_23769 : selected 8 ⟨600299, by decide⟩
    (prefixPartial 13 306522) = some ⟨13, 2, 0, 600299, 306522, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_306522_600299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306522 ⟨600299, by decide⟩ :=
  accepted_of_selected 13 306522 ⟨600299, by decide⟩ ⟨13, 2, 0, 600299, 306522, 1957, 16384⟩
    (by decide) selected_cut_23769

theorem selected_cut_23770 : selected 8 ⟨600314, by decide⟩
    (prefixPartial 13 306523) = some ⟨13, 2, 0, 600314, 306523, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_306523_600314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306523 ⟨600314, by decide⟩ :=
  accepted_of_selected 13 306523 ⟨600314, by decide⟩ ⟨13, 2, 0, 600314, 306523, 1009, 16384⟩
    (by decide) selected_cut_23770

theorem unmarked_context_12_76630_600315 : frontier 9 ⟨600315, by decide⟩
    (prefixCache 12 76630) (prefixPartial 12 76630) = false := by
  decide +kernel

theorem node_context_12_76630_600315 : EJMOriginalGlobalDAGData.nodes 9 ⟨600315, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600272, by decide⟩,⟨600299, by decide⟩,⟨600314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76630_600315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76630 ⟨600315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76630
    ⟨600315, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600272, by decide⟩,⟨600299, by decide⟩,⟨600314, by decide⟩]) unmarked_context_12_76630_600315 node_context_12_76630_600315
  intro a
  fin_cases a
  · exact context_13_306520_3444
  · exact context_13_306521_600272
  · exact context_13_306522_600299
  · exact context_13_306523_600314

theorem selected_cut_23771 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306524) = some ⟨13, 1, 0, 3444, 306524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306524, 1, 16384⟩
    (by decide) selected_cut_23771

theorem selected_cut_23772 : selected 8 ⟨600336, by decide⟩
    (prefixPartial 13 306525) = some ⟨13, 2, 0, 600336, 306525, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_306525_600336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306525 ⟨600336, by decide⟩ :=
  accepted_of_selected 13 306525 ⟨600336, by decide⟩ ⟨13, 2, 0, 600336, 306525, 1801, 16384⟩
    (by decide) selected_cut_23772

theorem selected_cut_23773 : selected 8 ⟨600357, by decide⟩
    (prefixPartial 13 306526) = some ⟨13, 2, 0, 600357, 306526, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_306526_600357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306526 ⟨600357, by decide⟩ :=
  accepted_of_selected 13 306526 ⟨600357, by decide⟩ ⟨13, 2, 0, 600357, 306526, 1957, 16384⟩
    (by decide) selected_cut_23773

theorem selected_cut_23774 : selected 8 ⟨600364, by decide⟩
    (prefixPartial 13 306527) = some ⟨13, 2, 0, 600364, 306527, 825, 16384⟩ := by
  decide +kernel

theorem context_13_306527_600364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306527 ⟨600364, by decide⟩ :=
  accepted_of_selected 13 306527 ⟨600364, by decide⟩ ⟨13, 2, 0, 600364, 306527, 825, 16384⟩
    (by decide) selected_cut_23774

theorem unmarked_context_12_76631_600365 : frontier 9 ⟨600365, by decide⟩
    (prefixCache 12 76631) (prefixPartial 12 76631) = false := by
  decide +kernel

theorem node_context_12_76631_600365 : EJMOriginalGlobalDAGData.nodes 9 ⟨600365, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600336, by decide⟩,⟨600357, by decide⟩,⟨600364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76631_600365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76631 ⟨600365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76631
    ⟨600365, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600336, by decide⟩,⟨600357, by decide⟩,⟨600364, by decide⟩]) unmarked_context_12_76631_600365 node_context_12_76631_600365
  intro a
  fin_cases a
  · exact context_13_306524_3444
  · exact context_13_306525_600336
  · exact context_13_306526_600357
  · exact context_13_306527_600364

theorem unmarked_context_11_19157_600366 : frontier 10 ⟨600366, by decide⟩
    (prefixCache 11 19157) (prefixPartial 11 19157) = false := by
  decide +kernel

theorem node_context_11_19157_600366 : EJMOriginalGlobalDAGData.nodes 10 ⟨600366, by decide⟩ =
    .split (coordinate 11) (![⟨600202, by decide⟩,⟨600246, by decide⟩,⟨600315, by decide⟩,⟨600365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19157_600366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19157 ⟨600366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19157
    ⟨600366, by decide⟩ (by decide) (![⟨600202, by decide⟩,⟨600246, by decide⟩,⟨600315, by decide⟩,⟨600365, by decide⟩]) unmarked_context_11_19157_600366 node_context_11_19157_600366
  intro a
  fin_cases a
  · exact context_12_76628_600202
  · exact context_12_76629_600246
  · exact context_12_76630_600315
  · exact context_12_76631_600365

theorem selected_cut_23775 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306528) = some ⟨13, 1, 0, 3444, 306528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306528, 1, 16384⟩
    (by decide) selected_cut_23775

theorem selected_cut_23776 : selected 8 ⟨600389, by decide⟩
    (prefixPartial 13 306529) = some ⟨13, 2, 0, 600389, 306529, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_306529_600389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306529 ⟨600389, by decide⟩ :=
  accepted_of_selected 13 306529 ⟨600389, by decide⟩ ⟨13, 2, 0, 600389, 306529, 1497, 16384⟩
    (by decide) selected_cut_23776

theorem selected_cut_23777 : selected 8 ⟨600409, by decide⟩
    (prefixPartial 13 306530) = some ⟨13, 2, 0, 600409, 306530, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_306530_600409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306530 ⟨600409, by decide⟩ :=
  accepted_of_selected 13 306530 ⟨600409, by decide⟩ ⟨13, 2, 0, 600409, 306530, 1621, 16384⟩
    (by decide) selected_cut_23777

theorem selected_cut_23778 : selected 8 ⟨600417, by decide⟩
    (prefixPartial 13 306531) = some ⟨13, 2, 0, 600417, 306531, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_306531_600417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306531 ⟨600417, by decide⟩ :=
  accepted_of_selected 13 306531 ⟨600417, by decide⟩ ⟨13, 2, 0, 600417, 306531, 1033, 16384⟩
    (by decide) selected_cut_23778

theorem unmarked_context_12_76632_600418 : frontier 9 ⟨600418, by decide⟩
    (prefixCache 12 76632) (prefixPartial 12 76632) = false := by
  decide +kernel

theorem node_context_12_76632_600418 : EJMOriginalGlobalDAGData.nodes 9 ⟨600418, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600389, by decide⟩,⟨600409, by decide⟩,⟨600417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76632_600418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76632 ⟨600418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76632
    ⟨600418, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600389, by decide⟩,⟨600409, by decide⟩,⟨600417, by decide⟩]) unmarked_context_12_76632_600418 node_context_12_76632_600418
  intro a
  fin_cases a
  · exact context_13_306528_3444
  · exact context_13_306529_600389
  · exact context_13_306530_600409
  · exact context_13_306531_600417

theorem selected_cut_23779 : selected 9 ⟨600473, by decide⟩
    (prefixPartial 12 76633) = some ⟨12, 2, 0, 600473, 76633, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_76633_600473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76633 ⟨600473, by decide⟩ :=
  accepted_of_selected 12 76633 ⟨600473, by decide⟩ ⟨12, 2, 0, 600473, 76633, 3925, 65536⟩
    (by decide) selected_cut_23779

theorem selected_cut_23780 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306536) = some ⟨13, 1, 0, 3444, 306536, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306536_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306536 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306536 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306536, 1, 16384⟩
    (by decide) selected_cut_23780

theorem selected_cut_23781 : selected 8 ⟨600496, by decide⟩
    (prefixPartial 13 306537) = some ⟨13, 2, 0, 600496, 306537, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_306537_600496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306537 ⟨600496, by decide⟩ :=
  accepted_of_selected 13 306537 ⟨600496, by decide⟩ ⟨13, 2, 0, 600496, 306537, 1585, 16384⟩
    (by decide) selected_cut_23781

theorem selected_cut_23782 : selected 8 ⟨600522, by decide⟩
    (prefixPartial 13 306538) = some ⟨13, 2, 0, 600522, 306538, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_306538_600522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306538 ⟨600522, by decide⟩ :=
  accepted_of_selected 13 306538 ⟨600522, by decide⟩ ⟨13, 2, 0, 600522, 306538, 1765, 16384⟩
    (by decide) selected_cut_23782

theorem selected_cut_23783 : selected 8 ⟨600530, by decide⟩
    (prefixPartial 13 306539) = some ⟨13, 2, 0, 600530, 306539, 945, 16384⟩ := by
  decide +kernel

theorem context_13_306539_600530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306539 ⟨600530, by decide⟩ :=
  accepted_of_selected 13 306539 ⟨600530, by decide⟩ ⟨13, 2, 0, 600530, 306539, 945, 16384⟩
    (by decide) selected_cut_23783

theorem unmarked_context_12_76634_600531 : frontier 9 ⟨600531, by decide⟩
    (prefixCache 12 76634) (prefixPartial 12 76634) = false := by
  decide +kernel

theorem node_context_12_76634_600531 : EJMOriginalGlobalDAGData.nodes 9 ⟨600531, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600496, by decide⟩,⟨600522, by decide⟩,⟨600530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76634_600531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76634 ⟨600531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76634
    ⟨600531, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600496, by decide⟩,⟨600522, by decide⟩,⟨600530, by decide⟩]) unmarked_context_12_76634_600531 node_context_12_76634_600531
  intro a
  fin_cases a
  · exact context_13_306536_3444
  · exact context_13_306537_600496
  · exact context_13_306538_600522
  · exact context_13_306539_600530

theorem selected_cut_23784 : selected 9 ⟨600579, by decide⟩
    (prefixPartial 12 76635) = some ⟨12, 2, 0, 600579, 76635, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_76635_600579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76635 ⟨600579, by decide⟩ :=
  accepted_of_selected 12 76635 ⟨600579, by decide⟩ ⟨12, 2, 0, 600579, 76635, 4009, 65536⟩
    (by decide) selected_cut_23784

theorem unmarked_context_11_19158_600580 : frontier 10 ⟨600580, by decide⟩
    (prefixCache 11 19158) (prefixPartial 11 19158) = false := by
  decide +kernel

theorem node_context_11_19158_600580 : EJMOriginalGlobalDAGData.nodes 10 ⟨600580, by decide⟩ =
    .split (coordinate 11) (![⟨600418, by decide⟩,⟨600473, by decide⟩,⟨600531, by decide⟩,⟨600579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19158_600580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19158 ⟨600580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19158
    ⟨600580, by decide⟩ (by decide) (![⟨600418, by decide⟩,⟨600473, by decide⟩,⟨600531, by decide⟩,⟨600579, by decide⟩]) unmarked_context_11_19158_600580 node_context_11_19158_600580
  intro a
  fin_cases a
  · exact context_12_76632_600418
  · exact context_12_76633_600473
  · exact context_12_76634_600531
  · exact context_12_76635_600579

theorem selected_cut_23785 : selected 9 ⟨600624, by decide⟩
    (prefixPartial 12 76636) = some ⟨12, 2, 0, 600624, 76636, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_76636_600624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76636 ⟨600624, by decide⟩ :=
  accepted_of_selected 12 76636 ⟨600624, by decide⟩ ⟨12, 2, 0, 600624, 76636, 3569, 65536⟩
    (by decide) selected_cut_23785

theorem selected_cut_23786 : selected 9 ⟨600669, by decide⟩
    (prefixPartial 12 76637) = some ⟨12, 2, 0, 600669, 76637, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_76637_600669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76637 ⟨600669, by decide⟩ :=
  accepted_of_selected 12 76637 ⟨600669, by decide⟩ ⟨12, 2, 0, 600669, 76637, 3513, 65536⟩
    (by decide) selected_cut_23786

theorem selected_cut_23787 : selected 9 ⟨600726, by decide⟩
    (prefixPartial 12 76638) = some ⟨12, 2, 0, 600726, 76638, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_76638_600726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76638 ⟨600726, by decide⟩ :=
  accepted_of_selected 12 76638 ⟨600726, by decide⟩ ⟨12, 2, 0, 600726, 76638, 3957, 65536⟩
    (by decide) selected_cut_23787

theorem selected_cut_23788 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306556) = some ⟨13, 1, 0, 3444, 306556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306556, 1, 16384⟩
    (by decide) selected_cut_23788

theorem selected_cut_23789 : selected 8 ⟨600757, by decide⟩
    (prefixPartial 13 306557) = some ⟨13, 2, 0, 600757, 306557, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_306557_600757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306557 ⟨600757, by decide⟩ :=
  accepted_of_selected 13 306557 ⟨600757, by decide⟩ ⟨13, 2, 0, 600757, 306557, 2089, 16384⟩
    (by decide) selected_cut_23789

theorem selected_cut_23790 : selected 8 ⟨600807, by decide⟩
    (prefixPartial 13 306558) = some ⟨13, 2, 0, 600807, 306558, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_306558_600807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306558 ⟨600807, by decide⟩ :=
  accepted_of_selected 13 306558 ⟨600807, by decide⟩ ⟨13, 2, 0, 600807, 306558, 2805, 16384⟩
    (by decide) selected_cut_23790

theorem selected_cut_23791 : selected 8 ⟨600817, by decide⟩
    (prefixPartial 13 306559) = some ⟨13, 2, 0, 600817, 306559, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_306559_600817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306559 ⟨600817, by decide⟩ :=
  accepted_of_selected 13 306559 ⟨600817, by decide⟩ ⟨13, 2, 0, 600817, 306559, 1221, 16384⟩
    (by decide) selected_cut_23791

theorem unmarked_context_12_76639_600818 : frontier 9 ⟨600818, by decide⟩
    (prefixCache 12 76639) (prefixPartial 12 76639) = false := by
  decide +kernel

theorem node_context_12_76639_600818 : EJMOriginalGlobalDAGData.nodes 9 ⟨600818, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨600757, by decide⟩,⟨600807, by decide⟩,⟨600817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76639_600818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76639 ⟨600818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76639
    ⟨600818, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨600757, by decide⟩,⟨600807, by decide⟩,⟨600817, by decide⟩]) unmarked_context_12_76639_600818 node_context_12_76639_600818
  intro a
  fin_cases a
  · exact context_13_306556_3444
  · exact context_13_306557_600757
  · exact context_13_306558_600807
  · exact context_13_306559_600817

theorem unmarked_context_11_19159_600819 : frontier 10 ⟨600819, by decide⟩
    (prefixCache 11 19159) (prefixPartial 11 19159) = false := by
  decide +kernel

theorem node_context_11_19159_600819 : EJMOriginalGlobalDAGData.nodes 10 ⟨600819, by decide⟩ =
    .split (coordinate 11) (![⟨600624, by decide⟩,⟨600669, by decide⟩,⟨600726, by decide⟩,⟨600818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19159_600819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19159 ⟨600819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19159
    ⟨600819, by decide⟩ (by decide) (![⟨600624, by decide⟩,⟨600669, by decide⟩,⟨600726, by decide⟩,⟨600818, by decide⟩]) unmarked_context_11_19159_600819 node_context_11_19159_600819
  intro a
  fin_cases a
  · exact context_12_76636_600624
  · exact context_12_76637_600669
  · exact context_12_76638_600726
  · exact context_12_76639_600818

theorem unmarked_context_10_4789_600820 : frontier 11 ⟨600820, by decide⟩
    (prefixCache 10 4789) (prefixPartial 10 4789) = false := by
  decide +kernel

theorem node_context_10_4789_600820 : EJMOriginalGlobalDAGData.nodes 11 ⟨600820, by decide⟩ =
    .split (coordinate 10) (![⟨600138, by decide⟩,⟨600366, by decide⟩,⟨600580, by decide⟩,⟨600819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4789_600820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4789 ⟨600820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4789
    ⟨600820, by decide⟩ (by decide) (![⟨600138, by decide⟩,⟨600366, by decide⟩,⟨600580, by decide⟩,⟨600819, by decide⟩]) unmarked_context_10_4789_600820 node_context_10_4789_600820
  intro a
  fin_cases a
  · exact context_11_19156_600138
  · exact context_11_19157_600366
  · exact context_11_19158_600580
  · exact context_11_19159_600819

theorem selected_cut_23792 : selected 9 ⟨600868, by decide⟩
    (prefixPartial 12 76640) = some ⟨12, 2, 0, 600868, 76640, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_76640_600868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76640 ⟨600868, by decide⟩ :=
  accepted_of_selected 12 76640 ⟨600868, by decide⟩ ⟨12, 2, 0, 600868, 76640, 3277, 65536⟩
    (by decide) selected_cut_23792

theorem selected_cut_23793 : selected 9 ⟨600900, by decide⟩
    (prefixPartial 12 76641) = some ⟨12, 2, 0, 600900, 76641, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_76641_600900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76641 ⟨600900, by decide⟩ :=
  accepted_of_selected 12 76641 ⟨600900, by decide⟩ ⟨12, 2, 0, 600900, 76641, 3081, 65536⟩
    (by decide) selected_cut_23793

theorem selected_cut_23794 : selected 9 ⟨600947, by decide⟩
    (prefixPartial 12 76642) = some ⟨12, 2, 0, 600947, 76642, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_76642_600947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76642 ⟨600947, by decide⟩ :=
  accepted_of_selected 12 76642 ⟨600947, by decide⟩ ⟨12, 2, 0, 600947, 76642, 3629, 65536⟩
    (by decide) selected_cut_23794

theorem selected_cut_23795 : selected 9 ⟨600984, by decide⟩
    (prefixPartial 12 76643) = some ⟨12, 2, 0, 600984, 76643, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_76643_600984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76643 ⟨600984, by decide⟩ :=
  accepted_of_selected 12 76643 ⟨600984, by decide⟩ ⟨12, 2, 0, 600984, 76643, 3413, 65536⟩
    (by decide) selected_cut_23795

theorem unmarked_context_11_19160_600985 : frontier 10 ⟨600985, by decide⟩
    (prefixCache 11 19160) (prefixPartial 11 19160) = false := by
  decide +kernel

theorem node_context_11_19160_600985 : EJMOriginalGlobalDAGData.nodes 10 ⟨600985, by decide⟩ =
    .split (coordinate 11) (![⟨600868, by decide⟩,⟨600900, by decide⟩,⟨600947, by decide⟩,⟨600984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19160_600985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19160 ⟨600985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19160
    ⟨600985, by decide⟩ (by decide) (![⟨600868, by decide⟩,⟨600900, by decide⟩,⟨600947, by decide⟩,⟨600984, by decide⟩]) unmarked_context_11_19160_600985 node_context_11_19160_600985
  intro a
  fin_cases a
  · exact context_12_76640_600868
  · exact context_12_76641_600900
  · exact context_12_76642_600947
  · exact context_12_76643_600984

theorem selected_cut_23796 : selected 9 ⟨601036, by decide⟩
    (prefixPartial 12 76644) = some ⟨12, 2, 0, 601036, 76644, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_76644_601036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76644 ⟨601036, by decide⟩ :=
  accepted_of_selected 12 76644 ⟨601036, by decide⟩ ⟨12, 2, 0, 601036, 76644, 3421, 65536⟩
    (by decide) selected_cut_23796

theorem selected_cut_23797 : selected 9 ⟨601075, by decide⟩
    (prefixPartial 12 76645) = some ⟨12, 2, 0, 601075, 76645, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_76645_601075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76645 ⟨601075, by decide⟩ :=
  accepted_of_selected 12 76645 ⟨601075, by decide⟩ ⟨12, 2, 0, 601075, 76645, 3117, 65536⟩
    (by decide) selected_cut_23797

theorem selected_cut_23798 : selected 9 ⟨601119, by decide⟩
    (prefixPartial 12 76646) = some ⟨12, 2, 0, 601119, 76646, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_76646_601119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76646 ⟨601119, by decide⟩ :=
  accepted_of_selected 12 76646 ⟨601119, by decide⟩ ⟨12, 2, 0, 601119, 76646, 3613, 65536⟩
    (by decide) selected_cut_23798

theorem selected_cut_23799 : selected 9 ⟨601155, by decide⟩
    (prefixPartial 12 76647) = some ⟨12, 2, 0, 601155, 76647, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_76647_601155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76647 ⟨601155, by decide⟩ :=
  accepted_of_selected 12 76647 ⟨601155, by decide⟩ ⟨12, 2, 0, 601155, 76647, 3577, 65536⟩
    (by decide) selected_cut_23799

theorem unmarked_context_11_19161_601156 : frontier 10 ⟨601156, by decide⟩
    (prefixCache 11 19161) (prefixPartial 11 19161) = false := by
  decide +kernel

theorem node_context_11_19161_601156 : EJMOriginalGlobalDAGData.nodes 10 ⟨601156, by decide⟩ =
    .split (coordinate 11) (![⟨601036, by decide⟩,⟨601075, by decide⟩,⟨601119, by decide⟩,⟨601155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19161_601156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19161 ⟨601156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19161
    ⟨601156, by decide⟩ (by decide) (![⟨601036, by decide⟩,⟨601075, by decide⟩,⟨601119, by decide⟩,⟨601155, by decide⟩]) unmarked_context_11_19161_601156 node_context_11_19161_601156
  intro a
  fin_cases a
  · exact context_12_76644_601036
  · exact context_12_76645_601075
  · exact context_12_76646_601119
  · exact context_12_76647_601155

theorem selected_cut_23800 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306592) = some ⟨13, 1, 0, 3444, 306592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306592, 1, 16384⟩
    (by decide) selected_cut_23800

theorem selected_cut_23801 : selected 8 ⟨601171, by decide⟩
    (prefixPartial 13 306593) = some ⟨13, 2, 0, 601171, 306593, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_306593_601171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306593 ⟨601171, by decide⟩ :=
  accepted_of_selected 13 306593 ⟨601171, by decide⟩ ⟨13, 2, 0, 601171, 306593, 1093, 16384⟩
    (by decide) selected_cut_23801

theorem selected_cut_23802 : selected 8 ⟨601195, by decide⟩
    (prefixPartial 13 306594) = some ⟨13, 2, 0, 601195, 306594, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_306594_601195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306594 ⟨601195, by decide⟩ :=
  accepted_of_selected 13 306594 ⟨601195, by decide⟩ ⟨13, 2, 0, 601195, 306594, 1969, 16384⟩
    (by decide) selected_cut_23802

theorem selected_cut_23803 : selected 8 ⟨601225, by decide⟩
    (prefixPartial 13 306595) = some ⟨13, 2, 0, 601225, 306595, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_306595_601225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306595 ⟨601225, by decide⟩ :=
  accepted_of_selected 13 306595 ⟨601225, by decide⟩ ⟨13, 2, 0, 601225, 306595, 1357, 16384⟩
    (by decide) selected_cut_23803

theorem unmarked_context_12_76648_601226 : frontier 9 ⟨601226, by decide⟩
    (prefixCache 12 76648) (prefixPartial 12 76648) = false := by
  decide +kernel

theorem node_context_12_76648_601226 : EJMOriginalGlobalDAGData.nodes 9 ⟨601226, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨601171, by decide⟩,⟨601195, by decide⟩,⟨601225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76648_601226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76648 ⟨601226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76648
    ⟨601226, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨601171, by decide⟩,⟨601195, by decide⟩,⟨601225, by decide⟩]) unmarked_context_12_76648_601226 node_context_12_76648_601226
  intro a
  fin_cases a
  · exact context_13_306592_3444
  · exact context_13_306593_601171
  · exact context_13_306594_601195
  · exact context_13_306595_601225

theorem selected_cut_23804 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306596) = some ⟨13, 1, 0, 3444, 306596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306596, 1, 16384⟩
    (by decide) selected_cut_23804

theorem selected_cut_23805 : selected 8 ⟨601237, by decide⟩
    (prefixPartial 13 306597) = some ⟨13, 2, 0, 601237, 306597, 949, 16384⟩ := by
  decide +kernel

theorem context_13_306597_601237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306597 ⟨601237, by decide⟩ :=
  accepted_of_selected 13 306597 ⟨601237, by decide⟩ ⟨13, 2, 0, 601237, 306597, 949, 16384⟩
    (by decide) selected_cut_23805

theorem selected_cut_23806 : selected 8 ⟨601260, by decide⟩
    (prefixPartial 13 306598) = some ⟨13, 2, 0, 601260, 306598, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_306598_601260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306598 ⟨601260, by decide⟩ :=
  accepted_of_selected 13 306598 ⟨601260, by decide⟩ ⟨13, 2, 0, 601260, 306598, 2101, 16384⟩
    (by decide) selected_cut_23806

theorem selected_cut_23807 : selected 8 ⟨601274, by decide⟩
    (prefixPartial 13 306599) = some ⟨13, 2, 0, 601274, 306599, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_306599_601274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306599 ⟨601274, by decide⟩ :=
  accepted_of_selected 13 306599 ⟨601274, by decide⟩ ⟨13, 2, 0, 601274, 306599, 1229, 16384⟩
    (by decide) selected_cut_23807

theorem unmarked_context_12_76649_601275 : frontier 9 ⟨601275, by decide⟩
    (prefixCache 12 76649) (prefixPartial 12 76649) = false := by
  decide +kernel

theorem node_context_12_76649_601275 : EJMOriginalGlobalDAGData.nodes 9 ⟨601275, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨601237, by decide⟩,⟨601260, by decide⟩,⟨601274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76649_601275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76649 ⟨601275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76649
    ⟨601275, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨601237, by decide⟩,⟨601260, by decide⟩,⟨601274, by decide⟩]) unmarked_context_12_76649_601275 node_context_12_76649_601275
  intro a
  fin_cases a
  · exact context_13_306596_3444
  · exact context_13_306597_601237
  · exact context_13_306598_601260
  · exact context_13_306599_601274

theorem selected_cut_23808 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 76650) = some ⟨12, 1, 0, 474208, 76650, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76650_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76650 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 76650 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 76650, 1, 65536⟩
    (by decide) selected_cut_23808

theorem selected_cut_23809 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306604) = some ⟨13, 1, 0, 3444, 306604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306604, 1, 16384⟩
    (by decide) selected_cut_23809

theorem selected_cut_23810 : selected 8 ⟨601287, by decide⟩
    (prefixPartial 13 306605) = some ⟨13, 2, 0, 601287, 306605, 993, 16384⟩ := by
  decide +kernel

theorem context_13_306605_601287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306605 ⟨601287, by decide⟩ :=
  accepted_of_selected 13 306605 ⟨601287, by decide⟩ ⟨13, 2, 0, 601287, 306605, 993, 16384⟩
    (by decide) selected_cut_23810

theorem selected_cut_23811 : selected 8 ⟨601321, by decide⟩
    (prefixPartial 13 306606) = some ⟨13, 2, 0, 601321, 306606, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_306606_601321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306606 ⟨601321, by decide⟩ :=
  accepted_of_selected 13 306606 ⟨601321, by decide⟩ ⟨13, 2, 0, 601321, 306606, 2321, 16384⟩
    (by decide) selected_cut_23811

theorem selected_cut_23812 : selected 8 ⟨601328, by decide⟩
    (prefixPartial 13 306607) = some ⟨13, 2, 0, 601328, 306607, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_306607_601328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306607 ⟨601328, by decide⟩ :=
  accepted_of_selected 13 306607 ⟨601328, by decide⟩ ⟨13, 2, 0, 601328, 306607, 1109, 16384⟩
    (by decide) selected_cut_23812

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
