/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover285
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_27459 : selected 7 ⟨694160, by decide⟩
    (prefixPartial 14 1466529) = some ⟨14, 2, 0, 694160, 1466529, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_1466529_694160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466529 ⟨694160, by decide⟩ :=
  accepted_of_selected 14 1466529 ⟨694160, by decide⟩ ⟨14, 2, 0, 694160, 1466529, 1293, 4096⟩
    (by decide) selected_cut_27459

theorem selected_cut_27460 : selected 7 ⟨694170, by decide⟩
    (prefixPartial 14 1466530) = some ⟨14, 2, 0, 694170, 1466530, 973, 4096⟩ := by
  decide +kernel

theorem context_14_1466530_694170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466530 ⟨694170, by decide⟩ :=
  accepted_of_selected 14 1466530 ⟨694170, by decide⟩ ⟨14, 2, 0, 694170, 1466530, 973, 4096⟩
    (by decide) selected_cut_27460

theorem selected_cut_27461 : selected 7 ⟨694205, by decide⟩
    (prefixPartial 14 1466531) = some ⟨14, 2, 0, 694205, 1466531, 1597, 4096⟩ := by
  decide +kernel

theorem context_14_1466531_694205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466531 ⟨694205, by decide⟩ :=
  accepted_of_selected 14 1466531 ⟨694205, by decide⟩ ⟨14, 2, 0, 694205, 1466531, 1597, 4096⟩
    (by decide) selected_cut_27461

theorem unmarked_context_13_366632_694206 : frontier 8 ⟨694206, by decide⟩
    (prefixCache 13 366632) (prefixPartial 13 366632) = false := by
  decide +kernel

theorem node_context_13_366632_694206 : EJMOriginalGlobalDAGData.nodes 8 ⟨694206, by decide⟩ =
    .split (coordinate 13) (![⟨694130, by decide⟩,⟨694160, by decide⟩,⟨694170, by decide⟩,⟨694205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_366632_694206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366632 ⟨694206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 366632
    ⟨694206, by decide⟩ (by decide) (![⟨694130, by decide⟩,⟨694160, by decide⟩,⟨694170, by decide⟩,⟨694205, by decide⟩]) unmarked_context_13_366632_694206 node_context_13_366632_694206
  intro a
  fin_cases a
  · exact context_14_1466528_694130
  · exact context_14_1466529_694160
  · exact context_14_1466530_694170
  · exact context_14_1466531_694205

theorem selected_cut_27462 : selected 7 ⟨694247, by decide⟩
    (prefixPartial 14 1466532) = some ⟨14, 2, 0, 694247, 1466532, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_1466532_694247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466532 ⟨694247, by decide⟩ :=
  accepted_of_selected 14 1466532 ⟨694247, by decide⟩ ⟨14, 2, 0, 694247, 1466532, 1297, 4096⟩
    (by decide) selected_cut_27462

theorem selected_cut_27463 : selected 7 ⟨694264, by decide⟩
    (prefixPartial 14 1466533) = some ⟨14, 2, 0, 694264, 1466533, 589, 4096⟩ := by
  decide +kernel

theorem context_14_1466533_694264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466533 ⟨694264, by decide⟩ :=
  accepted_of_selected 14 1466533 ⟨694264, by decide⟩ ⟨14, 2, 0, 694264, 1466533, 589, 4096⟩
    (by decide) selected_cut_27463

theorem selected_cut_27464 : selected 7 ⟨694287, by decide⟩
    (prefixPartial 14 1466534) = some ⟨14, 2, 0, 694287, 1466534, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_1466534_694287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466534 ⟨694287, by decide⟩ :=
  accepted_of_selected 14 1466534 ⟨694287, by decide⟩ ⟨14, 2, 0, 694287, 1466534, 1037, 4096⟩
    (by decide) selected_cut_27464

theorem selected_cut_27465 : selected 7 ⟨694312, by decide⟩
    (prefixPartial 14 1466535) = some ⟨14, 2, 0, 694312, 1466535, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_1466535_694312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466535 ⟨694312, by decide⟩ :=
  accepted_of_selected 14 1466535 ⟨694312, by decide⟩ ⟨14, 2, 0, 694312, 1466535, 1245, 4096⟩
    (by decide) selected_cut_27465

theorem unmarked_context_13_366633_694313 : frontier 8 ⟨694313, by decide⟩
    (prefixCache 13 366633) (prefixPartial 13 366633) = false := by
  decide +kernel

theorem node_context_13_366633_694313 : EJMOriginalGlobalDAGData.nodes 8 ⟨694313, by decide⟩ =
    .split (coordinate 13) (![⟨694247, by decide⟩,⟨694264, by decide⟩,⟨694287, by decide⟩,⟨694312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_366633_694313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366633 ⟨694313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 366633
    ⟨694313, by decide⟩ (by decide) (![⟨694247, by decide⟩,⟨694264, by decide⟩,⟨694287, by decide⟩,⟨694312, by decide⟩]) unmarked_context_13_366633_694313 node_context_13_366633_694313
  intro a
  fin_cases a
  · exact context_14_1466532_694247
  · exact context_14_1466533_694264
  · exact context_14_1466534_694287
  · exact context_14_1466535_694312

theorem selected_cut_27466 : selected 8 ⟨694358, by decide⟩
    (prefixPartial 13 366634) = some ⟨13, 2, 0, 694358, 366634, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_366634_694358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366634 ⟨694358, by decide⟩ :=
  accepted_of_selected 13 366634 ⟨694358, by decide⟩ ⟨13, 2, 0, 694358, 366634, 2661, 16384⟩
    (by decide) selected_cut_27466

theorem selected_cut_27467 : selected 8 ⟨694408, by decide⟩
    (prefixPartial 13 366635) = some ⟨13, 2, 0, 694408, 366635, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_366635_694408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366635 ⟨694408, by decide⟩ :=
  accepted_of_selected 13 366635 ⟨694408, by decide⟩ ⟨13, 2, 0, 694408, 366635, 1733, 16384⟩
    (by decide) selected_cut_27467

theorem unmarked_context_12_91658_694409 : frontier 9 ⟨694409, by decide⟩
    (prefixCache 12 91658) (prefixPartial 12 91658) = false := by
  decide +kernel

theorem node_context_12_91658_694409 : EJMOriginalGlobalDAGData.nodes 9 ⟨694409, by decide⟩ =
    .split (coordinate 12) (![⟨694206, by decide⟩,⟨694313, by decide⟩,⟨694358, by decide⟩,⟨694408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91658_694409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91658 ⟨694409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91658
    ⟨694409, by decide⟩ (by decide) (![⟨694206, by decide⟩,⟨694313, by decide⟩,⟨694358, by decide⟩,⟨694408, by decide⟩]) unmarked_context_12_91658_694409 node_context_12_91658_694409
  intro a
  fin_cases a
  · exact context_13_366632_694206
  · exact context_13_366633_694313
  · exact context_13_366634_694358
  · exact context_13_366635_694408

theorem selected_cut_27468 : selected 8 ⟨694482, by decide⟩
    (prefixPartial 13 366636) = some ⟨13, 2, 0, 694482, 366636, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_366636_694482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366636 ⟨694482, by decide⟩ :=
  accepted_of_selected 13 366636 ⟨694482, by decide⟩ ⟨13, 2, 0, 694482, 366636, 3389, 16384⟩
    (by decide) selected_cut_27468

theorem selected_cut_27469 : selected 8 ⟨694557, by decide⟩
    (prefixPartial 13 366637) = some ⟨13, 2, 0, 694557, 366637, 3321, 16384⟩ := by
  decide +kernel

theorem context_13_366637_694557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366637 ⟨694557, by decide⟩ :=
  accepted_of_selected 13 366637 ⟨694557, by decide⟩ ⟨13, 2, 0, 694557, 366637, 3321, 16384⟩
    (by decide) selected_cut_27469

theorem selected_cut_27470 : selected 8 ⟨694578, by decide⟩
    (prefixPartial 13 366638) = some ⟨13, 2, 0, 694578, 366638, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_366638_694578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366638 ⟨694578, by decide⟩ :=
  accepted_of_selected 13 366638 ⟨694578, by decide⟩ ⟨13, 2, 0, 694578, 366638, 1837, 16384⟩
    (by decide) selected_cut_27470

theorem selected_cut_27471 : selected 8 ⟨694587, by decide⟩
    (prefixPartial 13 366639) = some ⟨13, 2, 0, 694587, 366639, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_366639_694587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366639 ⟨694587, by decide⟩ :=
  accepted_of_selected 13 366639 ⟨694587, by decide⟩ ⟨13, 2, 0, 694587, 366639, 1037, 16384⟩
    (by decide) selected_cut_27471

theorem unmarked_context_12_91659_694588 : frontier 9 ⟨694588, by decide⟩
    (prefixCache 12 91659) (prefixPartial 12 91659) = false := by
  decide +kernel

theorem node_context_12_91659_694588 : EJMOriginalGlobalDAGData.nodes 9 ⟨694588, by decide⟩ =
    .split (coordinate 12) (![⟨694482, by decide⟩,⟨694557, by decide⟩,⟨694578, by decide⟩,⟨694587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91659_694588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91659 ⟨694588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91659
    ⟨694588, by decide⟩ (by decide) (![⟨694482, by decide⟩,⟨694557, by decide⟩,⟨694578, by decide⟩,⟨694587, by decide⟩]) unmarked_context_12_91659_694588 node_context_12_91659_694588
  intro a
  fin_cases a
  · exact context_13_366636_694482
  · exact context_13_366637_694557
  · exact context_13_366638_694578
  · exact context_13_366639_694587

theorem unmarked_context_11_22914_694589 : frontier 10 ⟨694589, by decide⟩
    (prefixCache 11 22914) (prefixPartial 11 22914) = false := by
  decide +kernel

theorem node_context_11_22914_694589 : EJMOriginalGlobalDAGData.nodes 10 ⟨694589, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨694105, by decide⟩,⟨694409, by decide⟩,⟨694588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22914_694589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22914 ⟨694589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22914
    ⟨694589, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨694105, by decide⟩,⟨694409, by decide⟩,⟨694588, by decide⟩]) unmarked_context_11_22914_694589 node_context_11_22914_694589
  intro a
  fin_cases a
  · exact context_12_91656_448748
  · exact context_12_91657_694105
  · exact context_12_91658_694409
  · exact context_12_91659_694588

theorem selected_cut_27472 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91660) = some ⟨12, 1, 0, 448748, 91660, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91660_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91660 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91660 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91660, 1, 65536⟩
    (by decide) selected_cut_27472

theorem selected_cut_27473 : selected 8 ⟨694654, by decide⟩
    (prefixPartial 13 366644) = some ⟨13, 2, 0, 694654, 366644, 3449, 16384⟩ := by
  decide +kernel

theorem context_13_366644_694654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366644 ⟨694654, by decide⟩ :=
  accepted_of_selected 13 366644 ⟨694654, by decide⟩ ⟨13, 2, 0, 694654, 366644, 3449, 16384⟩
    (by decide) selected_cut_27473

theorem selected_cut_27474 : selected 8 ⟨694724, by decide⟩
    (prefixPartial 13 366645) = some ⟨13, 2, 0, 694724, 366645, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_366645_694724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366645 ⟨694724, by decide⟩ :=
  accepted_of_selected 13 366645 ⟨694724, by decide⟩ ⟨13, 2, 0, 694724, 366645, 3181, 16384⟩
    (by decide) selected_cut_27474

theorem selected_cut_27475 : selected 8 ⟨694746, by decide⟩
    (prefixPartial 13 366646) = some ⟨13, 2, 0, 694746, 366646, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_366646_694746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366646 ⟨694746, by decide⟩ :=
  accepted_of_selected 13 366646 ⟨694746, by decide⟩ ⟨13, 2, 0, 694746, 366646, 1685, 16384⟩
    (by decide) selected_cut_27475

theorem selected_cut_27476 : selected 8 ⟨694758, by decide⟩
    (prefixPartial 13 366647) = some ⟨13, 2, 0, 694758, 366647, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_366647_694758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366647 ⟨694758, by decide⟩ :=
  accepted_of_selected 13 366647 ⟨694758, by decide⟩ ⟨13, 2, 0, 694758, 366647, 1061, 16384⟩
    (by decide) selected_cut_27476

theorem unmarked_context_12_91661_694759 : frontier 9 ⟨694759, by decide⟩
    (prefixCache 12 91661) (prefixPartial 12 91661) = false := by
  decide +kernel

theorem node_context_12_91661_694759 : EJMOriginalGlobalDAGData.nodes 9 ⟨694759, by decide⟩ =
    .split (coordinate 12) (![⟨694654, by decide⟩,⟨694724, by decide⟩,⟨694746, by decide⟩,⟨694758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91661_694759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91661 ⟨694759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91661
    ⟨694759, by decide⟩ (by decide) (![⟨694654, by decide⟩,⟨694724, by decide⟩,⟨694746, by decide⟩,⟨694758, by decide⟩]) unmarked_context_12_91661_694759 node_context_12_91661_694759
  intro a
  fin_cases a
  · exact context_13_366644_694654
  · exact context_13_366645_694724
  · exact context_13_366646_694746
  · exact context_13_366647_694758

theorem selected_cut_27477 : selected 8 ⟨694802, by decide⟩
    (prefixPartial 13 366648) = some ⟨13, 2, 0, 694802, 366648, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_366648_694802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366648 ⟨694802, by decide⟩ :=
  accepted_of_selected 13 366648 ⟨694802, by decide⟩ ⟨13, 2, 0, 694802, 366648, 2557, 16384⟩
    (by decide) selected_cut_27477

theorem selected_cut_27478 : selected 8 ⟨694844, by decide⟩
    (prefixPartial 13 366649) = some ⟨13, 2, 0, 694844, 366649, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_366649_694844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366649 ⟨694844, by decide⟩ :=
  accepted_of_selected 13 366649 ⟨694844, by decide⟩ ⟨13, 2, 0, 694844, 366649, 2581, 16384⟩
    (by decide) selected_cut_27478

theorem selected_cut_27479 : selected 8 ⟨694863, by decide⟩
    (prefixPartial 13 366650) = some ⟨13, 2, 0, 694863, 366650, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_366650_694863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366650 ⟨694863, by decide⟩ :=
  accepted_of_selected 13 366650 ⟨694863, by decide⟩ ⟨13, 2, 0, 694863, 366650, 1525, 16384⟩
    (by decide) selected_cut_27479

theorem selected_cut_27480 : selected 8 ⟨694878, by decide⟩
    (prefixPartial 13 366651) = some ⟨13, 2, 0, 694878, 366651, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_366651_694878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366651 ⟨694878, by decide⟩ :=
  accepted_of_selected 13 366651 ⟨694878, by decide⟩ ⟨13, 2, 0, 694878, 366651, 1141, 16384⟩
    (by decide) selected_cut_27480

theorem unmarked_context_12_91662_694879 : frontier 9 ⟨694879, by decide⟩
    (prefixCache 12 91662) (prefixPartial 12 91662) = false := by
  decide +kernel

theorem node_context_12_91662_694879 : EJMOriginalGlobalDAGData.nodes 9 ⟨694879, by decide⟩ =
    .split (coordinate 12) (![⟨694802, by decide⟩,⟨694844, by decide⟩,⟨694863, by decide⟩,⟨694878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91662_694879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91662 ⟨694879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91662
    ⟨694879, by decide⟩ (by decide) (![⟨694802, by decide⟩,⟨694844, by decide⟩,⟨694863, by decide⟩,⟨694878, by decide⟩]) unmarked_context_12_91662_694879 node_context_12_91662_694879
  intro a
  fin_cases a
  · exact context_13_366648_694802
  · exact context_13_366649_694844
  · exact context_13_366650_694863
  · exact context_13_366651_694878

theorem selected_cut_27481 : selected 8 ⟨694937, by decide⟩
    (prefixPartial 13 366652) = some ⟨13, 2, 0, 694937, 366652, 3353, 16384⟩ := by
  decide +kernel

theorem context_13_366652_694937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366652 ⟨694937, by decide⟩ :=
  accepted_of_selected 13 366652 ⟨694937, by decide⟩ ⟨13, 2, 0, 694937, 366652, 3353, 16384⟩
    (by decide) selected_cut_27481

theorem selected_cut_27482 : selected 8 ⟨695002, by decide⟩
    (prefixPartial 13 366653) = some ⟨13, 2, 0, 695002, 366653, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_366653_695002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366653 ⟨695002, by decide⟩ :=
  accepted_of_selected 13 366653 ⟨695002, by decide⟩ ⟨13, 2, 0, 695002, 366653, 3245, 16384⟩
    (by decide) selected_cut_27482

theorem selected_cut_27483 : selected 8 ⟨695025, by decide⟩
    (prefixPartial 13 366654) = some ⟨13, 2, 0, 695025, 366654, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_366654_695025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366654 ⟨695025, by decide⟩ :=
  accepted_of_selected 13 366654 ⟨695025, by decide⟩ ⟨13, 2, 0, 695025, 366654, 1853, 16384⟩
    (by decide) selected_cut_27483

theorem selected_cut_27484 : selected 8 ⟨695034, by decide⟩
    (prefixPartial 13 366655) = some ⟨13, 2, 0, 695034, 366655, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_366655_695034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366655 ⟨695034, by decide⟩ :=
  accepted_of_selected 13 366655 ⟨695034, by decide⟩ ⟨13, 2, 0, 695034, 366655, 1153, 16384⟩
    (by decide) selected_cut_27484

theorem unmarked_context_12_91663_695035 : frontier 9 ⟨695035, by decide⟩
    (prefixCache 12 91663) (prefixPartial 12 91663) = false := by
  decide +kernel

theorem node_context_12_91663_695035 : EJMOriginalGlobalDAGData.nodes 9 ⟨695035, by decide⟩ =
    .split (coordinate 12) (![⟨694937, by decide⟩,⟨695002, by decide⟩,⟨695025, by decide⟩,⟨695034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91663_695035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91663 ⟨695035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91663
    ⟨695035, by decide⟩ (by decide) (![⟨694937, by decide⟩,⟨695002, by decide⟩,⟨695025, by decide⟩,⟨695034, by decide⟩]) unmarked_context_12_91663_695035 node_context_12_91663_695035
  intro a
  fin_cases a
  · exact context_13_366652_694937
  · exact context_13_366653_695002
  · exact context_13_366654_695025
  · exact context_13_366655_695034

theorem unmarked_context_11_22915_695036 : frontier 10 ⟨695036, by decide⟩
    (prefixCache 11 22915) (prefixPartial 11 22915) = false := by
  decide +kernel

theorem node_context_11_22915_695036 : EJMOriginalGlobalDAGData.nodes 10 ⟨695036, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨694759, by decide⟩,⟨694879, by decide⟩,⟨695035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22915_695036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22915 ⟨695036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22915
    ⟨695036, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨694759, by decide⟩,⟨694879, by decide⟩,⟨695035, by decide⟩]) unmarked_context_11_22915_695036 node_context_11_22915_695036
  intro a
  fin_cases a
  · exact context_12_91660_448748
  · exact context_12_91661_694759
  · exact context_12_91662_694879
  · exact context_12_91663_695035

theorem unmarked_context_10_5728_695037 : frontier 11 ⟨695037, by decide⟩
    (prefixCache 10 5728) (prefixPartial 10 5728) = false := by
  decide +kernel

theorem node_context_10_5728_695037 : EJMOriginalGlobalDAGData.nodes 11 ⟨695037, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨693908, by decide⟩,⟨694589, by decide⟩,⟨695036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5728_695037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5728 ⟨695037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5728
    ⟨695037, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨693908, by decide⟩,⟨694589, by decide⟩,⟨695036, by decide⟩]) unmarked_context_10_5728_695037 node_context_10_5728_695037
  intro a
  fin_cases a
  · exact context_11_22912_434745
  · exact context_11_22913_693908
  · exact context_11_22914_694589
  · exact context_11_22915_695036

theorem selected_cut_27485 : selected 8 ⟨695066, by decide⟩
    (prefixPartial 13 366656) = some ⟨13, 2, 0, 695066, 366656, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_366656_695066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366656 ⟨695066, by decide⟩ :=
  accepted_of_selected 13 366656 ⟨695066, by decide⟩ ⟨13, 2, 0, 695066, 366656, 1905, 16384⟩
    (by decide) selected_cut_27485

theorem selected_cut_27486 : selected 8 ⟨695086, by decide⟩
    (prefixPartial 13 366657) = some ⟨13, 2, 0, 695086, 366657, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_366657_695086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366657 ⟨695086, by decide⟩ :=
  accepted_of_selected 13 366657 ⟨695086, by decide⟩ ⟨13, 2, 0, 695086, 366657, 1217, 16384⟩
    (by decide) selected_cut_27486

theorem selected_cut_27487 : selected 8 ⟨695107, by decide⟩
    (prefixPartial 13 366658) = some ⟨13, 2, 0, 695107, 366658, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_366658_695107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366658 ⟨695107, by decide⟩ :=
  accepted_of_selected 13 366658 ⟨695107, by decide⟩ ⟨13, 2, 0, 695107, 366658, 1245, 16384⟩
    (by decide) selected_cut_27487

theorem selected_cut_27488 : selected 8 ⟨695115, by decide⟩
    (prefixPartial 13 366659) = some ⟨13, 2, 0, 695115, 366659, 757, 16384⟩ := by
  decide +kernel

theorem context_13_366659_695115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366659 ⟨695115, by decide⟩ :=
  accepted_of_selected 13 366659 ⟨695115, by decide⟩ ⟨13, 2, 0, 695115, 366659, 757, 16384⟩
    (by decide) selected_cut_27488

theorem unmarked_context_12_91664_695116 : frontier 9 ⟨695116, by decide⟩
    (prefixCache 12 91664) (prefixPartial 12 91664) = false := by
  decide +kernel

theorem node_context_12_91664_695116 : EJMOriginalGlobalDAGData.nodes 9 ⟨695116, by decide⟩ =
    .split (coordinate 12) (![⟨695066, by decide⟩,⟨695086, by decide⟩,⟨695107, by decide⟩,⟨695115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91664_695116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91664 ⟨695116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91664
    ⟨695116, by decide⟩ (by decide) (![⟨695066, by decide⟩,⟨695086, by decide⟩,⟨695107, by decide⟩,⟨695115, by decide⟩]) unmarked_context_12_91664_695116 node_context_12_91664_695116
  intro a
  fin_cases a
  · exact context_13_366656_695066
  · exact context_13_366657_695086
  · exact context_13_366658_695107
  · exact context_13_366659_695115

theorem selected_cut_27489 : selected 8 ⟨695155, by decide⟩
    (prefixPartial 13 366660) = some ⟨13, 2, 0, 695155, 366660, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_366660_695155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366660 ⟨695155, by decide⟩ :=
  accepted_of_selected 13 366660 ⟨695155, by decide⟩ ⟨13, 2, 0, 695155, 366660, 2165, 16384⟩
    (by decide) selected_cut_27489

theorem selected_cut_27490 : selected 8 ⟨695176, by decide⟩
    (prefixPartial 13 366661) = some ⟨13, 2, 0, 695176, 366661, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_366661_695176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366661 ⟨695176, by decide⟩ :=
  accepted_of_selected 13 366661 ⟨695176, by decide⟩ ⟨13, 2, 0, 695176, 366661, 1501, 16384⟩
    (by decide) selected_cut_27490

theorem selected_cut_27491 : selected 8 ⟨695194, by decide⟩
    (prefixPartial 13 366662) = some ⟨13, 2, 0, 695194, 366662, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_366662_695194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366662 ⟨695194, by decide⟩ :=
  accepted_of_selected 13 366662 ⟨695194, by decide⟩ ⟨13, 2, 0, 695194, 366662, 1361, 16384⟩
    (by decide) selected_cut_27491

theorem selected_cut_27492 : selected 8 ⟨695200, by decide⟩
    (prefixPartial 13 366663) = some ⟨13, 2, 0, 695200, 366663, 797, 16384⟩ := by
  decide +kernel

theorem context_13_366663_695200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366663 ⟨695200, by decide⟩ :=
  accepted_of_selected 13 366663 ⟨695200, by decide⟩ ⟨13, 2, 0, 695200, 366663, 797, 16384⟩
    (by decide) selected_cut_27492

theorem unmarked_context_12_91665_695201 : frontier 9 ⟨695201, by decide⟩
    (prefixCache 12 91665) (prefixPartial 12 91665) = false := by
  decide +kernel

theorem node_context_12_91665_695201 : EJMOriginalGlobalDAGData.nodes 9 ⟨695201, by decide⟩ =
    .split (coordinate 12) (![⟨695155, by decide⟩,⟨695176, by decide⟩,⟨695194, by decide⟩,⟨695200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91665_695201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91665 ⟨695201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91665
    ⟨695201, by decide⟩ (by decide) (![⟨695155, by decide⟩,⟨695176, by decide⟩,⟨695194, by decide⟩,⟨695200, by decide⟩]) unmarked_context_12_91665_695201 node_context_12_91665_695201
  intro a
  fin_cases a
  · exact context_13_366660_695155
  · exact context_13_366661_695176
  · exact context_13_366662_695194
  · exact context_13_366663_695200

theorem selected_cut_27493 : selected 8 ⟨695225, by decide⟩
    (prefixPartial 13 366664) = some ⟨13, 2, 0, 695225, 366664, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_366664_695225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366664 ⟨695225, by decide⟩ :=
  accepted_of_selected 13 366664 ⟨695225, by decide⟩ ⟨13, 2, 0, 695225, 366664, 1525, 16384⟩
    (by decide) selected_cut_27493

theorem selected_cut_27494 : selected 8 ⟨695242, by decide⟩
    (prefixPartial 13 366665) = some ⟨13, 2, 0, 695242, 366665, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_366665_695242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366665 ⟨695242, by decide⟩ :=
  accepted_of_selected 13 366665 ⟨695242, by decide⟩ ⟨13, 2, 0, 695242, 366665, 1133, 16384⟩
    (by decide) selected_cut_27494

theorem selected_cut_27495 : selected 8 ⟨695259, by decide⟩
    (prefixPartial 13 366666) = some ⟨13, 2, 0, 695259, 366666, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_366666_695259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366666 ⟨695259, by decide⟩ :=
  accepted_of_selected 13 366666 ⟨695259, by decide⟩ ⟨13, 2, 0, 695259, 366666, 1061, 16384⟩
    (by decide) selected_cut_27495

theorem selected_cut_27496 : selected 8 ⟨695264, by decide⟩
    (prefixPartial 13 366667) = some ⟨13, 2, 0, 695264, 366667, 789, 16384⟩ := by
  decide +kernel

theorem context_13_366667_695264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366667 ⟨695264, by decide⟩ :=
  accepted_of_selected 13 366667 ⟨695264, by decide⟩ ⟨13, 2, 0, 695264, 366667, 789, 16384⟩
    (by decide) selected_cut_27496

theorem unmarked_context_12_91666_695265 : frontier 9 ⟨695265, by decide⟩
    (prefixCache 12 91666) (prefixPartial 12 91666) = false := by
  decide +kernel

theorem node_context_12_91666_695265 : EJMOriginalGlobalDAGData.nodes 9 ⟨695265, by decide⟩ =
    .split (coordinate 12) (![⟨695225, by decide⟩,⟨695242, by decide⟩,⟨695259, by decide⟩,⟨695264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91666_695265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91666 ⟨695265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91666
    ⟨695265, by decide⟩ (by decide) (![⟨695225, by decide⟩,⟨695242, by decide⟩,⟨695259, by decide⟩,⟨695264, by decide⟩]) unmarked_context_12_91666_695265 node_context_12_91666_695265
  intro a
  fin_cases a
  · exact context_13_366664_695225
  · exact context_13_366665_695242
  · exact context_13_366666_695259
  · exact context_13_366667_695264

theorem selected_cut_27497 : selected 8 ⟨695297, by decide⟩
    (prefixPartial 13 366668) = some ⟨13, 2, 0, 695297, 366668, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_366668_695297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366668 ⟨695297, by decide⟩ :=
  accepted_of_selected 13 366668 ⟨695297, by decide⟩ ⟨13, 2, 0, 695297, 366668, 2045, 16384⟩
    (by decide) selected_cut_27497

theorem selected_cut_27498 : selected 8 ⟨695322, by decide⟩
    (prefixPartial 13 366669) = some ⟨13, 2, 0, 695322, 366669, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_366669_695322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366669 ⟨695322, by decide⟩ :=
  accepted_of_selected 13 366669 ⟨695322, by decide⟩ ⟨13, 2, 0, 695322, 366669, 1841, 16384⟩
    (by decide) selected_cut_27498

theorem selected_cut_27499 : selected 8 ⟨695341, by decide⟩
    (prefixPartial 13 366670) = some ⟨13, 2, 0, 695341, 366670, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_366670_695341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366670 ⟨695341, by decide⟩ :=
  accepted_of_selected 13 366670 ⟨695341, by decide⟩ ⟨13, 2, 0, 695341, 366670, 1533, 16384⟩
    (by decide) selected_cut_27499

theorem selected_cut_27500 : selected 8 ⟨695347, by decide⟩
    (prefixPartial 13 366671) = some ⟨13, 2, 0, 695347, 366671, 869, 16384⟩ := by
  decide +kernel

theorem context_13_366671_695347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366671 ⟨695347, by decide⟩ :=
  accepted_of_selected 13 366671 ⟨695347, by decide⟩ ⟨13, 2, 0, 695347, 366671, 869, 16384⟩
    (by decide) selected_cut_27500

theorem unmarked_context_12_91667_695348 : frontier 9 ⟨695348, by decide⟩
    (prefixCache 12 91667) (prefixPartial 12 91667) = false := by
  decide +kernel

theorem node_context_12_91667_695348 : EJMOriginalGlobalDAGData.nodes 9 ⟨695348, by decide⟩ =
    .split (coordinate 12) (![⟨695297, by decide⟩,⟨695322, by decide⟩,⟨695341, by decide⟩,⟨695347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91667_695348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91667 ⟨695348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91667
    ⟨695348, by decide⟩ (by decide) (![⟨695297, by decide⟩,⟨695322, by decide⟩,⟨695341, by decide⟩,⟨695347, by decide⟩]) unmarked_context_12_91667_695348 node_context_12_91667_695348
  intro a
  fin_cases a
  · exact context_13_366668_695297
  · exact context_13_366669_695322
  · exact context_13_366670_695341
  · exact context_13_366671_695347

theorem unmarked_context_11_22916_695349 : frontier 10 ⟨695349, by decide⟩
    (prefixCache 11 22916) (prefixPartial 11 22916) = false := by
  decide +kernel

theorem node_context_11_22916_695349 : EJMOriginalGlobalDAGData.nodes 10 ⟨695349, by decide⟩ =
    .split (coordinate 11) (![⟨695116, by decide⟩,⟨695201, by decide⟩,⟨695265, by decide⟩,⟨695348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22916_695349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22916 ⟨695349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22916
    ⟨695349, by decide⟩ (by decide) (![⟨695116, by decide⟩,⟨695201, by decide⟩,⟨695265, by decide⟩,⟨695348, by decide⟩]) unmarked_context_11_22916_695349 node_context_11_22916_695349
  intro a
  fin_cases a
  · exact context_12_91664_695116
  · exact context_12_91665_695201
  · exact context_12_91666_695265
  · exact context_12_91667_695348

theorem selected_cut_27501 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 91668) = some ⟨12, 1, 0, 308705, 91668, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91668_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91668 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 91668 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 91668, 1, 65536⟩
    (by decide) selected_cut_27501

theorem selected_cut_27502 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 91669) = some ⟨12, 1, 0, 308705, 91669, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91669_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91669 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 91669 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 91669, 1, 65536⟩
    (by decide) selected_cut_27502

theorem selected_cut_27503 : selected 8 ⟨695383, by decide⟩
    (prefixPartial 13 366680) = some ⟨13, 2, 0, 695383, 366680, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_366680_695383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366680 ⟨695383, by decide⟩ :=
  accepted_of_selected 13 366680 ⟨695383, by decide⟩ ⟨13, 2, 0, 695383, 366680, 2377, 16384⟩
    (by decide) selected_cut_27503

theorem selected_cut_27504 : selected 8 ⟨695419, by decide⟩
    (prefixPartial 13 366681) = some ⟨13, 2, 0, 695419, 366681, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_366681_695419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366681 ⟨695419, by decide⟩ :=
  accepted_of_selected 13 366681 ⟨695419, by decide⟩ ⟨13, 2, 0, 695419, 366681, 2149, 16384⟩
    (by decide) selected_cut_27504

theorem selected_cut_27505 : selected 8 ⟨695437, by decide⟩
    (prefixPartial 13 366682) = some ⟨13, 2, 0, 695437, 366682, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_366682_695437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366682 ⟨695437, by decide⟩ :=
  accepted_of_selected 13 366682 ⟨695437, by decide⟩ ⟨13, 2, 0, 695437, 366682, 1533, 16384⟩
    (by decide) selected_cut_27505

theorem selected_cut_27506 : selected 8 ⟨695447, by decide⟩
    (prefixPartial 13 366683) = some ⟨13, 2, 0, 695447, 366683, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_366683_695447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366683 ⟨695447, by decide⟩ :=
  accepted_of_selected 13 366683 ⟨695447, by decide⟩ ⟨13, 2, 0, 695447, 366683, 1177, 16384⟩
    (by decide) selected_cut_27506

theorem unmarked_context_12_91670_695448 : frontier 9 ⟨695448, by decide⟩
    (prefixCache 12 91670) (prefixPartial 12 91670) = false := by
  decide +kernel

theorem node_context_12_91670_695448 : EJMOriginalGlobalDAGData.nodes 9 ⟨695448, by decide⟩ =
    .split (coordinate 12) (![⟨695383, by decide⟩,⟨695419, by decide⟩,⟨695437, by decide⟩,⟨695447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91670_695448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91670 ⟨695448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91670
    ⟨695448, by decide⟩ (by decide) (![⟨695383, by decide⟩,⟨695419, by decide⟩,⟨695437, by decide⟩,⟨695447, by decide⟩]) unmarked_context_12_91670_695448 node_context_12_91670_695448
  intro a
  fin_cases a
  · exact context_13_366680_695383
  · exact context_13_366681_695419
  · exact context_13_366682_695437
  · exact context_13_366683_695447

theorem selected_cut_27507 : selected 8 ⟨695499, by decide⟩
    (prefixPartial 13 366684) = some ⟨13, 2, 0, 695499, 366684, 3057, 16384⟩ := by
  decide +kernel

theorem context_13_366684_695499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366684 ⟨695499, by decide⟩ :=
  accepted_of_selected 13 366684 ⟨695499, by decide⟩ ⟨13, 2, 0, 695499, 366684, 3057, 16384⟩
    (by decide) selected_cut_27507

theorem selected_cut_27508 : selected 8 ⟨695555, by decide⟩
    (prefixPartial 13 366685) = some ⟨13, 2, 0, 695555, 366685, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_366685_695555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366685 ⟨695555, by decide⟩ :=
  accepted_of_selected 13 366685 ⟨695555, by decide⟩ ⟨13, 2, 0, 695555, 366685, 3009, 16384⟩
    (by decide) selected_cut_27508

theorem selected_cut_27509 : selected 8 ⟨695582, by decide⟩
    (prefixPartial 13 366686) = some ⟨13, 2, 0, 695582, 366686, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_366686_695582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366686 ⟨695582, by decide⟩ :=
  accepted_of_selected 13 366686 ⟨695582, by decide⟩ ⟨13, 2, 0, 695582, 366686, 2101, 16384⟩
    (by decide) selected_cut_27509

theorem selected_cut_27510 : selected 8 ⟨695594, by decide⟩
    (prefixPartial 13 366687) = some ⟨13, 2, 0, 695594, 366687, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_366687_695594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366687 ⟨695594, by decide⟩ :=
  accepted_of_selected 13 366687 ⟨695594, by decide⟩ ⟨13, 2, 0, 695594, 366687, 1209, 16384⟩
    (by decide) selected_cut_27510

theorem unmarked_context_12_91671_695595 : frontier 9 ⟨695595, by decide⟩
    (prefixCache 12 91671) (prefixPartial 12 91671) = false := by
  decide +kernel

theorem node_context_12_91671_695595 : EJMOriginalGlobalDAGData.nodes 9 ⟨695595, by decide⟩ =
    .split (coordinate 12) (![⟨695499, by decide⟩,⟨695555, by decide⟩,⟨695582, by decide⟩,⟨695594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91671_695595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91671 ⟨695595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91671
    ⟨695595, by decide⟩ (by decide) (![⟨695499, by decide⟩,⟨695555, by decide⟩,⟨695582, by decide⟩,⟨695594, by decide⟩]) unmarked_context_12_91671_695595 node_context_12_91671_695595
  intro a
  fin_cases a
  · exact context_13_366684_695499
  · exact context_13_366685_695555
  · exact context_13_366686_695582
  · exact context_13_366687_695594

theorem unmarked_context_11_22917_695596 : frontier 10 ⟨695596, by decide⟩
    (prefixCache 11 22917) (prefixPartial 11 22917) = false := by
  decide +kernel

theorem node_context_11_22917_695596 : EJMOriginalGlobalDAGData.nodes 10 ⟨695596, by decide⟩ =
    .split (coordinate 11) (![⟨308705, by decide⟩,⟨308705, by decide⟩,⟨695448, by decide⟩,⟨695595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22917_695596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22917 ⟨695596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22917
    ⟨695596, by decide⟩ (by decide) (![⟨308705, by decide⟩,⟨308705, by decide⟩,⟨695448, by decide⟩,⟨695595, by decide⟩]) unmarked_context_11_22917_695596 node_context_11_22917_695596
  intro a
  fin_cases a
  · exact context_12_91668_308705
  · exact context_12_91669_308705
  · exact context_12_91670_695448
  · exact context_12_91671_695595

theorem selected_cut_27511 : selected 8 ⟨695615, by decide⟩
    (prefixPartial 13 366688) = some ⟨13, 2, 0, 695615, 366688, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_366688_695615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366688 ⟨695615, by decide⟩ :=
  accepted_of_selected 13 366688 ⟨695615, by decide⟩ ⟨13, 2, 0, 695615, 366688, 1385, 16384⟩
    (by decide) selected_cut_27511

theorem selected_cut_27512 : selected 8 ⟨695635, by decide⟩
    (prefixPartial 13 366689) = some ⟨13, 2, 0, 695635, 366689, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_366689_695635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366689 ⟨695635, by decide⟩ :=
  accepted_of_selected 13 366689 ⟨695635, by decide⟩ ⟨13, 2, 0, 695635, 366689, 1345, 16384⟩
    (by decide) selected_cut_27512

theorem selected_cut_27513 : selected 8 ⟨695649, by decide⟩
    (prefixPartial 13 366690) = some ⟨13, 2, 0, 695649, 366690, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_366690_695649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366690 ⟨695649, by decide⟩ :=
  accepted_of_selected 13 366690 ⟨695649, by decide⟩ ⟨13, 2, 0, 695649, 366690, 1217, 16384⟩
    (by decide) selected_cut_27513

theorem selected_cut_27514 : selected 8 ⟨695656, by decide⟩
    (prefixPartial 13 366691) = some ⟨13, 2, 0, 695656, 366691, 865, 16384⟩ := by
  decide +kernel

theorem context_13_366691_695656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366691 ⟨695656, by decide⟩ :=
  accepted_of_selected 13 366691 ⟨695656, by decide⟩ ⟨13, 2, 0, 695656, 366691, 865, 16384⟩
    (by decide) selected_cut_27514

theorem unmarked_context_12_91672_695657 : frontier 9 ⟨695657, by decide⟩
    (prefixCache 12 91672) (prefixPartial 12 91672) = false := by
  decide +kernel

theorem node_context_12_91672_695657 : EJMOriginalGlobalDAGData.nodes 9 ⟨695657, by decide⟩ =
    .split (coordinate 12) (![⟨695615, by decide⟩,⟨695635, by decide⟩,⟨695649, by decide⟩,⟨695656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91672_695657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91672 ⟨695657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91672
    ⟨695657, by decide⟩ (by decide) (![⟨695615, by decide⟩,⟨695635, by decide⟩,⟨695649, by decide⟩,⟨695656, by decide⟩]) unmarked_context_12_91672_695657 node_context_12_91672_695657
  intro a
  fin_cases a
  · exact context_13_366688_695615
  · exact context_13_366689_695635
  · exact context_13_366690_695649
  · exact context_13_366691_695656

theorem selected_cut_27515 : selected 8 ⟨695678, by decide⟩
    (prefixPartial 13 366692) = some ⟨13, 2, 0, 695678, 366692, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_366692_695678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366692 ⟨695678, by decide⟩ :=
  accepted_of_selected 13 366692 ⟨695678, by decide⟩ ⟨13, 2, 0, 695678, 366692, 1677, 16384⟩
    (by decide) selected_cut_27515

theorem selected_cut_27516 : selected 8 ⟨695709, by decide⟩
    (prefixPartial 13 366693) = some ⟨13, 2, 0, 695709, 366693, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_366693_695709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366693 ⟨695709, by decide⟩ :=
  accepted_of_selected 13 366693 ⟨695709, by decide⟩ ⟨13, 2, 0, 695709, 366693, 1509, 16384⟩
    (by decide) selected_cut_27516

theorem selected_cut_27517 : selected 8 ⟨695726, by decide⟩
    (prefixPartial 13 366694) = some ⟨13, 2, 0, 695726, 366694, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_366694_695726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366694 ⟨695726, by decide⟩ :=
  accepted_of_selected 13 366694 ⟨695726, by decide⟩ ⟨13, 2, 0, 695726, 366694, 1333, 16384⟩
    (by decide) selected_cut_27517

theorem selected_cut_27518 : selected 8 ⟨695731, by decide⟩
    (prefixPartial 13 366695) = some ⟨13, 2, 0, 695731, 366695, 885, 16384⟩ := by
  decide +kernel

theorem context_13_366695_695731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366695 ⟨695731, by decide⟩ :=
  accepted_of_selected 13 366695 ⟨695731, by decide⟩ ⟨13, 2, 0, 695731, 366695, 885, 16384⟩
    (by decide) selected_cut_27518

theorem unmarked_context_12_91673_695732 : frontier 9 ⟨695732, by decide⟩
    (prefixCache 12 91673) (prefixPartial 12 91673) = false := by
  decide +kernel

theorem node_context_12_91673_695732 : EJMOriginalGlobalDAGData.nodes 9 ⟨695732, by decide⟩ =
    .split (coordinate 12) (![⟨695678, by decide⟩,⟨695709, by decide⟩,⟨695726, by decide⟩,⟨695731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91673_695732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91673 ⟨695732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91673
    ⟨695732, by decide⟩ (by decide) (![⟨695678, by decide⟩,⟨695709, by decide⟩,⟨695726, by decide⟩,⟨695731, by decide⟩]) unmarked_context_12_91673_695732 node_context_12_91673_695732
  intro a
  fin_cases a
  · exact context_13_366692_695678
  · exact context_13_366693_695709
  · exact context_13_366694_695726
  · exact context_13_366695_695731

theorem selected_cut_27519 : selected 8 ⟨695767, by decide⟩
    (prefixPartial 13 366696) = some ⟨13, 2, 0, 695767, 366696, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_366696_695767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366696 ⟨695767, by decide⟩ :=
  accepted_of_selected 13 366696 ⟨695767, by decide⟩ ⟨13, 2, 0, 695767, 366696, 1837, 16384⟩
    (by decide) selected_cut_27519

theorem selected_cut_27520 : selected 8 ⟨695822, by decide⟩
    (prefixPartial 13 366697) = some ⟨13, 2, 0, 695822, 366697, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_366697_695822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366697 ⟨695822, by decide⟩ :=
  accepted_of_selected 13 366697 ⟨695822, by decide⟩ ⟨13, 2, 0, 695822, 366697, 1609, 16384⟩
    (by decide) selected_cut_27520

theorem selected_cut_27521 : selected 8 ⟨695841, by decide⟩
    (prefixPartial 13 366698) = some ⟨13, 2, 0, 695841, 366698, 977, 16384⟩ := by
  decide +kernel

theorem context_13_366698_695841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366698 ⟨695841, by decide⟩ :=
  accepted_of_selected 13 366698 ⟨695841, by decide⟩ ⟨13, 2, 0, 695841, 366698, 977, 16384⟩
    (by decide) selected_cut_27521

theorem selected_cut_27522 : selected 8 ⟨695852, by decide⟩
    (prefixPartial 13 366699) = some ⟨13, 2, 0, 695852, 366699, 261, 16384⟩ := by
  decide +kernel

theorem context_13_366699_695852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366699 ⟨695852, by decide⟩ :=
  accepted_of_selected 13 366699 ⟨695852, by decide⟩ ⟨13, 2, 0, 695852, 366699, 261, 16384⟩
    (by decide) selected_cut_27522

theorem unmarked_context_12_91674_695853 : frontier 9 ⟨695853, by decide⟩
    (prefixCache 12 91674) (prefixPartial 12 91674) = false := by
  decide +kernel

theorem node_context_12_91674_695853 : EJMOriginalGlobalDAGData.nodes 9 ⟨695853, by decide⟩ =
    .split (coordinate 12) (![⟨695767, by decide⟩,⟨695822, by decide⟩,⟨695841, by decide⟩,⟨695852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91674_695853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91674 ⟨695853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91674
    ⟨695853, by decide⟩ (by decide) (![⟨695767, by decide⟩,⟨695822, by decide⟩,⟨695841, by decide⟩,⟨695852, by decide⟩]) unmarked_context_12_91674_695853 node_context_12_91674_695853
  intro a
  fin_cases a
  · exact context_13_366696_695767
  · exact context_13_366697_695822
  · exact context_13_366698_695841
  · exact context_13_366699_695852

theorem selected_cut_27523 : selected 8 ⟨695877, by decide⟩
    (prefixPartial 13 366700) = some ⟨13, 2, 0, 695877, 366700, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_366700_695877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366700 ⟨695877, by decide⟩ :=
  accepted_of_selected 13 366700 ⟨695877, by decide⟩ ⟨13, 2, 0, 695877, 366700, 1409, 16384⟩
    (by decide) selected_cut_27523

theorem selected_cut_27524 : selected 8 ⟨695909, by decide⟩
    (prefixPartial 13 366701) = some ⟨13, 2, 0, 695909, 366701, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_366701_695909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366701 ⟨695909, by decide⟩ :=
  accepted_of_selected 13 366701 ⟨695909, by decide⟩ ⟨13, 2, 0, 695909, 366701, 1721, 16384⟩
    (by decide) selected_cut_27524

theorem selected_cut_27525 : selected 8 ⟨695927, by decide⟩
    (prefixPartial 13 366702) = some ⟨13, 2, 0, 695927, 366702, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_366702_695927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366702 ⟨695927, by decide⟩ :=
  accepted_of_selected 13 366702 ⟨695927, by decide⟩ ⟨13, 2, 0, 695927, 366702, 1457, 16384⟩
    (by decide) selected_cut_27525

theorem selected_cut_27526 : selected 8 ⟨695932, by decide⟩
    (prefixPartial 13 366703) = some ⟨13, 2, 0, 695932, 366703, 809, 16384⟩ := by
  decide +kernel

theorem context_13_366703_695932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366703 ⟨695932, by decide⟩ :=
  accepted_of_selected 13 366703 ⟨695932, by decide⟩ ⟨13, 2, 0, 695932, 366703, 809, 16384⟩
    (by decide) selected_cut_27526

theorem unmarked_context_12_91675_695933 : frontier 9 ⟨695933, by decide⟩
    (prefixCache 12 91675) (prefixPartial 12 91675) = false := by
  decide +kernel

theorem node_context_12_91675_695933 : EJMOriginalGlobalDAGData.nodes 9 ⟨695933, by decide⟩ =
    .split (coordinate 12) (![⟨695877, by decide⟩,⟨695909, by decide⟩,⟨695927, by decide⟩,⟨695932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91675_695933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91675 ⟨695933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91675
    ⟨695933, by decide⟩ (by decide) (![⟨695877, by decide⟩,⟨695909, by decide⟩,⟨695927, by decide⟩,⟨695932, by decide⟩]) unmarked_context_12_91675_695933 node_context_12_91675_695933
  intro a
  fin_cases a
  · exact context_13_366700_695877
  · exact context_13_366701_695909
  · exact context_13_366702_695927
  · exact context_13_366703_695932

theorem unmarked_context_11_22918_695934 : frontier 10 ⟨695934, by decide⟩
    (prefixCache 11 22918) (prefixPartial 11 22918) = false := by
  decide +kernel

theorem node_context_11_22918_695934 : EJMOriginalGlobalDAGData.nodes 10 ⟨695934, by decide⟩ =
    .split (coordinate 11) (![⟨695657, by decide⟩,⟨695732, by decide⟩,⟨695853, by decide⟩,⟨695933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22918_695934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22918 ⟨695934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22918
    ⟨695934, by decide⟩ (by decide) (![⟨695657, by decide⟩,⟨695732, by decide⟩,⟨695853, by decide⟩,⟨695933, by decide⟩]) unmarked_context_11_22918_695934 node_context_11_22918_695934
  intro a
  fin_cases a
  · exact context_12_91672_695657
  · exact context_12_91673_695732
  · exact context_12_91674_695853
  · exact context_12_91675_695933

theorem selected_cut_27527 : selected 8 ⟨695952, by decide⟩
    (prefixPartial 13 366704) = some ⟨13, 2, 0, 695952, 366704, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_366704_695952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366704 ⟨695952, by decide⟩ :=
  accepted_of_selected 13 366704 ⟨695952, by decide⟩ ⟨13, 2, 0, 695952, 366704, 1353, 16384⟩
    (by decide) selected_cut_27527

theorem selected_cut_27528 : selected 8 ⟨695974, by decide⟩
    (prefixPartial 13 366705) = some ⟨13, 2, 0, 695974, 366705, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_366705_695974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366705 ⟨695974, by decide⟩ :=
  accepted_of_selected 13 366705 ⟨695974, by decide⟩ ⟨13, 2, 0, 695974, 366705, 1513, 16384⟩
    (by decide) selected_cut_27528

theorem selected_cut_27529 : selected 8 ⟨695994, by decide⟩
    (prefixPartial 13 366706) = some ⟨13, 2, 0, 695994, 366706, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_366706_695994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366706 ⟨695994, by decide⟩ :=
  accepted_of_selected 13 366706 ⟨695994, by decide⟩ ⟨13, 2, 0, 695994, 366706, 1161, 16384⟩
    (by decide) selected_cut_27529

theorem selected_cut_27530 : selected 8 ⟨696002, by decide⟩
    (prefixPartial 13 366707) = some ⟨13, 2, 0, 696002, 366707, 841, 16384⟩ := by
  decide +kernel

theorem context_13_366707_696002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366707 ⟨696002, by decide⟩ :=
  accepted_of_selected 13 366707 ⟨696002, by decide⟩ ⟨13, 2, 0, 696002, 366707, 841, 16384⟩
    (by decide) selected_cut_27530

theorem unmarked_context_12_91676_696003 : frontier 9 ⟨696003, by decide⟩
    (prefixCache 12 91676) (prefixPartial 12 91676) = false := by
  decide +kernel

theorem node_context_12_91676_696003 : EJMOriginalGlobalDAGData.nodes 9 ⟨696003, by decide⟩ =
    .split (coordinate 12) (![⟨695952, by decide⟩,⟨695974, by decide⟩,⟨695994, by decide⟩,⟨696002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91676_696003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91676 ⟨696003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91676
    ⟨696003, by decide⟩ (by decide) (![⟨695952, by decide⟩,⟨695974, by decide⟩,⟨695994, by decide⟩,⟨696002, by decide⟩]) unmarked_context_12_91676_696003 node_context_12_91676_696003
  intro a
  fin_cases a
  · exact context_13_366704_695952
  · exact context_13_366705_695974
  · exact context_13_366706_695994
  · exact context_13_366707_696002

theorem selected_cut_27531 : selected 8 ⟨696018, by decide⟩
    (prefixPartial 13 366708) = some ⟨13, 2, 0, 696018, 366708, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_366708_696018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366708 ⟨696018, by decide⟩ :=
  accepted_of_selected 13 366708 ⟨696018, by decide⟩ ⟨13, 2, 0, 696018, 366708, 1541, 16384⟩
    (by decide) selected_cut_27531

theorem selected_cut_27532 : selected 8 ⟨696049, by decide⟩
    (prefixPartial 13 366709) = some ⟨13, 2, 0, 696049, 366709, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_366709_696049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366709 ⟨696049, by decide⟩ :=
  accepted_of_selected 13 366709 ⟨696049, by decide⟩ ⟨13, 2, 0, 696049, 366709, 1737, 16384⟩
    (by decide) selected_cut_27532

theorem selected_cut_27533 : selected 8 ⟨696066, by decide⟩
    (prefixPartial 13 366710) = some ⟨13, 2, 0, 696066, 366710, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_366710_696066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366710 ⟨696066, by decide⟩ :=
  accepted_of_selected 13 366710 ⟨696066, by decide⟩ ⟨13, 2, 0, 696066, 366710, 1229, 16384⟩
    (by decide) selected_cut_27533

theorem selected_cut_27534 : selected 8 ⟨696070, by decide⟩
    (prefixPartial 13 366711) = some ⟨13, 2, 0, 696070, 366711, 801, 16384⟩ := by
  decide +kernel

theorem context_13_366711_696070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366711 ⟨696070, by decide⟩ :=
  accepted_of_selected 13 366711 ⟨696070, by decide⟩ ⟨13, 2, 0, 696070, 366711, 801, 16384⟩
    (by decide) selected_cut_27534

theorem unmarked_context_12_91677_696071 : frontier 9 ⟨696071, by decide⟩
    (prefixCache 12 91677) (prefixPartial 12 91677) = false := by
  decide +kernel

theorem node_context_12_91677_696071 : EJMOriginalGlobalDAGData.nodes 9 ⟨696071, by decide⟩ =
    .split (coordinate 12) (![⟨696018, by decide⟩,⟨696049, by decide⟩,⟨696066, by decide⟩,⟨696070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91677_696071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91677 ⟨696071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91677
    ⟨696071, by decide⟩ (by decide) (![⟨696018, by decide⟩,⟨696049, by decide⟩,⟨696066, by decide⟩,⟨696070, by decide⟩]) unmarked_context_12_91677_696071 node_context_12_91677_696071
  intro a
  fin_cases a
  · exact context_13_366708_696018
  · exact context_13_366709_696049
  · exact context_13_366710_696066
  · exact context_13_366711_696070

theorem selected_cut_27535 : selected 8 ⟨696087, by decide⟩
    (prefixPartial 13 366712) = some ⟨13, 2, 0, 696087, 366712, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_366712_696087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366712 ⟨696087, by decide⟩ :=
  accepted_of_selected 13 366712 ⟨696087, by decide⟩ ⟨13, 2, 0, 696087, 366712, 1101, 16384⟩
    (by decide) selected_cut_27535

theorem selected_cut_27536 : selected 8 ⟨696108, by decide⟩
    (prefixPartial 13 366713) = some ⟨13, 2, 0, 696108, 366713, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_366713_696108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366713 ⟨696108, by decide⟩ :=
  accepted_of_selected 13 366713 ⟨696108, by decide⟩ ⟨13, 2, 0, 696108, 366713, 1353, 16384⟩
    (by decide) selected_cut_27536

theorem selected_cut_27537 : selected 8 ⟨696121, by decide⟩
    (prefixPartial 13 366714) = some ⟨13, 2, 0, 696121, 366714, 997, 16384⟩ := by
  decide +kernel

theorem context_13_366714_696121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366714 ⟨696121, by decide⟩ :=
  accepted_of_selected 13 366714 ⟨696121, by decide⟩ ⟨13, 2, 0, 696121, 366714, 997, 16384⟩
    (by decide) selected_cut_27537

theorem selected_cut_27538 : selected 8 ⟨696129, by decide⟩
    (prefixPartial 13 366715) = some ⟨13, 2, 0, 696129, 366715, 825, 16384⟩ := by
  decide +kernel

theorem context_13_366715_696129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366715 ⟨696129, by decide⟩ :=
  accepted_of_selected 13 366715 ⟨696129, by decide⟩ ⟨13, 2, 0, 696129, 366715, 825, 16384⟩
    (by decide) selected_cut_27538

theorem unmarked_context_12_91678_696130 : frontier 9 ⟨696130, by decide⟩
    (prefixCache 12 91678) (prefixPartial 12 91678) = false := by
  decide +kernel

theorem node_context_12_91678_696130 : EJMOriginalGlobalDAGData.nodes 9 ⟨696130, by decide⟩ =
    .split (coordinate 12) (![⟨696087, by decide⟩,⟨696108, by decide⟩,⟨696121, by decide⟩,⟨696129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91678_696130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91678 ⟨696130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91678
    ⟨696130, by decide⟩ (by decide) (![⟨696087, by decide⟩,⟨696108, by decide⟩,⟨696121, by decide⟩,⟨696129, by decide⟩]) unmarked_context_12_91678_696130 node_context_12_91678_696130
  intro a
  fin_cases a
  · exact context_13_366712_696087
  · exact context_13_366713_696108
  · exact context_13_366714_696121
  · exact context_13_366715_696129

theorem selected_cut_27539 : selected 8 ⟨696153, by decide⟩
    (prefixPartial 13 366716) = some ⟨13, 2, 0, 696153, 366716, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_366716_696153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366716 ⟨696153, by decide⟩ :=
  accepted_of_selected 13 366716 ⟨696153, by decide⟩ ⟨13, 2, 0, 696153, 366716, 1385, 16384⟩
    (by decide) selected_cut_27539

theorem selected_cut_27540 : selected 8 ⟨696179, by decide⟩
    (prefixPartial 13 366717) = some ⟨13, 2, 0, 696179, 366717, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_366717_696179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366717 ⟨696179, by decide⟩ :=
  accepted_of_selected 13 366717 ⟨696179, by decide⟩ ⟨13, 2, 0, 696179, 366717, 1885, 16384⟩
    (by decide) selected_cut_27540

theorem selected_cut_27541 : selected 8 ⟨696201, by decide⟩
    (prefixPartial 13 366718) = some ⟨13, 2, 0, 696201, 366718, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_366718_696201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366718 ⟨696201, by decide⟩ :=
  accepted_of_selected 13 366718 ⟨696201, by decide⟩ ⟨13, 2, 0, 696201, 366718, 1473, 16384⟩
    (by decide) selected_cut_27541

theorem selected_cut_27542 : selected 8 ⟨696206, by decide⟩
    (prefixPartial 13 366719) = some ⟨13, 2, 0, 696206, 366719, 881, 16384⟩ := by
  decide +kernel

theorem context_13_366719_696206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366719 ⟨696206, by decide⟩ :=
  accepted_of_selected 13 366719 ⟨696206, by decide⟩ ⟨13, 2, 0, 696206, 366719, 881, 16384⟩
    (by decide) selected_cut_27542

theorem unmarked_context_12_91679_696207 : frontier 9 ⟨696207, by decide⟩
    (prefixCache 12 91679) (prefixPartial 12 91679) = false := by
  decide +kernel

theorem node_context_12_91679_696207 : EJMOriginalGlobalDAGData.nodes 9 ⟨696207, by decide⟩ =
    .split (coordinate 12) (![⟨696153, by decide⟩,⟨696179, by decide⟩,⟨696201, by decide⟩,⟨696206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91679_696207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91679 ⟨696207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91679
    ⟨696207, by decide⟩ (by decide) (![⟨696153, by decide⟩,⟨696179, by decide⟩,⟨696201, by decide⟩,⟨696206, by decide⟩]) unmarked_context_12_91679_696207 node_context_12_91679_696207
  intro a
  fin_cases a
  · exact context_13_366716_696153
  · exact context_13_366717_696179
  · exact context_13_366718_696201
  · exact context_13_366719_696206

theorem unmarked_context_11_22919_696208 : frontier 10 ⟨696208, by decide⟩
    (prefixCache 11 22919) (prefixPartial 11 22919) = false := by
  decide +kernel

theorem node_context_11_22919_696208 : EJMOriginalGlobalDAGData.nodes 10 ⟨696208, by decide⟩ =
    .split (coordinate 11) (![⟨696003, by decide⟩,⟨696071, by decide⟩,⟨696130, by decide⟩,⟨696207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22919_696208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22919 ⟨696208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22919
    ⟨696208, by decide⟩ (by decide) (![⟨696003, by decide⟩,⟨696071, by decide⟩,⟨696130, by decide⟩,⟨696207, by decide⟩]) unmarked_context_11_22919_696208 node_context_11_22919_696208
  intro a
  fin_cases a
  · exact context_12_91676_696003
  · exact context_12_91677_696071
  · exact context_12_91678_696130
  · exact context_12_91679_696207

theorem unmarked_context_10_5729_696209 : frontier 11 ⟨696209, by decide⟩
    (prefixCache 10 5729) (prefixPartial 10 5729) = false := by
  decide +kernel

theorem node_context_10_5729_696209 : EJMOriginalGlobalDAGData.nodes 11 ⟨696209, by decide⟩ =
    .split (coordinate 10) (![⟨695349, by decide⟩,⟨695596, by decide⟩,⟨695934, by decide⟩,⟨696208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5729_696209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5729 ⟨696209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5729
    ⟨696209, by decide⟩ (by decide) (![⟨695349, by decide⟩,⟨695596, by decide⟩,⟨695934, by decide⟩,⟨696208, by decide⟩]) unmarked_context_10_5729_696209 node_context_10_5729_696209
  intro a
  fin_cases a
  · exact context_11_22916_695349
  · exact context_11_22917_695596
  · exact context_11_22918_695934
  · exact context_11_22919_696208

theorem selected_cut_27543 : selected 8 ⟨696225, by decide⟩
    (prefixPartial 13 366720) = some ⟨13, 2, 0, 696225, 366720, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_366720_696225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366720 ⟨696225, by decide⟩ :=
  accepted_of_selected 13 366720 ⟨696225, by decide⟩ ⟨13, 2, 0, 696225, 366720, 1025, 16384⟩
    (by decide) selected_cut_27543

theorem selected_cut_27544 : selected 8 ⟨696243, by decide⟩
    (prefixPartial 13 366721) = some ⟨13, 2, 0, 696243, 366721, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_366721_696243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366721 ⟨696243, by decide⟩ :=
  accepted_of_selected 13 366721 ⟨696243, by decide⟩ ⟨13, 2, 0, 696243, 366721, 1317, 16384⟩
    (by decide) selected_cut_27544

theorem selected_cut_27545 : selected 8 ⟨696259, by decide⟩
    (prefixPartial 13 366722) = some ⟨13, 2, 0, 696259, 366722, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_366722_696259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366722 ⟨696259, by decide⟩ :=
  accepted_of_selected 13 366722 ⟨696259, by decide⟩ ⟨13, 2, 0, 696259, 366722, 1197, 16384⟩
    (by decide) selected_cut_27545

theorem selected_cut_27546 : selected 8 ⟨696263, by decide⟩
    (prefixPartial 13 366723) = some ⟨13, 2, 0, 696263, 366723, 705, 16384⟩ := by
  decide +kernel

theorem context_13_366723_696263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366723 ⟨696263, by decide⟩ :=
  accepted_of_selected 13 366723 ⟨696263, by decide⟩ ⟨13, 2, 0, 696263, 366723, 705, 16384⟩
    (by decide) selected_cut_27546

theorem unmarked_context_12_91680_696264 : frontier 9 ⟨696264, by decide⟩
    (prefixCache 12 91680) (prefixPartial 12 91680) = false := by
  decide +kernel

theorem node_context_12_91680_696264 : EJMOriginalGlobalDAGData.nodes 9 ⟨696264, by decide⟩ =
    .split (coordinate 12) (![⟨696225, by decide⟩,⟨696243, by decide⟩,⟨696259, by decide⟩,⟨696263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91680_696264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91680 ⟨696264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91680
    ⟨696264, by decide⟩ (by decide) (![⟨696225, by decide⟩,⟨696243, by decide⟩,⟨696259, by decide⟩,⟨696263, by decide⟩]) unmarked_context_12_91680_696264 node_context_12_91680_696264
  intro a
  fin_cases a
  · exact context_13_366720_696225
  · exact context_13_366721_696243
  · exact context_13_366722_696259
  · exact context_13_366723_696263

theorem selected_cut_27547 : selected 8 ⟨696280, by decide⟩
    (prefixPartial 13 366724) = some ⟨13, 2, 0, 696280, 366724, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_366724_696280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366724 ⟨696280, by decide⟩ :=
  accepted_of_selected 13 366724 ⟨696280, by decide⟩ ⟨13, 2, 0, 696280, 366724, 1193, 16384⟩
    (by decide) selected_cut_27547

theorem selected_cut_27548 : selected 8 ⟨696306, by decide⟩
    (prefixPartial 13 366725) = some ⟨13, 2, 0, 696306, 366725, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_366725_696306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366725 ⟨696306, by decide⟩ :=
  accepted_of_selected 13 366725 ⟨696306, by decide⟩ ⟨13, 2, 0, 696306, 366725, 1765, 16384⟩
    (by decide) selected_cut_27548

theorem selected_cut_27549 : selected 8 ⟨696323, by decide⟩
    (prefixPartial 13 366726) = some ⟨13, 2, 0, 696323, 366726, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_366726_696323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366726 ⟨696323, by decide⟩ :=
  accepted_of_selected 13 366726 ⟨696323, by decide⟩ ⟨13, 2, 0, 696323, 366726, 1353, 16384⟩
    (by decide) selected_cut_27549

theorem selected_cut_27550 : selected 8 ⟨696327, by decide⟩
    (prefixPartial 13 366727) = some ⟨13, 2, 0, 696327, 366727, 769, 16384⟩ := by
  decide +kernel

theorem context_13_366727_696327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366727 ⟨696327, by decide⟩ :=
  accepted_of_selected 13 366727 ⟨696327, by decide⟩ ⟨13, 2, 0, 696327, 366727, 769, 16384⟩
    (by decide) selected_cut_27550

theorem unmarked_context_12_91681_696328 : frontier 9 ⟨696328, by decide⟩
    (prefixCache 12 91681) (prefixPartial 12 91681) = false := by
  decide +kernel

theorem node_context_12_91681_696328 : EJMOriginalGlobalDAGData.nodes 9 ⟨696328, by decide⟩ =
    .split (coordinate 12) (![⟨696280, by decide⟩,⟨696306, by decide⟩,⟨696323, by decide⟩,⟨696327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91681_696328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91681 ⟨696328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91681
    ⟨696328, by decide⟩ (by decide) (![⟨696280, by decide⟩,⟨696306, by decide⟩,⟨696323, by decide⟩,⟨696327, by decide⟩]) unmarked_context_12_91681_696328 node_context_12_91681_696328
  intro a
  fin_cases a
  · exact context_13_366724_696280
  · exact context_13_366725_696306
  · exact context_13_366726_696323
  · exact context_13_366727_696327

theorem selected_cut_27551 : selected 9 ⟨696378, by decide⟩
    (prefixPartial 12 91682) = some ⟨12, 2, 0, 696378, 91682, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_91682_696378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91682 ⟨696378, by decide⟩ :=
  accepted_of_selected 12 91682 ⟨696378, by decide⟩ ⟨12, 2, 0, 696378, 91682, 3933, 65536⟩
    (by decide) selected_cut_27551

theorem selected_cut_27552 : selected 8 ⟨696395, by decide⟩
    (prefixPartial 13 366732) = some ⟨13, 2, 0, 696395, 366732, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_366732_696395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366732 ⟨696395, by decide⟩ :=
  accepted_of_selected 13 366732 ⟨696395, by decide⟩ ⟨13, 2, 0, 696395, 366732, 1121, 16384⟩
    (by decide) selected_cut_27552

theorem selected_cut_27553 : selected 8 ⟨696421, by decide⟩
    (prefixPartial 13 366733) = some ⟨13, 2, 0, 696421, 366733, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_366733_696421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366733 ⟨696421, by decide⟩ :=
  accepted_of_selected 13 366733 ⟨696421, by decide⟩ ⟨13, 2, 0, 696421, 366733, 1949, 16384⟩
    (by decide) selected_cut_27553

theorem selected_cut_27554 : selected 8 ⟨696443, by decide⟩
    (prefixPartial 13 366734) = some ⟨13, 2, 0, 696443, 366734, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_366734_696443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366734 ⟨696443, by decide⟩ :=
  accepted_of_selected 13 366734 ⟨696443, by decide⟩ ⟨13, 2, 0, 696443, 366734, 1409, 16384⟩
    (by decide) selected_cut_27554

theorem selected_cut_27555 : selected 8 ⟨696448, by decide⟩
    (prefixPartial 13 366735) = some ⟨13, 2, 0, 696448, 366735, 717, 16384⟩ := by
  decide +kernel

theorem context_13_366735_696448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366735 ⟨696448, by decide⟩ :=
  accepted_of_selected 13 366735 ⟨696448, by decide⟩ ⟨13, 2, 0, 696448, 366735, 717, 16384⟩
    (by decide) selected_cut_27555

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
