/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover349
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33604 : selected 8 ⟨865397, by decide⟩
    (prefixPartial 13 441520) = some ⟨13, 2, 0, 865397, 441520, 721, 16384⟩ := by
  decide +kernel

theorem context_13_441520_865397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441520 ⟨865397, by decide⟩ :=
  accepted_of_selected 13 441520 ⟨865397, by decide⟩ ⟨13, 2, 0, 865397, 441520, 721, 16384⟩
    (by decide) selected_cut_33604

theorem selected_cut_33605 : selected 8 ⟨865432, by decide⟩
    (prefixPartial 13 441521) = some ⟨13, 2, 0, 865432, 441521, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_441521_865432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441521 ⟨865432, by decide⟩ :=
  accepted_of_selected 13 441521 ⟨865432, by decide⟩ ⟨13, 2, 0, 865432, 441521, 2861, 16384⟩
    (by decide) selected_cut_33605

theorem selected_cut_33606 : selected 8 ⟨865453, by decide⟩
    (prefixPartial 13 441522) = some ⟨13, 2, 0, 865453, 441522, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_441522_865453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441522 ⟨865453, by decide⟩ :=
  accepted_of_selected 13 441522 ⟨865453, by decide⟩ ⟨13, 2, 0, 865453, 441522, 1353, 16384⟩
    (by decide) selected_cut_33606

theorem selected_cut_33607 : selected 8 ⟨865457, by decide⟩
    (prefixPartial 13 441523) = some ⟨13, 2, 0, 865457, 441523, 745, 16384⟩ := by
  decide +kernel

theorem context_13_441523_865457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441523 ⟨865457, by decide⟩ :=
  accepted_of_selected 13 441523 ⟨865457, by decide⟩ ⟨13, 2, 0, 865457, 441523, 745, 16384⟩
    (by decide) selected_cut_33607

theorem unmarked_context_12_110380_865458 : frontier 9 ⟨865458, by decide⟩
    (prefixCache 12 110380) (prefixPartial 12 110380) = false := by
  decide +kernel

theorem node_context_12_110380_865458 : EJMOriginalGlobalDAGData.nodes 9 ⟨865458, by decide⟩ =
    .split (coordinate 12) (![⟨865397, by decide⟩,⟨865432, by decide⟩,⟨865453, by decide⟩,⟨865457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110380_865458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110380 ⟨865458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110380
    ⟨865458, by decide⟩ (by decide) (![⟨865397, by decide⟩,⟨865432, by decide⟩,⟨865453, by decide⟩,⟨865457, by decide⟩]) unmarked_context_12_110380_865458 node_context_12_110380_865458
  intro a
  fin_cases a
  · exact context_13_441520_865397
  · exact context_13_441521_865432
  · exact context_13_441522_865453
  · exact context_13_441523_865457

theorem selected_cut_33608 : selected 8 ⟨865471, by decide⟩
    (prefixPartial 13 441524) = some ⟨13, 2, 0, 865471, 441524, 849, 16384⟩ := by
  decide +kernel

theorem context_13_441524_865471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441524 ⟨865471, by decide⟩ :=
  accepted_of_selected 13 441524 ⟨865471, by decide⟩ ⟨13, 2, 0, 865471, 441524, 849, 16384⟩
    (by decide) selected_cut_33608

theorem selected_cut_33609 : selected 8 ⟨865504, by decide⟩
    (prefixPartial 13 441525) = some ⟨13, 2, 0, 865504, 441525, 2989, 16384⟩ := by
  decide +kernel

theorem context_13_441525_865504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441525 ⟨865504, by decide⟩ :=
  accepted_of_selected 13 441525 ⟨865504, by decide⟩ ⟨13, 2, 0, 865504, 441525, 2989, 16384⟩
    (by decide) selected_cut_33609

theorem selected_cut_33610 : selected 8 ⟨865535, by decide⟩
    (prefixPartial 13 441526) = some ⟨13, 2, 0, 865535, 441526, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_441526_865535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441526 ⟨865535, by decide⟩ :=
  accepted_of_selected 13 441526 ⟨865535, by decide⟩ ⟨13, 2, 0, 865535, 441526, 1721, 16384⟩
    (by decide) selected_cut_33610

theorem selected_cut_33611 : selected 8 ⟨865540, by decide⟩
    (prefixPartial 13 441527) = some ⟨13, 2, 0, 865540, 441527, 613, 16384⟩ := by
  decide +kernel

theorem context_13_441527_865540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441527 ⟨865540, by decide⟩ :=
  accepted_of_selected 13 441527 ⟨865540, by decide⟩ ⟨13, 2, 0, 865540, 441527, 613, 16384⟩
    (by decide) selected_cut_33611

theorem unmarked_context_12_110381_865541 : frontier 9 ⟨865541, by decide⟩
    (prefixCache 12 110381) (prefixPartial 12 110381) = false := by
  decide +kernel

theorem node_context_12_110381_865541 : EJMOriginalGlobalDAGData.nodes 9 ⟨865541, by decide⟩ =
    .split (coordinate 12) (![⟨865471, by decide⟩,⟨865504, by decide⟩,⟨865535, by decide⟩,⟨865540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110381_865541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110381 ⟨865541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110381
    ⟨865541, by decide⟩ (by decide) (![⟨865471, by decide⟩,⟨865504, by decide⟩,⟨865535, by decide⟩,⟨865540, by decide⟩]) unmarked_context_12_110381_865541 node_context_12_110381_865541
  intro a
  fin_cases a
  · exact context_13_441524_865471
  · exact context_13_441525_865504
  · exact context_13_441526_865535
  · exact context_13_441527_865540

theorem selected_cut_33612 : selected 8 ⟨865554, by decide⟩
    (prefixPartial 13 441528) = some ⟨13, 2, 0, 865554, 441528, 549, 16384⟩ := by
  decide +kernel

theorem context_13_441528_865554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441528 ⟨865554, by decide⟩ :=
  accepted_of_selected 13 441528 ⟨865554, by decide⟩ ⟨13, 2, 0, 865554, 441528, 549, 16384⟩
    (by decide) selected_cut_33612

theorem selected_cut_33613 : selected 8 ⟨865588, by decide⟩
    (prefixPartial 13 441529) = some ⟨13, 2, 0, 865588, 441529, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_441529_865588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441529 ⟨865588, by decide⟩ :=
  accepted_of_selected 13 441529 ⟨865588, by decide⟩ ⟨13, 2, 0, 865588, 441529, 2705, 16384⟩
    (by decide) selected_cut_33613

theorem selected_cut_33614 : selected 8 ⟨865605, by decide⟩
    (prefixPartial 13 441530) = some ⟨13, 2, 0, 865605, 441530, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_441530_865605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441530 ⟨865605, by decide⟩ :=
  accepted_of_selected 13 441530 ⟨865605, by decide⟩ ⟨13, 2, 0, 865605, 441530, 1157, 16384⟩
    (by decide) selected_cut_33614

theorem selected_cut_33615 : selected 8 ⟨865609, by decide⟩
    (prefixPartial 13 441531) = some ⟨13, 2, 0, 865609, 441531, 709, 16384⟩ := by
  decide +kernel

theorem context_13_441531_865609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441531 ⟨865609, by decide⟩ :=
  accepted_of_selected 13 441531 ⟨865609, by decide⟩ ⟨13, 2, 0, 865609, 441531, 709, 16384⟩
    (by decide) selected_cut_33615

theorem unmarked_context_12_110382_865610 : frontier 9 ⟨865610, by decide⟩
    (prefixCache 12 110382) (prefixPartial 12 110382) = false := by
  decide +kernel

theorem node_context_12_110382_865610 : EJMOriginalGlobalDAGData.nodes 9 ⟨865610, by decide⟩ =
    .split (coordinate 12) (![⟨865554, by decide⟩,⟨865588, by decide⟩,⟨865605, by decide⟩,⟨865609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110382_865610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110382 ⟨865610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110382
    ⟨865610, by decide⟩ (by decide) (![⟨865554, by decide⟩,⟨865588, by decide⟩,⟨865605, by decide⟩,⟨865609, by decide⟩]) unmarked_context_12_110382_865610 node_context_12_110382_865610
  intro a
  fin_cases a
  · exact context_13_441528_865554
  · exact context_13_441529_865588
  · exact context_13_441530_865605
  · exact context_13_441531_865609

theorem selected_cut_33616 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 110383) = some ⟨12, 1, 0, 758968, 110383, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110383_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110383 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 110383 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 110383, 1, 65536⟩
    (by decide) selected_cut_33616

theorem unmarked_context_11_27595_865611 : frontier 10 ⟨865611, by decide⟩
    (prefixCache 11 27595) (prefixPartial 11 27595) = false := by
  decide +kernel

theorem node_context_11_27595_865611 : EJMOriginalGlobalDAGData.nodes 10 ⟨865611, by decide⟩ =
    .split (coordinate 11) (![⟨865458, by decide⟩,⟨865541, by decide⟩,⟨865610, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27595_865611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27595 ⟨865611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27595
    ⟨865611, by decide⟩ (by decide) (![⟨865458, by decide⟩,⟨865541, by decide⟩,⟨865610, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_27595_865611 node_context_11_27595_865611
  intro a
  fin_cases a
  · exact context_12_110380_865458
  · exact context_12_110381_865541
  · exact context_12_110382_865610
  · exact context_12_110383_758968

theorem unmarked_context_10_6898_865612 : frontier 11 ⟨865612, by decide⟩
    (prefixCache 10 6898) (prefixPartial 10 6898) = false := by
  decide +kernel

theorem node_context_10_6898_865612 : EJMOriginalGlobalDAGData.nodes 11 ⟨865612, by decide⟩ =
    .split (coordinate 10) (![⟨864538, by decide⟩,⟨864991, by decide⟩,⟨865387, by decide⟩,⟨865611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6898_865612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6898 ⟨865612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6898
    ⟨865612, by decide⟩ (by decide) (![⟨864538, by decide⟩,⟨864991, by decide⟩,⟨865387, by decide⟩,⟨865611, by decide⟩]) unmarked_context_10_6898_865612 node_context_10_6898_865612
  intro a
  fin_cases a
  · exact context_11_27592_864538
  · exact context_11_27593_864991
  · exact context_11_27594_865387
  · exact context_11_27595_865611

theorem selected_cut_33617 : selected 8 ⟨865620, by decide⟩
    (prefixPartial 13 441536) = some ⟨13, 2, 0, 865620, 441536, 629, 16384⟩ := by
  decide +kernel

theorem context_13_441536_865620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441536 ⟨865620, by decide⟩ :=
  accepted_of_selected 13 441536 ⟨865620, by decide⟩ ⟨13, 2, 0, 865620, 441536, 629, 16384⟩
    (by decide) selected_cut_33617

theorem selected_cut_33618 : selected 8 ⟨865655, by decide⟩
    (prefixPartial 13 441537) = some ⟨13, 2, 0, 865655, 441537, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_441537_865655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441537 ⟨865655, by decide⟩ :=
  accepted_of_selected 13 441537 ⟨865655, by decide⟩ ⟨13, 2, 0, 865655, 441537, 2833, 16384⟩
    (by decide) selected_cut_33618

theorem selected_cut_33619 : selected 8 ⟨865681, by decide⟩
    (prefixPartial 13 441538) = some ⟨13, 2, 0, 865681, 441538, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_441538_865681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441538 ⟨865681, by decide⟩ :=
  accepted_of_selected 13 441538 ⟨865681, by decide⟩ ⟨13, 2, 0, 865681, 441538, 1277, 16384⟩
    (by decide) selected_cut_33619

theorem selected_cut_33620 : selected 8 ⟨865687, by decide⟩
    (prefixPartial 13 441539) = some ⟨13, 2, 0, 865687, 441539, 713, 16384⟩ := by
  decide +kernel

theorem context_13_441539_865687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441539 ⟨865687, by decide⟩ :=
  accepted_of_selected 13 441539 ⟨865687, by decide⟩ ⟨13, 2, 0, 865687, 441539, 713, 16384⟩
    (by decide) selected_cut_33620

theorem unmarked_context_12_110384_865688 : frontier 9 ⟨865688, by decide⟩
    (prefixCache 12 110384) (prefixPartial 12 110384) = false := by
  decide +kernel

theorem node_context_12_110384_865688 : EJMOriginalGlobalDAGData.nodes 9 ⟨865688, by decide⟩ =
    .split (coordinate 12) (![⟨865620, by decide⟩,⟨865655, by decide⟩,⟨865681, by decide⟩,⟨865687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110384_865688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110384 ⟨865688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110384
    ⟨865688, by decide⟩ (by decide) (![⟨865620, by decide⟩,⟨865655, by decide⟩,⟨865681, by decide⟩,⟨865687, by decide⟩]) unmarked_context_12_110384_865688 node_context_12_110384_865688
  intro a
  fin_cases a
  · exact context_13_441536_865620
  · exact context_13_441537_865655
  · exact context_13_441538_865681
  · exact context_13_441539_865687

theorem selected_cut_33621 : selected 8 ⟨865697, by decide⟩
    (prefixPartial 13 441540) = some ⟨13, 2, 0, 865697, 441540, 585, 16384⟩ := by
  decide +kernel

theorem context_13_441540_865697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441540 ⟨865697, by decide⟩ :=
  accepted_of_selected 13 441540 ⟨865697, by decide⟩ ⟨13, 2, 0, 865697, 441540, 585, 16384⟩
    (by decide) selected_cut_33621

theorem selected_cut_33622 : selected 8 ⟨865732, by decide⟩
    (prefixPartial 13 441541) = some ⟨13, 2, 0, 865732, 441541, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_441541_865732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441541 ⟨865732, by decide⟩ :=
  accepted_of_selected 13 441541 ⟨865732, by decide⟩ ⟨13, 2, 0, 865732, 441541, 2773, 16384⟩
    (by decide) selected_cut_33622

theorem selected_cut_33623 : selected 8 ⟨865759, by decide⟩
    (prefixPartial 13 441542) = some ⟨13, 2, 0, 865759, 441542, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_441542_865759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441542 ⟨865759, by decide⟩ :=
  accepted_of_selected 13 441542 ⟨865759, by decide⟩ ⟨13, 2, 0, 865759, 441542, 1445, 16384⟩
    (by decide) selected_cut_33623

theorem selected_cut_33624 : selected 8 ⟨865764, by decide⟩
    (prefixPartial 13 441543) = some ⟨13, 2, 0, 865764, 441543, 577, 16384⟩ := by
  decide +kernel

theorem context_13_441543_865764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441543 ⟨865764, by decide⟩ :=
  accepted_of_selected 13 441543 ⟨865764, by decide⟩ ⟨13, 2, 0, 865764, 441543, 577, 16384⟩
    (by decide) selected_cut_33624

theorem unmarked_context_12_110385_865765 : frontier 9 ⟨865765, by decide⟩
    (prefixCache 12 110385) (prefixPartial 12 110385) = false := by
  decide +kernel

theorem node_context_12_110385_865765 : EJMOriginalGlobalDAGData.nodes 9 ⟨865765, by decide⟩ =
    .split (coordinate 12) (![⟨865697, by decide⟩,⟨865732, by decide⟩,⟨865759, by decide⟩,⟨865764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110385_865765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110385 ⟨865765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110385
    ⟨865765, by decide⟩ (by decide) (![⟨865697, by decide⟩,⟨865732, by decide⟩,⟨865759, by decide⟩,⟨865764, by decide⟩]) unmarked_context_12_110385_865765 node_context_12_110385_865765
  intro a
  fin_cases a
  · exact context_13_441540_865697
  · exact context_13_441541_865732
  · exact context_13_441542_865759
  · exact context_13_441543_865764

theorem selected_cut_33625 : selected 8 ⟨865773, by decide⟩
    (prefixPartial 13 441544) = some ⟨13, 2, 0, 865773, 441544, 453, 16384⟩ := by
  decide +kernel

theorem context_13_441544_865773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441544 ⟨865773, by decide⟩ :=
  accepted_of_selected 13 441544 ⟨865773, by decide⟩ ⟨13, 2, 0, 865773, 441544, 453, 16384⟩
    (by decide) selected_cut_33625

theorem selected_cut_33626 : selected 8 ⟨865807, by decide⟩
    (prefixPartial 13 441545) = some ⟨13, 2, 0, 865807, 441545, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_441545_865807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441545 ⟨865807, by decide⟩ :=
  accepted_of_selected 13 441545 ⟨865807, by decide⟩ ⟨13, 2, 0, 865807, 441545, 2513, 16384⟩
    (by decide) selected_cut_33626

theorem selected_cut_33627 : selected 8 ⟨865823, by decide⟩
    (prefixPartial 13 441546) = some ⟨13, 2, 0, 865823, 441546, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_441546_865823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441546 ⟨865823, by decide⟩ :=
  accepted_of_selected 13 441546 ⟨865823, by decide⟩ ⟨13, 2, 0, 865823, 441546, 1081, 16384⟩
    (by decide) selected_cut_33627

theorem selected_cut_33628 : selected 8 ⟨865827, by decide⟩
    (prefixPartial 13 441547) = some ⟨13, 2, 0, 865827, 441547, 593, 16384⟩ := by
  decide +kernel

theorem context_13_441547_865827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441547 ⟨865827, by decide⟩ :=
  accepted_of_selected 13 441547 ⟨865827, by decide⟩ ⟨13, 2, 0, 865827, 441547, 593, 16384⟩
    (by decide) selected_cut_33628

theorem unmarked_context_12_110386_865828 : frontier 9 ⟨865828, by decide⟩
    (prefixCache 12 110386) (prefixPartial 12 110386) = false := by
  decide +kernel

theorem node_context_12_110386_865828 : EJMOriginalGlobalDAGData.nodes 9 ⟨865828, by decide⟩ =
    .split (coordinate 12) (![⟨865773, by decide⟩,⟨865807, by decide⟩,⟨865823, by decide⟩,⟨865827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110386_865828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110386 ⟨865828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110386
    ⟨865828, by decide⟩ (by decide) (![⟨865773, by decide⟩,⟨865807, by decide⟩,⟨865823, by decide⟩,⟨865827, by decide⟩]) unmarked_context_12_110386_865828 node_context_12_110386_865828
  intro a
  fin_cases a
  · exact context_13_441544_865773
  · exact context_13_441545_865807
  · exact context_13_441546_865823
  · exact context_13_441547_865827

theorem selected_cut_33629 : selected 8 ⟨865835, by decide⟩
    (prefixPartial 13 441548) = some ⟨13, 2, 0, 865835, 441548, 445, 16384⟩ := by
  decide +kernel

theorem context_13_441548_865835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441548 ⟨865835, by decide⟩ :=
  accepted_of_selected 13 441548 ⟨865835, by decide⟩ ⟨13, 2, 0, 865835, 441548, 445, 16384⟩
    (by decide) selected_cut_33629

theorem selected_cut_33630 : selected 8 ⟨865863, by decide⟩
    (prefixPartial 13 441549) = some ⟨13, 2, 0, 865863, 441549, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_441549_865863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441549 ⟨865863, by decide⟩ :=
  accepted_of_selected 13 441549 ⟨865863, by decide⟩ ⟨13, 2, 0, 865863, 441549, 2749, 16384⟩
    (by decide) selected_cut_33630

theorem selected_cut_33631 : selected 8 ⟨865881, by decide⟩
    (prefixPartial 13 441550) = some ⟨13, 2, 0, 865881, 441550, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_441550_865881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441550 ⟨865881, by decide⟩ :=
  accepted_of_selected 13 441550 ⟨865881, by decide⟩ ⟨13, 2, 0, 865881, 441550, 1241, 16384⟩
    (by decide) selected_cut_33631

theorem selected_cut_33632 : selected 8 ⟨865884, by decide⟩
    (prefixPartial 13 441551) = some ⟨13, 2, 0, 865884, 441551, 581, 16384⟩ := by
  decide +kernel

theorem context_13_441551_865884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441551 ⟨865884, by decide⟩ :=
  accepted_of_selected 13 441551 ⟨865884, by decide⟩ ⟨13, 2, 0, 865884, 441551, 581, 16384⟩
    (by decide) selected_cut_33632

theorem unmarked_context_12_110387_865885 : frontier 9 ⟨865885, by decide⟩
    (prefixCache 12 110387) (prefixPartial 12 110387) = false := by
  decide +kernel

theorem node_context_12_110387_865885 : EJMOriginalGlobalDAGData.nodes 9 ⟨865885, by decide⟩ =
    .split (coordinate 12) (![⟨865835, by decide⟩,⟨865863, by decide⟩,⟨865881, by decide⟩,⟨865884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110387_865885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110387 ⟨865885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110387
    ⟨865885, by decide⟩ (by decide) (![⟨865835, by decide⟩,⟨865863, by decide⟩,⟨865881, by decide⟩,⟨865884, by decide⟩]) unmarked_context_12_110387_865885 node_context_12_110387_865885
  intro a
  fin_cases a
  · exact context_13_441548_865835
  · exact context_13_441549_865863
  · exact context_13_441550_865881
  · exact context_13_441551_865884

theorem unmarked_context_11_27596_865886 : frontier 10 ⟨865886, by decide⟩
    (prefixCache 11 27596) (prefixPartial 11 27596) = false := by
  decide +kernel

theorem node_context_11_27596_865886 : EJMOriginalGlobalDAGData.nodes 10 ⟨865886, by decide⟩ =
    .split (coordinate 11) (![⟨865688, by decide⟩,⟨865765, by decide⟩,⟨865828, by decide⟩,⟨865885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27596_865886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27596 ⟨865886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27596
    ⟨865886, by decide⟩ (by decide) (![⟨865688, by decide⟩,⟨865765, by decide⟩,⟨865828, by decide⟩,⟨865885, by decide⟩]) unmarked_context_11_27596_865886 node_context_11_27596_865886
  intro a
  fin_cases a
  · exact context_12_110384_865688
  · exact context_12_110385_865765
  · exact context_12_110386_865828
  · exact context_12_110387_865885

theorem selected_cut_33633 : selected 8 ⟨865891, by decide⟩
    (prefixPartial 13 441552) = some ⟨13, 2, 0, 865891, 441552, 329, 16384⟩ := by
  decide +kernel

theorem context_13_441552_865891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441552 ⟨865891, by decide⟩ :=
  accepted_of_selected 13 441552 ⟨865891, by decide⟩ ⟨13, 2, 0, 865891, 441552, 329, 16384⟩
    (by decide) selected_cut_33633

theorem selected_cut_33634 : selected 8 ⟨865941, by decide⟩
    (prefixPartial 13 441553) = some ⟨13, 2, 0, 865941, 441553, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_441553_865941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441553 ⟨865941, by decide⟩ :=
  accepted_of_selected 13 441553 ⟨865941, by decide⟩ ⟨13, 2, 0, 865941, 441553, 3025, 16384⟩
    (by decide) selected_cut_33634

theorem selected_cut_33635 : selected 8 ⟨865974, by decide⟩
    (prefixPartial 13 441554) = some ⟨13, 2, 0, 865974, 441554, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_441554_865974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441554 ⟨865974, by decide⟩ :=
  accepted_of_selected 13 441554 ⟨865974, by decide⟩ ⟨13, 2, 0, 865974, 441554, 1393, 16384⟩
    (by decide) selected_cut_33635

theorem selected_cut_33636 : selected 8 ⟨865979, by decide⟩
    (prefixPartial 13 441555) = some ⟨13, 2, 0, 865979, 441555, 729, 16384⟩ := by
  decide +kernel

theorem context_13_441555_865979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441555 ⟨865979, by decide⟩ :=
  accepted_of_selected 13 441555 ⟨865979, by decide⟩ ⟨13, 2, 0, 865979, 441555, 729, 16384⟩
    (by decide) selected_cut_33636

theorem unmarked_context_12_110388_865980 : frontier 9 ⟨865980, by decide⟩
    (prefixCache 12 110388) (prefixPartial 12 110388) = false := by
  decide +kernel

theorem node_context_12_110388_865980 : EJMOriginalGlobalDAGData.nodes 9 ⟨865980, by decide⟩ =
    .split (coordinate 12) (![⟨865891, by decide⟩,⟨865941, by decide⟩,⟨865974, by decide⟩,⟨865979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110388_865980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110388 ⟨865980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110388
    ⟨865980, by decide⟩ (by decide) (![⟨865891, by decide⟩,⟨865941, by decide⟩,⟨865974, by decide⟩,⟨865979, by decide⟩]) unmarked_context_12_110388_865980 node_context_12_110388_865980
  intro a
  fin_cases a
  · exact context_13_441552_865891
  · exact context_13_441553_865941
  · exact context_13_441554_865974
  · exact context_13_441555_865979

theorem selected_cut_33637 : selected 8 ⟨865984, by decide⟩
    (prefixPartial 13 441556) = some ⟨13, 2, 0, 865984, 441556, 261, 16384⟩ := by
  decide +kernel

theorem context_13_441556_865984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441556 ⟨865984, by decide⟩ :=
  accepted_of_selected 13 441556 ⟨865984, by decide⟩ ⟨13, 2, 0, 865984, 441556, 261, 16384⟩
    (by decide) selected_cut_33637

theorem selected_cut_33638 : selected 8 ⟨866013, by decide⟩
    (prefixPartial 13 441557) = some ⟨13, 2, 0, 866013, 441557, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_441557_866013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441557 ⟨866013, by decide⟩ :=
  accepted_of_selected 13 441557 ⟨866013, by decide⟩ ⟨13, 2, 0, 866013, 441557, 2665, 16384⟩
    (by decide) selected_cut_33638

theorem selected_cut_33639 : selected 8 ⟨866035, by decide⟩
    (prefixPartial 13 441558) = some ⟨13, 2, 0, 866035, 441558, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_441558_866035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441558 ⟨866035, by decide⟩ :=
  accepted_of_selected 13 441558 ⟨866035, by decide⟩ ⟨13, 2, 0, 866035, 441558, 1557, 16384⟩
    (by decide) selected_cut_33639

theorem selected_cut_33640 : selected 8 ⟨866040, by decide⟩
    (prefixPartial 13 441559) = some ⟨13, 2, 0, 866040, 441559, 561, 16384⟩ := by
  decide +kernel

theorem context_13_441559_866040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441559 ⟨866040, by decide⟩ :=
  accepted_of_selected 13 441559 ⟨866040, by decide⟩ ⟨13, 2, 0, 866040, 441559, 561, 16384⟩
    (by decide) selected_cut_33640

theorem unmarked_context_12_110389_866041 : frontier 9 ⟨866041, by decide⟩
    (prefixCache 12 110389) (prefixPartial 12 110389) = false := by
  decide +kernel

theorem node_context_12_110389_866041 : EJMOriginalGlobalDAGData.nodes 9 ⟨866041, by decide⟩ =
    .split (coordinate 12) (![⟨865984, by decide⟩,⟨866013, by decide⟩,⟨866035, by decide⟩,⟨866040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110389_866041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110389 ⟨866041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110389
    ⟨866041, by decide⟩ (by decide) (![⟨865984, by decide⟩,⟨866013, by decide⟩,⟨866035, by decide⟩,⟨866040, by decide⟩]) unmarked_context_12_110389_866041 node_context_12_110389_866041
  intro a
  fin_cases a
  · exact context_13_441556_865984
  · exact context_13_441557_866013
  · exact context_13_441558_866035
  · exact context_13_441559_866040

theorem selected_cut_33641 : selected 8 ⟨866046, by decide⟩
    (prefixPartial 13 441560) = some ⟨13, 2, 0, 866046, 441560, 213, 16384⟩ := by
  decide +kernel

theorem context_13_441560_866046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441560 ⟨866046, by decide⟩ :=
  accepted_of_selected 13 441560 ⟨866046, by decide⟩ ⟨13, 2, 0, 866046, 441560, 213, 16384⟩
    (by decide) selected_cut_33641

theorem selected_cut_33642 : selected 8 ⟨866078, by decide⟩
    (prefixPartial 13 441561) = some ⟨13, 2, 0, 866078, 441561, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_441561_866078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441561 ⟨866078, by decide⟩ :=
  accepted_of_selected 13 441561 ⟨866078, by decide⟩ ⟨13, 2, 0, 866078, 441561, 2545, 16384⟩
    (by decide) selected_cut_33642

theorem selected_cut_33643 : selected 8 ⟨866096, by decide⟩
    (prefixPartial 13 441562) = some ⟨13, 2, 0, 866096, 441562, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_441562_866096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441562 ⟨866096, by decide⟩ :=
  accepted_of_selected 13 441562 ⟨866096, by decide⟩ ⟨13, 2, 0, 866096, 441562, 1177, 16384⟩
    (by decide) selected_cut_33643

theorem selected_cut_33644 : selected 8 ⟨866101, by decide⟩
    (prefixPartial 13 441563) = some ⟨13, 2, 0, 866101, 441563, 665, 16384⟩ := by
  decide +kernel

theorem context_13_441563_866101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441563 ⟨866101, by decide⟩ :=
  accepted_of_selected 13 441563 ⟨866101, by decide⟩ ⟨13, 2, 0, 866101, 441563, 665, 16384⟩
    (by decide) selected_cut_33644

theorem unmarked_context_12_110390_866102 : frontier 9 ⟨866102, by decide⟩
    (prefixCache 12 110390) (prefixPartial 12 110390) = false := by
  decide +kernel

theorem node_context_12_110390_866102 : EJMOriginalGlobalDAGData.nodes 9 ⟨866102, by decide⟩ =
    .split (coordinate 12) (![⟨866046, by decide⟩,⟨866078, by decide⟩,⟨866096, by decide⟩,⟨866101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110390_866102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110390 ⟨866102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110390
    ⟨866102, by decide⟩ (by decide) (![⟨866046, by decide⟩,⟨866078, by decide⟩,⟨866096, by decide⟩,⟨866101, by decide⟩]) unmarked_context_12_110390_866102 node_context_12_110390_866102
  intro a
  fin_cases a
  · exact context_13_441560_866046
  · exact context_13_441561_866078
  · exact context_13_441562_866096
  · exact context_13_441563_866101

theorem selected_cut_33645 : selected 8 ⟨866106, by decide⟩
    (prefixPartial 13 441564) = some ⟨13, 2, 0, 866106, 441564, 221, 16384⟩ := by
  decide +kernel

theorem context_13_441564_866106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441564 ⟨866106, by decide⟩ :=
  accepted_of_selected 13 441564 ⟨866106, by decide⟩ ⟨13, 2, 0, 866106, 441564, 221, 16384⟩
    (by decide) selected_cut_33645

theorem selected_cut_33646 : selected 8 ⟨866142, by decide⟩
    (prefixPartial 13 441565) = some ⟨13, 2, 0, 866142, 441565, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_441565_866142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441565 ⟨866142, by decide⟩ :=
  accepted_of_selected 13 441565 ⟨866142, by decide⟩ ⟨13, 2, 0, 866142, 441565, 2793, 16384⟩
    (by decide) selected_cut_33646

theorem selected_cut_33647 : selected 8 ⟨866167, by decide⟩
    (prefixPartial 13 441566) = some ⟨13, 2, 0, 866167, 441566, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_441566_866167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441566 ⟨866167, by decide⟩ :=
  accepted_of_selected 13 441566 ⟨866167, by decide⟩ ⟨13, 2, 0, 866167, 441566, 1509, 16384⟩
    (by decide) selected_cut_33647

theorem selected_cut_33648 : selected 8 ⟨866171, by decide⟩
    (prefixPartial 13 441567) = some ⟨13, 2, 0, 866171, 441567, 597, 16384⟩ := by
  decide +kernel

theorem context_13_441567_866171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441567 ⟨866171, by decide⟩ :=
  accepted_of_selected 13 441567 ⟨866171, by decide⟩ ⟨13, 2, 0, 866171, 441567, 597, 16384⟩
    (by decide) selected_cut_33648

theorem unmarked_context_12_110391_866172 : frontier 9 ⟨866172, by decide⟩
    (prefixCache 12 110391) (prefixPartial 12 110391) = false := by
  decide +kernel

theorem node_context_12_110391_866172 : EJMOriginalGlobalDAGData.nodes 9 ⟨866172, by decide⟩ =
    .split (coordinate 12) (![⟨866106, by decide⟩,⟨866142, by decide⟩,⟨866167, by decide⟩,⟨866171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110391_866172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110391 ⟨866172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110391
    ⟨866172, by decide⟩ (by decide) (![⟨866106, by decide⟩,⟨866142, by decide⟩,⟨866167, by decide⟩,⟨866171, by decide⟩]) unmarked_context_12_110391_866172 node_context_12_110391_866172
  intro a
  fin_cases a
  · exact context_13_441564_866106
  · exact context_13_441565_866142
  · exact context_13_441566_866167
  · exact context_13_441567_866171

theorem unmarked_context_11_27597_866173 : frontier 10 ⟨866173, by decide⟩
    (prefixCache 11 27597) (prefixPartial 11 27597) = false := by
  decide +kernel

theorem node_context_11_27597_866173 : EJMOriginalGlobalDAGData.nodes 10 ⟨866173, by decide⟩ =
    .split (coordinate 11) (![⟨865980, by decide⟩,⟨866041, by decide⟩,⟨866102, by decide⟩,⟨866172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27597_866173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27597 ⟨866173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27597
    ⟨866173, by decide⟩ (by decide) (![⟨865980, by decide⟩,⟨866041, by decide⟩,⟨866102, by decide⟩,⟨866172, by decide⟩]) unmarked_context_11_27597_866173 node_context_11_27597_866173
  intro a
  fin_cases a
  · exact context_12_110388_865980
  · exact context_12_110389_866041
  · exact context_12_110390_866102
  · exact context_12_110391_866172

theorem selected_cut_33649 : selected 8 ⟨866176, by decide⟩
    (prefixPartial 13 441568) = some ⟨13, 2, 0, 866176, 441568, 141, 16384⟩ := by
  decide +kernel

theorem context_13_441568_866176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441568 ⟨866176, by decide⟩ :=
  accepted_of_selected 13 441568 ⟨866176, by decide⟩ ⟨13, 2, 0, 866176, 441568, 141, 16384⟩
    (by decide) selected_cut_33649

theorem selected_cut_33650 : selected 8 ⟨866233, by decide⟩
    (prefixPartial 13 441569) = some ⟨13, 2, 0, 866233, 441569, 2941, 16384⟩ := by
  decide +kernel

theorem context_13_441569_866233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441569 ⟨866233, by decide⟩ :=
  accepted_of_selected 13 441569 ⟨866233, by decide⟩ ⟨13, 2, 0, 866233, 441569, 2941, 16384⟩
    (by decide) selected_cut_33650

theorem selected_cut_33651 : selected 8 ⟨866273, by decide⟩
    (prefixPartial 13 441570) = some ⟨13, 2, 0, 866273, 441570, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_441570_866273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441570 ⟨866273, by decide⟩ :=
  accepted_of_selected 13 441570 ⟨866273, by decide⟩ ⟨13, 2, 0, 866273, 441570, 1481, 16384⟩
    (by decide) selected_cut_33651

theorem selected_cut_33652 : selected 8 ⟨866279, by decide⟩
    (prefixPartial 13 441571) = some ⟨13, 2, 0, 866279, 441571, 661, 16384⟩ := by
  decide +kernel

theorem context_13_441571_866279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441571 ⟨866279, by decide⟩ :=
  accepted_of_selected 13 441571 ⟨866279, by decide⟩ ⟨13, 2, 0, 866279, 441571, 661, 16384⟩
    (by decide) selected_cut_33652

theorem unmarked_context_12_110392_866280 : frontier 9 ⟨866280, by decide⟩
    (prefixCache 12 110392) (prefixPartial 12 110392) = false := by
  decide +kernel

theorem node_context_12_110392_866280 : EJMOriginalGlobalDAGData.nodes 9 ⟨866280, by decide⟩ =
    .split (coordinate 12) (![⟨866176, by decide⟩,⟨866233, by decide⟩,⟨866273, by decide⟩,⟨866279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110392_866280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110392 ⟨866280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110392
    ⟨866280, by decide⟩ (by decide) (![⟨866176, by decide⟩,⟨866233, by decide⟩,⟨866273, by decide⟩,⟨866279, by decide⟩]) unmarked_context_12_110392_866280 node_context_12_110392_866280
  intro a
  fin_cases a
  · exact context_13_441568_866176
  · exact context_13_441569_866233
  · exact context_13_441570_866273
  · exact context_13_441571_866279

theorem selected_cut_33653 : selected 8 ⟨866283, by decide⟩
    (prefixPartial 13 441572) = some ⟨13, 2, 0, 866283, 441572, 125, 16384⟩ := by
  decide +kernel

theorem context_13_441572_866283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441572 ⟨866283, by decide⟩ :=
  accepted_of_selected 13 441572 ⟨866283, by decide⟩ ⟨13, 2, 0, 866283, 441572, 125, 16384⟩
    (by decide) selected_cut_33653

theorem selected_cut_33654 : selected 8 ⟨866313, by decide⟩
    (prefixPartial 13 441573) = some ⟨13, 2, 0, 866313, 441573, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_441573_866313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441573 ⟨866313, by decide⟩ :=
  accepted_of_selected 13 441573 ⟨866313, by decide⟩ ⟨13, 2, 0, 866313, 441573, 2509, 16384⟩
    (by decide) selected_cut_33654

theorem selected_cut_33655 : selected 8 ⟨866341, by decide⟩
    (prefixPartial 13 441574) = some ⟨13, 2, 0, 866341, 441574, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_441574_866341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441574 ⟨866341, by decide⟩ :=
  accepted_of_selected 13 441574 ⟨866341, by decide⟩ ⟨13, 2, 0, 866341, 441574, 1613, 16384⟩
    (by decide) selected_cut_33655

theorem selected_cut_33656 : selected 8 ⟨866345, by decide⟩
    (prefixPartial 13 441575) = some ⟨13, 2, 0, 866345, 441575, 597, 16384⟩ := by
  decide +kernel

theorem context_13_441575_866345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441575 ⟨866345, by decide⟩ :=
  accepted_of_selected 13 441575 ⟨866345, by decide⟩ ⟨13, 2, 0, 866345, 441575, 597, 16384⟩
    (by decide) selected_cut_33656

theorem unmarked_context_12_110393_866346 : frontier 9 ⟨866346, by decide⟩
    (prefixCache 12 110393) (prefixPartial 12 110393) = false := by
  decide +kernel

theorem node_context_12_110393_866346 : EJMOriginalGlobalDAGData.nodes 9 ⟨866346, by decide⟩ =
    .split (coordinate 12) (![⟨866283, by decide⟩,⟨866313, by decide⟩,⟨866341, by decide⟩,⟨866345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110393_866346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110393 ⟨866346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110393
    ⟨866346, by decide⟩ (by decide) (![⟨866283, by decide⟩,⟨866313, by decide⟩,⟨866341, by decide⟩,⟨866345, by decide⟩]) unmarked_context_12_110393_866346 node_context_12_110393_866346
  intro a
  fin_cases a
  · exact context_13_441572_866283
  · exact context_13_441573_866313
  · exact context_13_441574_866341
  · exact context_13_441575_866345

theorem selected_cut_33657 : selected 8 ⟨866349, by decide⟩
    (prefixPartial 13 441576) = some ⟨13, 2, 0, 866349, 441576, 61, 16384⟩ := by
  decide +kernel

theorem context_13_441576_866349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441576 ⟨866349, by decide⟩ :=
  accepted_of_selected 13 441576 ⟨866349, by decide⟩ ⟨13, 2, 0, 866349, 441576, 61, 16384⟩
    (by decide) selected_cut_33657

theorem selected_cut_33658 : selected 8 ⟨866378, by decide⟩
    (prefixPartial 13 441577) = some ⟨13, 2, 0, 866378, 441577, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_441577_866378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441577 ⟨866378, by decide⟩ :=
  accepted_of_selected 13 441577 ⟨866378, by decide⟩ ⟨13, 2, 0, 866378, 441577, 2377, 16384⟩
    (by decide) selected_cut_33658

theorem selected_cut_33659 : selected 8 ⟨866401, by decide⟩
    (prefixPartial 13 441578) = some ⟨13, 2, 0, 866401, 441578, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_441578_866401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441578 ⟨866401, by decide⟩ :=
  accepted_of_selected 13 441578 ⟨866401, by decide⟩ ⟨13, 2, 0, 866401, 441578, 1173, 16384⟩
    (by decide) selected_cut_33659

theorem selected_cut_33660 : selected 8 ⟨866405, by decide⟩
    (prefixPartial 13 441579) = some ⟨13, 2, 0, 866405, 441579, 561, 16384⟩ := by
  decide +kernel

theorem context_13_441579_866405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441579 ⟨866405, by decide⟩ :=
  accepted_of_selected 13 441579 ⟨866405, by decide⟩ ⟨13, 2, 0, 866405, 441579, 561, 16384⟩
    (by decide) selected_cut_33660

theorem unmarked_context_12_110394_866406 : frontier 9 ⟨866406, by decide⟩
    (prefixCache 12 110394) (prefixPartial 12 110394) = false := by
  decide +kernel

theorem node_context_12_110394_866406 : EJMOriginalGlobalDAGData.nodes 9 ⟨866406, by decide⟩ =
    .split (coordinate 12) (![⟨866349, by decide⟩,⟨866378, by decide⟩,⟨866401, by decide⟩,⟨866405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110394_866406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110394 ⟨866406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110394
    ⟨866406, by decide⟩ (by decide) (![⟨866349, by decide⟩,⟨866378, by decide⟩,⟨866401, by decide⟩,⟨866405, by decide⟩]) unmarked_context_12_110394_866406 node_context_12_110394_866406
  intro a
  fin_cases a
  · exact context_13_441576_866349
  · exact context_13_441577_866378
  · exact context_13_441578_866401
  · exact context_13_441579_866405

theorem selected_cut_33661 : selected 8 ⟨866409, by decide⟩
    (prefixPartial 13 441580) = some ⟨13, 2, 0, 866409, 441580, 45, 16384⟩ := by
  decide +kernel

theorem context_13_441580_866409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441580 ⟨866409, by decide⟩ :=
  accepted_of_selected 13 441580 ⟨866409, by decide⟩ ⟨13, 2, 0, 866409, 441580, 45, 16384⟩
    (by decide) selected_cut_33661

theorem selected_cut_33662 : selected 8 ⟨866445, by decide⟩
    (prefixPartial 13 441581) = some ⟨13, 2, 0, 866445, 441581, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_441581_866445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441581 ⟨866445, by decide⟩ :=
  accepted_of_selected 13 441581 ⟨866445, by decide⟩ ⟨13, 2, 0, 866445, 441581, 2701, 16384⟩
    (by decide) selected_cut_33662

theorem selected_cut_33663 : selected 8 ⟨866467, by decide⟩
    (prefixPartial 13 441582) = some ⟨13, 2, 0, 866467, 441582, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_441582_866467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441582 ⟨866467, by decide⟩ :=
  accepted_of_selected 13 441582 ⟨866467, by decide⟩ ⟨13, 2, 0, 866467, 441582, 1457, 16384⟩
    (by decide) selected_cut_33663

theorem selected_cut_33664 : selected 8 ⟨866470, by decide⟩
    (prefixPartial 13 441583) = some ⟨13, 2, 0, 866470, 441583, 533, 16384⟩ := by
  decide +kernel

theorem context_13_441583_866470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441583 ⟨866470, by decide⟩ :=
  accepted_of_selected 13 441583 ⟨866470, by decide⟩ ⟨13, 2, 0, 866470, 441583, 533, 16384⟩
    (by decide) selected_cut_33664

theorem unmarked_context_12_110395_866471 : frontier 9 ⟨866471, by decide⟩
    (prefixCache 12 110395) (prefixPartial 12 110395) = false := by
  decide +kernel

theorem node_context_12_110395_866471 : EJMOriginalGlobalDAGData.nodes 9 ⟨866471, by decide⟩ =
    .split (coordinate 12) (![⟨866409, by decide⟩,⟨866445, by decide⟩,⟨866467, by decide⟩,⟨866470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110395_866471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110395 ⟨866471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110395
    ⟨866471, by decide⟩ (by decide) (![⟨866409, by decide⟩,⟨866445, by decide⟩,⟨866467, by decide⟩,⟨866470, by decide⟩]) unmarked_context_12_110395_866471 node_context_12_110395_866471
  intro a
  fin_cases a
  · exact context_13_441580_866409
  · exact context_13_441581_866445
  · exact context_13_441582_866467
  · exact context_13_441583_866470

theorem unmarked_context_11_27598_866472 : frontier 10 ⟨866472, by decide⟩
    (prefixCache 11 27598) (prefixPartial 11 27598) = false := by
  decide +kernel

theorem node_context_11_27598_866472 : EJMOriginalGlobalDAGData.nodes 10 ⟨866472, by decide⟩ =
    .split (coordinate 11) (![⟨866280, by decide⟩,⟨866346, by decide⟩,⟨866406, by decide⟩,⟨866471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27598_866472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27598 ⟨866472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27598
    ⟨866472, by decide⟩ (by decide) (![⟨866280, by decide⟩,⟨866346, by decide⟩,⟨866406, by decide⟩,⟨866471, by decide⟩]) unmarked_context_11_27598_866472 node_context_11_27598_866472
  intro a
  fin_cases a
  · exact context_12_110392_866280
  · exact context_12_110393_866346
  · exact context_12_110394_866406
  · exact context_12_110395_866471

theorem selected_cut_33665 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 27599) = some ⟨11, 1, 0, 793294, 27599, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27599_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27599 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 27599 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 27599, 1, 262144⟩
    (by decide) selected_cut_33665

theorem unmarked_context_10_6899_866473 : frontier 11 ⟨866473, by decide⟩
    (prefixCache 10 6899) (prefixPartial 10 6899) = false := by
  decide +kernel

theorem node_context_10_6899_866473 : EJMOriginalGlobalDAGData.nodes 11 ⟨866473, by decide⟩ =
    .split (coordinate 10) (![⟨865886, by decide⟩,⟨866173, by decide⟩,⟨866472, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6899_866473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6899 ⟨866473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6899
    ⟨866473, by decide⟩ (by decide) (![⟨865886, by decide⟩,⟨866173, by decide⟩,⟨866472, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6899_866473 node_context_10_6899_866473
  intro a
  fin_cases a
  · exact context_11_27596_865886
  · exact context_11_27597_866173
  · exact context_11_27598_866472
  · exact context_11_27599_793294

theorem unmarked_context_9_1724_866474 : frontier 12 ⟨866474, by decide⟩
    (prefixCache 9 1724) (prefixPartial 9 1724) = false := by
  decide +kernel

theorem node_context_9_1724_866474 : EJMOriginalGlobalDAGData.nodes 12 ⟨866474, by decide⟩ =
    .split (coordinate 9) (![⟨862194, by decide⟩,⟨864091, by decide⟩,⟨865612, by decide⟩,⟨866473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1724_866474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1724 ⟨866474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1724
    ⟨866474, by decide⟩ (by decide) (![⟨862194, by decide⟩,⟨864091, by decide⟩,⟨865612, by decide⟩,⟨866473, by decide⟩]) unmarked_context_9_1724_866474 node_context_9_1724_866474
  intro a
  fin_cases a
  · exact context_10_6896_862194
  · exact context_10_6897_864091
  · exact context_10_6898_865612
  · exact context_10_6899_866473

theorem selected_cut_33666 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441600) = some ⟨13, 1, 0, 3444, 441600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441600, 1, 16384⟩
    (by decide) selected_cut_33666

theorem selected_cut_33667 : selected 8 ⟨866527, by decide⟩
    (prefixPartial 13 441601) = some ⟨13, 2, 0, 866527, 441601, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_441601_866527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441601 ⟨866527, by decide⟩ :=
  accepted_of_selected 13 441601 ⟨866527, by decide⟩ ⟨13, 2, 0, 866527, 441601, 3441, 16384⟩
    (by decide) selected_cut_33667

theorem selected_cut_33668 : selected 8 ⟨866547, by decide⟩
    (prefixPartial 13 441602) = some ⟨13, 2, 0, 866547, 441602, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_441602_866547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441602 ⟨866547, by decide⟩ :=
  accepted_of_selected 13 441602 ⟨866547, by decide⟩ ⟨13, 2, 0, 866547, 441602, 1165, 16384⟩
    (by decide) selected_cut_33668

theorem selected_cut_33669 : selected 8 ⟨866550, by decide⟩
    (prefixPartial 13 441603) = some ⟨13, 2, 0, 866550, 441603, 681, 16384⟩ := by
  decide +kernel

theorem context_13_441603_866550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441603 ⟨866550, by decide⟩ :=
  accepted_of_selected 13 441603 ⟨866550, by decide⟩ ⟨13, 2, 0, 866550, 441603, 681, 16384⟩
    (by decide) selected_cut_33669

theorem unmarked_context_12_110400_866551 : frontier 9 ⟨866551, by decide⟩
    (prefixCache 12 110400) (prefixPartial 12 110400) = false := by
  decide +kernel

theorem node_context_12_110400_866551 : EJMOriginalGlobalDAGData.nodes 9 ⟨866551, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866527, by decide⟩,⟨866547, by decide⟩,⟨866550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110400_866551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110400 ⟨866551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110400
    ⟨866551, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866527, by decide⟩,⟨866547, by decide⟩,⟨866550, by decide⟩]) unmarked_context_12_110400_866551 node_context_12_110400_866551
  intro a
  fin_cases a
  · exact context_13_441600_3444
  · exact context_13_441601_866527
  · exact context_13_441602_866547
  · exact context_13_441603_866550

theorem selected_cut_33670 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441604) = some ⟨13, 1, 0, 3444, 441604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441604, 1, 16384⟩
    (by decide) selected_cut_33670

theorem selected_cut_33671 : selected 8 ⟨866593, by decide⟩
    (prefixPartial 13 441605) = some ⟨13, 2, 0, 866593, 441605, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_441605_866593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441605 ⟨866593, by decide⟩ :=
  accepted_of_selected 13 441605 ⟨866593, by decide⟩ ⟨13, 2, 0, 866593, 441605, 2833, 16384⟩
    (by decide) selected_cut_33671

theorem selected_cut_33672 : selected 8 ⟨866611, by decide⟩
    (prefixPartial 13 441606) = some ⟨13, 2, 0, 866611, 441606, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_441606_866611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441606 ⟨866611, by decide⟩ :=
  accepted_of_selected 13 441606 ⟨866611, by decide⟩ ⟨13, 2, 0, 866611, 441606, 1245, 16384⟩
    (by decide) selected_cut_33672

theorem selected_cut_33673 : selected 8 ⟨866616, by decide⟩
    (prefixPartial 13 441607) = some ⟨13, 2, 0, 866616, 441607, 593, 16384⟩ := by
  decide +kernel

theorem context_13_441607_866616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441607 ⟨866616, by decide⟩ :=
  accepted_of_selected 13 441607 ⟨866616, by decide⟩ ⟨13, 2, 0, 866616, 441607, 593, 16384⟩
    (by decide) selected_cut_33673

theorem unmarked_context_12_110401_866617 : frontier 9 ⟨866617, by decide⟩
    (prefixCache 12 110401) (prefixPartial 12 110401) = false := by
  decide +kernel

theorem node_context_12_110401_866617 : EJMOriginalGlobalDAGData.nodes 9 ⟨866617, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866593, by decide⟩,⟨866611, by decide⟩,⟨866616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110401_866617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110401 ⟨866617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110401
    ⟨866617, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866593, by decide⟩,⟨866611, by decide⟩,⟨866616, by decide⟩]) unmarked_context_12_110401_866617 node_context_12_110401_866617
  intro a
  fin_cases a
  · exact context_13_441604_3444
  · exact context_13_441605_866593
  · exact context_13_441606_866611
  · exact context_13_441607_866616

theorem selected_cut_33674 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441608) = some ⟨13, 1, 0, 3444, 441608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441608, 1, 16384⟩
    (by decide) selected_cut_33674

theorem selected_cut_33675 : selected 8 ⟨866666, by decide⟩
    (prefixPartial 13 441609) = some ⟨13, 2, 0, 866666, 441609, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_441609_866666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441609 ⟨866666, by decide⟩ :=
  accepted_of_selected 13 441609 ⟨866666, by decide⟩ ⟨13, 2, 0, 866666, 441609, 2901, 16384⟩
    (by decide) selected_cut_33675

theorem selected_cut_33676 : selected 8 ⟨866692, by decide⟩
    (prefixPartial 13 441610) = some ⟨13, 2, 0, 866692, 441610, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_441610_866692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441610 ⟨866692, by decide⟩ :=
  accepted_of_selected 13 441610 ⟨866692, by decide⟩ ⟨13, 2, 0, 866692, 441610, 1173, 16384⟩
    (by decide) selected_cut_33676

theorem selected_cut_33677 : selected 8 ⟨866696, by decide⟩
    (prefixPartial 13 441611) = some ⟨13, 2, 0, 866696, 441611, 533, 16384⟩ := by
  decide +kernel

theorem context_13_441611_866696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441611 ⟨866696, by decide⟩ :=
  accepted_of_selected 13 441611 ⟨866696, by decide⟩ ⟨13, 2, 0, 866696, 441611, 533, 16384⟩
    (by decide) selected_cut_33677

theorem unmarked_context_12_110402_866697 : frontier 9 ⟨866697, by decide⟩
    (prefixCache 12 110402) (prefixPartial 12 110402) = false := by
  decide +kernel

theorem node_context_12_110402_866697 : EJMOriginalGlobalDAGData.nodes 9 ⟨866697, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866666, by decide⟩,⟨866692, by decide⟩,⟨866696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110402_866697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110402 ⟨866697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110402
    ⟨866697, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866666, by decide⟩,⟨866692, by decide⟩,⟨866696, by decide⟩]) unmarked_context_12_110402_866697 node_context_12_110402_866697
  intro a
  fin_cases a
  · exact context_13_441608_3444
  · exact context_13_441609_866666
  · exact context_13_441610_866692
  · exact context_13_441611_866696

theorem selected_cut_33678 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441612) = some ⟨13, 1, 0, 3444, 441612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441612, 1, 16384⟩
    (by decide) selected_cut_33678

theorem selected_cut_33679 : selected 8 ⟨866734, by decide⟩
    (prefixPartial 13 441613) = some ⟨13, 2, 0, 866734, 441613, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_441613_866734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441613 ⟨866734, by decide⟩ :=
  accepted_of_selected 13 441613 ⟨866734, by decide⟩ ⟨13, 2, 0, 866734, 441613, 2849, 16384⟩
    (by decide) selected_cut_33679

theorem selected_cut_33680 : selected 8 ⟨866757, by decide⟩
    (prefixPartial 13 441614) = some ⟨13, 2, 0, 866757, 441614, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_441614_866757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441614 ⟨866757, by decide⟩ :=
  accepted_of_selected 13 441614 ⟨866757, by decide⟩ ⟨13, 2, 0, 866757, 441614, 1261, 16384⟩
    (by decide) selected_cut_33680

theorem selected_cut_33681 : selected 8 ⟨866762, by decide⟩
    (prefixPartial 13 441615) = some ⟨13, 2, 0, 866762, 441615, 557, 16384⟩ := by
  decide +kernel

theorem context_13_441615_866762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441615 ⟨866762, by decide⟩ :=
  accepted_of_selected 13 441615 ⟨866762, by decide⟩ ⟨13, 2, 0, 866762, 441615, 557, 16384⟩
    (by decide) selected_cut_33681

theorem unmarked_context_12_110403_866763 : frontier 9 ⟨866763, by decide⟩
    (prefixCache 12 110403) (prefixPartial 12 110403) = false := by
  decide +kernel

theorem node_context_12_110403_866763 : EJMOriginalGlobalDAGData.nodes 9 ⟨866763, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866734, by decide⟩,⟨866757, by decide⟩,⟨866762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110403_866763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110403 ⟨866763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110403
    ⟨866763, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866734, by decide⟩,⟨866757, by decide⟩,⟨866762, by decide⟩]) unmarked_context_12_110403_866763 node_context_12_110403_866763
  intro a
  fin_cases a
  · exact context_13_441612_3444
  · exact context_13_441613_866734
  · exact context_13_441614_866757
  · exact context_13_441615_866762

theorem unmarked_context_11_27600_866764 : frontier 10 ⟨866764, by decide⟩
    (prefixCache 11 27600) (prefixPartial 11 27600) = false := by
  decide +kernel

theorem node_context_11_27600_866764 : EJMOriginalGlobalDAGData.nodes 10 ⟨866764, by decide⟩ =
    .split (coordinate 11) (![⟨866551, by decide⟩,⟨866617, by decide⟩,⟨866697, by decide⟩,⟨866763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27600_866764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27600 ⟨866764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27600
    ⟨866764, by decide⟩ (by decide) (![⟨866551, by decide⟩,⟨866617, by decide⟩,⟨866697, by decide⟩,⟨866763, by decide⟩]) unmarked_context_11_27600_866764 node_context_11_27600_866764
  intro a
  fin_cases a
  · exact context_12_110400_866551
  · exact context_12_110401_866617
  · exact context_12_110402_866697
  · exact context_12_110403_866763

theorem selected_cut_33682 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441616) = some ⟨13, 1, 0, 3444, 441616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441616, 1, 16384⟩
    (by decide) selected_cut_33682

theorem selected_cut_33683 : selected 8 ⟨866820, by decide⟩
    (prefixPartial 13 441617) = some ⟨13, 2, 0, 866820, 441617, 3325, 16384⟩ := by
  decide +kernel

theorem context_13_441617_866820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441617 ⟨866820, by decide⟩ :=
  accepted_of_selected 13 441617 ⟨866820, by decide⟩ ⟨13, 2, 0, 866820, 441617, 3325, 16384⟩
    (by decide) selected_cut_33683

theorem selected_cut_33684 : selected 8 ⟨866846, by decide⟩
    (prefixPartial 13 441618) = some ⟨13, 2, 0, 866846, 441618, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_441618_866846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441618 ⟨866846, by decide⟩ :=
  accepted_of_selected 13 441618 ⟨866846, by decide⟩ ⟨13, 2, 0, 866846, 441618, 1325, 16384⟩
    (by decide) selected_cut_33684

theorem selected_cut_33685 : selected 8 ⟨866851, by decide⟩
    (prefixPartial 13 441619) = some ⟨13, 2, 0, 866851, 441619, 785, 16384⟩ := by
  decide +kernel

theorem context_13_441619_866851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441619 ⟨866851, by decide⟩ :=
  accepted_of_selected 13 441619 ⟨866851, by decide⟩ ⟨13, 2, 0, 866851, 441619, 785, 16384⟩
    (by decide) selected_cut_33685

theorem unmarked_context_12_110404_866852 : frontier 9 ⟨866852, by decide⟩
    (prefixCache 12 110404) (prefixPartial 12 110404) = false := by
  decide +kernel

theorem node_context_12_110404_866852 : EJMOriginalGlobalDAGData.nodes 9 ⟨866852, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866820, by decide⟩,⟨866846, by decide⟩,⟨866851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110404_866852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110404 ⟨866852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110404
    ⟨866852, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866820, by decide⟩,⟨866846, by decide⟩,⟨866851, by decide⟩]) unmarked_context_12_110404_866852 node_context_12_110404_866852
  intro a
  fin_cases a
  · exact context_13_441616_3444
  · exact context_13_441617_866820
  · exact context_13_441618_866846
  · exact context_13_441619_866851

theorem selected_cut_33686 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441620) = some ⟨13, 1, 0, 3444, 441620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441620, 1, 16384⟩
    (by decide) selected_cut_33686

theorem selected_cut_33687 : selected 8 ⟨866889, by decide⟩
    (prefixPartial 13 441621) = some ⟨13, 2, 0, 866889, 441621, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_441621_866889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441621 ⟨866889, by decide⟩ :=
  accepted_of_selected 13 441621 ⟨866889, by decide⟩ ⟨13, 2, 0, 866889, 441621, 2533, 16384⟩
    (by decide) selected_cut_33687

theorem selected_cut_33688 : selected 8 ⟨866913, by decide⟩
    (prefixPartial 13 441622) = some ⟨13, 2, 0, 866913, 441622, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_441622_866913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441622 ⟨866913, by decide⟩ :=
  accepted_of_selected 13 441622 ⟨866913, by decide⟩ ⟨13, 2, 0, 866913, 441622, 1357, 16384⟩
    (by decide) selected_cut_33688

theorem selected_cut_33689 : selected 8 ⟨866918, by decide⟩
    (prefixPartial 13 441623) = some ⟨13, 2, 0, 866918, 441623, 649, 16384⟩ := by
  decide +kernel

theorem context_13_441623_866918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441623 ⟨866918, by decide⟩ :=
  accepted_of_selected 13 441623 ⟨866918, by decide⟩ ⟨13, 2, 0, 866918, 441623, 649, 16384⟩
    (by decide) selected_cut_33689

theorem unmarked_context_12_110405_866919 : frontier 9 ⟨866919, by decide⟩
    (prefixCache 12 110405) (prefixPartial 12 110405) = false := by
  decide +kernel

theorem node_context_12_110405_866919 : EJMOriginalGlobalDAGData.nodes 9 ⟨866919, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866889, by decide⟩,⟨866913, by decide⟩,⟨866918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110405_866919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110405 ⟨866919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110405
    ⟨866919, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866889, by decide⟩,⟨866913, by decide⟩,⟨866918, by decide⟩]) unmarked_context_12_110405_866919 node_context_12_110405_866919
  intro a
  fin_cases a
  · exact context_13_441620_3444
  · exact context_13_441621_866889
  · exact context_13_441622_866913
  · exact context_13_441623_866918

theorem selected_cut_33690 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441624) = some ⟨13, 1, 0, 3444, 441624, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441624_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441624 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441624 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441624, 1, 16384⟩
    (by decide) selected_cut_33690

theorem selected_cut_33691 : selected 8 ⟨866968, by decide⟩
    (prefixPartial 13 441625) = some ⟨13, 2, 0, 866968, 441625, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_441625_866968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441625 ⟨866968, by decide⟩ :=
  accepted_of_selected 13 441625 ⟨866968, by decide⟩ ⟨13, 2, 0, 866968, 441625, 2629, 16384⟩
    (by decide) selected_cut_33691

theorem selected_cut_33692 : selected 8 ⟨866991, by decide⟩
    (prefixPartial 13 441626) = some ⟨13, 2, 0, 866991, 441626, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_441626_866991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441626 ⟨866991, by decide⟩ :=
  accepted_of_selected 13 441626 ⟨866991, by decide⟩ ⟨13, 2, 0, 866991, 441626, 1253, 16384⟩
    (by decide) selected_cut_33692

theorem selected_cut_33693 : selected 8 ⟨866995, by decide⟩
    (prefixPartial 13 441627) = some ⟨13, 2, 0, 866995, 441627, 653, 16384⟩ := by
  decide +kernel

theorem context_13_441627_866995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441627 ⟨866995, by decide⟩ :=
  accepted_of_selected 13 441627 ⟨866995, by decide⟩ ⟨13, 2, 0, 866995, 441627, 653, 16384⟩
    (by decide) selected_cut_33693

theorem unmarked_context_12_110406_866996 : frontier 9 ⟨866996, by decide⟩
    (prefixCache 12 110406) (prefixPartial 12 110406) = false := by
  decide +kernel

theorem node_context_12_110406_866996 : EJMOriginalGlobalDAGData.nodes 9 ⟨866996, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨866968, by decide⟩,⟨866991, by decide⟩,⟨866995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110406_866996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110406 ⟨866996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110406
    ⟨866996, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨866968, by decide⟩,⟨866991, by decide⟩,⟨866995, by decide⟩]) unmarked_context_12_110406_866996 node_context_12_110406_866996
  intro a
  fin_cases a
  · exact context_13_441624_3444
  · exact context_13_441625_866968
  · exact context_13_441626_866991
  · exact context_13_441627_866995

theorem selected_cut_33694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441628) = some ⟨13, 1, 0, 3444, 441628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441628, 1, 16384⟩
    (by decide) selected_cut_33694

theorem selected_cut_33695 : selected 8 ⟨867030, by decide⟩
    (prefixPartial 13 441629) = some ⟨13, 2, 0, 867030, 441629, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_441629_867030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441629 ⟨867030, by decide⟩ :=
  accepted_of_selected 13 441629 ⟨867030, by decide⟩ ⟨13, 2, 0, 867030, 441629, 2553, 16384⟩
    (by decide) selected_cut_33695

theorem selected_cut_33696 : selected 8 ⟨867062, by decide⟩
    (prefixPartial 13 441630) = some ⟨13, 2, 0, 867062, 441630, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_441630_867062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441630 ⟨867062, by decide⟩ :=
  accepted_of_selected 13 441630 ⟨867062, by decide⟩ ⟨13, 2, 0, 867062, 441630, 1457, 16384⟩
    (by decide) selected_cut_33696

theorem selected_cut_33697 : selected 8 ⟨867067, by decide⟩
    (prefixPartial 13 441631) = some ⟨13, 2, 0, 867067, 441631, 677, 16384⟩ := by
  decide +kernel

theorem context_13_441631_867067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441631 ⟨867067, by decide⟩ :=
  accepted_of_selected 13 441631 ⟨867067, by decide⟩ ⟨13, 2, 0, 867067, 441631, 677, 16384⟩
    (by decide) selected_cut_33697

theorem unmarked_context_12_110407_867068 : frontier 9 ⟨867068, by decide⟩
    (prefixCache 12 110407) (prefixPartial 12 110407) = false := by
  decide +kernel

theorem node_context_12_110407_867068 : EJMOriginalGlobalDAGData.nodes 9 ⟨867068, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867030, by decide⟩,⟨867062, by decide⟩,⟨867067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110407_867068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110407 ⟨867068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110407
    ⟨867068, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867030, by decide⟩,⟨867062, by decide⟩,⟨867067, by decide⟩]) unmarked_context_12_110407_867068 node_context_12_110407_867068
  intro a
  fin_cases a
  · exact context_13_441628_3444
  · exact context_13_441629_867030
  · exact context_13_441630_867062
  · exact context_13_441631_867067

theorem unmarked_context_11_27601_867069 : frontier 10 ⟨867069, by decide⟩
    (prefixCache 11 27601) (prefixPartial 11 27601) = false := by
  decide +kernel

theorem node_context_11_27601_867069 : EJMOriginalGlobalDAGData.nodes 10 ⟨867069, by decide⟩ =
    .split (coordinate 11) (![⟨866852, by decide⟩,⟨866919, by decide⟩,⟨866996, by decide⟩,⟨867068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27601_867069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27601 ⟨867069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27601
    ⟨867069, by decide⟩ (by decide) (![⟨866852, by decide⟩,⟨866919, by decide⟩,⟨866996, by decide⟩,⟨867068, by decide⟩]) unmarked_context_11_27601_867069 node_context_11_27601_867069
  intro a
  fin_cases a
  · exact context_12_110404_866852
  · exact context_12_110405_866919
  · exact context_12_110406_866996
  · exact context_12_110407_867068

theorem selected_cut_33698 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441632) = some ⟨13, 1, 0, 3444, 441632, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441632_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441632 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441632 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441632, 1, 16384⟩
    (by decide) selected_cut_33698

theorem selected_cut_33699 : selected 8 ⟨867123, by decide⟩
    (prefixPartial 13 441633) = some ⟨13, 2, 0, 867123, 441633, 3017, 16384⟩ := by
  decide +kernel

theorem context_13_441633_867123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441633 ⟨867123, by decide⟩ :=
  accepted_of_selected 13 441633 ⟨867123, by decide⟩ ⟨13, 2, 0, 867123, 441633, 3017, 16384⟩
    (by decide) selected_cut_33699

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
