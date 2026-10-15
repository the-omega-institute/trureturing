/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover296
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28516 : selected 8 ⟨719411, by decide⟩
    (prefixPartial 13 369898) = some ⟨13, 2, 0, 719411, 369898, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_369898_719411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369898 ⟨719411, by decide⟩ :=
  accepted_of_selected 13 369898 ⟨719411, by decide⟩ ⟨13, 2, 0, 719411, 369898, 1493, 16384⟩
    (by decide) selected_cut_28516

theorem selected_cut_28517 : selected 8 ⟨719419, by decide⟩
    (prefixPartial 13 369899) = some ⟨13, 2, 0, 719419, 369899, 841, 16384⟩ := by
  decide +kernel

theorem context_13_369899_719419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369899 ⟨719419, by decide⟩ :=
  accepted_of_selected 13 369899 ⟨719419, by decide⟩ ⟨13, 2, 0, 719419, 369899, 841, 16384⟩
    (by decide) selected_cut_28517

theorem unmarked_context_12_92474_719420 : frontier 9 ⟨719420, by decide⟩
    (prefixCache 12 92474) (prefixPartial 12 92474) = false := by
  decide +kernel

theorem node_context_12_92474_719420 : EJMOriginalGlobalDAGData.nodes 9 ⟨719420, by decide⟩ =
    .split (coordinate 12) (![⟨719370, by decide⟩,⟨719391, by decide⟩,⟨719411, by decide⟩,⟨719419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92474_719420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92474 ⟨719420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92474
    ⟨719420, by decide⟩ (by decide) (![⟨719370, by decide⟩,⟨719391, by decide⟩,⟨719411, by decide⟩,⟨719419, by decide⟩]) unmarked_context_12_92474_719420 node_context_12_92474_719420
  intro a
  fin_cases a
  · exact context_13_369896_719370
  · exact context_13_369897_719391
  · exact context_13_369898_719411
  · exact context_13_369899_719419

theorem selected_cut_28518 : selected 8 ⟨719426, by decide⟩
    (prefixPartial 13 369900) = some ⟨13, 2, 0, 719426, 369900, 313, 16384⟩ := by
  decide +kernel

theorem context_13_369900_719426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369900 ⟨719426, by decide⟩ :=
  accepted_of_selected 13 369900 ⟨719426, by decide⟩ ⟨13, 2, 0, 719426, 369900, 313, 16384⟩
    (by decide) selected_cut_28518

theorem selected_cut_28519 : selected 8 ⟨719453, by decide⟩
    (prefixPartial 13 369901) = some ⟨13, 2, 0, 719453, 369901, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_369901_719453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369901 ⟨719453, by decide⟩ :=
  accepted_of_selected 13 369901 ⟨719453, by decide⟩ ⟨13, 2, 0, 719453, 369901, 2125, 16384⟩
    (by decide) selected_cut_28519

theorem selected_cut_28520 : selected 8 ⟨719472, by decide⟩
    (prefixPartial 13 369902) = some ⟨13, 2, 0, 719472, 369902, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_369902_719472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369902 ⟨719472, by decide⟩ :=
  accepted_of_selected 13 369902 ⟨719472, by decide⟩ ⟨13, 2, 0, 719472, 369902, 1653, 16384⟩
    (by decide) selected_cut_28520

theorem selected_cut_28521 : selected 8 ⟨719479, by decide⟩
    (prefixPartial 13 369903) = some ⟨13, 2, 0, 719479, 369903, 805, 16384⟩ := by
  decide +kernel

theorem context_13_369903_719479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369903 ⟨719479, by decide⟩ :=
  accepted_of_selected 13 369903 ⟨719479, by decide⟩ ⟨13, 2, 0, 719479, 369903, 805, 16384⟩
    (by decide) selected_cut_28521

theorem unmarked_context_12_92475_719480 : frontier 9 ⟨719480, by decide⟩
    (prefixCache 12 92475) (prefixPartial 12 92475) = false := by
  decide +kernel

theorem node_context_12_92475_719480 : EJMOriginalGlobalDAGData.nodes 9 ⟨719480, by decide⟩ =
    .split (coordinate 12) (![⟨719426, by decide⟩,⟨719453, by decide⟩,⟨719472, by decide⟩,⟨719479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92475_719480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92475 ⟨719480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92475
    ⟨719480, by decide⟩ (by decide) (![⟨719426, by decide⟩,⟨719453, by decide⟩,⟨719472, by decide⟩,⟨719479, by decide⟩]) unmarked_context_12_92475_719480 node_context_12_92475_719480
  intro a
  fin_cases a
  · exact context_13_369900_719426
  · exact context_13_369901_719453
  · exact context_13_369902_719472
  · exact context_13_369903_719479

theorem unmarked_context_11_23118_719481 : frontier 10 ⟨719481, by decide⟩
    (prefixCache 11 23118) (prefixPartial 11 23118) = false := by
  decide +kernel

theorem node_context_11_23118_719481 : EJMOriginalGlobalDAGData.nodes 10 ⟨719481, by decide⟩ =
    .split (coordinate 11) (![⟨719309, by decide⟩,⟨719364, by decide⟩,⟨719420, by decide⟩,⟨719480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23118_719481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23118 ⟨719481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23118
    ⟨719481, by decide⟩ (by decide) (![⟨719309, by decide⟩,⟨719364, by decide⟩,⟨719420, by decide⟩,⟨719480, by decide⟩]) unmarked_context_11_23118_719481 node_context_11_23118_719481
  intro a
  fin_cases a
  · exact context_12_92472_719309
  · exact context_12_92473_719364
  · exact context_12_92474_719420
  · exact context_12_92475_719480

theorem selected_cut_28522 : selected 8 ⟨719485, by decide⟩
    (prefixPartial 13 369904) = some ⟨13, 2, 0, 719485, 369904, 197, 16384⟩ := by
  decide +kernel

theorem context_13_369904_719485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369904 ⟨719485, by decide⟩ :=
  accepted_of_selected 13 369904 ⟨719485, by decide⟩ ⟨13, 2, 0, 719485, 369904, 197, 16384⟩
    (by decide) selected_cut_28522

theorem selected_cut_28523 : selected 8 ⟨719511, by decide⟩
    (prefixPartial 13 369905) = some ⟨13, 2, 0, 719511, 369905, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_369905_719511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369905 ⟨719511, by decide⟩ :=
  accepted_of_selected 13 369905 ⟨719511, by decide⟩ ⟨13, 2, 0, 719511, 369905, 2173, 16384⟩
    (by decide) selected_cut_28523

theorem selected_cut_28524 : selected 8 ⟨719533, by decide⟩
    (prefixPartial 13 369906) = some ⟨13, 2, 0, 719533, 369906, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_369906_719533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369906 ⟨719533, by decide⟩ :=
  accepted_of_selected 13 369906 ⟨719533, by decide⟩ ⟨13, 2, 0, 719533, 369906, 1765, 16384⟩
    (by decide) selected_cut_28524

theorem selected_cut_28525 : selected 8 ⟨719538, by decide⟩
    (prefixPartial 13 369907) = some ⟨13, 2, 0, 719538, 369907, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_369907_719538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369907 ⟨719538, by decide⟩ :=
  accepted_of_selected 13 369907 ⟨719538, by decide⟩ ⟨13, 2, 0, 719538, 369907, 1017, 16384⟩
    (by decide) selected_cut_28525

theorem unmarked_context_12_92476_719539 : frontier 9 ⟨719539, by decide⟩
    (prefixCache 12 92476) (prefixPartial 12 92476) = false := by
  decide +kernel

theorem node_context_12_92476_719539 : EJMOriginalGlobalDAGData.nodes 9 ⟨719539, by decide⟩ =
    .split (coordinate 12) (![⟨719485, by decide⟩,⟨719511, by decide⟩,⟨719533, by decide⟩,⟨719538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92476_719539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92476 ⟨719539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92476
    ⟨719539, by decide⟩ (by decide) (![⟨719485, by decide⟩,⟨719511, by decide⟩,⟨719533, by decide⟩,⟨719538, by decide⟩]) unmarked_context_12_92476_719539 node_context_12_92476_719539
  intro a
  fin_cases a
  · exact context_13_369904_719485
  · exact context_13_369905_719511
  · exact context_13_369906_719533
  · exact context_13_369907_719538

theorem selected_cut_28526 : selected 8 ⟨719543, by decide⟩
    (prefixPartial 13 369908) = some ⟨13, 2, 0, 719543, 369908, 169, 16384⟩ := by
  decide +kernel

theorem context_13_369908_719543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369908 ⟨719543, by decide⟩ :=
  accepted_of_selected 13 369908 ⟨719543, by decide⟩ ⟨13, 2, 0, 719543, 369908, 169, 16384⟩
    (by decide) selected_cut_28526

theorem selected_cut_28527 : selected 8 ⟨719567, by decide⟩
    (prefixPartial 13 369909) = some ⟨13, 2, 0, 719567, 369909, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_369909_719567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369909 ⟨719567, by decide⟩ :=
  accepted_of_selected 13 369909 ⟨719567, by decide⟩ ⟨13, 2, 0, 719567, 369909, 1685, 16384⟩
    (by decide) selected_cut_28527

theorem selected_cut_28528 : selected 8 ⟨719586, by decide⟩
    (prefixPartial 13 369910) = some ⟨13, 2, 0, 719586, 369910, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_369910_719586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369910 ⟨719586, by decide⟩ :=
  accepted_of_selected 13 369910 ⟨719586, by decide⟩ ⟨13, 2, 0, 719586, 369910, 1577, 16384⟩
    (by decide) selected_cut_28528

theorem selected_cut_28529 : selected 8 ⟨719592, by decide⟩
    (prefixPartial 13 369911) = some ⟨13, 2, 0, 719592, 369911, 909, 16384⟩ := by
  decide +kernel

theorem context_13_369911_719592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369911 ⟨719592, by decide⟩ :=
  accepted_of_selected 13 369911 ⟨719592, by decide⟩ ⟨13, 2, 0, 719592, 369911, 909, 16384⟩
    (by decide) selected_cut_28529

theorem unmarked_context_12_92477_719593 : frontier 9 ⟨719593, by decide⟩
    (prefixCache 12 92477) (prefixPartial 12 92477) = false := by
  decide +kernel

theorem node_context_12_92477_719593 : EJMOriginalGlobalDAGData.nodes 9 ⟨719593, by decide⟩ =
    .split (coordinate 12) (![⟨719543, by decide⟩,⟨719567, by decide⟩,⟨719586, by decide⟩,⟨719592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92477_719593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92477 ⟨719593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92477
    ⟨719593, by decide⟩ (by decide) (![⟨719543, by decide⟩,⟨719567, by decide⟩,⟨719586, by decide⟩,⟨719592, by decide⟩]) unmarked_context_12_92477_719593 node_context_12_92477_719593
  intro a
  fin_cases a
  · exact context_13_369908_719543
  · exact context_13_369909_719567
  · exact context_13_369910_719586
  · exact context_13_369911_719592

theorem selected_cut_28530 : selected 8 ⟨719597, by decide⟩
    (prefixPartial 13 369912) = some ⟨13, 2, 0, 719597, 369912, 149, 16384⟩ := by
  decide +kernel

theorem context_13_369912_719597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369912 ⟨719597, by decide⟩ :=
  accepted_of_selected 13 369912 ⟨719597, by decide⟩ ⟨13, 2, 0, 719597, 369912, 149, 16384⟩
    (by decide) selected_cut_28530

theorem selected_cut_28531 : selected 8 ⟨719622, by decide⟩
    (prefixPartial 13 369913) = some ⟨13, 2, 0, 719622, 369913, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_369913_719622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369913 ⟨719622, by decide⟩ :=
  accepted_of_selected 13 369913 ⟨719622, by decide⟩ ⟨13, 2, 0, 719622, 369913, 1957, 16384⟩
    (by decide) selected_cut_28531

theorem selected_cut_28532 : selected 8 ⟨719643, by decide⟩
    (prefixPartial 13 369914) = some ⟨13, 2, 0, 719643, 369914, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_369914_719643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369914 ⟨719643, by decide⟩ :=
  accepted_of_selected 13 369914 ⟨719643, by decide⟩ ⟨13, 2, 0, 719643, 369914, 1693, 16384⟩
    (by decide) selected_cut_28532

theorem selected_cut_28533 : selected 8 ⟨719653, by decide⟩
    (prefixPartial 13 369915) = some ⟨13, 2, 0, 719653, 369915, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_369915_719653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369915 ⟨719653, by decide⟩ :=
  accepted_of_selected 13 369915 ⟨719653, by decide⟩ ⟨13, 2, 0, 719653, 369915, 1037, 16384⟩
    (by decide) selected_cut_28533

theorem unmarked_context_12_92478_719654 : frontier 9 ⟨719654, by decide⟩
    (prefixCache 12 92478) (prefixPartial 12 92478) = false := by
  decide +kernel

theorem node_context_12_92478_719654 : EJMOriginalGlobalDAGData.nodes 9 ⟨719654, by decide⟩ =
    .split (coordinate 12) (![⟨719597, by decide⟩,⟨719622, by decide⟩,⟨719643, by decide⟩,⟨719653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92478_719654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92478 ⟨719654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92478
    ⟨719654, by decide⟩ (by decide) (![⟨719597, by decide⟩,⟨719622, by decide⟩,⟨719643, by decide⟩,⟨719653, by decide⟩]) unmarked_context_12_92478_719654 node_context_12_92478_719654
  intro a
  fin_cases a
  · exact context_13_369912_719597
  · exact context_13_369913_719622
  · exact context_13_369914_719643
  · exact context_13_369915_719653

theorem selected_cut_28534 : selected 8 ⟨719658, by decide⟩
    (prefixPartial 13 369916) = some ⟨13, 2, 0, 719658, 369916, 85, 16384⟩ := by
  decide +kernel

theorem context_13_369916_719658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369916 ⟨719658, by decide⟩ :=
  accepted_of_selected 13 369916 ⟨719658, by decide⟩ ⟨13, 2, 0, 719658, 369916, 85, 16384⟩
    (by decide) selected_cut_28534

theorem selected_cut_28535 : selected 8 ⟨719688, by decide⟩
    (prefixPartial 13 369917) = some ⟨13, 2, 0, 719688, 369917, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_369917_719688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369917 ⟨719688, by decide⟩ :=
  accepted_of_selected 13 369917 ⟨719688, by decide⟩ ⟨13, 2, 0, 719688, 369917, 2377, 16384⟩
    (by decide) selected_cut_28535

theorem selected_cut_28536 : selected 8 ⟨719706, by decide⟩
    (prefixPartial 13 369918) = some ⟨13, 2, 0, 719706, 369918, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_369918_719706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369918 ⟨719706, by decide⟩ :=
  accepted_of_selected 13 369918 ⟨719706, by decide⟩ ⟨13, 2, 0, 719706, 369918, 1801, 16384⟩
    (by decide) selected_cut_28536

theorem selected_cut_28537 : selected 8 ⟨719710, by decide⟩
    (prefixPartial 13 369919) = some ⟨13, 2, 0, 719710, 369919, 985, 16384⟩ := by
  decide +kernel

theorem context_13_369919_719710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369919 ⟨719710, by decide⟩ :=
  accepted_of_selected 13 369919 ⟨719710, by decide⟩ ⟨13, 2, 0, 719710, 369919, 985, 16384⟩
    (by decide) selected_cut_28537

theorem unmarked_context_12_92479_719711 : frontier 9 ⟨719711, by decide⟩
    (prefixCache 12 92479) (prefixPartial 12 92479) = false := by
  decide +kernel

theorem node_context_12_92479_719711 : EJMOriginalGlobalDAGData.nodes 9 ⟨719711, by decide⟩ =
    .split (coordinate 12) (![⟨719658, by decide⟩,⟨719688, by decide⟩,⟨719706, by decide⟩,⟨719710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92479_719711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92479 ⟨719711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92479
    ⟨719711, by decide⟩ (by decide) (![⟨719658, by decide⟩,⟨719688, by decide⟩,⟨719706, by decide⟩,⟨719710, by decide⟩]) unmarked_context_12_92479_719711 node_context_12_92479_719711
  intro a
  fin_cases a
  · exact context_13_369916_719658
  · exact context_13_369917_719688
  · exact context_13_369918_719706
  · exact context_13_369919_719710

theorem unmarked_context_11_23119_719712 : frontier 10 ⟨719712, by decide⟩
    (prefixCache 11 23119) (prefixPartial 11 23119) = false := by
  decide +kernel

theorem node_context_11_23119_719712 : EJMOriginalGlobalDAGData.nodes 10 ⟨719712, by decide⟩ =
    .split (coordinate 11) (![⟨719539, by decide⟩,⟨719593, by decide⟩,⟨719654, by decide⟩,⟨719711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23119_719712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23119 ⟨719712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23119
    ⟨719712, by decide⟩ (by decide) (![⟨719539, by decide⟩,⟨719593, by decide⟩,⟨719654, by decide⟩,⟨719711, by decide⟩]) unmarked_context_11_23119_719712 node_context_11_23119_719712
  intro a
  fin_cases a
  · exact context_12_92476_719539
  · exact context_12_92477_719593
  · exact context_12_92478_719654
  · exact context_12_92479_719711

theorem unmarked_context_10_5779_719713 : frontier 11 ⟨719713, by decide⟩
    (prefixCache 10 5779) (prefixPartial 10 5779) = false := by
  decide +kernel

theorem node_context_10_5779_719713 : EJMOriginalGlobalDAGData.nodes 11 ⟨719713, by decide⟩ =
    .split (coordinate 10) (![⟨719081, by decide⟩,⟨719255, by decide⟩,⟨719481, by decide⟩,⟨719712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5779_719713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5779 ⟨719713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5779
    ⟨719713, by decide⟩ (by decide) (![⟨719081, by decide⟩,⟨719255, by decide⟩,⟨719481, by decide⟩,⟨719712, by decide⟩]) unmarked_context_10_5779_719713 node_context_10_5779_719713
  intro a
  fin_cases a
  · exact context_11_23116_719081
  · exact context_11_23117_719255
  · exact context_11_23118_719481
  · exact context_11_23119_719712

theorem unmarked_context_9_1444_719714 : frontier 12 ⟨719714, by decide⟩
    (prefixCache 9 1444) (prefixPartial 9 1444) = false := by
  decide +kernel

theorem node_context_9_1444_719714 : EJMOriginalGlobalDAGData.nodes 12 ⟨719714, by decide⟩ =
    .split (coordinate 9) (![⟨716983, by decide⟩,⟨717971, by decide⟩,⟨718827, by decide⟩,⟨719713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1444_719714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1444 ⟨719714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1444
    ⟨719714, by decide⟩ (by decide) (![⟨716983, by decide⟩,⟨717971, by decide⟩,⟨718827, by decide⟩,⟨719713, by decide⟩]) unmarked_context_9_1444_719714 node_context_9_1444_719714
  intro a
  fin_cases a
  · exact context_10_5776_716983
  · exact context_10_5777_717971
  · exact context_10_5778_718827
  · exact context_10_5779_719713

theorem selected_cut_28538 : selected 9 ⟨719764, by decide⟩
    (prefixPartial 12 92480) = some ⟨12, 2, 0, 719764, 92480, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_92480_719764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92480 ⟨719764, by decide⟩ :=
  accepted_of_selected 12 92480 ⟨719764, by decide⟩ ⟨12, 2, 0, 719764, 92480, 3917, 65536⟩
    (by decide) selected_cut_28538

theorem selected_cut_28539 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 92481) = some ⟨12, 1, 0, 170504, 92481, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92481_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92481 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 92481 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 92481, 1, 65536⟩
    (by decide) selected_cut_28539

theorem selected_cut_28540 : selected 9 ⟨719812, by decide⟩
    (prefixPartial 12 92482) = some ⟨12, 2, 0, 719812, 92482, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_92482_719812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92482 ⟨719812, by decide⟩ :=
  accepted_of_selected 12 92482 ⟨719812, by decide⟩ ⟨12, 2, 0, 719812, 92482, 4073, 65536⟩
    (by decide) selected_cut_28540

theorem selected_cut_28541 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 369932) = some ⟨13, 1, 0, 3444, 369932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_369932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 369932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 369932, 1, 16384⟩
    (by decide) selected_cut_28541

theorem selected_cut_28542 : selected 8 ⟨719832, by decide⟩
    (prefixPartial 13 369933) = some ⟨13, 2, 0, 719832, 369933, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_369933_719832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369933 ⟨719832, by decide⟩ :=
  accepted_of_selected 13 369933 ⟨719832, by decide⟩ ⟨13, 2, 0, 719832, 369933, 1781, 16384⟩
    (by decide) selected_cut_28542

theorem selected_cut_28543 : selected 8 ⟨719851, by decide⟩
    (prefixPartial 13 369934) = some ⟨13, 2, 0, 719851, 369934, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_369934_719851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369934 ⟨719851, by decide⟩ :=
  accepted_of_selected 13 369934 ⟨719851, by decide⟩ ⟨13, 2, 0, 719851, 369934, 1517, 16384⟩
    (by decide) selected_cut_28543

theorem selected_cut_28544 : selected 8 ⟨719858, by decide⟩
    (prefixPartial 13 369935) = some ⟨13, 2, 0, 719858, 369935, 841, 16384⟩ := by
  decide +kernel

theorem context_13_369935_719858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369935 ⟨719858, by decide⟩ :=
  accepted_of_selected 13 369935 ⟨719858, by decide⟩ ⟨13, 2, 0, 719858, 369935, 841, 16384⟩
    (by decide) selected_cut_28544

theorem unmarked_context_12_92483_719859 : frontier 9 ⟨719859, by decide⟩
    (prefixCache 12 92483) (prefixPartial 12 92483) = false := by
  decide +kernel

theorem node_context_12_92483_719859 : EJMOriginalGlobalDAGData.nodes 9 ⟨719859, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨719832, by decide⟩,⟨719851, by decide⟩,⟨719858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92483_719859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92483 ⟨719859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92483
    ⟨719859, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨719832, by decide⟩,⟨719851, by decide⟩,⟨719858, by decide⟩]) unmarked_context_12_92483_719859 node_context_12_92483_719859
  intro a
  fin_cases a
  · exact context_13_369932_3444
  · exact context_13_369933_719832
  · exact context_13_369934_719851
  · exact context_13_369935_719858

theorem unmarked_context_11_23120_719860 : frontier 10 ⟨719860, by decide⟩
    (prefixCache 11 23120) (prefixPartial 11 23120) = false := by
  decide +kernel

theorem node_context_11_23120_719860 : EJMOriginalGlobalDAGData.nodes 10 ⟨719860, by decide⟩ =
    .split (coordinate 11) (![⟨719764, by decide⟩,⟨170504, by decide⟩,⟨719812, by decide⟩,⟨719859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23120_719860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23120 ⟨719860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23120
    ⟨719860, by decide⟩ (by decide) (![⟨719764, by decide⟩,⟨170504, by decide⟩,⟨719812, by decide⟩,⟨719859, by decide⟩]) unmarked_context_11_23120_719860 node_context_11_23120_719860
  intro a
  fin_cases a
  · exact context_12_92480_719764
  · exact context_12_92481_170504
  · exact context_12_92482_719812
  · exact context_12_92483_719859

theorem selected_cut_28545 : selected 9 ⟨719901, by decide⟩
    (prefixPartial 12 92484) = some ⟨12, 2, 0, 719901, 92484, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_92484_719901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92484 ⟨719901, by decide⟩ :=
  accepted_of_selected 12 92484 ⟨719901, by decide⟩ ⟨12, 2, 0, 719901, 92484, 2877, 65536⟩
    (by decide) selected_cut_28545

theorem selected_cut_28546 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 92485) = some ⟨12, 1, 0, 170504, 92485, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92485_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92485 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 92485 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 92485, 1, 65536⟩
    (by decide) selected_cut_28546

theorem selected_cut_28547 : selected 9 ⟨719945, by decide⟩
    (prefixPartial 12 92486) = some ⟨12, 2, 0, 719945, 92486, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_92486_719945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92486 ⟨719945, by decide⟩ :=
  accepted_of_selected 12 92486 ⟨719945, by decide⟩ ⟨12, 2, 0, 719945, 92486, 2997, 65536⟩
    (by decide) selected_cut_28547

theorem selected_cut_28548 : selected 9 ⟨719992, by decide⟩
    (prefixPartial 12 92487) = some ⟨12, 2, 0, 719992, 92487, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_92487_719992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92487 ⟨719992, by decide⟩ :=
  accepted_of_selected 12 92487 ⟨719992, by decide⟩ ⟨12, 2, 0, 719992, 92487, 2981, 65536⟩
    (by decide) selected_cut_28548

theorem unmarked_context_11_23121_719993 : frontier 10 ⟨719993, by decide⟩
    (prefixCache 11 23121) (prefixPartial 11 23121) = false := by
  decide +kernel

theorem node_context_11_23121_719993 : EJMOriginalGlobalDAGData.nodes 10 ⟨719993, by decide⟩ =
    .split (coordinate 11) (![⟨719901, by decide⟩,⟨170504, by decide⟩,⟨719945, by decide⟩,⟨719992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23121_719993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23121 ⟨719993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23121
    ⟨719993, by decide⟩ (by decide) (![⟨719901, by decide⟩,⟨170504, by decide⟩,⟨719945, by decide⟩,⟨719992, by decide⟩]) unmarked_context_11_23121_719993 node_context_11_23121_719993
  intro a
  fin_cases a
  · exact context_12_92484_719901
  · exact context_12_92485_170504
  · exact context_12_92486_719945
  · exact context_12_92487_719992

theorem selected_cut_28549 : selected 9 ⟨720042, by decide⟩
    (prefixPartial 12 92488) = some ⟨12, 2, 0, 720042, 92488, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_92488_720042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92488 ⟨720042, by decide⟩ :=
  accepted_of_selected 12 92488 ⟨720042, by decide⟩ ⟨12, 2, 0, 720042, 92488, 3565, 65536⟩
    (by decide) selected_cut_28549

theorem selected_cut_28550 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 92489) = some ⟨12, 1, 0, 126371, 92489, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92489_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92489 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 92489 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 92489, 1, 65536⟩
    (by decide) selected_cut_28550

theorem selected_cut_28551 : selected 9 ⟨720089, by decide⟩
    (prefixPartial 12 92490) = some ⟨12, 2, 0, 720089, 92490, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_92490_720089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92490 ⟨720089, by decide⟩ :=
  accepted_of_selected 12 92490 ⟨720089, by decide⟩ ⟨12, 2, 0, 720089, 92490, 3469, 65536⟩
    (by decide) selected_cut_28551

theorem selected_cut_28552 : selected 9 ⟨720138, by decide⟩
    (prefixPartial 12 92491) = some ⟨12, 2, 0, 720138, 92491, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_92491_720138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92491 ⟨720138, by decide⟩ :=
  accepted_of_selected 12 92491 ⟨720138, by decide⟩ ⟨12, 2, 0, 720138, 92491, 3485, 65536⟩
    (by decide) selected_cut_28552

theorem unmarked_context_11_23122_720139 : frontier 10 ⟨720139, by decide⟩
    (prefixCache 11 23122) (prefixPartial 11 23122) = false := by
  decide +kernel

theorem node_context_11_23122_720139 : EJMOriginalGlobalDAGData.nodes 10 ⟨720139, by decide⟩ =
    .split (coordinate 11) (![⟨720042, by decide⟩,⟨126371, by decide⟩,⟨720089, by decide⟩,⟨720138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23122_720139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23122 ⟨720139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23122
    ⟨720139, by decide⟩ (by decide) (![⟨720042, by decide⟩,⟨126371, by decide⟩,⟨720089, by decide⟩,⟨720138, by decide⟩]) unmarked_context_11_23122_720139 node_context_11_23122_720139
  intro a
  fin_cases a
  · exact context_12_92488_720042
  · exact context_12_92489_126371
  · exact context_12_92490_720089
  · exact context_12_92491_720138

theorem selected_cut_28553 : selected 9 ⟨720185, by decide⟩
    (prefixPartial 12 92492) = some ⟨12, 2, 0, 720185, 92492, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_92492_720185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92492 ⟨720185, by decide⟩ :=
  accepted_of_selected 12 92492 ⟨720185, by decide⟩ ⟨12, 2, 0, 720185, 92492, 3701, 65536⟩
    (by decide) selected_cut_28553

theorem selected_cut_28554 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 92493) = some ⟨12, 1, 0, 320864, 92493, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92493_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92493 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 92493 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 92493, 1, 65536⟩
    (by decide) selected_cut_28554

theorem selected_cut_28555 : selected 9 ⟨720229, by decide⟩
    (prefixPartial 12 92494) = some ⟨12, 2, 0, 720229, 92494, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_92494_720229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92494 ⟨720229, by decide⟩ :=
  accepted_of_selected 12 92494 ⟨720229, by decide⟩ ⟨12, 2, 0, 720229, 92494, 3629, 65536⟩
    (by decide) selected_cut_28555

theorem selected_cut_28556 : selected 9 ⟨720273, by decide⟩
    (prefixPartial 12 92495) = some ⟨12, 2, 0, 720273, 92495, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_92495_720273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92495 ⟨720273, by decide⟩ :=
  accepted_of_selected 12 92495 ⟨720273, by decide⟩ ⟨12, 2, 0, 720273, 92495, 3701, 65536⟩
    (by decide) selected_cut_28556

theorem unmarked_context_11_23123_720274 : frontier 10 ⟨720274, by decide⟩
    (prefixCache 11 23123) (prefixPartial 11 23123) = false := by
  decide +kernel

theorem node_context_11_23123_720274 : EJMOriginalGlobalDAGData.nodes 10 ⟨720274, by decide⟩ =
    .split (coordinate 11) (![⟨720185, by decide⟩,⟨320864, by decide⟩,⟨720229, by decide⟩,⟨720273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23123_720274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23123 ⟨720274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23123
    ⟨720274, by decide⟩ (by decide) (![⟨720185, by decide⟩,⟨320864, by decide⟩,⟨720229, by decide⟩,⟨720273, by decide⟩]) unmarked_context_11_23123_720274 node_context_11_23123_720274
  intro a
  fin_cases a
  · exact context_12_92492_720185
  · exact context_12_92493_320864
  · exact context_12_92494_720229
  · exact context_12_92495_720273

theorem unmarked_context_10_5780_720275 : frontier 11 ⟨720275, by decide⟩
    (prefixCache 10 5780) (prefixPartial 10 5780) = false := by
  decide +kernel

theorem node_context_10_5780_720275 : EJMOriginalGlobalDAGData.nodes 11 ⟨720275, by decide⟩ =
    .split (coordinate 10) (![⟨719860, by decide⟩,⟨719993, by decide⟩,⟨720139, by decide⟩,⟨720274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5780_720275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5780 ⟨720275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5780
    ⟨720275, by decide⟩ (by decide) (![⟨719860, by decide⟩,⟨719993, by decide⟩,⟨720139, by decide⟩,⟨720274, by decide⟩]) unmarked_context_10_5780_720275 node_context_10_5780_720275
  intro a
  fin_cases a
  · exact context_11_23120_719860
  · exact context_11_23121_719993
  · exact context_11_23122_720139
  · exact context_11_23123_720274

theorem selected_cut_28557 : selected 9 ⟨720323, by decide⟩
    (prefixPartial 12 92496) = some ⟨12, 2, 0, 720323, 92496, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_92496_720323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92496 ⟨720323, by decide⟩ :=
  accepted_of_selected 12 92496 ⟨720323, by decide⟩ ⟨12, 2, 0, 720323, 92496, 3221, 65536⟩
    (by decide) selected_cut_28557

theorem selected_cut_28558 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92497) = some ⟨12, 1, 0, 642341, 92497, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92497_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92497 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92497 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92497, 1, 65536⟩
    (by decide) selected_cut_28558

theorem selected_cut_28559 : selected 9 ⟨720369, by decide⟩
    (prefixPartial 12 92498) = some ⟨12, 2, 0, 720369, 92498, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_92498_720369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92498 ⟨720369, by decide⟩ :=
  accepted_of_selected 12 92498 ⟨720369, by decide⟩ ⟨12, 2, 0, 720369, 92498, 3533, 65536⟩
    (by decide) selected_cut_28559

theorem selected_cut_28560 : selected 9 ⟨720416, by decide⟩
    (prefixPartial 12 92499) = some ⟨12, 2, 0, 720416, 92499, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_92499_720416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92499 ⟨720416, by decide⟩ :=
  accepted_of_selected 12 92499 ⟨720416, by decide⟩ ⟨12, 2, 0, 720416, 92499, 3449, 65536⟩
    (by decide) selected_cut_28560

theorem unmarked_context_11_23124_720417 : frontier 10 ⟨720417, by decide⟩
    (prefixCache 11 23124) (prefixPartial 11 23124) = false := by
  decide +kernel

theorem node_context_11_23124_720417 : EJMOriginalGlobalDAGData.nodes 10 ⟨720417, by decide⟩ =
    .split (coordinate 11) (![⟨720323, by decide⟩,⟨642341, by decide⟩,⟨720369, by decide⟩,⟨720416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23124_720417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23124 ⟨720417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23124
    ⟨720417, by decide⟩ (by decide) (![⟨720323, by decide⟩,⟨642341, by decide⟩,⟨720369, by decide⟩,⟨720416, by decide⟩]) unmarked_context_11_23124_720417 node_context_11_23124_720417
  intro a
  fin_cases a
  · exact context_12_92496_720323
  · exact context_12_92497_642341
  · exact context_12_92498_720369
  · exact context_12_92499_720416

theorem selected_cut_28561 : selected 9 ⟨720455, by decide⟩
    (prefixPartial 12 92500) = some ⟨12, 2, 0, 720455, 92500, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_92500_720455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92500 ⟨720455, by decide⟩ :=
  accepted_of_selected 12 92500 ⟨720455, by decide⟩ ⟨12, 2, 0, 720455, 92500, 2597, 65536⟩
    (by decide) selected_cut_28561

theorem selected_cut_28562 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92501) = some ⟨12, 1, 0, 642341, 92501, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92501_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92501 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92501 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92501, 1, 65536⟩
    (by decide) selected_cut_28562

theorem selected_cut_28563 : selected 9 ⟨720494, by decide⟩
    (prefixPartial 12 92502) = some ⟨12, 2, 0, 720494, 92502, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_92502_720494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92502 ⟨720494, by decide⟩ :=
  accepted_of_selected 12 92502 ⟨720494, by decide⟩ ⟨12, 2, 0, 720494, 92502, 2777, 65536⟩
    (by decide) selected_cut_28563

theorem selected_cut_28564 : selected 9 ⟨720534, by decide⟩
    (prefixPartial 12 92503) = some ⟨12, 2, 0, 720534, 92503, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_92503_720534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92503 ⟨720534, by decide⟩ :=
  accepted_of_selected 12 92503 ⟨720534, by decide⟩ ⟨12, 2, 0, 720534, 92503, 2721, 65536⟩
    (by decide) selected_cut_28564

theorem unmarked_context_11_23125_720535 : frontier 10 ⟨720535, by decide⟩
    (prefixCache 11 23125) (prefixPartial 11 23125) = false := by
  decide +kernel

theorem node_context_11_23125_720535 : EJMOriginalGlobalDAGData.nodes 10 ⟨720535, by decide⟩ =
    .split (coordinate 11) (![⟨720455, by decide⟩,⟨642341, by decide⟩,⟨720494, by decide⟩,⟨720534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23125_720535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23125 ⟨720535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23125
    ⟨720535, by decide⟩ (by decide) (![⟨720455, by decide⟩,⟨642341, by decide⟩,⟨720494, by decide⟩,⟨720534, by decide⟩]) unmarked_context_11_23125_720535 node_context_11_23125_720535
  intro a
  fin_cases a
  · exact context_12_92500_720455
  · exact context_12_92501_642341
  · exact context_12_92502_720494
  · exact context_12_92503_720534

theorem selected_cut_28565 : selected 9 ⟨720572, by decide⟩
    (prefixPartial 12 92504) = some ⟨12, 2, 0, 720572, 92504, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_92504_720572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92504 ⟨720572, by decide⟩ :=
  accepted_of_selected 12 92504 ⟨720572, by decide⟩ ⟨12, 2, 0, 720572, 92504, 2973, 65536⟩
    (by decide) selected_cut_28565

theorem selected_cut_28566 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92505) = some ⟨12, 1, 0, 642341, 92505, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92505_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92505 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92505 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92505, 1, 65536⟩
    (by decide) selected_cut_28566

theorem selected_cut_28567 : selected 9 ⟨720614, by decide⟩
    (prefixPartial 12 92506) = some ⟨12, 2, 0, 720614, 92506, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_92506_720614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92506 ⟨720614, by decide⟩ :=
  accepted_of_selected 12 92506 ⟨720614, by decide⟩ ⟨12, 2, 0, 720614, 92506, 2953, 65536⟩
    (by decide) selected_cut_28567

theorem selected_cut_28568 : selected 9 ⟨720652, by decide⟩
    (prefixPartial 12 92507) = some ⟨12, 2, 0, 720652, 92507, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_92507_720652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92507 ⟨720652, by decide⟩ :=
  accepted_of_selected 12 92507 ⟨720652, by decide⟩ ⟨12, 2, 0, 720652, 92507, 2817, 65536⟩
    (by decide) selected_cut_28568

theorem unmarked_context_11_23126_720653 : frontier 10 ⟨720653, by decide⟩
    (prefixCache 11 23126) (prefixPartial 11 23126) = false := by
  decide +kernel

theorem node_context_11_23126_720653 : EJMOriginalGlobalDAGData.nodes 10 ⟨720653, by decide⟩ =
    .split (coordinate 11) (![⟨720572, by decide⟩,⟨642341, by decide⟩,⟨720614, by decide⟩,⟨720652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23126_720653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23126 ⟨720653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23126
    ⟨720653, by decide⟩ (by decide) (![⟨720572, by decide⟩,⟨642341, by decide⟩,⟨720614, by decide⟩,⟨720652, by decide⟩]) unmarked_context_11_23126_720653 node_context_11_23126_720653
  intro a
  fin_cases a
  · exact context_12_92504_720572
  · exact context_12_92505_642341
  · exact context_12_92506_720614
  · exact context_12_92507_720652

theorem selected_cut_28569 : selected 9 ⟨720689, by decide⟩
    (prefixPartial 12 92508) = some ⟨12, 2, 0, 720689, 92508, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_92508_720689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92508 ⟨720689, by decide⟩ :=
  accepted_of_selected 12 92508 ⟨720689, by decide⟩ ⟨12, 2, 0, 720689, 92508, 3077, 65536⟩
    (by decide) selected_cut_28569

theorem selected_cut_28570 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92509) = some ⟨12, 1, 0, 642341, 92509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92509_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92509 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92509 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92509, 1, 65536⟩
    (by decide) selected_cut_28570

theorem selected_cut_28571 : selected 9 ⟨720727, by decide⟩
    (prefixPartial 12 92510) = some ⟨12, 2, 0, 720727, 92510, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_92510_720727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92510 ⟨720727, by decide⟩ :=
  accepted_of_selected 12 92510 ⟨720727, by decide⟩ ⟨12, 2, 0, 720727, 92510, 3009, 65536⟩
    (by decide) selected_cut_28571

theorem selected_cut_28572 : selected 9 ⟨720766, by decide⟩
    (prefixPartial 12 92511) = some ⟨12, 2, 0, 720766, 92511, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_92511_720766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92511 ⟨720766, by decide⟩ :=
  accepted_of_selected 12 92511 ⟨720766, by decide⟩ ⟨12, 2, 0, 720766, 92511, 3001, 65536⟩
    (by decide) selected_cut_28572

theorem unmarked_context_11_23127_720767 : frontier 10 ⟨720767, by decide⟩
    (prefixCache 11 23127) (prefixPartial 11 23127) = false := by
  decide +kernel

theorem node_context_11_23127_720767 : EJMOriginalGlobalDAGData.nodes 10 ⟨720767, by decide⟩ =
    .split (coordinate 11) (![⟨720689, by decide⟩,⟨642341, by decide⟩,⟨720727, by decide⟩,⟨720766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23127_720767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23127 ⟨720767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23127
    ⟨720767, by decide⟩ (by decide) (![⟨720689, by decide⟩,⟨642341, by decide⟩,⟨720727, by decide⟩,⟨720766, by decide⟩]) unmarked_context_11_23127_720767 node_context_11_23127_720767
  intro a
  fin_cases a
  · exact context_12_92508_720689
  · exact context_12_92509_642341
  · exact context_12_92510_720727
  · exact context_12_92511_720766

theorem unmarked_context_10_5781_720768 : frontier 11 ⟨720768, by decide⟩
    (prefixCache 10 5781) (prefixPartial 10 5781) = false := by
  decide +kernel

theorem node_context_10_5781_720768 : EJMOriginalGlobalDAGData.nodes 11 ⟨720768, by decide⟩ =
    .split (coordinate 10) (![⟨720417, by decide⟩,⟨720535, by decide⟩,⟨720653, by decide⟩,⟨720767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5781_720768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5781 ⟨720768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5781
    ⟨720768, by decide⟩ (by decide) (![⟨720417, by decide⟩,⟨720535, by decide⟩,⟨720653, by decide⟩,⟨720767, by decide⟩]) unmarked_context_10_5781_720768 node_context_10_5781_720768
  intro a
  fin_cases a
  · exact context_11_23124_720417
  · exact context_11_23125_720535
  · exact context_11_23126_720653
  · exact context_11_23127_720767

theorem selected_cut_28573 : selected 9 ⟨720805, by decide⟩
    (prefixPartial 12 92512) = some ⟨12, 2, 0, 720805, 92512, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_92512_720805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92512 ⟨720805, by decide⟩ :=
  accepted_of_selected 12 92512 ⟨720805, by decide⟩ ⟨12, 2, 0, 720805, 92512, 3173, 65536⟩
    (by decide) selected_cut_28573

theorem selected_cut_28574 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 92513) = some ⟨12, 1, 0, 126884, 92513, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92513_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92513 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 92513 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 92513, 1, 65536⟩
    (by decide) selected_cut_28574

theorem selected_cut_28575 : selected 9 ⟨720848, by decide⟩
    (prefixPartial 12 92514) = some ⟨12, 2, 0, 720848, 92514, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_92514_720848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92514 ⟨720848, by decide⟩ :=
  accepted_of_selected 12 92514 ⟨720848, by decide⟩ ⟨12, 2, 0, 720848, 92514, 3393, 65536⟩
    (by decide) selected_cut_28575

theorem selected_cut_28576 : selected 9 ⟨720886, by decide⟩
    (prefixPartial 12 92515) = some ⟨12, 2, 0, 720886, 92515, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_92515_720886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92515 ⟨720886, by decide⟩ :=
  accepted_of_selected 12 92515 ⟨720886, by decide⟩ ⟨12, 2, 0, 720886, 92515, 3173, 65536⟩
    (by decide) selected_cut_28576

theorem unmarked_context_11_23128_720887 : frontier 10 ⟨720887, by decide⟩
    (prefixCache 11 23128) (prefixPartial 11 23128) = false := by
  decide +kernel

theorem node_context_11_23128_720887 : EJMOriginalGlobalDAGData.nodes 10 ⟨720887, by decide⟩ =
    .split (coordinate 11) (![⟨720805, by decide⟩,⟨126884, by decide⟩,⟨720848, by decide⟩,⟨720886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23128_720887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23128 ⟨720887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23128
    ⟨720887, by decide⟩ (by decide) (![⟨720805, by decide⟩,⟨126884, by decide⟩,⟨720848, by decide⟩,⟨720886, by decide⟩]) unmarked_context_11_23128_720887 node_context_11_23128_720887
  intro a
  fin_cases a
  · exact context_12_92512_720805
  · exact context_12_92513_126884
  · exact context_12_92514_720848
  · exact context_12_92515_720886

theorem selected_cut_28577 : selected 9 ⟨720920, by decide⟩
    (prefixPartial 12 92516) = some ⟨12, 2, 0, 720920, 92516, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_92516_720920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92516 ⟨720920, by decide⟩ :=
  accepted_of_selected 12 92516 ⟨720920, by decide⟩ ⟨12, 2, 0, 720920, 92516, 2529, 65536⟩
    (by decide) selected_cut_28577

theorem selected_cut_28578 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 92517) = some ⟨12, 1, 0, 365907, 92517, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92517_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92517 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 92517 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 92517, 1, 65536⟩
    (by decide) selected_cut_28578

theorem selected_cut_28579 : selected 9 ⟨720954, by decide⟩
    (prefixPartial 12 92518) = some ⟨12, 2, 0, 720954, 92518, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_92518_720954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92518 ⟨720954, by decide⟩ :=
  accepted_of_selected 12 92518 ⟨720954, by decide⟩ ⟨12, 2, 0, 720954, 92518, 2521, 65536⟩
    (by decide) selected_cut_28579

theorem selected_cut_28580 : selected 9 ⟨720989, by decide⟩
    (prefixPartial 12 92519) = some ⟨12, 2, 0, 720989, 92519, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_92519_720989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92519 ⟨720989, by decide⟩ :=
  accepted_of_selected 12 92519 ⟨720989, by decide⟩ ⟨12, 2, 0, 720989, 92519, 2369, 65536⟩
    (by decide) selected_cut_28580

theorem unmarked_context_11_23129_720990 : frontier 10 ⟨720990, by decide⟩
    (prefixCache 11 23129) (prefixPartial 11 23129) = false := by
  decide +kernel

theorem node_context_11_23129_720990 : EJMOriginalGlobalDAGData.nodes 10 ⟨720990, by decide⟩ =
    .split (coordinate 11) (![⟨720920, by decide⟩,⟨365907, by decide⟩,⟨720954, by decide⟩,⟨720989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23129_720990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23129 ⟨720990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23129
    ⟨720990, by decide⟩ (by decide) (![⟨720920, by decide⟩,⟨365907, by decide⟩,⟨720954, by decide⟩,⟨720989, by decide⟩]) unmarked_context_11_23129_720990 node_context_11_23129_720990
  intro a
  fin_cases a
  · exact context_12_92516_720920
  · exact context_12_92517_365907
  · exact context_12_92518_720954
  · exact context_12_92519_720989

theorem selected_cut_28581 : selected 9 ⟨721041, by decide⟩
    (prefixPartial 12 92520) = some ⟨12, 2, 0, 721041, 92520, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_92520_721041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92520 ⟨721041, by decide⟩ :=
  accepted_of_selected 12 92520 ⟨721041, by decide⟩ ⟨12, 2, 0, 721041, 92520, 3757, 65536⟩
    (by decide) selected_cut_28581

theorem selected_cut_28582 : selected 9 ⟨364560, by decide⟩
    (prefixPartial 12 92521) = some ⟨12, 1, 0, 364560, 92521, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92521_364560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92521 ⟨364560, by decide⟩ :=
  accepted_of_selected 12 92521 ⟨364560, by decide⟩ ⟨12, 1, 0, 364560, 92521, 1, 65536⟩
    (by decide) selected_cut_28582

theorem selected_cut_28583 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 92522) = some ⟨12, 1, 0, 474208, 92522, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92522_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92522 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 92522 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 92522, 1, 65536⟩
    (by decide) selected_cut_28583

theorem selected_cut_28584 : selected 9 ⟨721088, by decide⟩
    (prefixPartial 12 92523) = some ⟨12, 2, 0, 721088, 92523, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_92523_721088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92523 ⟨721088, by decide⟩ :=
  accepted_of_selected 12 92523 ⟨721088, by decide⟩ ⟨12, 2, 0, 721088, 92523, 3749, 65536⟩
    (by decide) selected_cut_28584

theorem unmarked_context_11_23130_721089 : frontier 10 ⟨721089, by decide⟩
    (prefixCache 11 23130) (prefixPartial 11 23130) = false := by
  decide +kernel

theorem node_context_11_23130_721089 : EJMOriginalGlobalDAGData.nodes 10 ⟨721089, by decide⟩ =
    .split (coordinate 11) (![⟨721041, by decide⟩,⟨364560, by decide⟩,⟨474208, by decide⟩,⟨721088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23130_721089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23130 ⟨721089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23130
    ⟨721089, by decide⟩ (by decide) (![⟨721041, by decide⟩,⟨364560, by decide⟩,⟨474208, by decide⟩,⟨721088, by decide⟩]) unmarked_context_11_23130_721089 node_context_11_23130_721089
  intro a
  fin_cases a
  · exact context_12_92520_721041
  · exact context_12_92521_364560
  · exact context_12_92522_474208
  · exact context_12_92523_721088

theorem selected_cut_28585 : selected 9 ⟨721120, by decide⟩
    (prefixPartial 12 92524) = some ⟨12, 2, 0, 721120, 92524, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_92524_721120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92524 ⟨721120, by decide⟩ :=
  accepted_of_selected 12 92524 ⟨721120, by decide⟩ ⟨12, 2, 0, 721120, 92524, 3013, 65536⟩
    (by decide) selected_cut_28585

theorem selected_cut_28586 : selected 9 ⟨691822, by decide⟩
    (prefixPartial 12 92525) = some ⟨12, 1, 0, 691822, 92525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92525_691822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92525 ⟨691822, by decide⟩ :=
  accepted_of_selected 12 92525 ⟨691822, by decide⟩ ⟨12, 1, 0, 691822, 92525, 1, 65536⟩
    (by decide) selected_cut_28586

theorem selected_cut_28587 : selected 9 ⟨721158, by decide⟩
    (prefixPartial 12 92526) = some ⟨12, 2, 0, 721158, 92526, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_92526_721158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92526 ⟨721158, by decide⟩ :=
  accepted_of_selected 12 92526 ⟨721158, by decide⟩ ⟨12, 2, 0, 721158, 92526, 2921, 65536⟩
    (by decide) selected_cut_28587

theorem selected_cut_28588 : selected 9 ⟨721194, by decide⟩
    (prefixPartial 12 92527) = some ⟨12, 2, 0, 721194, 92527, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_92527_721194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92527 ⟨721194, by decide⟩ :=
  accepted_of_selected 12 92527 ⟨721194, by decide⟩ ⟨12, 2, 0, 721194, 92527, 2841, 65536⟩
    (by decide) selected_cut_28588

theorem unmarked_context_11_23131_721195 : frontier 10 ⟨721195, by decide⟩
    (prefixCache 11 23131) (prefixPartial 11 23131) = false := by
  decide +kernel

theorem node_context_11_23131_721195 : EJMOriginalGlobalDAGData.nodes 10 ⟨721195, by decide⟩ =
    .split (coordinate 11) (![⟨721120, by decide⟩,⟨691822, by decide⟩,⟨721158, by decide⟩,⟨721194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23131_721195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23131 ⟨721195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23131
    ⟨721195, by decide⟩ (by decide) (![⟨721120, by decide⟩,⟨691822, by decide⟩,⟨721158, by decide⟩,⟨721194, by decide⟩]) unmarked_context_11_23131_721195 node_context_11_23131_721195
  intro a
  fin_cases a
  · exact context_12_92524_721120
  · exact context_12_92525_691822
  · exact context_12_92526_721158
  · exact context_12_92527_721194

theorem unmarked_context_10_5782_721196 : frontier 11 ⟨721196, by decide⟩
    (prefixCache 10 5782) (prefixPartial 10 5782) = false := by
  decide +kernel

theorem node_context_10_5782_721196 : EJMOriginalGlobalDAGData.nodes 11 ⟨721196, by decide⟩ =
    .split (coordinate 10) (![⟨720887, by decide⟩,⟨720990, by decide⟩,⟨721089, by decide⟩,⟨721195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5782_721196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5782 ⟨721196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5782
    ⟨721196, by decide⟩ (by decide) (![⟨720887, by decide⟩,⟨720990, by decide⟩,⟨721089, by decide⟩,⟨721195, by decide⟩]) unmarked_context_10_5782_721196 node_context_10_5782_721196
  intro a
  fin_cases a
  · exact context_11_23128_720887
  · exact context_11_23129_720990
  · exact context_11_23130_721089
  · exact context_11_23131_721195

theorem selected_cut_28589 : selected 9 ⟨721232, by decide⟩
    (prefixPartial 12 92528) = some ⟨12, 2, 0, 721232, 92528, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_92528_721232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92528 ⟨721232, by decide⟩ :=
  accepted_of_selected 12 92528 ⟨721232, by decide⟩ ⟨12, 2, 0, 721232, 92528, 3329, 65536⟩
    (by decide) selected_cut_28589

theorem selected_cut_28590 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 92529) = some ⟨12, 1, 0, 126884, 92529, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92529_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92529 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 92529 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 92529, 1, 65536⟩
    (by decide) selected_cut_28590

theorem selected_cut_28591 : selected 9 ⟨721276, by decide⟩
    (prefixPartial 12 92530) = some ⟨12, 2, 0, 721276, 92530, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_92530_721276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92530 ⟨721276, by decide⟩ :=
  accepted_of_selected 12 92530 ⟨721276, by decide⟩ ⟨12, 2, 0, 721276, 92530, 3541, 65536⟩
    (by decide) selected_cut_28591

theorem selected_cut_28592 : selected 9 ⟨721314, by decide⟩
    (prefixPartial 12 92531) = some ⟨12, 2, 0, 721314, 92531, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_92531_721314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92531 ⟨721314, by decide⟩ :=
  accepted_of_selected 12 92531 ⟨721314, by decide⟩ ⟨12, 2, 0, 721314, 92531, 3421, 65536⟩
    (by decide) selected_cut_28592

theorem unmarked_context_11_23132_721315 : frontier 10 ⟨721315, by decide⟩
    (prefixCache 11 23132) (prefixPartial 11 23132) = false := by
  decide +kernel

theorem node_context_11_23132_721315 : EJMOriginalGlobalDAGData.nodes 10 ⟨721315, by decide⟩ =
    .split (coordinate 11) (![⟨721232, by decide⟩,⟨126884, by decide⟩,⟨721276, by decide⟩,⟨721314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23132_721315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23132 ⟨721315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23132
    ⟨721315, by decide⟩ (by decide) (![⟨721232, by decide⟩,⟨126884, by decide⟩,⟨721276, by decide⟩,⟨721314, by decide⟩]) unmarked_context_11_23132_721315 node_context_11_23132_721315
  intro a
  fin_cases a
  · exact context_12_92528_721232
  · exact context_12_92529_126884
  · exact context_12_92530_721276
  · exact context_12_92531_721314

theorem selected_cut_28593 : selected 9 ⟨721350, by decide⟩
    (prefixPartial 12 92532) = some ⟨12, 2, 0, 721350, 92532, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_92532_721350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92532 ⟨721350, by decide⟩ :=
  accepted_of_selected 12 92532 ⟨721350, by decide⟩ ⟨12, 2, 0, 721350, 92532, 2673, 65536⟩
    (by decide) selected_cut_28593

theorem selected_cut_28594 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 92533) = some ⟨12, 1, 0, 642794, 92533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92533_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92533 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 92533 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 92533, 1, 65536⟩
    (by decide) selected_cut_28594

theorem selected_cut_28595 : selected 9 ⟨721387, by decide⟩
    (prefixPartial 12 92534) = some ⟨12, 2, 0, 721387, 92534, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_92534_721387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92534 ⟨721387, by decide⟩ :=
  accepted_of_selected 12 92534 ⟨721387, by decide⟩ ⟨12, 2, 0, 721387, 92534, 2733, 65536⟩
    (by decide) selected_cut_28595

theorem selected_cut_28596 : selected 9 ⟨721416, by decide⟩
    (prefixPartial 12 92535) = some ⟨12, 2, 0, 721416, 92535, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_92535_721416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92535 ⟨721416, by decide⟩ :=
  accepted_of_selected 12 92535 ⟨721416, by decide⟩ ⟨12, 2, 0, 721416, 92535, 2645, 65536⟩
    (by decide) selected_cut_28596

theorem unmarked_context_11_23133_721417 : frontier 10 ⟨721417, by decide⟩
    (prefixCache 11 23133) (prefixPartial 11 23133) = false := by
  decide +kernel

theorem node_context_11_23133_721417 : EJMOriginalGlobalDAGData.nodes 10 ⟨721417, by decide⟩ =
    .split (coordinate 11) (![⟨721350, by decide⟩,⟨642794, by decide⟩,⟨721387, by decide⟩,⟨721416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23133_721417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23133 ⟨721417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23133
    ⟨721417, by decide⟩ (by decide) (![⟨721350, by decide⟩,⟨642794, by decide⟩,⟨721387, by decide⟩,⟨721416, by decide⟩]) unmarked_context_11_23133_721417 node_context_11_23133_721417
  intro a
  fin_cases a
  · exact context_12_92532_721350
  · exact context_12_92533_642794
  · exact context_12_92534_721387
  · exact context_12_92535_721416

theorem selected_cut_28597 : selected 9 ⟨721452, by decide⟩
    (prefixPartial 12 92536) = some ⟨12, 2, 0, 721452, 92536, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_92536_721452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92536 ⟨721452, by decide⟩ :=
  accepted_of_selected 12 92536 ⟨721452, by decide⟩ ⟨12, 2, 0, 721452, 92536, 3033, 65536⟩
    (by decide) selected_cut_28597

theorem selected_cut_28598 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 92537) = some ⟨12, 1, 0, 691709, 92537, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92537_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92537 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 92537 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 92537, 1, 65536⟩
    (by decide) selected_cut_28598

theorem selected_cut_28599 : selected 9 ⟨721488, by decide⟩
    (prefixPartial 12 92538) = some ⟨12, 2, 0, 721488, 92538, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_92538_721488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92538 ⟨721488, by decide⟩ :=
  accepted_of_selected 12 92538 ⟨721488, by decide⟩ ⟨12, 2, 0, 721488, 92538, 2969, 65536⟩
    (by decide) selected_cut_28599

theorem selected_cut_28600 : selected 9 ⟨721525, by decide⟩
    (prefixPartial 12 92539) = some ⟨12, 2, 0, 721525, 92539, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_92539_721525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92539 ⟨721525, by decide⟩ :=
  accepted_of_selected 12 92539 ⟨721525, by decide⟩ ⟨12, 2, 0, 721525, 92539, 2905, 65536⟩
    (by decide) selected_cut_28600

theorem unmarked_context_11_23134_721526 : frontier 10 ⟨721526, by decide⟩
    (prefixCache 11 23134) (prefixPartial 11 23134) = false := by
  decide +kernel

theorem node_context_11_23134_721526 : EJMOriginalGlobalDAGData.nodes 10 ⟨721526, by decide⟩ =
    .split (coordinate 11) (![⟨721452, by decide⟩,⟨691709, by decide⟩,⟨721488, by decide⟩,⟨721525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23134_721526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23134 ⟨721526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23134
    ⟨721526, by decide⟩ (by decide) (![⟨721452, by decide⟩,⟨691709, by decide⟩,⟨721488, by decide⟩,⟨721525, by decide⟩]) unmarked_context_11_23134_721526 node_context_11_23134_721526
  intro a
  fin_cases a
  · exact context_12_92536_721452
  · exact context_12_92537_691709
  · exact context_12_92538_721488
  · exact context_12_92539_721525

theorem selected_cut_28601 : selected 9 ⟨721559, by decide⟩
    (prefixPartial 12 92540) = some ⟨12, 2, 0, 721559, 92540, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_92540_721559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92540 ⟨721559, by decide⟩ :=
  accepted_of_selected 12 92540 ⟨721559, by decide⟩ ⟨12, 2, 0, 721559, 92540, 3029, 65536⟩
    (by decide) selected_cut_28601

theorem selected_cut_28602 : selected 9 ⟨691822, by decide⟩
    (prefixPartial 12 92541) = some ⟨12, 1, 0, 691822, 92541, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92541_691822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92541 ⟨691822, by decide⟩ :=
  accepted_of_selected 12 92541 ⟨691822, by decide⟩ ⟨12, 1, 0, 691822, 92541, 1, 65536⟩
    (by decide) selected_cut_28602

theorem selected_cut_28603 : selected 9 ⟨721593, by decide⟩
    (prefixPartial 12 92542) = some ⟨12, 2, 0, 721593, 92542, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_92542_721593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92542 ⟨721593, by decide⟩ :=
  accepted_of_selected 12 92542 ⟨721593, by decide⟩ ⟨12, 2, 0, 721593, 92542, 2941, 65536⟩
    (by decide) selected_cut_28603

theorem selected_cut_28604 : selected 9 ⟨721627, by decide⟩
    (prefixPartial 12 92543) = some ⟨12, 2, 0, 721627, 92543, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_92543_721627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92543 ⟨721627, by decide⟩ :=
  accepted_of_selected 12 92543 ⟨721627, by decide⟩ ⟨12, 2, 0, 721627, 92543, 2901, 65536⟩
    (by decide) selected_cut_28604

theorem unmarked_context_11_23135_721628 : frontier 10 ⟨721628, by decide⟩
    (prefixCache 11 23135) (prefixPartial 11 23135) = false := by
  decide +kernel

theorem node_context_11_23135_721628 : EJMOriginalGlobalDAGData.nodes 10 ⟨721628, by decide⟩ =
    .split (coordinate 11) (![⟨721559, by decide⟩,⟨691822, by decide⟩,⟨721593, by decide⟩,⟨721627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23135_721628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23135 ⟨721628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23135
    ⟨721628, by decide⟩ (by decide) (![⟨721559, by decide⟩,⟨691822, by decide⟩,⟨721593, by decide⟩,⟨721627, by decide⟩]) unmarked_context_11_23135_721628 node_context_11_23135_721628
  intro a
  fin_cases a
  · exact context_12_92540_721559
  · exact context_12_92541_691822
  · exact context_12_92542_721593
  · exact context_12_92543_721627

theorem unmarked_context_10_5783_721629 : frontier 11 ⟨721629, by decide⟩
    (prefixCache 10 5783) (prefixPartial 10 5783) = false := by
  decide +kernel

theorem node_context_10_5783_721629 : EJMOriginalGlobalDAGData.nodes 11 ⟨721629, by decide⟩ =
    .split (coordinate 10) (![⟨721315, by decide⟩,⟨721417, by decide⟩,⟨721526, by decide⟩,⟨721628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5783_721629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5783 ⟨721629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5783
    ⟨721629, by decide⟩ (by decide) (![⟨721315, by decide⟩,⟨721417, by decide⟩,⟨721526, by decide⟩,⟨721628, by decide⟩]) unmarked_context_10_5783_721629 node_context_10_5783_721629
  intro a
  fin_cases a
  · exact context_11_23132_721315
  · exact context_11_23133_721417
  · exact context_11_23134_721526
  · exact context_11_23135_721628

theorem unmarked_context_9_1445_721630 : frontier 12 ⟨721630, by decide⟩
    (prefixCache 9 1445) (prefixPartial 9 1445) = false := by
  decide +kernel

theorem node_context_9_1445_721630 : EJMOriginalGlobalDAGData.nodes 12 ⟨721630, by decide⟩ =
    .split (coordinate 9) (![⟨720275, by decide⟩,⟨720768, by decide⟩,⟨721196, by decide⟩,⟨721629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1445_721630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1445 ⟨721630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1445
    ⟨721630, by decide⟩ (by decide) (![⟨720275, by decide⟩,⟨720768, by decide⟩,⟨721196, by decide⟩,⟨721629, by decide⟩]) unmarked_context_9_1445_721630 node_context_9_1445_721630
  intro a
  fin_cases a
  · exact context_10_5780_720275
  · exact context_10_5781_720768
  · exact context_10_5782_721196
  · exact context_10_5783_721629

theorem selected_cut_28605 : selected 9 ⟨721657, by decide⟩
    (prefixPartial 12 92544) = some ⟨12, 2, 0, 721657, 92544, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_92544_721657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92544 ⟨721657, by decide⟩ :=
  accepted_of_selected 12 92544 ⟨721657, by decide⟩ ⟨12, 2, 0, 721657, 92544, 2289, 65536⟩
    (by decide) selected_cut_28605

theorem selected_cut_28606 : selected 9 ⟨721686, by decide⟩
    (prefixPartial 12 92545) = some ⟨12, 2, 0, 721686, 92545, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_92545_721686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92545 ⟨721686, by decide⟩ :=
  accepted_of_selected 12 92545 ⟨721686, by decide⟩ ⟨12, 2, 0, 721686, 92545, 1841, 65536⟩
    (by decide) selected_cut_28606

theorem selected_cut_28607 : selected 9 ⟨721718, by decide⟩
    (prefixPartial 12 92546) = some ⟨12, 2, 0, 721718, 92546, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_92546_721718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92546 ⟨721718, by decide⟩ :=
  accepted_of_selected 12 92546 ⟨721718, by decide⟩ ⟨12, 2, 0, 721718, 92546, 2621, 65536⟩
    (by decide) selected_cut_28607

theorem selected_cut_28608 : selected 9 ⟨721741, by decide⟩
    (prefixPartial 12 92547) = some ⟨12, 2, 0, 721741, 92547, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_92547_721741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92547 ⟨721741, by decide⟩ :=
  accepted_of_selected 12 92547 ⟨721741, by decide⟩ ⟨12, 2, 0, 721741, 92547, 2169, 65536⟩
    (by decide) selected_cut_28608

theorem unmarked_context_11_23136_721742 : frontier 10 ⟨721742, by decide⟩
    (prefixCache 11 23136) (prefixPartial 11 23136) = false := by
  decide +kernel

theorem node_context_11_23136_721742 : EJMOriginalGlobalDAGData.nodes 10 ⟨721742, by decide⟩ =
    .split (coordinate 11) (![⟨721657, by decide⟩,⟨721686, by decide⟩,⟨721718, by decide⟩,⟨721741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23136_721742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23136 ⟨721742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23136
    ⟨721742, by decide⟩ (by decide) (![⟨721657, by decide⟩,⟨721686, by decide⟩,⟨721718, by decide⟩,⟨721741, by decide⟩]) unmarked_context_11_23136_721742 node_context_11_23136_721742
  intro a
  fin_cases a
  · exact context_12_92544_721657
  · exact context_12_92545_721686
  · exact context_12_92546_721718
  · exact context_12_92547_721741

theorem selected_cut_28609 : selected 9 ⟨721770, by decide⟩
    (prefixPartial 12 92548) = some ⟨12, 2, 0, 721770, 92548, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_92548_721770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92548 ⟨721770, by decide⟩ :=
  accepted_of_selected 12 92548 ⟨721770, by decide⟩ ⟨12, 2, 0, 721770, 92548, 2057, 65536⟩
    (by decide) selected_cut_28609

theorem selected_cut_28610 : selected 9 ⟨721771, by decide⟩
    (prefixPartial 12 92549) = some ⟨12, 1, 0, 721771, 92549, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92549_721771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92549 ⟨721771, by decide⟩ :=
  accepted_of_selected 12 92549 ⟨721771, by decide⟩ ⟨12, 1, 0, 721771, 92549, 1, 65536⟩
    (by decide) selected_cut_28610

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
