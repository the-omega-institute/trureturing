/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover216
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20835 : selected 8 ⟨533194, by decide⟩
    (prefixPartial 13 298119) = some ⟨13, 2, 0, 533194, 298119, 577, 16384⟩ := by
  decide +kernel

theorem context_13_298119_533194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298119 ⟨533194, by decide⟩ :=
  accepted_of_selected 13 298119 ⟨533194, by decide⟩ ⟨13, 2, 0, 533194, 298119, 577, 16384⟩
    (by decide) selected_cut_20835

theorem unmarked_context_12_74529_533195 : frontier 9 ⟨533195, by decide⟩
    (prefixCache 12 74529) (prefixPartial 12 74529) = false := by
  decide +kernel

theorem node_context_12_74529_533195 : EJMOriginalGlobalDAGData.nodes 9 ⟨533195, by decide⟩ =
    .split (coordinate 12) (![⟨533140, by decide⟩,⟨533173, by decide⟩,⟨533189, by decide⟩,⟨533194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74529_533195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74529 ⟨533195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74529
    ⟨533195, by decide⟩ (by decide) (![⟨533140, by decide⟩,⟨533173, by decide⟩,⟨533189, by decide⟩,⟨533194, by decide⟩]) unmarked_context_12_74529_533195 node_context_12_74529_533195
  intro a
  fin_cases a
  · exact context_13_298116_533140
  · exact context_13_298117_533173
  · exact context_13_298118_533189
  · exact context_13_298119_533194

theorem selected_cut_20836 : selected 9 ⟨533270, by decide⟩
    (prefixPartial 12 74530) = some ⟨12, 2, 0, 533270, 74530, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_74530_533270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74530 ⟨533270, by decide⟩ :=
  accepted_of_selected 12 74530 ⟨533270, by decide⟩ ⟨12, 2, 0, 533270, 74530, 4093, 65536⟩
    (by decide) selected_cut_20836

theorem selected_cut_20837 : selected 9 ⟨533347, by decide⟩
    (prefixPartial 12 74531) = some ⟨12, 2, 0, 533347, 74531, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_74531_533347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74531 ⟨533347, by decide⟩ :=
  accepted_of_selected 12 74531 ⟨533347, by decide⟩ ⟨12, 2, 0, 533347, 74531, 3741, 65536⟩
    (by decide) selected_cut_20837

theorem unmarked_context_11_18632_533348 : frontier 10 ⟨533348, by decide⟩
    (prefixCache 11 18632) (prefixPartial 11 18632) = false := by
  decide +kernel

theorem node_context_11_18632_533348 : EJMOriginalGlobalDAGData.nodes 10 ⟨533348, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨533195, by decide⟩,⟨533270, by decide⟩,⟨533347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18632_533348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18632 ⟨533348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18632
    ⟨533348, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨533195, by decide⟩,⟨533270, by decide⟩,⟨533347, by decide⟩]) unmarked_context_11_18632_533348 node_context_11_18632_533348
  intro a
  fin_cases a
  · exact context_12_74528_435790
  · exact context_12_74529_533195
  · exact context_12_74530_533270
  · exact context_12_74531_533347

theorem selected_cut_20838 : selected 8 ⟨533385, by decide⟩
    (prefixPartial 13 298128) = some ⟨13, 2, 0, 533385, 298128, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_298128_533385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298128 ⟨533385, by decide⟩ :=
  accepted_of_selected 13 298128 ⟨533385, by decide⟩ ⟨13, 2, 0, 533385, 298128, 1317, 16384⟩
    (by decide) selected_cut_20838

theorem selected_cut_20839 : selected 8 ⟨533452, by decide⟩
    (prefixPartial 13 298129) = some ⟨13, 2, 0, 533452, 298129, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_298129_533452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298129 ⟨533452, by decide⟩ :=
  accepted_of_selected 13 298129 ⟨533452, by decide⟩ ⟨13, 2, 0, 533452, 298129, 2725, 16384⟩
    (by decide) selected_cut_20839

theorem selected_cut_20840 : selected 8 ⟨533481, by decide⟩
    (prefixPartial 13 298130) = some ⟨13, 2, 0, 533481, 298130, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_298130_533481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298130 ⟨533481, by decide⟩ :=
  accepted_of_selected 13 298130 ⟨533481, by decide⟩ ⟨13, 2, 0, 533481, 298130, 1625, 16384⟩
    (by decide) selected_cut_20840

theorem selected_cut_20841 : selected 8 ⟨533487, by decide⟩
    (prefixPartial 13 298131) = some ⟨13, 2, 0, 533487, 298131, 961, 16384⟩ := by
  decide +kernel

theorem context_13_298131_533487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298131 ⟨533487, by decide⟩ :=
  accepted_of_selected 13 298131 ⟨533487, by decide⟩ ⟨13, 2, 0, 533487, 298131, 961, 16384⟩
    (by decide) selected_cut_20841

theorem unmarked_context_12_74532_533488 : frontier 9 ⟨533488, by decide⟩
    (prefixCache 12 74532) (prefixPartial 12 74532) = false := by
  decide +kernel

theorem node_context_12_74532_533488 : EJMOriginalGlobalDAGData.nodes 9 ⟨533488, by decide⟩ =
    .split (coordinate 12) (![⟨533385, by decide⟩,⟨533452, by decide⟩,⟨533481, by decide⟩,⟨533487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74532_533488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74532 ⟨533488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74532
    ⟨533488, by decide⟩ (by decide) (![⟨533385, by decide⟩,⟨533452, by decide⟩,⟨533481, by decide⟩,⟨533487, by decide⟩]) unmarked_context_12_74532_533488 node_context_12_74532_533488
  intro a
  fin_cases a
  · exact context_13_298128_533385
  · exact context_13_298129_533452
  · exact context_13_298130_533481
  · exact context_13_298131_533487

theorem selected_cut_20842 : selected 8 ⟨533520, by decide⟩
    (prefixPartial 13 298132) = some ⟨13, 2, 0, 533520, 298132, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_298132_533520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298132 ⟨533520, by decide⟩ :=
  accepted_of_selected 13 298132 ⟨533520, by decide⟩ ⟨13, 2, 0, 533520, 298132, 1221, 16384⟩
    (by decide) selected_cut_20842

theorem selected_cut_20843 : selected 8 ⟨533550, by decide⟩
    (prefixPartial 13 298133) = some ⟨13, 2, 0, 533550, 298133, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_298133_533550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298133 ⟨533550, by decide⟩ :=
  accepted_of_selected 13 298133 ⟨533550, by decide⟩ ⟨13, 2, 0, 533550, 298133, 1405, 16384⟩
    (by decide) selected_cut_20843

theorem selected_cut_20844 : selected 8 ⟨533562, by decide⟩
    (prefixPartial 13 298134) = some ⟨13, 2, 0, 533562, 298134, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_298134_533562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298134 ⟨533562, by decide⟩ :=
  accepted_of_selected 13 298134 ⟨533562, by decide⟩ ⟨13, 2, 0, 533562, 298134, 1569, 16384⟩
    (by decide) selected_cut_20844

theorem selected_cut_20845 : selected 8 ⟨533567, by decide⟩
    (prefixPartial 13 298135) = some ⟨13, 2, 0, 533567, 298135, 725, 16384⟩ := by
  decide +kernel

theorem context_13_298135_533567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298135 ⟨533567, by decide⟩ :=
  accepted_of_selected 13 298135 ⟨533567, by decide⟩ ⟨13, 2, 0, 533567, 298135, 725, 16384⟩
    (by decide) selected_cut_20845

theorem unmarked_context_12_74533_533568 : frontier 9 ⟨533568, by decide⟩
    (prefixCache 12 74533) (prefixPartial 12 74533) = false := by
  decide +kernel

theorem node_context_12_74533_533568 : EJMOriginalGlobalDAGData.nodes 9 ⟨533568, by decide⟩ =
    .split (coordinate 12) (![⟨533520, by decide⟩,⟨533550, by decide⟩,⟨533562, by decide⟩,⟨533567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74533_533568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74533 ⟨533568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74533
    ⟨533568, by decide⟩ (by decide) (![⟨533520, by decide⟩,⟨533550, by decide⟩,⟨533562, by decide⟩,⟨533567, by decide⟩]) unmarked_context_12_74533_533568 node_context_12_74533_533568
  intro a
  fin_cases a
  · exact context_13_298132_533520
  · exact context_13_298133_533550
  · exact context_13_298134_533562
  · exact context_13_298135_533567

theorem selected_cut_20846 : selected 8 ⟨533594, by decide⟩
    (prefixPartial 13 298136) = some ⟨13, 2, 0, 533594, 298136, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_298136_533594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298136 ⟨533594, by decide⟩ :=
  accepted_of_selected 13 298136 ⟨533594, by decide⟩ ⟨13, 2, 0, 533594, 298136, 1001, 16384⟩
    (by decide) selected_cut_20846

theorem selected_cut_20847 : selected 8 ⟨533627, by decide⟩
    (prefixPartial 13 298137) = some ⟨13, 2, 0, 533627, 298137, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_298137_533627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298137 ⟨533627, by decide⟩ :=
  accepted_of_selected 13 298137 ⟨533627, by decide⟩ ⟨13, 2, 0, 533627, 298137, 1705, 16384⟩
    (by decide) selected_cut_20847

theorem selected_cut_20848 : selected 8 ⟨533640, by decide⟩
    (prefixPartial 13 298138) = some ⟨13, 2, 0, 533640, 298138, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_298138_533640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298138 ⟨533640, by decide⟩ :=
  accepted_of_selected 13 298138 ⟨533640, by decide⟩ ⟨13, 2, 0, 533640, 298138, 1081, 16384⟩
    (by decide) selected_cut_20848

theorem selected_cut_20849 : selected 8 ⟨533647, by decide⟩
    (prefixPartial 13 298139) = some ⟨13, 2, 0, 533647, 298139, 721, 16384⟩ := by
  decide +kernel

theorem context_13_298139_533647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298139 ⟨533647, by decide⟩ :=
  accepted_of_selected 13 298139 ⟨533647, by decide⟩ ⟨13, 2, 0, 533647, 298139, 721, 16384⟩
    (by decide) selected_cut_20849

theorem unmarked_context_12_74534_533648 : frontier 9 ⟨533648, by decide⟩
    (prefixCache 12 74534) (prefixPartial 12 74534) = false := by
  decide +kernel

theorem node_context_12_74534_533648 : EJMOriginalGlobalDAGData.nodes 9 ⟨533648, by decide⟩ =
    .split (coordinate 12) (![⟨533594, by decide⟩,⟨533627, by decide⟩,⟨533640, by decide⟩,⟨533647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74534_533648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74534 ⟨533648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74534
    ⟨533648, by decide⟩ (by decide) (![⟨533594, by decide⟩,⟨533627, by decide⟩,⟨533640, by decide⟩,⟨533647, by decide⟩]) unmarked_context_12_74534_533648 node_context_12_74534_533648
  intro a
  fin_cases a
  · exact context_13_298136_533594
  · exact context_13_298137_533627
  · exact context_13_298138_533640
  · exact context_13_298139_533647

theorem selected_cut_20850 : selected 8 ⟨533676, by decide⟩
    (prefixPartial 13 298140) = some ⟨13, 2, 0, 533676, 298140, 985, 16384⟩ := by
  decide +kernel

theorem context_13_298140_533676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298140 ⟨533676, by decide⟩ :=
  accepted_of_selected 13 298140 ⟨533676, by decide⟩ ⟨13, 2, 0, 533676, 298140, 985, 16384⟩
    (by decide) selected_cut_20850

theorem selected_cut_20851 : selected 8 ⟨533705, by decide⟩
    (prefixPartial 13 298141) = some ⟨13, 2, 0, 533705, 298141, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_298141_533705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298141 ⟨533705, by decide⟩ :=
  accepted_of_selected 13 298141 ⟨533705, by decide⟩ ⟨13, 2, 0, 533705, 298141, 1533, 16384⟩
    (by decide) selected_cut_20851

theorem selected_cut_20852 : selected 8 ⟨533719, by decide⟩
    (prefixPartial 13 298142) = some ⟨13, 2, 0, 533719, 298142, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_298142_533719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298142 ⟨533719, by decide⟩ :=
  accepted_of_selected 13 298142 ⟨533719, by decide⟩ ⟨13, 2, 0, 533719, 298142, 1265, 16384⟩
    (by decide) selected_cut_20852

theorem selected_cut_20853 : selected 8 ⟨533724, by decide⟩
    (prefixPartial 13 298143) = some ⟨13, 2, 0, 533724, 298143, 613, 16384⟩ := by
  decide +kernel

theorem context_13_298143_533724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298143 ⟨533724, by decide⟩ :=
  accepted_of_selected 13 298143 ⟨533724, by decide⟩ ⟨13, 2, 0, 533724, 298143, 613, 16384⟩
    (by decide) selected_cut_20853

theorem unmarked_context_12_74535_533725 : frontier 9 ⟨533725, by decide⟩
    (prefixCache 12 74535) (prefixPartial 12 74535) = false := by
  decide +kernel

theorem node_context_12_74535_533725 : EJMOriginalGlobalDAGData.nodes 9 ⟨533725, by decide⟩ =
    .split (coordinate 12) (![⟨533676, by decide⟩,⟨533705, by decide⟩,⟨533719, by decide⟩,⟨533724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74535_533725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74535 ⟨533725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74535
    ⟨533725, by decide⟩ (by decide) (![⟨533676, by decide⟩,⟨533705, by decide⟩,⟨533719, by decide⟩,⟨533724, by decide⟩]) unmarked_context_12_74535_533725 node_context_12_74535_533725
  intro a
  fin_cases a
  · exact context_13_298140_533676
  · exact context_13_298141_533705
  · exact context_13_298142_533719
  · exact context_13_298143_533724

theorem unmarked_context_11_18633_533726 : frontier 10 ⟨533726, by decide⟩
    (prefixCache 11 18633) (prefixPartial 11 18633) = false := by
  decide +kernel

theorem node_context_11_18633_533726 : EJMOriginalGlobalDAGData.nodes 10 ⟨533726, by decide⟩ =
    .split (coordinate 11) (![⟨533488, by decide⟩,⟨533568, by decide⟩,⟨533648, by decide⟩,⟨533725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18633_533726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18633 ⟨533726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18633
    ⟨533726, by decide⟩ (by decide) (![⟨533488, by decide⟩,⟨533568, by decide⟩,⟨533648, by decide⟩,⟨533725, by decide⟩]) unmarked_context_11_18633_533726 node_context_11_18633_533726
  intro a
  fin_cases a
  · exact context_12_74532_533488
  · exact context_12_74533_533568
  · exact context_12_74534_533648
  · exact context_12_74535_533725

theorem selected_cut_20854 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 74536) = some ⟨12, 1, 0, 435790, 74536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74536_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74536 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 74536 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 74536, 1, 65536⟩
    (by decide) selected_cut_20854

theorem selected_cut_20855 : selected 8 ⟨533745, by decide⟩
    (prefixPartial 13 298148) = some ⟨13, 2, 0, 533745, 298148, 933, 16384⟩ := by
  decide +kernel

theorem context_13_298148_533745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298148 ⟨533745, by decide⟩ :=
  accepted_of_selected 13 298148 ⟨533745, by decide⟩ ⟨13, 2, 0, 533745, 298148, 933, 16384⟩
    (by decide) selected_cut_20855

theorem selected_cut_20856 : selected 8 ⟨533774, by decide⟩
    (prefixPartial 13 298149) = some ⟨13, 2, 0, 533774, 298149, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_298149_533774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298149 ⟨533774, by decide⟩ :=
  accepted_of_selected 13 298149 ⟨533774, by decide⟩ ⟨13, 2, 0, 533774, 298149, 1445, 16384⟩
    (by decide) selected_cut_20856

theorem selected_cut_20857 : selected 8 ⟨533791, by decide⟩
    (prefixPartial 13 298150) = some ⟨13, 2, 0, 533791, 298150, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_298150_533791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298150 ⟨533791, by decide⟩ :=
  accepted_of_selected 13 298150 ⟨533791, by decide⟩ ⟨13, 2, 0, 533791, 298150, 1529, 16384⟩
    (by decide) selected_cut_20857

theorem selected_cut_20858 : selected 8 ⟨533799, by decide⟩
    (prefixPartial 13 298151) = some ⟨13, 2, 0, 533799, 298151, 793, 16384⟩ := by
  decide +kernel

theorem context_13_298151_533799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298151 ⟨533799, by decide⟩ :=
  accepted_of_selected 13 298151 ⟨533799, by decide⟩ ⟨13, 2, 0, 533799, 298151, 793, 16384⟩
    (by decide) selected_cut_20858

theorem unmarked_context_12_74537_533800 : frontier 9 ⟨533800, by decide⟩
    (prefixCache 12 74537) (prefixPartial 12 74537) = false := by
  decide +kernel

theorem node_context_12_74537_533800 : EJMOriginalGlobalDAGData.nodes 9 ⟨533800, by decide⟩ =
    .split (coordinate 12) (![⟨533745, by decide⟩,⟨533774, by decide⟩,⟨533791, by decide⟩,⟨533799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74537_533800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74537 ⟨533800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74537
    ⟨533800, by decide⟩ (by decide) (![⟨533745, by decide⟩,⟨533774, by decide⟩,⟨533791, by decide⟩,⟨533799, by decide⟩]) unmarked_context_12_74537_533800 node_context_12_74537_533800
  intro a
  fin_cases a
  · exact context_13_298148_533745
  · exact context_13_298149_533774
  · exact context_13_298150_533791
  · exact context_13_298151_533799

theorem selected_cut_20859 : selected 9 ⟨533872, by decide⟩
    (prefixPartial 12 74538) = some ⟨12, 2, 0, 533872, 74538, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_74538_533872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74538 ⟨533872, by decide⟩ :=
  accepted_of_selected 12 74538 ⟨533872, by decide⟩ ⟨12, 2, 0, 533872, 74538, 3877, 65536⟩
    (by decide) selected_cut_20859

theorem selected_cut_20860 : selected 9 ⟨533936, by decide⟩
    (prefixPartial 12 74539) = some ⟨12, 2, 0, 533936, 74539, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_74539_533936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74539 ⟨533936, by decide⟩ :=
  accepted_of_selected 12 74539 ⟨533936, by decide⟩ ⟨12, 2, 0, 533936, 74539, 3953, 65536⟩
    (by decide) selected_cut_20860

theorem unmarked_context_11_18634_533937 : frontier 10 ⟨533937, by decide⟩
    (prefixCache 11 18634) (prefixPartial 11 18634) = false := by
  decide +kernel

theorem node_context_11_18634_533937 : EJMOriginalGlobalDAGData.nodes 10 ⟨533937, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨533800, by decide⟩,⟨533872, by decide⟩,⟨533936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18634_533937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18634 ⟨533937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18634
    ⟨533937, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨533800, by decide⟩,⟨533872, by decide⟩,⟨533936, by decide⟩]) unmarked_context_11_18634_533937 node_context_11_18634_533937
  intro a
  fin_cases a
  · exact context_12_74536_435790
  · exact context_12_74537_533800
  · exact context_12_74538_533872
  · exact context_12_74539_533936

theorem selected_cut_20861 : selected 8 ⟨533955, by decide⟩
    (prefixPartial 13 298160) = some ⟨13, 2, 0, 533955, 298160, 857, 16384⟩ := by
  decide +kernel

theorem context_13_298160_533955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298160 ⟨533955, by decide⟩ :=
  accepted_of_selected 13 298160 ⟨533955, by decide⟩ ⟨13, 2, 0, 533955, 298160, 857, 16384⟩
    (by decide) selected_cut_20861

theorem selected_cut_20862 : selected 8 ⟨534003, by decide⟩
    (prefixPartial 13 298161) = some ⟨13, 2, 0, 534003, 298161, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_298161_534003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298161 ⟨534003, by decide⟩ :=
  accepted_of_selected 13 298161 ⟨534003, by decide⟩ ⟨13, 2, 0, 534003, 298161, 2513, 16384⟩
    (by decide) selected_cut_20862

theorem selected_cut_20863 : selected 8 ⟨534023, by decide⟩
    (prefixPartial 13 298162) = some ⟨13, 2, 0, 534023, 298162, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_298162_534023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298162 ⟨534023, by decide⟩ :=
  accepted_of_selected 13 298162 ⟨534023, by decide⟩ ⟨13, 2, 0, 534023, 298162, 1465, 16384⟩
    (by decide) selected_cut_20863

theorem selected_cut_20864 : selected 8 ⟨534033, by decide⟩
    (prefixPartial 13 298163) = some ⟨13, 2, 0, 534033, 298163, 921, 16384⟩ := by
  decide +kernel

theorem context_13_298163_534033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298163 ⟨534033, by decide⟩ :=
  accepted_of_selected 13 298163 ⟨534033, by decide⟩ ⟨13, 2, 0, 534033, 298163, 921, 16384⟩
    (by decide) selected_cut_20864

theorem unmarked_context_12_74540_534034 : frontier 9 ⟨534034, by decide⟩
    (prefixCache 12 74540) (prefixPartial 12 74540) = false := by
  decide +kernel

theorem node_context_12_74540_534034 : EJMOriginalGlobalDAGData.nodes 9 ⟨534034, by decide⟩ =
    .split (coordinate 12) (![⟨533955, by decide⟩,⟨534003, by decide⟩,⟨534023, by decide⟩,⟨534033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74540_534034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74540 ⟨534034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74540
    ⟨534034, by decide⟩ (by decide) (![⟨533955, by decide⟩,⟨534003, by decide⟩,⟨534023, by decide⟩,⟨534033, by decide⟩]) unmarked_context_12_74540_534034 node_context_12_74540_534034
  intro a
  fin_cases a
  · exact context_13_298160_533955
  · exact context_13_298161_534003
  · exact context_13_298162_534023
  · exact context_13_298163_534033

theorem selected_cut_20865 : selected 8 ⟨534055, by decide⟩
    (prefixPartial 13 298164) = some ⟨13, 2, 0, 534055, 298164, 737, 16384⟩ := by
  decide +kernel

theorem context_13_298164_534055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298164 ⟨534055, by decide⟩ :=
  accepted_of_selected 13 298164 ⟨534055, by decide⟩ ⟨13, 2, 0, 534055, 298164, 737, 16384⟩
    (by decide) selected_cut_20865

theorem selected_cut_20866 : selected 8 ⟨534084, by decide⟩
    (prefixPartial 13 298165) = some ⟨13, 2, 0, 534084, 298165, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_298165_534084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298165 ⟨534084, by decide⟩ :=
  accepted_of_selected 13 298165 ⟨534084, by decide⟩ ⟨13, 2, 0, 534084, 298165, 1541, 16384⟩
    (by decide) selected_cut_20866

theorem selected_cut_20867 : selected 8 ⟨534098, by decide⟩
    (prefixPartial 13 298166) = some ⟨13, 2, 0, 534098, 298166, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_298166_534098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298166 ⟨534098, by decide⟩ :=
  accepted_of_selected 13 298166 ⟨534098, by decide⟩ ⟨13, 2, 0, 534098, 298166, 1573, 16384⟩
    (by decide) selected_cut_20867

theorem selected_cut_20868 : selected 8 ⟨534107, by decide⟩
    (prefixPartial 13 298167) = some ⟨13, 2, 0, 534107, 298167, 741, 16384⟩ := by
  decide +kernel

theorem context_13_298167_534107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298167 ⟨534107, by decide⟩ :=
  accepted_of_selected 13 298167 ⟨534107, by decide⟩ ⟨13, 2, 0, 534107, 298167, 741, 16384⟩
    (by decide) selected_cut_20868

theorem unmarked_context_12_74541_534108 : frontier 9 ⟨534108, by decide⟩
    (prefixCache 12 74541) (prefixPartial 12 74541) = false := by
  decide +kernel

theorem node_context_12_74541_534108 : EJMOriginalGlobalDAGData.nodes 9 ⟨534108, by decide⟩ =
    .split (coordinate 12) (![⟨534055, by decide⟩,⟨534084, by decide⟩,⟨534098, by decide⟩,⟨534107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74541_534108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74541 ⟨534108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74541
    ⟨534108, by decide⟩ (by decide) (![⟨534055, by decide⟩,⟨534084, by decide⟩,⟨534098, by decide⟩,⟨534107, by decide⟩]) unmarked_context_12_74541_534108 node_context_12_74541_534108
  intro a
  fin_cases a
  · exact context_13_298164_534055
  · exact context_13_298165_534084
  · exact context_13_298166_534098
  · exact context_13_298167_534107

theorem selected_cut_20869 : selected 9 ⟨534172, by decide⟩
    (prefixPartial 12 74542) = some ⟨12, 2, 0, 534172, 74542, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_74542_534172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74542 ⟨534172, by decide⟩ :=
  accepted_of_selected 12 74542 ⟨534172, by decide⟩ ⟨12, 2, 0, 534172, 74542, 3809, 65536⟩
    (by decide) selected_cut_20869

theorem selected_cut_20870 : selected 8 ⟨534194, by decide⟩
    (prefixPartial 13 298172) = some ⟨13, 2, 0, 534194, 298172, 957, 16384⟩ := by
  decide +kernel

theorem context_13_298172_534194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298172 ⟨534194, by decide⟩ :=
  accepted_of_selected 13 298172 ⟨534194, by decide⟩ ⟨13, 2, 0, 534194, 298172, 957, 16384⟩
    (by decide) selected_cut_20870

theorem selected_cut_20871 : selected 8 ⟨534243, by decide⟩
    (prefixPartial 13 298173) = some ⟨13, 2, 0, 534243, 298173, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_298173_534243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298173 ⟨534243, by decide⟩ :=
  accepted_of_selected 13 298173 ⟨534243, by decide⟩ ⟨13, 2, 0, 534243, 298173, 2481, 16384⟩
    (by decide) selected_cut_20871

theorem selected_cut_20872 : selected 8 ⟨534254, by decide⟩
    (prefixPartial 13 298174) = some ⟨13, 2, 0, 534254, 298174, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_298174_534254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298174 ⟨534254, by decide⟩ :=
  accepted_of_selected 13 298174 ⟨534254, by decide⟩ ⟨13, 2, 0, 534254, 298174, 1781, 16384⟩
    (by decide) selected_cut_20872

theorem selected_cut_20873 : selected 8 ⟨534261, by decide⟩
    (prefixPartial 13 298175) = some ⟨13, 2, 0, 534261, 298175, 909, 16384⟩ := by
  decide +kernel

theorem context_13_298175_534261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298175 ⟨534261, by decide⟩ :=
  accepted_of_selected 13 298175 ⟨534261, by decide⟩ ⟨13, 2, 0, 534261, 298175, 909, 16384⟩
    (by decide) selected_cut_20873

theorem unmarked_context_12_74543_534262 : frontier 9 ⟨534262, by decide⟩
    (prefixCache 12 74543) (prefixPartial 12 74543) = false := by
  decide +kernel

theorem node_context_12_74543_534262 : EJMOriginalGlobalDAGData.nodes 9 ⟨534262, by decide⟩ =
    .split (coordinate 12) (![⟨534194, by decide⟩,⟨534243, by decide⟩,⟨534254, by decide⟩,⟨534261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74543_534262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74543 ⟨534262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74543
    ⟨534262, by decide⟩ (by decide) (![⟨534194, by decide⟩,⟨534243, by decide⟩,⟨534254, by decide⟩,⟨534261, by decide⟩]) unmarked_context_12_74543_534262 node_context_12_74543_534262
  intro a
  fin_cases a
  · exact context_13_298172_534194
  · exact context_13_298173_534243
  · exact context_13_298174_534254
  · exact context_13_298175_534261

theorem unmarked_context_11_18635_534263 : frontier 10 ⟨534263, by decide⟩
    (prefixCache 11 18635) (prefixPartial 11 18635) = false := by
  decide +kernel

theorem node_context_11_18635_534263 : EJMOriginalGlobalDAGData.nodes 10 ⟨534263, by decide⟩ =
    .split (coordinate 11) (![⟨534034, by decide⟩,⟨534108, by decide⟩,⟨534172, by decide⟩,⟨534262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18635_534263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18635 ⟨534263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18635
    ⟨534263, by decide⟩ (by decide) (![⟨534034, by decide⟩,⟨534108, by decide⟩,⟨534172, by decide⟩,⟨534262, by decide⟩]) unmarked_context_11_18635_534263 node_context_11_18635_534263
  intro a
  fin_cases a
  · exact context_12_74540_534034
  · exact context_12_74541_534108
  · exact context_12_74542_534172
  · exact context_12_74543_534262

theorem unmarked_context_10_4658_534264 : frontier 11 ⟨534264, by decide⟩
    (prefixCache 10 4658) (prefixPartial 10 4658) = false := by
  decide +kernel

theorem node_context_10_4658_534264 : EJMOriginalGlobalDAGData.nodes 11 ⟨534264, by decide⟩ =
    .split (coordinate 10) (![⟨533348, by decide⟩,⟨533726, by decide⟩,⟨533937, by decide⟩,⟨534263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4658_534264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4658 ⟨534264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4658
    ⟨534264, by decide⟩ (by decide) (![⟨533348, by decide⟩,⟨533726, by decide⟩,⟨533937, by decide⟩,⟨534263, by decide⟩]) unmarked_context_10_4658_534264 node_context_10_4658_534264
  intro a
  fin_cases a
  · exact context_11_18632_533348
  · exact context_11_18633_533726
  · exact context_11_18634_533937
  · exact context_11_18635_534263

theorem selected_cut_20874 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 74544) = some ⟨12, 1, 0, 445562, 74544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74544_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74544 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 74544 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 74544, 1, 65536⟩
    (by decide) selected_cut_20874

theorem selected_cut_20875 : selected 9 ⟨534328, by decide⟩
    (prefixPartial 12 74545) = some ⟨12, 2, 0, 534328, 74545, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_74545_534328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74545 ⟨534328, by decide⟩ :=
  accepted_of_selected 12 74545 ⟨534328, by decide⟩ ⟨12, 2, 0, 534328, 74545, 4021, 65536⟩
    (by decide) selected_cut_20875

theorem selected_cut_20876 : selected 9 ⟨534382, by decide⟩
    (prefixPartial 12 74546) = some ⟨12, 2, 0, 534382, 74546, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_74546_534382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74546 ⟨534382, by decide⟩ :=
  accepted_of_selected 12 74546 ⟨534382, by decide⟩ ⟨12, 2, 0, 534382, 74546, 3749, 65536⟩
    (by decide) selected_cut_20876

theorem selected_cut_20877 : selected 9 ⟨534439, by decide⟩
    (prefixPartial 12 74547) = some ⟨12, 2, 0, 534439, 74547, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_74547_534439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74547 ⟨534439, by decide⟩ :=
  accepted_of_selected 12 74547 ⟨534439, by decide⟩ ⟨12, 2, 0, 534439, 74547, 3137, 65536⟩
    (by decide) selected_cut_20877

theorem unmarked_context_11_18636_534440 : frontier 10 ⟨534440, by decide⟩
    (prefixCache 11 18636) (prefixPartial 11 18636) = false := by
  decide +kernel

theorem node_context_11_18636_534440 : EJMOriginalGlobalDAGData.nodes 10 ⟨534440, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨534328, by decide⟩,⟨534382, by decide⟩,⟨534439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18636_534440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18636 ⟨534440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18636
    ⟨534440, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨534328, by decide⟩,⟨534382, by decide⟩,⟨534439, by decide⟩]) unmarked_context_11_18636_534440 node_context_11_18636_534440
  intro a
  fin_cases a
  · exact context_12_74544_445562
  · exact context_12_74545_534328
  · exact context_12_74546_534382
  · exact context_12_74547_534439

theorem selected_cut_20878 : selected 8 ⟨534449, by decide⟩
    (prefixPartial 13 298192) = some ⟨13, 2, 0, 534449, 298192, 425, 16384⟩ := by
  decide +kernel

theorem context_13_298192_534449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298192 ⟨534449, by decide⟩ :=
  accepted_of_selected 13 298192 ⟨534449, by decide⟩ ⟨13, 2, 0, 534449, 298192, 425, 16384⟩
    (by decide) selected_cut_20878

theorem selected_cut_20879 : selected 8 ⟨534493, by decide⟩
    (prefixPartial 13 298193) = some ⟨13, 2, 0, 534493, 298193, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_298193_534493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298193 ⟨534493, by decide⟩ :=
  accepted_of_selected 13 298193 ⟨534493, by decide⟩ ⟨13, 2, 0, 534493, 298193, 2261, 16384⟩
    (by decide) selected_cut_20879

theorem selected_cut_20880 : selected 8 ⟨534526, by decide⟩
    (prefixPartial 13 298194) = some ⟨13, 2, 0, 534526, 298194, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_298194_534526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298194 ⟨534526, by decide⟩ :=
  accepted_of_selected 13 298194 ⟨534526, by decide⟩ ⟨13, 2, 0, 534526, 298194, 1693, 16384⟩
    (by decide) selected_cut_20880

theorem selected_cut_20881 : selected 8 ⟨534545, by decide⟩
    (prefixPartial 13 298195) = some ⟨13, 2, 0, 534545, 298195, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_298195_534545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298195 ⟨534545, by decide⟩ :=
  accepted_of_selected 13 298195 ⟨534545, by decide⟩ ⟨13, 2, 0, 534545, 298195, 1041, 16384⟩
    (by decide) selected_cut_20881

theorem unmarked_context_12_74548_534546 : frontier 9 ⟨534546, by decide⟩
    (prefixCache 12 74548) (prefixPartial 12 74548) = false := by
  decide +kernel

theorem node_context_12_74548_534546 : EJMOriginalGlobalDAGData.nodes 9 ⟨534546, by decide⟩ =
    .split (coordinate 12) (![⟨534449, by decide⟩,⟨534493, by decide⟩,⟨534526, by decide⟩,⟨534545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74548_534546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74548 ⟨534546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74548
    ⟨534546, by decide⟩ (by decide) (![⟨534449, by decide⟩,⟨534493, by decide⟩,⟨534526, by decide⟩,⟨534545, by decide⟩]) unmarked_context_12_74548_534546 node_context_12_74548_534546
  intro a
  fin_cases a
  · exact context_13_298192_534449
  · exact context_13_298193_534493
  · exact context_13_298194_534526
  · exact context_13_298195_534545

theorem selected_cut_20882 : selected 8 ⟨534553, by decide⟩
    (prefixPartial 13 298196) = some ⟨13, 2, 0, 534553, 298196, 329, 16384⟩ := by
  decide +kernel

theorem context_13_298196_534553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298196 ⟨534553, by decide⟩ :=
  accepted_of_selected 13 298196 ⟨534553, by decide⟩ ⟨13, 2, 0, 534553, 298196, 329, 16384⟩
    (by decide) selected_cut_20882

theorem selected_cut_20883 : selected 8 ⟨534573, by decide⟩
    (prefixPartial 13 298197) = some ⟨13, 2, 0, 534573, 298197, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_298197_534573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298197 ⟨534573, by decide⟩ :=
  accepted_of_selected 13 298197 ⟨534573, by decide⟩ ⟨13, 2, 0, 534573, 298197, 1357, 16384⟩
    (by decide) selected_cut_20883

theorem selected_cut_20884 : selected 8 ⟨534586, by decide⟩
    (prefixPartial 13 298198) = some ⟨13, 2, 0, 534586, 298198, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_298198_534586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298198 ⟨534586, by decide⟩ :=
  accepted_of_selected 13 298198 ⟨534586, by decide⟩ ⟨13, 2, 0, 534586, 298198, 1561, 16384⟩
    (by decide) selected_cut_20884

theorem selected_cut_20885 : selected 8 ⟨534597, by decide⟩
    (prefixPartial 13 298199) = some ⟨13, 2, 0, 534597, 298199, 901, 16384⟩ := by
  decide +kernel

theorem context_13_298199_534597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298199 ⟨534597, by decide⟩ :=
  accepted_of_selected 13 298199 ⟨534597, by decide⟩ ⟨13, 2, 0, 534597, 298199, 901, 16384⟩
    (by decide) selected_cut_20885

theorem unmarked_context_12_74549_534598 : frontier 9 ⟨534598, by decide⟩
    (prefixCache 12 74549) (prefixPartial 12 74549) = false := by
  decide +kernel

theorem node_context_12_74549_534598 : EJMOriginalGlobalDAGData.nodes 9 ⟨534598, by decide⟩ =
    .split (coordinate 12) (![⟨534553, by decide⟩,⟨534573, by decide⟩,⟨534586, by decide⟩,⟨534597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74549_534598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74549 ⟨534598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74549
    ⟨534598, by decide⟩ (by decide) (![⟨534553, by decide⟩,⟨534573, by decide⟩,⟨534586, by decide⟩,⟨534597, by decide⟩]) unmarked_context_12_74549_534598 node_context_12_74549_534598
  intro a
  fin_cases a
  · exact context_13_298196_534553
  · exact context_13_298197_534573
  · exact context_13_298198_534586
  · exact context_13_298199_534597

theorem selected_cut_20886 : selected 9 ⟨534654, by decide⟩
    (prefixPartial 12 74550) = some ⟨12, 2, 0, 534654, 74550, 4029, 65536⟩ := by
  decide +kernel

theorem context_12_74550_534654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74550 ⟨534654, by decide⟩ :=
  accepted_of_selected 12 74550 ⟨534654, by decide⟩ ⟨12, 2, 0, 534654, 74550, 4029, 65536⟩
    (by decide) selected_cut_20886

theorem selected_cut_20887 : selected 9 ⟨534710, by decide⟩
    (prefixPartial 12 74551) = some ⟨12, 2, 0, 534710, 74551, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_74551_534710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74551 ⟨534710, by decide⟩ :=
  accepted_of_selected 12 74551 ⟨534710, by decide⟩ ⟨12, 2, 0, 534710, 74551, 3425, 65536⟩
    (by decide) selected_cut_20887

theorem unmarked_context_11_18637_534711 : frontier 10 ⟨534711, by decide⟩
    (prefixCache 11 18637) (prefixPartial 11 18637) = false := by
  decide +kernel

theorem node_context_11_18637_534711 : EJMOriginalGlobalDAGData.nodes 10 ⟨534711, by decide⟩ =
    .split (coordinate 11) (![⟨534546, by decide⟩,⟨534598, by decide⟩,⟨534654, by decide⟩,⟨534710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18637_534711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18637 ⟨534711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18637
    ⟨534711, by decide⟩ (by decide) (![⟨534546, by decide⟩,⟨534598, by decide⟩,⟨534654, by decide⟩,⟨534710, by decide⟩]) unmarked_context_11_18637_534711 node_context_11_18637_534711
  intro a
  fin_cases a
  · exact context_12_74548_534546
  · exact context_12_74549_534598
  · exact context_12_74550_534654
  · exact context_12_74551_534710

theorem selected_cut_20888 : selected 8 ⟨534716, by decide⟩
    (prefixPartial 13 298208) = some ⟨13, 2, 0, 534716, 298208, 249, 16384⟩ := by
  decide +kernel

theorem context_13_298208_534716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298208 ⟨534716, by decide⟩ :=
  accepted_of_selected 13 298208 ⟨534716, by decide⟩ ⟨13, 2, 0, 534716, 298208, 249, 16384⟩
    (by decide) selected_cut_20888

theorem selected_cut_20889 : selected 8 ⟨534762, by decide⟩
    (prefixPartial 13 298209) = some ⟨13, 2, 0, 534762, 298209, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_298209_534762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298209 ⟨534762, by decide⟩ :=
  accepted_of_selected 13 298209 ⟨534762, by decide⟩ ⟨13, 2, 0, 534762, 298209, 2513, 16384⟩
    (by decide) selected_cut_20889

theorem selected_cut_20890 : selected 8 ⟨534784, by decide⟩
    (prefixPartial 13 298210) = some ⟨13, 2, 0, 534784, 298210, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_298210_534784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298210 ⟨534784, by decide⟩ :=
  accepted_of_selected 13 298210 ⟨534784, by decide⟩ ⟨13, 2, 0, 534784, 298210, 1601, 16384⟩
    (by decide) selected_cut_20890

theorem selected_cut_20891 : selected 8 ⟨534800, by decide⟩
    (prefixPartial 13 298211) = some ⟨13, 2, 0, 534800, 298211, 901, 16384⟩ := by
  decide +kernel

theorem context_13_298211_534800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298211 ⟨534800, by decide⟩ :=
  accepted_of_selected 13 298211 ⟨534800, by decide⟩ ⟨13, 2, 0, 534800, 298211, 901, 16384⟩
    (by decide) selected_cut_20891

theorem unmarked_context_12_74552_534801 : frontier 9 ⟨534801, by decide⟩
    (prefixCache 12 74552) (prefixPartial 12 74552) = false := by
  decide +kernel

theorem node_context_12_74552_534801 : EJMOriginalGlobalDAGData.nodes 9 ⟨534801, by decide⟩ =
    .split (coordinate 12) (![⟨534716, by decide⟩,⟨534762, by decide⟩,⟨534784, by decide⟩,⟨534800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74552_534801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74552 ⟨534801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74552
    ⟨534801, by decide⟩ (by decide) (![⟨534716, by decide⟩,⟨534762, by decide⟩,⟨534784, by decide⟩,⟨534800, by decide⟩]) unmarked_context_12_74552_534801 node_context_12_74552_534801
  intro a
  fin_cases a
  · exact context_13_298208_534716
  · exact context_13_298209_534762
  · exact context_13_298210_534784
  · exact context_13_298211_534800

theorem selected_cut_20892 : selected 9 ⟨534862, by decide⟩
    (prefixPartial 12 74553) = some ⟨12, 2, 0, 534862, 74553, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_74553_534862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74553 ⟨534862, by decide⟩ :=
  accepted_of_selected 12 74553 ⟨534862, by decide⟩ ⟨12, 2, 0, 534862, 74553, 4005, 65536⟩
    (by decide) selected_cut_20892

theorem selected_cut_20893 : selected 9 ⟨534919, by decide⟩
    (prefixPartial 12 74554) = some ⟨12, 2, 0, 534919, 74554, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_74554_534919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74554 ⟨534919, by decide⟩ :=
  accepted_of_selected 12 74554 ⟨534919, by decide⟩ ⟨12, 2, 0, 534919, 74554, 3757, 65536⟩
    (by decide) selected_cut_20893

theorem selected_cut_20894 : selected 9 ⟨534971, by decide⟩
    (prefixPartial 12 74555) = some ⟨12, 2, 0, 534971, 74555, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_74555_534971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74555 ⟨534971, by decide⟩ :=
  accepted_of_selected 12 74555 ⟨534971, by decide⟩ ⟨12, 2, 0, 534971, 74555, 3197, 65536⟩
    (by decide) selected_cut_20894

theorem unmarked_context_11_18638_534972 : frontier 10 ⟨534972, by decide⟩
    (prefixCache 11 18638) (prefixPartial 11 18638) = false := by
  decide +kernel

theorem node_context_11_18638_534972 : EJMOriginalGlobalDAGData.nodes 10 ⟨534972, by decide⟩ =
    .split (coordinate 11) (![⟨534801, by decide⟩,⟨534862, by decide⟩,⟨534919, by decide⟩,⟨534971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18638_534972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18638 ⟨534972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18638
    ⟨534972, by decide⟩ (by decide) (![⟨534801, by decide⟩,⟨534862, by decide⟩,⟨534919, by decide⟩,⟨534971, by decide⟩]) unmarked_context_11_18638_534972 node_context_11_18638_534972
  intro a
  fin_cases a
  · exact context_12_74552_534801
  · exact context_12_74553_534862
  · exact context_12_74554_534919
  · exact context_12_74555_534971

theorem selected_cut_20895 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 74556) = some ⟨12, 1, 0, 445562, 74556, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74556_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74556 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 74556 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 74556, 1, 65536⟩
    (by decide) selected_cut_20895

theorem selected_cut_20896 : selected 9 ⟨535018, by decide⟩
    (prefixPartial 12 74557) = some ⟨12, 2, 0, 535018, 74557, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_74557_535018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74557 ⟨535018, by decide⟩ :=
  accepted_of_selected 12 74557 ⟨535018, by decide⟩ ⟨12, 2, 0, 535018, 74557, 3921, 65536⟩
    (by decide) selected_cut_20896

theorem selected_cut_20897 : selected 9 ⟨535065, by decide⟩
    (prefixPartial 12 74558) = some ⟨12, 2, 0, 535065, 74558, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_74558_535065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74558 ⟨535065, by decide⟩ :=
  accepted_of_selected 12 74558 ⟨535065, by decide⟩ ⟨12, 2, 0, 535065, 74558, 3641, 65536⟩
    (by decide) selected_cut_20897

theorem selected_cut_20898 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 74559) = some ⟨12, 1, 0, 512556, 74559, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74559_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74559 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 74559 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 74559, 1, 65536⟩
    (by decide) selected_cut_20898

theorem unmarked_context_11_18639_535066 : frontier 10 ⟨535066, by decide⟩
    (prefixCache 11 18639) (prefixPartial 11 18639) = false := by
  decide +kernel

theorem node_context_11_18639_535066 : EJMOriginalGlobalDAGData.nodes 10 ⟨535066, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨535018, by decide⟩,⟨535065, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18639_535066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18639 ⟨535066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18639
    ⟨535066, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨535018, by decide⟩,⟨535065, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_18639_535066 node_context_11_18639_535066
  intro a
  fin_cases a
  · exact context_12_74556_445562
  · exact context_12_74557_535018
  · exact context_12_74558_535065
  · exact context_12_74559_512556

theorem unmarked_context_10_4659_535067 : frontier 11 ⟨535067, by decide⟩
    (prefixCache 10 4659) (prefixPartial 10 4659) = false := by
  decide +kernel

theorem node_context_10_4659_535067 : EJMOriginalGlobalDAGData.nodes 11 ⟨535067, by decide⟩ =
    .split (coordinate 10) (![⟨534440, by decide⟩,⟨534711, by decide⟩,⟨534972, by decide⟩,⟨535066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4659_535067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4659 ⟨535067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4659
    ⟨535067, by decide⟩ (by decide) (![⟨534440, by decide⟩,⟨534711, by decide⟩,⟨534972, by decide⟩,⟨535066, by decide⟩]) unmarked_context_10_4659_535067 node_context_10_4659_535067
  intro a
  fin_cases a
  · exact context_11_18636_534440
  · exact context_11_18637_534711
  · exact context_11_18638_534972
  · exact context_11_18639_535066

theorem unmarked_context_9_1164_535068 : frontier 12 ⟨535068, by decide⟩
    (prefixCache 9 1164) (prefixPartial 9 1164) = false := by
  decide +kernel

theorem node_context_9_1164_535068 : EJMOriginalGlobalDAGData.nodes 12 ⟨535068, by decide⟩ =
    .split (coordinate 9) (![⟨531819, by decide⟩,⟨533105, by decide⟩,⟨534264, by decide⟩,⟨535067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1164_535068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1164 ⟨535068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1164
    ⟨535068, by decide⟩ (by decide) (![⟨531819, by decide⟩,⟨533105, by decide⟩,⟨534264, by decide⟩,⟨535067, by decide⟩]) unmarked_context_9_1164_535068 node_context_9_1164_535068
  intro a
  fin_cases a
  · exact context_10_4656_531819
  · exact context_10_4657_533105
  · exact context_10_4658_534264
  · exact context_10_4659_535067

theorem selected_cut_20899 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 4660) = some ⟨10, 1, 0, 145424, 4660, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4660_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4660 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 4660 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 4660, 1, 1048576⟩
    (by decide) selected_cut_20899

theorem selected_cut_20900 : selected 9 ⟨535126, by decide⟩
    (prefixPartial 12 74576) = some ⟨12, 2, 0, 535126, 74576, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_74576_535126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74576 ⟨535126, by decide⟩ :=
  accepted_of_selected 12 74576 ⟨535126, by decide⟩ ⟨12, 2, 0, 535126, 74576, 2985, 65536⟩
    (by decide) selected_cut_20900

theorem selected_cut_20901 : selected 9 ⟨535210, by decide⟩
    (prefixPartial 12 74577) = some ⟨12, 2, 0, 535210, 74577, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_74577_535210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74577 ⟨535210, by decide⟩ :=
  accepted_of_selected 12 74577 ⟨535210, by decide⟩ ⟨12, 2, 0, 535210, 74577, 3497, 65536⟩
    (by decide) selected_cut_20901

theorem selected_cut_20902 : selected 9 ⟨535279, by decide⟩
    (prefixPartial 12 74578) = some ⟨12, 2, 0, 535279, 74578, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_74578_535279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74578 ⟨535279, by decide⟩ :=
  accepted_of_selected 12 74578 ⟨535279, by decide⟩ ⟨12, 2, 0, 535279, 74578, 3757, 65536⟩
    (by decide) selected_cut_20902

theorem selected_cut_20903 : selected 9 ⟨535328, by decide⟩
    (prefixPartial 12 74579) = some ⟨12, 2, 0, 535328, 74579, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_74579_535328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74579 ⟨535328, by decide⟩ :=
  accepted_of_selected 12 74579 ⟨535328, by decide⟩ ⟨12, 2, 0, 535328, 74579, 3269, 65536⟩
    (by decide) selected_cut_20903

theorem unmarked_context_11_18644_535329 : frontier 10 ⟨535329, by decide⟩
    (prefixCache 11 18644) (prefixPartial 11 18644) = false := by
  decide +kernel

theorem node_context_11_18644_535329 : EJMOriginalGlobalDAGData.nodes 10 ⟨535329, by decide⟩ =
    .split (coordinate 11) (![⟨535126, by decide⟩,⟨535210, by decide⟩,⟨535279, by decide⟩,⟨535328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18644_535329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18644 ⟨535329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18644
    ⟨535329, by decide⟩ (by decide) (![⟨535126, by decide⟩,⟨535210, by decide⟩,⟨535279, by decide⟩,⟨535328, by decide⟩]) unmarked_context_11_18644_535329 node_context_11_18644_535329
  intro a
  fin_cases a
  · exact context_12_74576_535126
  · exact context_12_74577_535210
  · exact context_12_74578_535279
  · exact context_12_74579_535328

theorem selected_cut_20904 : selected 9 ⟨535393, by decide⟩
    (prefixPartial 12 74580) = some ⟨12, 2, 0, 535393, 74580, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_74580_535393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74580 ⟨535393, by decide⟩ :=
  accepted_of_selected 12 74580 ⟨535393, by decide⟩ ⟨12, 2, 0, 535393, 74580, 3069, 65536⟩
    (by decide) selected_cut_20904

theorem selected_cut_20905 : selected 9 ⟨535457, by decide⟩
    (prefixPartial 12 74581) = some ⟨12, 2, 0, 535457, 74581, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_74581_535457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74581 ⟨535457, by decide⟩ :=
  accepted_of_selected 12 74581 ⟨535457, by decide⟩ ⟨12, 2, 0, 535457, 74581, 3401, 65536⟩
    (by decide) selected_cut_20905

theorem selected_cut_20906 : selected 9 ⟨535528, by decide⟩
    (prefixPartial 12 74582) = some ⟨12, 2, 0, 535528, 74582, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_74582_535528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74582 ⟨535528, by decide⟩ :=
  accepted_of_selected 12 74582 ⟨535528, by decide⟩ ⟨12, 2, 0, 535528, 74582, 3673, 65536⟩
    (by decide) selected_cut_20906

theorem selected_cut_20907 : selected 9 ⟨535585, by decide⟩
    (prefixPartial 12 74583) = some ⟨12, 2, 0, 535585, 74583, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_74583_535585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74583 ⟨535585, by decide⟩ :=
  accepted_of_selected 12 74583 ⟨535585, by decide⟩ ⟨12, 2, 0, 535585, 74583, 3365, 65536⟩
    (by decide) selected_cut_20907

theorem unmarked_context_11_18645_535586 : frontier 10 ⟨535586, by decide⟩
    (prefixCache 11 18645) (prefixPartial 11 18645) = false := by
  decide +kernel

theorem node_context_11_18645_535586 : EJMOriginalGlobalDAGData.nodes 10 ⟨535586, by decide⟩ =
    .split (coordinate 11) (![⟨535393, by decide⟩,⟨535457, by decide⟩,⟨535528, by decide⟩,⟨535585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18645_535586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18645 ⟨535586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18645
    ⟨535586, by decide⟩ (by decide) (![⟨535393, by decide⟩,⟨535457, by decide⟩,⟨535528, by decide⟩,⟨535585, by decide⟩]) unmarked_context_11_18645_535586 node_context_11_18645_535586
  intro a
  fin_cases a
  · exact context_12_74580_535393
  · exact context_12_74581_535457
  · exact context_12_74582_535528
  · exact context_12_74583_535585

theorem selected_cut_20908 : selected 9 ⟨535649, by decide⟩
    (prefixPartial 12 74584) = some ⟨12, 2, 0, 535649, 74584, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_74584_535649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74584 ⟨535649, by decide⟩ :=
  accepted_of_selected 12 74584 ⟨535649, by decide⟩ ⟨12, 2, 0, 535649, 74584, 2885, 65536⟩
    (by decide) selected_cut_20908

theorem selected_cut_20909 : selected 9 ⟨535746, by decide⟩
    (prefixPartial 12 74585) = some ⟨12, 2, 0, 535746, 74585, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_74585_535746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74585 ⟨535746, by decide⟩ :=
  accepted_of_selected 12 74585 ⟨535746, by decide⟩ ⟨12, 2, 0, 535746, 74585, 3509, 65536⟩
    (by decide) selected_cut_20909

theorem selected_cut_20910 : selected 9 ⟨535814, by decide⟩
    (prefixPartial 12 74586) = some ⟨12, 2, 0, 535814, 74586, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_74586_535814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74586 ⟨535814, by decide⟩ :=
  accepted_of_selected 12 74586 ⟨535814, by decide⟩ ⟨12, 2, 0, 535814, 74586, 3413, 65536⟩
    (by decide) selected_cut_20910

theorem selected_cut_20911 : selected 9 ⟨535870, by decide⟩
    (prefixPartial 12 74587) = some ⟨12, 2, 0, 535870, 74587, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_74587_535870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74587 ⟨535870, by decide⟩ :=
  accepted_of_selected 12 74587 ⟨535870, by decide⟩ ⟨12, 2, 0, 535870, 74587, 3097, 65536⟩
    (by decide) selected_cut_20911

theorem unmarked_context_11_18646_535871 : frontier 10 ⟨535871, by decide⟩
    (prefixCache 11 18646) (prefixPartial 11 18646) = false := by
  decide +kernel

theorem node_context_11_18646_535871 : EJMOriginalGlobalDAGData.nodes 10 ⟨535871, by decide⟩ =
    .split (coordinate 11) (![⟨535649, by decide⟩,⟨535746, by decide⟩,⟨535814, by decide⟩,⟨535870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18646_535871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18646 ⟨535871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18646
    ⟨535871, by decide⟩ (by decide) (![⟨535649, by decide⟩,⟨535746, by decide⟩,⟨535814, by decide⟩,⟨535870, by decide⟩]) unmarked_context_11_18646_535871 node_context_11_18646_535871
  intro a
  fin_cases a
  · exact context_12_74584_535649
  · exact context_12_74585_535746
  · exact context_12_74586_535814
  · exact context_12_74587_535870

theorem selected_cut_20912 : selected 9 ⟨535912, by decide⟩
    (prefixPartial 12 74588) = some ⟨12, 2, 0, 535912, 74588, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_74588_535912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74588 ⟨535912, by decide⟩ :=
  accepted_of_selected 12 74588 ⟨535912, by decide⟩ ⟨12, 2, 0, 535912, 74588, 2513, 65536⟩
    (by decide) selected_cut_20912

theorem selected_cut_20913 : selected 9 ⟨535969, by decide⟩
    (prefixPartial 12 74589) = some ⟨12, 2, 0, 535969, 74589, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_74589_535969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74589 ⟨535969, by decide⟩ :=
  accepted_of_selected 12 74589 ⟨535969, by decide⟩ ⟨12, 2, 0, 535969, 74589, 3093, 65536⟩
    (by decide) selected_cut_20913

theorem selected_cut_20914 : selected 9 ⟨536037, by decide⟩
    (prefixPartial 12 74590) = some ⟨12, 2, 0, 536037, 74590, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_74590_536037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74590 ⟨536037, by decide⟩ :=
  accepted_of_selected 12 74590 ⟨536037, by decide⟩ ⟨12, 2, 0, 536037, 74590, 3061, 65536⟩
    (by decide) selected_cut_20914

theorem selected_cut_20915 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 298364) = some ⟨13, 1, 0, 3444, 298364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_298364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 298364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 298364, 1, 16384⟩
    (by decide) selected_cut_20915

theorem selected_cut_20916 : selected 8 ⟨536080, by decide⟩
    (prefixPartial 13 298365) = some ⟨13, 2, 0, 536080, 298365, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_298365_536080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298365 ⟨536080, by decide⟩ :=
  accepted_of_selected 13 298365 ⟨536080, by decide⟩ ⟨13, 2, 0, 536080, 298365, 1833, 16384⟩
    (by decide) selected_cut_20916

theorem selected_cut_20917 : selected 8 ⟨536127, by decide⟩
    (prefixPartial 13 298366) = some ⟨13, 2, 0, 536127, 298366, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_298366_536127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298366 ⟨536127, by decide⟩ :=
  accepted_of_selected 13 298366 ⟨536127, by decide⟩ ⟨13, 2, 0, 536127, 298366, 1401, 16384⟩
    (by decide) selected_cut_20917

theorem selected_cut_20918 : selected 8 ⟨536147, by decide⟩
    (prefixPartial 13 298367) = some ⟨13, 2, 0, 536147, 298367, 993, 16384⟩ := by
  decide +kernel

theorem context_13_298367_536147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298367 ⟨536147, by decide⟩ :=
  accepted_of_selected 13 298367 ⟨536147, by decide⟩ ⟨13, 2, 0, 536147, 298367, 993, 16384⟩
    (by decide) selected_cut_20918

theorem unmarked_context_12_74591_536148 : frontier 9 ⟨536148, by decide⟩
    (prefixCache 12 74591) (prefixPartial 12 74591) = false := by
  decide +kernel

theorem node_context_12_74591_536148 : EJMOriginalGlobalDAGData.nodes 9 ⟨536148, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨536080, by decide⟩,⟨536127, by decide⟩,⟨536147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74591_536148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74591 ⟨536148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74591
    ⟨536148, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨536080, by decide⟩,⟨536127, by decide⟩,⟨536147, by decide⟩]) unmarked_context_12_74591_536148 node_context_12_74591_536148
  intro a
  fin_cases a
  · exact context_13_298364_3444
  · exact context_13_298365_536080
  · exact context_13_298366_536127
  · exact context_13_298367_536147

theorem unmarked_context_11_18647_536149 : frontier 10 ⟨536149, by decide⟩
    (prefixCache 11 18647) (prefixPartial 11 18647) = false := by
  decide +kernel

theorem node_context_11_18647_536149 : EJMOriginalGlobalDAGData.nodes 10 ⟨536149, by decide⟩ =
    .split (coordinate 11) (![⟨535912, by decide⟩,⟨535969, by decide⟩,⟨536037, by decide⟩,⟨536148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18647_536149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18647 ⟨536149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18647
    ⟨536149, by decide⟩ (by decide) (![⟨535912, by decide⟩,⟨535969, by decide⟩,⟨536037, by decide⟩,⟨536148, by decide⟩]) unmarked_context_11_18647_536149 node_context_11_18647_536149
  intro a
  fin_cases a
  · exact context_12_74588_535912
  · exact context_12_74589_535969
  · exact context_12_74590_536037
  · exact context_12_74591_536148

theorem unmarked_context_10_4661_536150 : frontier 11 ⟨536150, by decide⟩
    (prefixCache 10 4661) (prefixPartial 10 4661) = false := by
  decide +kernel

theorem node_context_10_4661_536150 : EJMOriginalGlobalDAGData.nodes 11 ⟨536150, by decide⟩ =
    .split (coordinate 10) (![⟨535329, by decide⟩,⟨535586, by decide⟩,⟨535871, by decide⟩,⟨536149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4661_536150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4661 ⟨536150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4661
    ⟨536150, by decide⟩ (by decide) (![⟨535329, by decide⟩,⟨535586, by decide⟩,⟨535871, by decide⟩,⟨536149, by decide⟩]) unmarked_context_10_4661_536150 node_context_10_4661_536150
  intro a
  fin_cases a
  · exact context_11_18644_535329
  · exact context_11_18645_535586
  · exact context_11_18646_535871
  · exact context_11_18647_536149

theorem selected_cut_20919 : selected 9 ⟨536196, by decide⟩
    (prefixPartial 12 74592) = some ⟨12, 2, 0, 536196, 74592, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_74592_536196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74592 ⟨536196, by decide⟩ :=
  accepted_of_selected 12 74592 ⟨536196, by decide⟩ ⟨12, 2, 0, 536196, 74592, 1349, 65536⟩
    (by decide) selected_cut_20919

theorem selected_cut_20920 : selected 9 ⟨536240, by decide⟩
    (prefixPartial 12 74593) = some ⟨12, 2, 0, 536240, 74593, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_74593_536240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74593 ⟨536240, by decide⟩ :=
  accepted_of_selected 12 74593 ⟨536240, by decide⟩ ⟨12, 2, 0, 536240, 74593, 2325, 65536⟩
    (by decide) selected_cut_20920

theorem selected_cut_20921 : selected 9 ⟨536279, by decide⟩
    (prefixPartial 12 74594) = some ⟨12, 2, 0, 536279, 74594, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_74594_536279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74594 ⟨536279, by decide⟩ :=
  accepted_of_selected 12 74594 ⟨536279, by decide⟩ ⟨12, 2, 0, 536279, 74594, 2265, 65536⟩
    (by decide) selected_cut_20921

theorem selected_cut_20922 : selected 9 ⟨536318, by decide⟩
    (prefixPartial 12 74595) = some ⟨12, 2, 0, 536318, 74595, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_74595_536318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74595 ⟨536318, by decide⟩ :=
  accepted_of_selected 12 74595 ⟨536318, by decide⟩ ⟨12, 2, 0, 536318, 74595, 2153, 65536⟩
    (by decide) selected_cut_20922

theorem unmarked_context_11_18648_536319 : frontier 10 ⟨536319, by decide⟩
    (prefixCache 11 18648) (prefixPartial 11 18648) = false := by
  decide +kernel

theorem node_context_11_18648_536319 : EJMOriginalGlobalDAGData.nodes 10 ⟨536319, by decide⟩ =
    .split (coordinate 11) (![⟨536196, by decide⟩,⟨536240, by decide⟩,⟨536279, by decide⟩,⟨536318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18648_536319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18648 ⟨536319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18648
    ⟨536319, by decide⟩ (by decide) (![⟨536196, by decide⟩,⟨536240, by decide⟩,⟨536279, by decide⟩,⟨536318, by decide⟩]) unmarked_context_11_18648_536319 node_context_11_18648_536319
  intro a
  fin_cases a
  · exact context_12_74592_536196
  · exact context_12_74593_536240
  · exact context_12_74594_536279
  · exact context_12_74595_536318

theorem selected_cut_20923 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 74596) = some ⟨12, 1, 0, 4595, 74596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74596_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74596 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 74596 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 74596, 1, 65536⟩
    (by decide) selected_cut_20923

theorem selected_cut_20924 : selected 9 ⟨536348, by decide⟩
    (prefixPartial 12 74597) = some ⟨12, 2, 0, 536348, 74597, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_74597_536348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74597 ⟨536348, by decide⟩ :=
  accepted_of_selected 12 74597 ⟨536348, by decide⟩ ⟨12, 2, 0, 536348, 74597, 2401, 65536⟩
    (by decide) selected_cut_20924

theorem selected_cut_20925 : selected 9 ⟨536382, by decide⟩
    (prefixPartial 12 74598) = some ⟨12, 2, 0, 536382, 74598, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_74598_536382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74598 ⟨536382, by decide⟩ :=
  accepted_of_selected 12 74598 ⟨536382, by decide⟩ ⟨12, 2, 0, 536382, 74598, 1489, 65536⟩
    (by decide) selected_cut_20925

theorem selected_cut_20926 : selected 9 ⟨536415, by decide⟩
    (prefixPartial 12 74599) = some ⟨12, 2, 0, 536415, 74599, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_74599_536415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74599 ⟨536415, by decide⟩ :=
  accepted_of_selected 12 74599 ⟨536415, by decide⟩ ⟨12, 2, 0, 536415, 74599, 2217, 65536⟩
    (by decide) selected_cut_20926

theorem unmarked_context_11_18649_536416 : frontier 10 ⟨536416, by decide⟩
    (prefixCache 11 18649) (prefixPartial 11 18649) = false := by
  decide +kernel

theorem node_context_11_18649_536416 : EJMOriginalGlobalDAGData.nodes 10 ⟨536416, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨536348, by decide⟩,⟨536382, by decide⟩,⟨536415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18649_536416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18649 ⟨536416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18649
    ⟨536416, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨536348, by decide⟩,⟨536382, by decide⟩,⟨536415, by decide⟩]) unmarked_context_11_18649_536416 node_context_11_18649_536416
  intro a
  fin_cases a
  · exact context_12_74596_4595
  · exact context_12_74597_536348
  · exact context_12_74598_536382
  · exact context_12_74599_536415

theorem selected_cut_20927 : selected 10 ⟨536495, by decide⟩
    (prefixPartial 11 18650) = some ⟨11, 2, 0, 536495, 18650, 3889, 262144⟩ := by
  decide +kernel

theorem context_11_18650_536495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18650 ⟨536495, by decide⟩ :=
  accepted_of_selected 11 18650 ⟨536495, by decide⟩ ⟨11, 2, 0, 536495, 18650, 3889, 262144⟩
    (by decide) selected_cut_20927

theorem selected_cut_20928 : selected 10 ⟨536572, by decide⟩
    (prefixPartial 11 18651) = some ⟨11, 2, 0, 536572, 18651, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_18651_536572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18651 ⟨536572, by decide⟩ :=
  accepted_of_selected 11 18651 ⟨536572, by decide⟩ ⟨11, 2, 0, 536572, 18651, 1805, 262144⟩
    (by decide) selected_cut_20928

theorem unmarked_context_10_4662_536573 : frontier 11 ⟨536573, by decide⟩
    (prefixCache 10 4662) (prefixPartial 10 4662) = false := by
  decide +kernel

theorem node_context_10_4662_536573 : EJMOriginalGlobalDAGData.nodes 11 ⟨536573, by decide⟩ =
    .split (coordinate 10) (![⟨536319, by decide⟩,⟨536416, by decide⟩,⟨536495, by decide⟩,⟨536572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4662_536573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4662 ⟨536573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4662
    ⟨536573, by decide⟩ (by decide) (![⟨536319, by decide⟩,⟨536416, by decide⟩,⟨536495, by decide⟩,⟨536572, by decide⟩]) unmarked_context_10_4662_536573 node_context_10_4662_536573
  intro a
  fin_cases a
  · exact context_11_18648_536319
  · exact context_11_18649_536416
  · exact context_11_18650_536495
  · exact context_11_18651_536572

theorem selected_cut_20929 : selected 9 ⟨536607, by decide⟩
    (prefixPartial 12 74608) = some ⟨12, 2, 0, 536607, 74608, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_74608_536607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74608 ⟨536607, by decide⟩ :=
  accepted_of_selected 12 74608 ⟨536607, by decide⟩ ⟨12, 2, 0, 536607, 74608, 1933, 65536⟩
    (by decide) selected_cut_20929

theorem selected_cut_20930 : selected 9 ⟨536637, by decide⟩
    (prefixPartial 12 74609) = some ⟨12, 2, 0, 536637, 74609, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_74609_536637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74609 ⟨536637, by decide⟩ :=
  accepted_of_selected 12 74609 ⟨536637, by decide⟩ ⟨12, 2, 0, 536637, 74609, 2061, 65536⟩
    (by decide) selected_cut_20930

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
