/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover018
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_01827 : selected 9 ⟨61201, by decide⟩
    (prefixPartial 12 4734) = some ⟨12, 2, 0, 61201, 4734, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_4734_61201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4734 ⟨61201, by decide⟩ :=
  accepted_of_selected 12 4734 ⟨61201, by decide⟩ ⟨12, 2, 0, 61201, 4734, 3621, 65536⟩
    (by decide) selected_cut_01827

theorem selected_cut_01828 : selected 9 ⟨61235, by decide⟩
    (prefixPartial 12 4735) = some ⟨12, 2, 0, 61235, 4735, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_4735_61235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4735 ⟨61235, by decide⟩ :=
  accepted_of_selected 12 4735 ⟨61235, by decide⟩ ⟨12, 2, 0, 61235, 4735, 3761, 65536⟩
    (by decide) selected_cut_01828

theorem unmarked_context_11_1183_61236 : frontier 10 ⟨61236, by decide⟩
    (prefixCache 11 1183) (prefixPartial 11 1183) = false := by
  decide +kernel

theorem node_context_11_1183_61236 : EJMOriginalGlobalDAGData.nodes 10 ⟨61236, by decide⟩ =
    .split (coordinate 11) (![⟨61107, by decide⟩,⟨61154, by decide⟩,⟨61201, by decide⟩,⟨61235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1183_61236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1183 ⟨61236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1183
    ⟨61236, by decide⟩ (by decide) (![⟨61107, by decide⟩,⟨61154, by decide⟩,⟨61201, by decide⟩,⟨61235, by decide⟩]) unmarked_context_11_1183_61236 node_context_11_1183_61236
  intro a
  fin_cases a
  · exact context_12_4732_61107
  · exact context_12_4733_61154
  · exact context_12_4734_61201
  · exact context_12_4735_61235

theorem unmarked_context_10_295_61237 : frontier 11 ⟨61237, by decide⟩
    (prefixCache 10 295) (prefixPartial 10 295) = false := by
  decide +kernel

theorem node_context_10_295_61237 : EJMOriginalGlobalDAGData.nodes 11 ⟨61237, by decide⟩ =
    .split (coordinate 10) (![⟨60581, by decide⟩,⟨60805, by decide⟩,⟨61075, by decide⟩,⟨61236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_295_61237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 295 ⟨61237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 295
    ⟨61237, by decide⟩ (by decide) (![⟨60581, by decide⟩,⟨60805, by decide⟩,⟨61075, by decide⟩,⟨61236, by decide⟩]) unmarked_context_10_295_61237 node_context_10_295_61237
  intro a
  fin_cases a
  · exact context_11_1180_60581
  · exact context_11_1181_60805
  · exact context_11_1182_61075
  · exact context_11_1183_61236

theorem unmarked_context_9_73_61238 : frontier 12 ⟨61238, by decide⟩
    (prefixCache 9 73) (prefixPartial 9 73) = false := by
  decide +kernel

theorem node_context_9_73_61238 : EJMOriginalGlobalDAGData.nodes 12 ⟨61238, by decide⟩ =
    .split (coordinate 9) (![⟨58202, by decide⟩,⟨59389, by decide⟩,⟨60406, by decide⟩,⟨61237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_73_61238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 73 ⟨61238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 73
    ⟨61238, by decide⟩ (by decide) (![⟨58202, by decide⟩,⟨59389, by decide⟩,⟨60406, by decide⟩,⟨61237, by decide⟩]) unmarked_context_9_73_61238 node_context_9_73_61238
  intro a
  fin_cases a
  · exact context_10_292_58202
  · exact context_10_293_59389
  · exact context_10_294_60406
  · exact context_10_295_61237

theorem selected_cut_01829 : selected 9 ⟨61272, by decide⟩
    (prefixPartial 12 4736) = some ⟨12, 2, 0, 61272, 4736, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_4736_61272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4736 ⟨61272, by decide⟩ :=
  accepted_of_selected 12 4736 ⟨61272, by decide⟩ ⟨12, 2, 0, 61272, 4736, 3153, 65536⟩
    (by decide) selected_cut_01829

theorem selected_cut_01830 : selected 9 ⟨61343, by decide⟩
    (prefixPartial 12 4737) = some ⟨12, 2, 0, 61343, 4737, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_4737_61343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4737 ⟨61343, by decide⟩ :=
  accepted_of_selected 12 4737 ⟨61343, by decide⟩ ⟨12, 2, 0, 61343, 4737, 4045, 65536⟩
    (by decide) selected_cut_01830

theorem selected_cut_01831 : selected 9 ⟨61398, by decide⟩
    (prefixPartial 12 4738) = some ⟨12, 2, 0, 61398, 4738, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_4738_61398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4738 ⟨61398, by decide⟩ :=
  accepted_of_selected 12 4738 ⟨61398, by decide⟩ ⟨12, 2, 0, 61398, 4738, 3721, 65536⟩
    (by decide) selected_cut_01831

theorem selected_cut_01832 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18956) = some ⟨13, 1, 0, 3444, 18956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18956, 1, 16384⟩
    (by decide) selected_cut_01832

theorem selected_cut_01833 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18957) = some ⟨13, 1, 0, 3444, 18957, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18957_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18957 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18957 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18957, 1, 16384⟩
    (by decide) selected_cut_01833

theorem selected_cut_01834 : selected 8 ⟨61426, by decide⟩
    (prefixPartial 13 18958) = some ⟨13, 2, 0, 61426, 18958, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_18958_61426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18958 ⟨61426, by decide⟩ :=
  accepted_of_selected 13 18958 ⟨61426, by decide⟩ ⟨13, 2, 0, 61426, 18958, 2293, 16384⟩
    (by decide) selected_cut_01834

theorem selected_cut_01835 : selected 8 ⟨61466, by decide⟩
    (prefixPartial 13 18959) = some ⟨13, 2, 0, 61466, 18959, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_18959_61466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18959 ⟨61466, by decide⟩ :=
  accepted_of_selected 13 18959 ⟨61466, by decide⟩ ⟨13, 2, 0, 61466, 18959, 1829, 16384⟩
    (by decide) selected_cut_01835

theorem unmarked_context_12_4739_61467 : frontier 9 ⟨61467, by decide⟩
    (prefixCache 12 4739) (prefixPartial 12 4739) = false := by
  decide +kernel

theorem node_context_12_4739_61467 : EJMOriginalGlobalDAGData.nodes 9 ⟨61467, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨61426, by decide⟩,⟨61466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4739_61467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4739 ⟨61467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4739
    ⟨61467, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨61426, by decide⟩,⟨61466, by decide⟩]) unmarked_context_12_4739_61467 node_context_12_4739_61467
  intro a
  fin_cases a
  · exact context_13_18956_3444
  · exact context_13_18957_3444
  · exact context_13_18958_61426
  · exact context_13_18959_61466

theorem unmarked_context_11_1184_61468 : frontier 10 ⟨61468, by decide⟩
    (prefixCache 11 1184) (prefixPartial 11 1184) = false := by
  decide +kernel

theorem node_context_11_1184_61468 : EJMOriginalGlobalDAGData.nodes 10 ⟨61468, by decide⟩ =
    .split (coordinate 11) (![⟨61272, by decide⟩,⟨61343, by decide⟩,⟨61398, by decide⟩,⟨61467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1184_61468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1184 ⟨61468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1184
    ⟨61468, by decide⟩ (by decide) (![⟨61272, by decide⟩,⟨61343, by decide⟩,⟨61398, by decide⟩,⟨61467, by decide⟩]) unmarked_context_11_1184_61468 node_context_11_1184_61468
  intro a
  fin_cases a
  · exact context_12_4736_61272
  · exact context_12_4737_61343
  · exact context_12_4738_61398
  · exact context_12_4739_61467

theorem selected_cut_01836 : selected 9 ⟨61499, by decide⟩
    (prefixPartial 12 4740) = some ⟨12, 2, 0, 61499, 4740, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_4740_61499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4740 ⟨61499, by decide⟩ :=
  accepted_of_selected 12 4740 ⟨61499, by decide⟩ ⟨12, 2, 0, 61499, 4740, 2209, 65536⟩
    (by decide) selected_cut_01836

theorem selected_cut_01837 : selected 9 ⟨61536, by decide⟩
    (prefixPartial 12 4741) = some ⟨12, 2, 0, 61536, 4741, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_4741_61536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4741 ⟨61536, by decide⟩ :=
  accepted_of_selected 12 4741 ⟨61536, by decide⟩ ⟨12, 2, 0, 61536, 4741, 2901, 65536⟩
    (by decide) selected_cut_01837

theorem selected_cut_01838 : selected 9 ⟨61572, by decide⟩
    (prefixPartial 12 4742) = some ⟨12, 2, 0, 61572, 4742, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_4742_61572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4742 ⟨61572, by decide⟩ :=
  accepted_of_selected 12 4742 ⟨61572, by decide⟩ ⟨12, 2, 0, 61572, 4742, 2773, 65536⟩
    (by decide) selected_cut_01838

theorem selected_cut_01839 : selected 9 ⟨61607, by decide⟩
    (prefixPartial 12 4743) = some ⟨12, 2, 0, 61607, 4743, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_4743_61607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4743 ⟨61607, by decide⟩ :=
  accepted_of_selected 12 4743 ⟨61607, by decide⟩ ⟨12, 2, 0, 61607, 4743, 2945, 65536⟩
    (by decide) selected_cut_01839

theorem unmarked_context_11_1185_61608 : frontier 10 ⟨61608, by decide⟩
    (prefixCache 11 1185) (prefixPartial 11 1185) = false := by
  decide +kernel

theorem node_context_11_1185_61608 : EJMOriginalGlobalDAGData.nodes 10 ⟨61608, by decide⟩ =
    .split (coordinate 11) (![⟨61499, by decide⟩,⟨61536, by decide⟩,⟨61572, by decide⟩,⟨61607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1185_61608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1185 ⟨61608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1185
    ⟨61608, by decide⟩ (by decide) (![⟨61499, by decide⟩,⟨61536, by decide⟩,⟨61572, by decide⟩,⟨61607, by decide⟩]) unmarked_context_11_1185_61608 node_context_11_1185_61608
  intro a
  fin_cases a
  · exact context_12_4740_61499
  · exact context_12_4741_61536
  · exact context_12_4742_61572
  · exact context_12_4743_61607

theorem selected_cut_01840 : selected 9 ⟨61634, by decide⟩
    (prefixPartial 12 4744) = some ⟨12, 2, 0, 61634, 4744, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_4744_61634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4744 ⟨61634, by decide⟩ :=
  accepted_of_selected 12 4744 ⟨61634, by decide⟩ ⟨12, 2, 0, 61634, 4744, 1945, 65536⟩
    (by decide) selected_cut_01840

theorem selected_cut_01841 : selected 9 ⟨61668, by decide⟩
    (prefixPartial 12 4745) = some ⟨12, 2, 0, 61668, 4745, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_4745_61668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4745 ⟨61668, by decide⟩ :=
  accepted_of_selected 12 4745 ⟨61668, by decide⟩ ⟨12, 2, 0, 61668, 4745, 2649, 65536⟩
    (by decide) selected_cut_01841

theorem selected_cut_01842 : selected 9 ⟨61721, by decide⟩
    (prefixPartial 12 4746) = some ⟨12, 2, 0, 61721, 4746, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_4746_61721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4746 ⟨61721, by decide⟩ :=
  accepted_of_selected 12 4746 ⟨61721, by decide⟩ ⟨12, 2, 0, 61721, 4746, 3757, 65536⟩
    (by decide) selected_cut_01842

theorem selected_cut_01843 : selected 9 ⟨61750, by decide⟩
    (prefixPartial 12 4747) = some ⟨12, 2, 0, 61750, 4747, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_4747_61750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4747 ⟨61750, by decide⟩ :=
  accepted_of_selected 12 4747 ⟨61750, by decide⟩ ⟨12, 2, 0, 61750, 4747, 2561, 65536⟩
    (by decide) selected_cut_01843

theorem unmarked_context_11_1186_61751 : frontier 10 ⟨61751, by decide⟩
    (prefixCache 11 1186) (prefixPartial 11 1186) = false := by
  decide +kernel

theorem node_context_11_1186_61751 : EJMOriginalGlobalDAGData.nodes 10 ⟨61751, by decide⟩ =
    .split (coordinate 11) (![⟨61634, by decide⟩,⟨61668, by decide⟩,⟨61721, by decide⟩,⟨61750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1186_61751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1186 ⟨61751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1186
    ⟨61751, by decide⟩ (by decide) (![⟨61634, by decide⟩,⟨61668, by decide⟩,⟨61721, by decide⟩,⟨61750, by decide⟩]) unmarked_context_11_1186_61751 node_context_11_1186_61751
  intro a
  fin_cases a
  · exact context_12_4744_61634
  · exact context_12_4745_61668
  · exact context_12_4746_61721
  · exact context_12_4747_61750

theorem selected_cut_01844 : selected 9 ⟨61776, by decide⟩
    (prefixPartial 12 4748) = some ⟨12, 2, 0, 61776, 4748, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_4748_61776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4748 ⟨61776, by decide⟩ :=
  accepted_of_selected 12 4748 ⟨61776, by decide⟩ ⟨12, 2, 0, 61776, 4748, 2149, 65536⟩
    (by decide) selected_cut_01844

theorem selected_cut_01845 : selected 9 ⟨61807, by decide⟩
    (prefixPartial 12 4749) = some ⟨12, 2, 0, 61807, 4749, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_4749_61807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4749 ⟨61807, by decide⟩ :=
  accepted_of_selected 12 4749 ⟨61807, by decide⟩ ⟨12, 2, 0, 61807, 4749, 2761, 65536⟩
    (by decide) selected_cut_01845

theorem selected_cut_01846 : selected 9 ⟨61837, by decide⟩
    (prefixPartial 12 4750) = some ⟨12, 2, 0, 61837, 4750, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_4750_61837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4750 ⟨61837, by decide⟩ :=
  accepted_of_selected 12 4750 ⟨61837, by decide⟩ ⟨12, 2, 0, 61837, 4750, 2497, 65536⟩
    (by decide) selected_cut_01846

theorem selected_cut_01847 : selected 9 ⟨61868, by decide⟩
    (prefixPartial 12 4751) = some ⟨12, 2, 0, 61868, 4751, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_4751_61868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4751 ⟨61868, by decide⟩ :=
  accepted_of_selected 12 4751 ⟨61868, by decide⟩ ⟨12, 2, 0, 61868, 4751, 2621, 65536⟩
    (by decide) selected_cut_01847

theorem unmarked_context_11_1187_61869 : frontier 10 ⟨61869, by decide⟩
    (prefixCache 11 1187) (prefixPartial 11 1187) = false := by
  decide +kernel

theorem node_context_11_1187_61869 : EJMOriginalGlobalDAGData.nodes 10 ⟨61869, by decide⟩ =
    .split (coordinate 11) (![⟨61776, by decide⟩,⟨61807, by decide⟩,⟨61837, by decide⟩,⟨61868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1187_61869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1187 ⟨61869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1187
    ⟨61869, by decide⟩ (by decide) (![⟨61776, by decide⟩,⟨61807, by decide⟩,⟨61837, by decide⟩,⟨61868, by decide⟩]) unmarked_context_11_1187_61869 node_context_11_1187_61869
  intro a
  fin_cases a
  · exact context_12_4748_61776
  · exact context_12_4749_61807
  · exact context_12_4750_61837
  · exact context_12_4751_61868

theorem unmarked_context_10_296_61870 : frontier 11 ⟨61870, by decide⟩
    (prefixCache 10 296) (prefixPartial 10 296) = false := by
  decide +kernel

theorem node_context_10_296_61870 : EJMOriginalGlobalDAGData.nodes 11 ⟨61870, by decide⟩ =
    .split (coordinate 10) (![⟨61468, by decide⟩,⟨61608, by decide⟩,⟨61751, by decide⟩,⟨61869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_296_61870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 296 ⟨61870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 296
    ⟨61870, by decide⟩ (by decide) (![⟨61468, by decide⟩,⟨61608, by decide⟩,⟨61751, by decide⟩,⟨61869, by decide⟩]) unmarked_context_10_296_61870 node_context_10_296_61870
  intro a
  fin_cases a
  · exact context_11_1184_61468
  · exact context_11_1185_61608
  · exact context_11_1186_61751
  · exact context_11_1187_61869

theorem selected_cut_01848 : selected 9 ⟨61901, by decide⟩
    (prefixPartial 12 4752) = some ⟨12, 2, 0, 61901, 4752, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_4752_61901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4752 ⟨61901, by decide⟩ :=
  accepted_of_selected 12 4752 ⟨61901, by decide⟩ ⟨12, 2, 0, 61901, 4752, 2109, 65536⟩
    (by decide) selected_cut_01848

theorem selected_cut_01849 : selected 9 ⟨61940, by decide⟩
    (prefixPartial 12 4753) = some ⟨12, 2, 0, 61940, 4753, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_4753_61940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4753 ⟨61940, by decide⟩ :=
  accepted_of_selected 12 4753 ⟨61940, by decide⟩ ⟨12, 2, 0, 61940, 4753, 2857, 65536⟩
    (by decide) selected_cut_01849

theorem selected_cut_01850 : selected 9 ⟨61966, by decide⟩
    (prefixPartial 12 4754) = some ⟨12, 2, 0, 61966, 4754, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_4754_61966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4754 ⟨61966, by decide⟩ :=
  accepted_of_selected 12 4754 ⟨61966, by decide⟩ ⟨12, 2, 0, 61966, 4754, 2565, 65536⟩
    (by decide) selected_cut_01850

theorem selected_cut_01851 : selected 9 ⟨61997, by decide⟩
    (prefixPartial 12 4755) = some ⟨12, 2, 0, 61997, 4755, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_4755_61997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4755 ⟨61997, by decide⟩ :=
  accepted_of_selected 12 4755 ⟨61997, by decide⟩ ⟨12, 2, 0, 61997, 4755, 2721, 65536⟩
    (by decide) selected_cut_01851

theorem unmarked_context_11_1188_61998 : frontier 10 ⟨61998, by decide⟩
    (prefixCache 11 1188) (prefixPartial 11 1188) = false := by
  decide +kernel

theorem node_context_11_1188_61998 : EJMOriginalGlobalDAGData.nodes 10 ⟨61998, by decide⟩ =
    .split (coordinate 11) (![⟨61901, by decide⟩,⟨61940, by decide⟩,⟨61966, by decide⟩,⟨61997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1188_61998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1188 ⟨61998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1188
    ⟨61998, by decide⟩ (by decide) (![⟨61901, by decide⟩,⟨61940, by decide⟩,⟨61966, by decide⟩,⟨61997, by decide⟩]) unmarked_context_11_1188_61998 node_context_11_1188_61998
  intro a
  fin_cases a
  · exact context_12_4752_61901
  · exact context_12_4753_61940
  · exact context_12_4754_61966
  · exact context_12_4755_61997

theorem selected_cut_01852 : selected 9 ⟨62040, by decide⟩
    (prefixPartial 12 4756) = some ⟨12, 2, 0, 62040, 4756, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_4756_62040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4756 ⟨62040, by decide⟩ :=
  accepted_of_selected 12 4756 ⟨62040, by decide⟩ ⟨12, 2, 0, 62040, 4756, 2513, 65536⟩
    (by decide) selected_cut_01852

theorem selected_cut_01853 : selected 9 ⟨62093, by decide⟩
    (prefixPartial 12 4757) = some ⟨12, 2, 0, 62093, 4757, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_4757_62093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4757 ⟨62093, by decide⟩ :=
  accepted_of_selected 12 4757 ⟨62093, by decide⟩ ⟨12, 2, 0, 62093, 4757, 3217, 65536⟩
    (by decide) selected_cut_01853

theorem selected_cut_01854 : selected 9 ⟨62133, by decide⟩
    (prefixPartial 12 4758) = some ⟨12, 2, 0, 62133, 4758, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_4758_62133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4758 ⟨62133, by decide⟩ :=
  accepted_of_selected 12 4758 ⟨62133, by decide⟩ ⟨12, 2, 0, 62133, 4758, 2957, 65536⟩
    (by decide) selected_cut_01854

theorem selected_cut_01855 : selected 9 ⟨62172, by decide⟩
    (prefixPartial 12 4759) = some ⟨12, 2, 0, 62172, 4759, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_4759_62172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4759 ⟨62172, by decide⟩ :=
  accepted_of_selected 12 4759 ⟨62172, by decide⟩ ⟨12, 2, 0, 62172, 4759, 3097, 65536⟩
    (by decide) selected_cut_01855

theorem unmarked_context_11_1189_62173 : frontier 10 ⟨62173, by decide⟩
    (prefixCache 11 1189) (prefixPartial 11 1189) = false := by
  decide +kernel

theorem node_context_11_1189_62173 : EJMOriginalGlobalDAGData.nodes 10 ⟨62173, by decide⟩ =
    .split (coordinate 11) (![⟨62040, by decide⟩,⟨62093, by decide⟩,⟨62133, by decide⟩,⟨62172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1189_62173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1189 ⟨62173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1189
    ⟨62173, by decide⟩ (by decide) (![⟨62040, by decide⟩,⟨62093, by decide⟩,⟨62133, by decide⟩,⟨62172, by decide⟩]) unmarked_context_11_1189_62173 node_context_11_1189_62173
  intro a
  fin_cases a
  · exact context_12_4756_62040
  · exact context_12_4757_62093
  · exact context_12_4758_62133
  · exact context_12_4759_62172

theorem selected_cut_01856 : selected 9 ⟨62203, by decide⟩
    (prefixPartial 12 4760) = some ⟨12, 2, 0, 62203, 4760, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_4760_62203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4760 ⟨62203, by decide⟩ :=
  accepted_of_selected 12 4760 ⟨62203, by decide⟩ ⟨12, 2, 0, 62203, 4760, 2225, 65536⟩
    (by decide) selected_cut_01856

theorem selected_cut_01857 : selected 9 ⟨62251, by decide⟩
    (prefixPartial 12 4761) = some ⟨12, 2, 0, 62251, 4761, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_4761_62251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4761 ⟨62251, by decide⟩ :=
  accepted_of_selected 12 4761 ⟨62251, by decide⟩ ⟨12, 2, 0, 62251, 4761, 3093, 65536⟩
    (by decide) selected_cut_01857

theorem selected_cut_01858 : selected 9 ⟨62359, by decide⟩
    (prefixPartial 12 4762) = some ⟨12, 2, 0, 62359, 4762, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_4762_62359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4762 ⟨62359, by decide⟩ :=
  accepted_of_selected 12 4762 ⟨62359, by decide⟩ ⟨12, 2, 0, 62359, 4762, 4057, 65536⟩
    (by decide) selected_cut_01858

theorem selected_cut_01859 : selected 9 ⟨62396, by decide⟩
    (prefixPartial 12 4763) = some ⟨12, 2, 0, 62396, 4763, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_4763_62396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4763 ⟨62396, by decide⟩ :=
  accepted_of_selected 12 4763 ⟨62396, by decide⟩ ⟨12, 2, 0, 62396, 4763, 2693, 65536⟩
    (by decide) selected_cut_01859

theorem unmarked_context_11_1190_62397 : frontier 10 ⟨62397, by decide⟩
    (prefixCache 11 1190) (prefixPartial 11 1190) = false := by
  decide +kernel

theorem node_context_11_1190_62397 : EJMOriginalGlobalDAGData.nodes 10 ⟨62397, by decide⟩ =
    .split (coordinate 11) (![⟨62203, by decide⟩,⟨62251, by decide⟩,⟨62359, by decide⟩,⟨62396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1190_62397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1190 ⟨62397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1190
    ⟨62397, by decide⟩ (by decide) (![⟨62203, by decide⟩,⟨62251, by decide⟩,⟨62359, by decide⟩,⟨62396, by decide⟩]) unmarked_context_11_1190_62397 node_context_11_1190_62397
  intro a
  fin_cases a
  · exact context_12_4760_62203
  · exact context_12_4761_62251
  · exact context_12_4762_62359
  · exact context_12_4763_62396

theorem selected_cut_01860 : selected 9 ⟨62430, by decide⟩
    (prefixPartial 12 4764) = some ⟨12, 2, 0, 62430, 4764, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_4764_62430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4764 ⟨62430, by decide⟩ :=
  accepted_of_selected 12 4764 ⟨62430, by decide⟩ ⟨12, 2, 0, 62430, 4764, 2333, 65536⟩
    (by decide) selected_cut_01860

theorem selected_cut_01861 : selected 9 ⟨62476, by decide⟩
    (prefixPartial 12 4765) = some ⟨12, 2, 0, 62476, 4765, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_4765_62476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4765 ⟨62476, by decide⟩ :=
  accepted_of_selected 12 4765 ⟨62476, by decide⟩ ⟨12, 2, 0, 62476, 4765, 2961, 65536⟩
    (by decide) selected_cut_01861

theorem selected_cut_01862 : selected 9 ⟨62514, by decide⟩
    (prefixPartial 12 4766) = some ⟨12, 2, 0, 62514, 4766, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_4766_62514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4766 ⟨62514, by decide⟩ :=
  accepted_of_selected 12 4766 ⟨62514, by decide⟩ ⟨12, 2, 0, 62514, 4766, 2581, 65536⟩
    (by decide) selected_cut_01862

theorem selected_cut_01863 : selected 9 ⟨62550, by decide⟩
    (prefixPartial 12 4767) = some ⟨12, 2, 0, 62550, 4767, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_4767_62550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4767 ⟨62550, by decide⟩ :=
  accepted_of_selected 12 4767 ⟨62550, by decide⟩ ⟨12, 2, 0, 62550, 4767, 2733, 65536⟩
    (by decide) selected_cut_01863

theorem unmarked_context_11_1191_62551 : frontier 10 ⟨62551, by decide⟩
    (prefixCache 11 1191) (prefixPartial 11 1191) = false := by
  decide +kernel

theorem node_context_11_1191_62551 : EJMOriginalGlobalDAGData.nodes 10 ⟨62551, by decide⟩ =
    .split (coordinate 11) (![⟨62430, by decide⟩,⟨62476, by decide⟩,⟨62514, by decide⟩,⟨62550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1191_62551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1191 ⟨62551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1191
    ⟨62551, by decide⟩ (by decide) (![⟨62430, by decide⟩,⟨62476, by decide⟩,⟨62514, by decide⟩,⟨62550, by decide⟩]) unmarked_context_11_1191_62551 node_context_11_1191_62551
  intro a
  fin_cases a
  · exact context_12_4764_62430
  · exact context_12_4765_62476
  · exact context_12_4766_62514
  · exact context_12_4767_62550

theorem unmarked_context_10_297_62552 : frontier 11 ⟨62552, by decide⟩
    (prefixCache 10 297) (prefixPartial 10 297) = false := by
  decide +kernel

theorem node_context_10_297_62552 : EJMOriginalGlobalDAGData.nodes 11 ⟨62552, by decide⟩ =
    .split (coordinate 10) (![⟨61998, by decide⟩,⟨62173, by decide⟩,⟨62397, by decide⟩,⟨62551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_297_62552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 297 ⟨62552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 297
    ⟨62552, by decide⟩ (by decide) (![⟨61998, by decide⟩,⟨62173, by decide⟩,⟨62397, by decide⟩,⟨62551, by decide⟩]) unmarked_context_10_297_62552 node_context_10_297_62552
  intro a
  fin_cases a
  · exact context_11_1188_61998
  · exact context_11_1189_62173
  · exact context_11_1190_62397
  · exact context_11_1191_62551

theorem selected_cut_01864 : selected 9 ⟨62569, by decide⟩
    (prefixPartial 12 4768) = some ⟨12, 2, 0, 62569, 4768, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_4768_62569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4768 ⟨62569, by decide⟩ :=
  accepted_of_selected 12 4768 ⟨62569, by decide⟩ ⟨12, 2, 0, 62569, 4768, 1417, 65536⟩
    (by decide) selected_cut_01864

theorem selected_cut_01865 : selected 9 ⟨62593, by decide⟩
    (prefixPartial 12 4769) = some ⟨12, 2, 0, 62593, 4769, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_4769_62593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4769 ⟨62593, by decide⟩ :=
  accepted_of_selected 12 4769 ⟨62593, by decide⟩ ⟨12, 2, 0, 62593, 4769, 2053, 65536⟩
    (by decide) selected_cut_01865

theorem selected_cut_01866 : selected 9 ⟨62615, by decide⟩
    (prefixPartial 12 4770) = some ⟨12, 2, 0, 62615, 4770, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_4770_62615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4770 ⟨62615, by decide⟩ :=
  accepted_of_selected 12 4770 ⟨62615, by decide⟩ ⟨12, 2, 0, 62615, 4770, 1777, 65536⟩
    (by decide) selected_cut_01866

theorem selected_cut_01867 : selected 9 ⟨62633, by decide⟩
    (prefixPartial 12 4771) = some ⟨12, 2, 0, 62633, 4771, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_4771_62633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4771 ⟨62633, by decide⟩ :=
  accepted_of_selected 12 4771 ⟨62633, by decide⟩ ⟨12, 2, 0, 62633, 4771, 1845, 65536⟩
    (by decide) selected_cut_01867

theorem unmarked_context_11_1192_62634 : frontier 10 ⟨62634, by decide⟩
    (prefixCache 11 1192) (prefixPartial 11 1192) = false := by
  decide +kernel

theorem node_context_11_1192_62634 : EJMOriginalGlobalDAGData.nodes 10 ⟨62634, by decide⟩ =
    .split (coordinate 11) (![⟨62569, by decide⟩,⟨62593, by decide⟩,⟨62615, by decide⟩,⟨62633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1192_62634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1192 ⟨62634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1192
    ⟨62634, by decide⟩ (by decide) (![⟨62569, by decide⟩,⟨62593, by decide⟩,⟨62615, by decide⟩,⟨62633, by decide⟩]) unmarked_context_11_1192_62634 node_context_11_1192_62634
  intro a
  fin_cases a
  · exact context_12_4768_62569
  · exact context_12_4769_62593
  · exact context_12_4770_62615
  · exact context_12_4771_62633

theorem selected_cut_01868 : selected 9 ⟨62656, by decide⟩
    (prefixPartial 12 4772) = some ⟨12, 2, 0, 62656, 4772, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_4772_62656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4772 ⟨62656, by decide⟩ :=
  accepted_of_selected 12 4772 ⟨62656, by decide⟩ ⟨12, 2, 0, 62656, 4772, 1649, 65536⟩
    (by decide) selected_cut_01868

theorem selected_cut_01869 : selected 9 ⟨62684, by decide⟩
    (prefixPartial 12 4773) = some ⟨12, 2, 0, 62684, 4773, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_4773_62684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4773 ⟨62684, by decide⟩ :=
  accepted_of_selected 12 4773 ⟨62684, by decide⟩ ⟨12, 2, 0, 62684, 4773, 2225, 65536⟩
    (by decide) selected_cut_01869

theorem selected_cut_01870 : selected 9 ⟨62708, by decide⟩
    (prefixPartial 12 4774) = some ⟨12, 2, 0, 62708, 4774, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_4774_62708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4774 ⟨62708, by decide⟩ :=
  accepted_of_selected 12 4774 ⟨62708, by decide⟩ ⟨12, 2, 0, 62708, 4774, 1989, 65536⟩
    (by decide) selected_cut_01870

theorem selected_cut_01871 : selected 9 ⟨62733, by decide⟩
    (prefixPartial 12 4775) = some ⟨12, 2, 0, 62733, 4775, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_4775_62733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4775 ⟨62733, by decide⟩ :=
  accepted_of_selected 12 4775 ⟨62733, by decide⟩ ⟨12, 2, 0, 62733, 4775, 2025, 65536⟩
    (by decide) selected_cut_01871

theorem unmarked_context_11_1193_62734 : frontier 10 ⟨62734, by decide⟩
    (prefixCache 11 1193) (prefixPartial 11 1193) = false := by
  decide +kernel

theorem node_context_11_1193_62734 : EJMOriginalGlobalDAGData.nodes 10 ⟨62734, by decide⟩ =
    .split (coordinate 11) (![⟨62656, by decide⟩,⟨62684, by decide⟩,⟨62708, by decide⟩,⟨62733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1193_62734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1193 ⟨62734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1193
    ⟨62734, by decide⟩ (by decide) (![⟨62656, by decide⟩,⟨62684, by decide⟩,⟨62708, by decide⟩,⟨62733, by decide⟩]) unmarked_context_11_1193_62734 node_context_11_1193_62734
  intro a
  fin_cases a
  · exact context_12_4772_62656
  · exact context_12_4773_62684
  · exact context_12_4774_62708
  · exact context_12_4775_62733

theorem selected_cut_01872 : selected 9 ⟨62754, by decide⟩
    (prefixPartial 12 4776) = some ⟨12, 2, 0, 62754, 4776, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_4776_62754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4776 ⟨62754, by decide⟩ :=
  accepted_of_selected 12 4776 ⟨62754, by decide⟩ ⟨12, 2, 0, 62754, 4776, 1437, 65536⟩
    (by decide) selected_cut_01872

theorem selected_cut_01873 : selected 9 ⟨62776, by decide⟩
    (prefixPartial 12 4777) = some ⟨12, 2, 0, 62776, 4777, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_4777_62776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4777 ⟨62776, by decide⟩ :=
  accepted_of_selected 12 4777 ⟨62776, by decide⟩ ⟨12, 2, 0, 62776, 4777, 1965, 65536⟩
    (by decide) selected_cut_01873

theorem selected_cut_01874 : selected 9 ⟨62823, by decide⟩
    (prefixPartial 12 4778) = some ⟨12, 2, 0, 62823, 4778, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_4778_62823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4778 ⟨62823, by decide⟩ :=
  accepted_of_selected 12 4778 ⟨62823, by decide⟩ ⟨12, 2, 0, 62823, 4778, 2345, 65536⟩
    (by decide) selected_cut_01874

theorem selected_cut_01875 : selected 9 ⟨62845, by decide⟩
    (prefixPartial 12 4779) = some ⟨12, 2, 0, 62845, 4779, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_4779_62845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4779 ⟨62845, by decide⟩ :=
  accepted_of_selected 12 4779 ⟨62845, by decide⟩ ⟨12, 2, 0, 62845, 4779, 1741, 65536⟩
    (by decide) selected_cut_01875

theorem unmarked_context_11_1194_62846 : frontier 10 ⟨62846, by decide⟩
    (prefixCache 11 1194) (prefixPartial 11 1194) = false := by
  decide +kernel

theorem node_context_11_1194_62846 : EJMOriginalGlobalDAGData.nodes 10 ⟨62846, by decide⟩ =
    .split (coordinate 11) (![⟨62754, by decide⟩,⟨62776, by decide⟩,⟨62823, by decide⟩,⟨62845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1194_62846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1194 ⟨62846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1194
    ⟨62846, by decide⟩ (by decide) (![⟨62754, by decide⟩,⟨62776, by decide⟩,⟨62823, by decide⟩,⟨62845, by decide⟩]) unmarked_context_11_1194_62846 node_context_11_1194_62846
  intro a
  fin_cases a
  · exact context_12_4776_62754
  · exact context_12_4777_62776
  · exact context_12_4778_62823
  · exact context_12_4779_62845

theorem selected_cut_01876 : selected 9 ⟨62864, by decide⟩
    (prefixPartial 12 4780) = some ⟨12, 2, 0, 62864, 4780, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_4780_62864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4780 ⟨62864, by decide⟩ :=
  accepted_of_selected 12 4780 ⟨62864, by decide⟩ ⟨12, 2, 0, 62864, 4780, 1605, 65536⟩
    (by decide) selected_cut_01876

theorem selected_cut_01877 : selected 9 ⟨62886, by decide⟩
    (prefixPartial 12 4781) = some ⟨12, 2, 0, 62886, 4781, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_4781_62886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4781 ⟨62886, by decide⟩ :=
  accepted_of_selected 12 4781 ⟨62886, by decide⟩ ⟨12, 2, 0, 62886, 4781, 1973, 65536⟩
    (by decide) selected_cut_01877

theorem selected_cut_01878 : selected 9 ⟨62903, by decide⟩
    (prefixPartial 12 4782) = some ⟨12, 2, 0, 62903, 4782, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_4782_62903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4782 ⟨62903, by decide⟩ :=
  accepted_of_selected 12 4782 ⟨62903, by decide⟩ ⟨12, 2, 0, 62903, 4782, 1709, 65536⟩
    (by decide) selected_cut_01878

theorem selected_cut_01879 : selected 9 ⟨62921, by decide⟩
    (prefixPartial 12 4783) = some ⟨12, 2, 0, 62921, 4783, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_4783_62921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4783 ⟨62921, by decide⟩ :=
  accepted_of_selected 12 4783 ⟨62921, by decide⟩ ⟨12, 2, 0, 62921, 4783, 1813, 65536⟩
    (by decide) selected_cut_01879

theorem unmarked_context_11_1195_62922 : frontier 10 ⟨62922, by decide⟩
    (prefixCache 11 1195) (prefixPartial 11 1195) = false := by
  decide +kernel

theorem node_context_11_1195_62922 : EJMOriginalGlobalDAGData.nodes 10 ⟨62922, by decide⟩ =
    .split (coordinate 11) (![⟨62864, by decide⟩,⟨62886, by decide⟩,⟨62903, by decide⟩,⟨62921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1195_62922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1195 ⟨62922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1195
    ⟨62922, by decide⟩ (by decide) (![⟨62864, by decide⟩,⟨62886, by decide⟩,⟨62903, by decide⟩,⟨62921, by decide⟩]) unmarked_context_11_1195_62922 node_context_11_1195_62922
  intro a
  fin_cases a
  · exact context_12_4780_62864
  · exact context_12_4781_62886
  · exact context_12_4782_62903
  · exact context_12_4783_62921

theorem unmarked_context_10_298_62923 : frontier 11 ⟨62923, by decide⟩
    (prefixCache 10 298) (prefixPartial 10 298) = false := by
  decide +kernel

theorem node_context_10_298_62923 : EJMOriginalGlobalDAGData.nodes 11 ⟨62923, by decide⟩ =
    .split (coordinate 10) (![⟨62634, by decide⟩,⟨62734, by decide⟩,⟨62846, by decide⟩,⟨62922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_298_62923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 298 ⟨62923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 298
    ⟨62923, by decide⟩ (by decide) (![⟨62634, by decide⟩,⟨62734, by decide⟩,⟨62846, by decide⟩,⟨62922, by decide⟩]) unmarked_context_10_298_62923 node_context_10_298_62923
  intro a
  fin_cases a
  · exact context_11_1192_62634
  · exact context_11_1193_62734
  · exact context_11_1194_62846
  · exact context_11_1195_62922

theorem selected_cut_01880 : selected 9 ⟨62938, by decide⟩
    (prefixPartial 12 4784) = some ⟨12, 2, 0, 62938, 4784, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_4784_62938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4784 ⟨62938, by decide⟩ :=
  accepted_of_selected 12 4784 ⟨62938, by decide⟩ ⟨12, 2, 0, 62938, 4784, 1157, 65536⟩
    (by decide) selected_cut_01880

theorem selected_cut_01881 : selected 9 ⟨62959, by decide⟩
    (prefixPartial 12 4785) = some ⟨12, 2, 0, 62959, 4785, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_4785_62959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4785 ⟨62959, by decide⟩ :=
  accepted_of_selected 12 4785 ⟨62959, by decide⟩ ⟨12, 2, 0, 62959, 4785, 1549, 65536⟩
    (by decide) selected_cut_01881

theorem selected_cut_01882 : selected 9 ⟨62978, by decide⟩
    (prefixPartial 12 4786) = some ⟨12, 2, 0, 62978, 4786, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_4786_62978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4786 ⟨62978, by decide⟩ :=
  accepted_of_selected 12 4786 ⟨62978, by decide⟩ ⟨12, 2, 0, 62978, 4786, 1369, 65536⟩
    (by decide) selected_cut_01882

theorem selected_cut_01883 : selected 9 ⟨62998, by decide⟩
    (prefixPartial 12 4787) = some ⟨12, 2, 0, 62998, 4787, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_4787_62998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4787 ⟨62998, by decide⟩ :=
  accepted_of_selected 12 4787 ⟨62998, by decide⟩ ⟨12, 2, 0, 62998, 4787, 1505, 65536⟩
    (by decide) selected_cut_01883

theorem unmarked_context_11_1196_62999 : frontier 10 ⟨62999, by decide⟩
    (prefixCache 11 1196) (prefixPartial 11 1196) = false := by
  decide +kernel

theorem node_context_11_1196_62999 : EJMOriginalGlobalDAGData.nodes 10 ⟨62999, by decide⟩ =
    .split (coordinate 11) (![⟨62938, by decide⟩,⟨62959, by decide⟩,⟨62978, by decide⟩,⟨62998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1196_62999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1196 ⟨62999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1196
    ⟨62999, by decide⟩ (by decide) (![⟨62938, by decide⟩,⟨62959, by decide⟩,⟨62978, by decide⟩,⟨62998, by decide⟩]) unmarked_context_11_1196_62999 node_context_11_1196_62999
  intro a
  fin_cases a
  · exact context_12_4784_62938
  · exact context_12_4785_62959
  · exact context_12_4786_62978
  · exact context_12_4787_62998

theorem selected_cut_01884 : selected 9 ⟨63017, by decide⟩
    (prefixPartial 12 4788) = some ⟨12, 2, 0, 63017, 4788, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_4788_63017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4788 ⟨63017, by decide⟩ :=
  accepted_of_selected 12 4788 ⟨63017, by decide⟩ ⟨12, 2, 0, 63017, 4788, 1389, 65536⟩
    (by decide) selected_cut_01884

theorem selected_cut_01885 : selected 9 ⟨63041, by decide⟩
    (prefixPartial 12 4789) = some ⟨12, 2, 0, 63041, 4789, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_4789_63041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4789 ⟨63041, by decide⟩ :=
  accepted_of_selected 12 4789 ⟨63041, by decide⟩ ⟨12, 2, 0, 63041, 4789, 1701, 65536⟩
    (by decide) selected_cut_01885

theorem selected_cut_01886 : selected 9 ⟨63063, by decide⟩
    (prefixPartial 12 4790) = some ⟨12, 2, 0, 63063, 4790, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_4790_63063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4790 ⟨63063, by decide⟩ :=
  accepted_of_selected 12 4790 ⟨63063, by decide⟩ ⟨12, 2, 0, 63063, 4790, 1561, 65536⟩
    (by decide) selected_cut_01886

theorem selected_cut_01887 : selected 9 ⟨63094, by decide⟩
    (prefixPartial 12 4791) = some ⟨12, 2, 0, 63094, 4791, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_4791_63094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4791 ⟨63094, by decide⟩ :=
  accepted_of_selected 12 4791 ⟨63094, by decide⟩ ⟨12, 2, 0, 63094, 4791, 1753, 65536⟩
    (by decide) selected_cut_01887

theorem unmarked_context_11_1197_63095 : frontier 10 ⟨63095, by decide⟩
    (prefixCache 11 1197) (prefixPartial 11 1197) = false := by
  decide +kernel

theorem node_context_11_1197_63095 : EJMOriginalGlobalDAGData.nodes 10 ⟨63095, by decide⟩ =
    .split (coordinate 11) (![⟨63017, by decide⟩,⟨63041, by decide⟩,⟨63063, by decide⟩,⟨63094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1197_63095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1197 ⟨63095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1197
    ⟨63095, by decide⟩ (by decide) (![⟨63017, by decide⟩,⟨63041, by decide⟩,⟨63063, by decide⟩,⟨63094, by decide⟩]) unmarked_context_11_1197_63095 node_context_11_1197_63095
  intro a
  fin_cases a
  · exact context_12_4788_63017
  · exact context_12_4789_63041
  · exact context_12_4790_63063
  · exact context_12_4791_63094

theorem selected_cut_01888 : selected 9 ⟨63109, by decide⟩
    (prefixPartial 12 4792) = some ⟨12, 2, 0, 63109, 4792, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_4792_63109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4792 ⟨63109, by decide⟩ :=
  accepted_of_selected 12 4792 ⟨63109, by decide⟩ ⟨12, 2, 0, 63109, 4792, 1225, 65536⟩
    (by decide) selected_cut_01888

theorem selected_cut_01889 : selected 9 ⟨63131, by decide⟩
    (prefixPartial 12 4793) = some ⟨12, 2, 0, 63131, 4793, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_4793_63131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4793 ⟨63131, by decide⟩ :=
  accepted_of_selected 12 4793 ⟨63131, by decide⟩ ⟨12, 2, 0, 63131, 4793, 1621, 65536⟩
    (by decide) selected_cut_01889

theorem selected_cut_01890 : selected 9 ⟨63166, by decide⟩
    (prefixPartial 12 4794) = some ⟨12, 2, 0, 63166, 4794, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_4794_63166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4794 ⟨63166, by decide⟩ :=
  accepted_of_selected 12 4794 ⟨63166, by decide⟩ ⟨12, 2, 0, 63166, 4794, 1977, 65536⟩
    (by decide) selected_cut_01890

theorem selected_cut_01891 : selected 9 ⟨63189, by decide⟩
    (prefixPartial 12 4795) = some ⟨12, 2, 0, 63189, 4795, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_4795_63189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4795 ⟨63189, by decide⟩ :=
  accepted_of_selected 12 4795 ⟨63189, by decide⟩ ⟨12, 2, 0, 63189, 4795, 1517, 65536⟩
    (by decide) selected_cut_01891

theorem unmarked_context_11_1198_63190 : frontier 10 ⟨63190, by decide⟩
    (prefixCache 11 1198) (prefixPartial 11 1198) = false := by
  decide +kernel

theorem node_context_11_1198_63190 : EJMOriginalGlobalDAGData.nodes 10 ⟨63190, by decide⟩ =
    .split (coordinate 11) (![⟨63109, by decide⟩,⟨63131, by decide⟩,⟨63166, by decide⟩,⟨63189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1198_63190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1198 ⟨63190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1198
    ⟨63190, by decide⟩ (by decide) (![⟨63109, by decide⟩,⟨63131, by decide⟩,⟨63166, by decide⟩,⟨63189, by decide⟩]) unmarked_context_11_1198_63190 node_context_11_1198_63190
  intro a
  fin_cases a
  · exact context_12_4792_63109
  · exact context_12_4793_63131
  · exact context_12_4794_63166
  · exact context_12_4795_63189

theorem selected_cut_01892 : selected 9 ⟨63203, by decide⟩
    (prefixPartial 12 4796) = some ⟨12, 2, 0, 63203, 4796, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_4796_63203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4796 ⟨63203, by decide⟩ :=
  accepted_of_selected 12 4796 ⟨63203, by decide⟩ ⟨12, 2, 0, 63203, 4796, 1157, 65536⟩
    (by decide) selected_cut_01892

theorem selected_cut_01893 : selected 9 ⟨63219, by decide⟩
    (prefixPartial 12 4797) = some ⟨12, 2, 0, 63219, 4797, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_4797_63219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4797 ⟨63219, by decide⟩ :=
  accepted_of_selected 12 4797 ⟨63219, by decide⟩ ⟨12, 2, 0, 63219, 4797, 1385, 65536⟩
    (by decide) selected_cut_01893

theorem selected_cut_01894 : selected 9 ⟨63231, by decide⟩
    (prefixPartial 12 4798) = some ⟨12, 2, 0, 63231, 4798, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_4798_63231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4798 ⟨63231, by decide⟩ :=
  accepted_of_selected 12 4798 ⟨63231, by decide⟩ ⟨12, 2, 0, 63231, 4798, 1189, 65536⟩
    (by decide) selected_cut_01894

theorem selected_cut_01895 : selected 9 ⟨63251, by decide⟩
    (prefixPartial 12 4799) = some ⟨12, 2, 0, 63251, 4799, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_4799_63251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4799 ⟨63251, by decide⟩ :=
  accepted_of_selected 12 4799 ⟨63251, by decide⟩ ⟨12, 2, 0, 63251, 4799, 1389, 65536⟩
    (by decide) selected_cut_01895

theorem unmarked_context_11_1199_63252 : frontier 10 ⟨63252, by decide⟩
    (prefixCache 11 1199) (prefixPartial 11 1199) = false := by
  decide +kernel

theorem node_context_11_1199_63252 : EJMOriginalGlobalDAGData.nodes 10 ⟨63252, by decide⟩ =
    .split (coordinate 11) (![⟨63203, by decide⟩,⟨63219, by decide⟩,⟨63231, by decide⟩,⟨63251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1199_63252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1199 ⟨63252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1199
    ⟨63252, by decide⟩ (by decide) (![⟨63203, by decide⟩,⟨63219, by decide⟩,⟨63231, by decide⟩,⟨63251, by decide⟩]) unmarked_context_11_1199_63252 node_context_11_1199_63252
  intro a
  fin_cases a
  · exact context_12_4796_63203
  · exact context_12_4797_63219
  · exact context_12_4798_63231
  · exact context_12_4799_63251

theorem unmarked_context_10_299_63253 : frontier 11 ⟨63253, by decide⟩
    (prefixCache 10 299) (prefixPartial 10 299) = false := by
  decide +kernel

theorem node_context_10_299_63253 : EJMOriginalGlobalDAGData.nodes 11 ⟨63253, by decide⟩ =
    .split (coordinate 10) (![⟨62999, by decide⟩,⟨63095, by decide⟩,⟨63190, by decide⟩,⟨63252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_299_63253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 299 ⟨63253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 299
    ⟨63253, by decide⟩ (by decide) (![⟨62999, by decide⟩,⟨63095, by decide⟩,⟨63190, by decide⟩,⟨63252, by decide⟩]) unmarked_context_10_299_63253 node_context_10_299_63253
  intro a
  fin_cases a
  · exact context_11_1196_62999
  · exact context_11_1197_63095
  · exact context_11_1198_63190
  · exact context_11_1199_63252

theorem unmarked_context_9_74_63254 : frontier 12 ⟨63254, by decide⟩
    (prefixCache 9 74) (prefixPartial 9 74) = false := by
  decide +kernel

theorem node_context_9_74_63254 : EJMOriginalGlobalDAGData.nodes 12 ⟨63254, by decide⟩ =
    .split (coordinate 9) (![⟨61870, by decide⟩,⟨62552, by decide⟩,⟨62923, by decide⟩,⟨63253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_74_63254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 74 ⟨63254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 74
    ⟨63254, by decide⟩ (by decide) (![⟨61870, by decide⟩,⟨62552, by decide⟩,⟨62923, by decide⟩,⟨63253, by decide⟩]) unmarked_context_9_74_63254 node_context_9_74_63254
  intro a
  fin_cases a
  · exact context_10_296_61870
  · exact context_10_297_62552
  · exact context_10_298_62923
  · exact context_10_299_63253

theorem selected_cut_01896 : selected 9 ⟨63272, by decide⟩
    (prefixPartial 12 4800) = some ⟨12, 2, 0, 63272, 4800, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_4800_63272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4800 ⟨63272, by decide⟩ :=
  accepted_of_selected 12 4800 ⟨63272, by decide⟩ ⟨12, 2, 0, 63272, 4800, 1217, 65536⟩
    (by decide) selected_cut_01896

theorem selected_cut_01897 : selected 9 ⟨63298, by decide⟩
    (prefixPartial 12 4801) = some ⟨12, 2, 0, 63298, 4801, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_4801_63298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4801 ⟨63298, by decide⟩ :=
  accepted_of_selected 12 4801 ⟨63298, by decide⟩ ⟨12, 2, 0, 63298, 4801, 1525, 65536⟩
    (by decide) selected_cut_01897

theorem selected_cut_01898 : selected 9 ⟨63323, by decide⟩
    (prefixPartial 12 4802) = some ⟨12, 2, 0, 63323, 4802, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_4802_63323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4802 ⟨63323, by decide⟩ :=
  accepted_of_selected 12 4802 ⟨63323, by decide⟩ ⟨12, 2, 0, 63323, 4802, 1501, 65536⟩
    (by decide) selected_cut_01898

theorem selected_cut_01899 : selected 9 ⟨63344, by decide⟩
    (prefixPartial 12 4803) = some ⟨12, 2, 0, 63344, 4803, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_4803_63344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4803 ⟨63344, by decide⟩ :=
  accepted_of_selected 12 4803 ⟨63344, by decide⟩ ⟨12, 2, 0, 63344, 4803, 1473, 65536⟩
    (by decide) selected_cut_01899

theorem unmarked_context_11_1200_63345 : frontier 10 ⟨63345, by decide⟩
    (prefixCache 11 1200) (prefixPartial 11 1200) = false := by
  decide +kernel

theorem node_context_11_1200_63345 : EJMOriginalGlobalDAGData.nodes 10 ⟨63345, by decide⟩ =
    .split (coordinate 11) (![⟨63272, by decide⟩,⟨63298, by decide⟩,⟨63323, by decide⟩,⟨63344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1200_63345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1200 ⟨63345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1200
    ⟨63345, by decide⟩ (by decide) (![⟨63272, by decide⟩,⟨63298, by decide⟩,⟨63323, by decide⟩,⟨63344, by decide⟩]) unmarked_context_11_1200_63345 node_context_11_1200_63345
  intro a
  fin_cases a
  · exact context_12_4800_63272
  · exact context_12_4801_63298
  · exact context_12_4802_63323
  · exact context_12_4803_63344

theorem selected_cut_01900 : selected 10 ⟨63385, by decide⟩
    (prefixPartial 11 1201) = some ⟨11, 2, 0, 63385, 1201, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_1201_63385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1201 ⟨63385, by decide⟩ :=
  accepted_of_selected 11 1201 ⟨63385, by decide⟩ ⟨11, 2, 0, 63385, 1201, 3565, 262144⟩
    (by decide) selected_cut_01900

theorem selected_cut_01901 : selected 10 ⟨63424, by decide⟩
    (prefixPartial 11 1202) = some ⟨11, 2, 0, 63424, 1202, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_1202_63424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1202 ⟨63424, by decide⟩ :=
  accepted_of_selected 11 1202 ⟨63424, by decide⟩ ⟨11, 2, 0, 63424, 1202, 3337, 262144⟩
    (by decide) selected_cut_01901

theorem selected_cut_01902 : selected 10 ⟨63496, by decide⟩
    (prefixPartial 11 1203) = some ⟨11, 2, 0, 63496, 1203, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_1203_63496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1203 ⟨63496, by decide⟩ :=
  accepted_of_selected 11 1203 ⟨63496, by decide⟩ ⟨11, 2, 0, 63496, 1203, 3313, 262144⟩
    (by decide) selected_cut_01902

theorem unmarked_context_10_300_63497 : frontier 11 ⟨63497, by decide⟩
    (prefixCache 10 300) (prefixPartial 10 300) = false := by
  decide +kernel

theorem node_context_10_300_63497 : EJMOriginalGlobalDAGData.nodes 11 ⟨63497, by decide⟩ =
    .split (coordinate 10) (![⟨63345, by decide⟩,⟨63385, by decide⟩,⟨63424, by decide⟩,⟨63496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_300_63497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 300 ⟨63497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 300
    ⟨63497, by decide⟩ (by decide) (![⟨63345, by decide⟩,⟨63385, by decide⟩,⟨63424, by decide⟩,⟨63496, by decide⟩]) unmarked_context_10_300_63497 node_context_10_300_63497
  intro a
  fin_cases a
  · exact context_11_1200_63345
  · exact context_11_1201_63385
  · exact context_11_1202_63424
  · exact context_11_1203_63496

theorem selected_cut_01903 : selected 10 ⟨63526, by decide⟩
    (prefixPartial 11 1204) = some ⟨11, 2, 0, 63526, 1204, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_1204_63526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1204 ⟨63526, by decide⟩ :=
  accepted_of_selected 11 1204 ⟨63526, by decide⟩ ⟨11, 2, 0, 63526, 1204, 2725, 262144⟩
    (by decide) selected_cut_01903

theorem selected_cut_01904 : selected 10 ⟨63556, by decide⟩
    (prefixPartial 11 1205) = some ⟨11, 2, 0, 63556, 1205, 2689, 262144⟩ := by
  decide +kernel

theorem context_11_1205_63556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1205 ⟨63556, by decide⟩ :=
  accepted_of_selected 11 1205 ⟨63556, by decide⟩ ⟨11, 2, 0, 63556, 1205, 2689, 262144⟩
    (by decide) selected_cut_01904

theorem selected_cut_01905 : selected 10 ⟨63585, by decide⟩
    (prefixPartial 11 1206) = some ⟨11, 2, 0, 63585, 1206, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_1206_63585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1206 ⟨63585, by decide⟩ :=
  accepted_of_selected 11 1206 ⟨63585, by decide⟩ ⟨11, 2, 0, 63585, 1206, 2441, 262144⟩
    (by decide) selected_cut_01905

theorem selected_cut_01906 : selected 10 ⟨63611, by decide⟩
    (prefixPartial 11 1207) = some ⟨11, 2, 0, 63611, 1207, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_1207_63611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1207 ⟨63611, by decide⟩ :=
  accepted_of_selected 11 1207 ⟨63611, by decide⟩ ⟨11, 2, 0, 63611, 1207, 2057, 262144⟩
    (by decide) selected_cut_01906

theorem unmarked_context_10_301_63612 : frontier 11 ⟨63612, by decide⟩
    (prefixCache 10 301) (prefixPartial 10 301) = false := by
  decide +kernel

theorem node_context_10_301_63612 : EJMOriginalGlobalDAGData.nodes 11 ⟨63612, by decide⟩ =
    .split (coordinate 10) (![⟨63526, by decide⟩,⟨63556, by decide⟩,⟨63585, by decide⟩,⟨63611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_301_63612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 301 ⟨63612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 301
    ⟨63612, by decide⟩ (by decide) (![⟨63526, by decide⟩,⟨63556, by decide⟩,⟨63585, by decide⟩,⟨63611, by decide⟩]) unmarked_context_10_301_63612 node_context_10_301_63612
  intro a
  fin_cases a
  · exact context_11_1204_63526
  · exact context_11_1205_63556
  · exact context_11_1206_63585
  · exact context_11_1207_63611

theorem selected_cut_01907 : selected 10 ⟨63631, by decide⟩
    (prefixPartial 11 1208) = some ⟨11, 2, 0, 63631, 1208, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_1208_63631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1208 ⟨63631, by decide⟩ :=
  accepted_of_selected 11 1208 ⟨63631, by decide⟩ ⟨11, 2, 0, 63631, 1208, 1401, 262144⟩
    (by decide) selected_cut_01907

theorem selected_cut_01908 : selected 10 ⟨63652, by decide⟩
    (prefixPartial 11 1209) = some ⟨11, 2, 0, 63652, 1209, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_1209_63652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1209 ⟨63652, by decide⟩ :=
  accepted_of_selected 11 1209 ⟨63652, by decide⟩ ⟨11, 2, 0, 63652, 1209, 1381, 262144⟩
    (by decide) selected_cut_01908

theorem selected_cut_01909 : selected 10 ⟨63672, by decide⟩
    (prefixPartial 11 1210) = some ⟨11, 2, 0, 63672, 1210, 1157, 262144⟩ := by
  decide +kernel

theorem context_11_1210_63672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1210 ⟨63672, by decide⟩ :=
  accepted_of_selected 11 1210 ⟨63672, by decide⟩ ⟨11, 2, 0, 63672, 1210, 1157, 262144⟩
    (by decide) selected_cut_01909

theorem selected_cut_01910 : selected 10 ⟨63687, by decide⟩
    (prefixPartial 11 1211) = some ⟨11, 2, 0, 63687, 1211, 945, 262144⟩ := by
  decide +kernel

theorem context_11_1211_63687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1211 ⟨63687, by decide⟩ :=
  accepted_of_selected 11 1211 ⟨63687, by decide⟩ ⟨11, 2, 0, 63687, 1211, 945, 262144⟩
    (by decide) selected_cut_01910

theorem unmarked_context_10_302_63688 : frontier 11 ⟨63688, by decide⟩
    (prefixCache 10 302) (prefixPartial 10 302) = false := by
  decide +kernel

theorem node_context_10_302_63688 : EJMOriginalGlobalDAGData.nodes 11 ⟨63688, by decide⟩ =
    .split (coordinate 10) (![⟨63631, by decide⟩,⟨63652, by decide⟩,⟨63672, by decide⟩,⟨63687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_302_63688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 302 ⟨63688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 302
    ⟨63688, by decide⟩ (by decide) (![⟨63631, by decide⟩,⟨63652, by decide⟩,⟨63672, by decide⟩,⟨63687, by decide⟩]) unmarked_context_10_302_63688 node_context_10_302_63688
  intro a
  fin_cases a
  · exact context_11_1208_63631
  · exact context_11_1209_63652
  · exact context_11_1210_63672
  · exact context_11_1211_63687

theorem selected_cut_01911 : selected 11 ⟨63746, by decide⟩
    (prefixPartial 10 303) = some ⟨10, 2, 0, 63746, 303, 1721, 1048576⟩ := by
  decide +kernel

theorem context_10_303_63746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 303 ⟨63746, by decide⟩ :=
  accepted_of_selected 10 303 ⟨63746, by decide⟩ ⟨10, 2, 0, 63746, 303, 1721, 1048576⟩
    (by decide) selected_cut_01911

theorem unmarked_context_9_75_63747 : frontier 12 ⟨63747, by decide⟩
    (prefixCache 9 75) (prefixPartial 9 75) = false := by
  decide +kernel

theorem node_context_9_75_63747 : EJMOriginalGlobalDAGData.nodes 12 ⟨63747, by decide⟩ =
    .split (coordinate 9) (![⟨63497, by decide⟩,⟨63612, by decide⟩,⟨63688, by decide⟩,⟨63746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_75_63747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 75 ⟨63747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 75
    ⟨63747, by decide⟩ (by decide) (![⟨63497, by decide⟩,⟨63612, by decide⟩,⟨63688, by decide⟩,⟨63746, by decide⟩]) unmarked_context_9_75_63747 node_context_9_75_63747
  intro a
  fin_cases a
  · exact context_10_300_63497
  · exact context_10_301_63612
  · exact context_10_302_63688
  · exact context_10_303_63746

theorem unmarked_context_8_18_63748 : frontier 13 ⟨63748, by decide⟩
    (prefixCache 8 18) (prefixPartial 8 18) = false := by
  decide +kernel

theorem node_context_8_18_63748 : EJMOriginalGlobalDAGData.nodes 13 ⟨63748, by decide⟩ =
    .split (coordinate 8) (![⟨56714, by decide⟩,⟨61238, by decide⟩,⟨63254, by decide⟩,⟨63747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_18_63748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 18 ⟨63748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 18
    ⟨63748, by decide⟩ (by decide) (![⟨56714, by decide⟩,⟨61238, by decide⟩,⟨63254, by decide⟩,⟨63747, by decide⟩]) unmarked_context_8_18_63748 node_context_8_18_63748
  intro a
  fin_cases a
  · exact context_9_72_56714
  · exact context_9_73_61238
  · exact context_9_74_63254
  · exact context_9_75_63747

theorem selected_cut_01912 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 19) = some ⟨8, 1, 0, 14298, 19, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_19_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 19 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 19 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 19, 1, 16777216⟩
    (by decide) selected_cut_01912

theorem unmarked_context_7_4_63749 : frontier 14 ⟨63749, by decide⟩
    (prefixCache 7 4) (prefixPartial 7 4) = false := by
  decide +kernel

theorem node_context_7_4_63749 : EJMOriginalGlobalDAGData.nodes 14 ⟨63749, by decide⟩ =
    .split (coordinate 7) (![⟨39813, by decide⟩,⟨48545, by decide⟩,⟨63748, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_4_63749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 4 ⟨63749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 4
    ⟨63749, by decide⟩ (by decide) (![⟨39813, by decide⟩,⟨48545, by decide⟩,⟨63748, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_4_63749 node_context_7_4_63749
  intro a
  fin_cases a
  · exact context_8_16_39813
  · exact context_8_17_48545
  · exact context_8_18_63748
  · exact context_8_19_14298

theorem selected_cut_01913 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 20) = some ⟨8, 1, 0, 14300, 20, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_20_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 20 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 20 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 20, 1, 16777216⟩
    (by decide) selected_cut_01913

theorem selected_cut_01914 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 5376) = some ⟨12, 1, 0, 34034, 5376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5376_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5376 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 5376 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 5376, 1, 65536⟩
    (by decide) selected_cut_01914

theorem selected_cut_01915 : selected 8 ⟨63807, by decide⟩
    (prefixPartial 13 21508) = some ⟨13, 2, 0, 63807, 21508, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_21508_63807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21508 ⟨63807, by decide⟩ :=
  accepted_of_selected 13 21508 ⟨63807, by decide⟩ ⟨13, 2, 0, 63807, 21508, 2569, 16384⟩
    (by decide) selected_cut_01915

theorem selected_cut_01916 : selected 8 ⟨63834, by decide⟩
    (prefixPartial 13 21509) = some ⟨13, 2, 0, 63834, 21509, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_21509_63834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21509 ⟨63834, by decide⟩ :=
  accepted_of_selected 13 21509 ⟨63834, by decide⟩ ⟨13, 2, 0, 63834, 21509, 1617, 16384⟩
    (by decide) selected_cut_01916

theorem selected_cut_01917 : selected 8 ⟨63852, by decide⟩
    (prefixPartial 13 21510) = some ⟨13, 2, 0, 63852, 21510, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_21510_63852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21510 ⟨63852, by decide⟩ :=
  accepted_of_selected 13 21510 ⟨63852, by decide⟩ ⟨13, 2, 0, 63852, 21510, 2073, 16384⟩
    (by decide) selected_cut_01917

theorem selected_cut_01918 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 21511) = some ⟨13, 1, 0, 414, 21511, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21511_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21511 ⟨414, by decide⟩ :=
  accepted_of_selected 13 21511 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 21511, 1, 16384⟩
    (by decide) selected_cut_01918

theorem unmarked_context_12_5377_63853 : frontier 9 ⟨63853, by decide⟩
    (prefixCache 12 5377) (prefixPartial 12 5377) = false := by
  decide +kernel

theorem node_context_12_5377_63853 : EJMOriginalGlobalDAGData.nodes 9 ⟨63853, by decide⟩ =
    .split (coordinate 12) (![⟨63807, by decide⟩,⟨63834, by decide⟩,⟨63852, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5377_63853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5377 ⟨63853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5377
    ⟨63853, by decide⟩ (by decide) (![⟨63807, by decide⟩,⟨63834, by decide⟩,⟨63852, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_5377_63853 node_context_12_5377_63853
  intro a
  fin_cases a
  · exact context_13_21508_63807
  · exact context_13_21509_63834
  · exact context_13_21510_63852
  · exact context_13_21511_414

theorem selected_cut_01919 : selected 7 ⟨63889, by decide⟩
    (prefixPartial 14 86048) = some ⟨14, 2, 0, 63889, 86048, 1733, 4096⟩ := by
  decide +kernel

theorem context_14_86048_63889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86048 ⟨63889, by decide⟩ :=
  accepted_of_selected 14 86048 ⟨63889, by decide⟩ ⟨14, 2, 0, 63889, 86048, 1733, 4096⟩
    (by decide) selected_cut_01919

theorem selected_cut_01920 : selected 7 ⟨63910, by decide⟩
    (prefixPartial 14 86049) = some ⟨14, 2, 0, 63910, 86049, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_86049_63910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86049 ⟨63910, by decide⟩ :=
  accepted_of_selected 14 86049 ⟨63910, by decide⟩ ⟨14, 2, 0, 63910, 86049, 1429, 4096⟩
    (by decide) selected_cut_01920

theorem selected_cut_01921 : selected 7 ⟨63935, by decide⟩
    (prefixPartial 14 86050) = some ⟨14, 2, 0, 63935, 86050, 1505, 4096⟩ := by
  decide +kernel

theorem context_14_86050_63935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86050 ⟨63935, by decide⟩ :=
  accepted_of_selected 14 86050 ⟨63935, by decide⟩ ⟨14, 2, 0, 63935, 86050, 1505, 4096⟩
    (by decide) selected_cut_01921

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
