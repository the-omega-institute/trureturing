/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover383
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36867 : selected 9 ⟨982260, by decide⟩
    (prefixPartial 12 297738) = some ⟨12, 2, 0, 982260, 297738, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_297738_982260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297738 ⟨982260, by decide⟩ :=
  accepted_of_selected 12 297738 ⟨982260, by decide⟩ ⟨12, 2, 0, 982260, 297738, 1825, 65536⟩
    (by decide) selected_cut_36867

theorem selected_cut_36868 : selected 9 ⟨982324, by decide⟩
    (prefixPartial 12 297739) = some ⟨12, 2, 0, 982324, 297739, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_297739_982324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297739 ⟨982324, by decide⟩ :=
  accepted_of_selected 12 297739 ⟨982324, by decide⟩ ⟨12, 2, 0, 982324, 297739, 3305, 65536⟩
    (by decide) selected_cut_36868

theorem unmarked_context_11_74434_982325 : frontier 10 ⟨982325, by decide⟩
    (prefixCache 11 74434) (prefixPartial 11 74434) = false := by
  decide +kernel

theorem node_context_11_74434_982325 : EJMOriginalGlobalDAGData.nodes 10 ⟨982325, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨982260, by decide⟩,⟨982324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74434_982325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74434 ⟨982325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74434
    ⟨982325, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨982260, by decide⟩,⟨982324, by decide⟩]) unmarked_context_11_74434_982325 node_context_11_74434_982325
  intro a
  fin_cases a
  · exact context_12_297736_895
  · exact context_12_297737_895
  · exact context_12_297738_982260
  · exact context_12_297739_982324

theorem selected_cut_36869 : selected 10 ⟨982326, by decide⟩
    (prefixPartial 11 74435) = some ⟨11, 2, 0, 982326, 74435, 5, 262144⟩ := by
  decide +kernel

theorem context_11_74435_982326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74435 ⟨982326, by decide⟩ :=
  accepted_of_selected 11 74435 ⟨982326, by decide⟩ ⟨11, 2, 0, 982326, 74435, 5, 262144⟩
    (by decide) selected_cut_36869

theorem unmarked_context_10_18608_982327 : frontier 11 ⟨982327, by decide⟩
    (prefixCache 10 18608) (prefixPartial 10 18608) = false := by
  decide +kernel

theorem node_context_10_18608_982327 : EJMOriginalGlobalDAGData.nodes 11 ⟨982327, by decide⟩ =
    .split (coordinate 10) (![⟨982029, by decide⟩,⟨982211, by decide⟩,⟨982325, by decide⟩,⟨982326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18608_982327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18608 ⟨982327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18608
    ⟨982327, by decide⟩ (by decide) (![⟨982029, by decide⟩,⟨982211, by decide⟩,⟨982325, by decide⟩,⟨982326, by decide⟩]) unmarked_context_10_18608_982327 node_context_10_18608_982327
  intro a
  fin_cases a
  · exact context_11_74432_982029
  · exact context_11_74433_982211
  · exact context_11_74434_982325
  · exact context_11_74435_982326

theorem selected_cut_36870 : selected 9 ⟨982328, by decide⟩
    (prefixPartial 12 297744) = some ⟨12, 1, 0, 982328, 297744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297744_982328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297744 ⟨982328, by decide⟩ :=
  accepted_of_selected 12 297744 ⟨982328, by decide⟩ ⟨12, 1, 0, 982328, 297744, 1, 65536⟩
    (by decide) selected_cut_36870

theorem selected_cut_36871 : selected 9 ⟨982409, by decide⟩
    (prefixPartial 12 297745) = some ⟨12, 2, 0, 982409, 297745, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_297745_982409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297745 ⟨982409, by decide⟩ :=
  accepted_of_selected 12 297745 ⟨982409, by decide⟩ ⟨12, 2, 0, 982409, 297745, 3477, 65536⟩
    (by decide) selected_cut_36871

theorem selected_cut_36872 : selected 9 ⟨982482, by decide⟩
    (prefixPartial 12 297746) = some ⟨12, 2, 0, 982482, 297746, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_297746_982482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297746 ⟨982482, by decide⟩ :=
  accepted_of_selected 12 297746 ⟨982482, by decide⟩ ⟨12, 2, 0, 982482, 297746, 3249, 65536⟩
    (by decide) selected_cut_36872

theorem selected_cut_36873 : selected 9 ⟨982576, by decide⟩
    (prefixPartial 12 297747) = some ⟨12, 2, 0, 982576, 297747, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_297747_982576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297747 ⟨982576, by decide⟩ :=
  accepted_of_selected 12 297747 ⟨982576, by decide⟩ ⟨12, 2, 0, 982576, 297747, 2133, 65536⟩
    (by decide) selected_cut_36873

theorem unmarked_context_11_74436_982577 : frontier 10 ⟨982577, by decide⟩
    (prefixCache 11 74436) (prefixPartial 11 74436) = false := by
  decide +kernel

theorem node_context_11_74436_982577 : EJMOriginalGlobalDAGData.nodes 10 ⟨982577, by decide⟩ =
    .split (coordinate 11) (![⟨982328, by decide⟩,⟨982409, by decide⟩,⟨982482, by decide⟩,⟨982576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74436_982577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74436 ⟨982577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74436
    ⟨982577, by decide⟩ (by decide) (![⟨982328, by decide⟩,⟨982409, by decide⟩,⟨982482, by decide⟩,⟨982576, by decide⟩]) unmarked_context_11_74436_982577 node_context_11_74436_982577
  intro a
  fin_cases a
  · exact context_12_297744_982328
  · exact context_12_297745_982409
  · exact context_12_297746_982482
  · exact context_12_297747_982576

theorem selected_cut_36874 : selected 9 ⟨982637, by decide⟩
    (prefixPartial 12 297748) = some ⟨12, 2, 0, 982637, 297748, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_297748_982637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297748 ⟨982637, by decide⟩ :=
  accepted_of_selected 12 297748 ⟨982637, by decide⟩ ⟨12, 2, 0, 982637, 297748, 2745, 65536⟩
    (by decide) selected_cut_36874

theorem selected_cut_36875 : selected 9 ⟨982694, by decide⟩
    (prefixPartial 12 297749) = some ⟨12, 2, 0, 982694, 297749, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_297749_982694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297749 ⟨982694, by decide⟩ :=
  accepted_of_selected 12 297749 ⟨982694, by decide⟩ ⟨12, 2, 0, 982694, 297749, 2873, 65536⟩
    (by decide) selected_cut_36875

theorem selected_cut_36876 : selected 9 ⟨982758, by decide⟩
    (prefixPartial 12 297750) = some ⟨12, 2, 0, 982758, 297750, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_297750_982758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297750 ⟨982758, by decide⟩ :=
  accepted_of_selected 12 297750 ⟨982758, by decide⟩ ⟨12, 2, 0, 982758, 297750, 2865, 65536⟩
    (by decide) selected_cut_36876

theorem selected_cut_36877 : selected 9 ⟨982829, by decide⟩
    (prefixPartial 12 297751) = some ⟨12, 2, 0, 982829, 297751, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_297751_982829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297751 ⟨982829, by decide⟩ :=
  accepted_of_selected 12 297751 ⟨982829, by decide⟩ ⟨12, 2, 0, 982829, 297751, 2957, 65536⟩
    (by decide) selected_cut_36877

theorem unmarked_context_11_74437_982830 : frontier 10 ⟨982830, by decide⟩
    (prefixCache 11 74437) (prefixPartial 11 74437) = false := by
  decide +kernel

theorem node_context_11_74437_982830 : EJMOriginalGlobalDAGData.nodes 10 ⟨982830, by decide⟩ =
    .split (coordinate 11) (![⟨982637, by decide⟩,⟨982694, by decide⟩,⟨982758, by decide⟩,⟨982829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74437_982830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74437 ⟨982830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74437
    ⟨982830, by decide⟩ (by decide) (![⟨982637, by decide⟩,⟨982694, by decide⟩,⟨982758, by decide⟩,⟨982829, by decide⟩]) unmarked_context_11_74437_982830 node_context_11_74437_982830
  intro a
  fin_cases a
  · exact context_12_297748_982637
  · exact context_12_297749_982694
  · exact context_12_297750_982758
  · exact context_12_297751_982829

theorem selected_cut_36878 : selected 9 ⟨982887, by decide⟩
    (prefixPartial 12 297752) = some ⟨12, 2, 0, 982887, 297752, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_297752_982887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297752 ⟨982887, by decide⟩ :=
  accepted_of_selected 12 297752 ⟨982887, by decide⟩ ⟨12, 2, 0, 982887, 297752, 2501, 65536⟩
    (by decide) selected_cut_36878

theorem selected_cut_36879 : selected 9 ⟨982943, by decide⟩
    (prefixPartial 12 297753) = some ⟨12, 2, 0, 982943, 297753, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_297753_982943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297753 ⟨982943, by decide⟩ :=
  accepted_of_selected 12 297753 ⟨982943, by decide⟩ ⟨12, 2, 0, 982943, 297753, 2841, 65536⟩
    (by decide) selected_cut_36879

theorem selected_cut_36880 : selected 9 ⟨982996, by decide⟩
    (prefixPartial 12 297754) = some ⟨12, 2, 0, 982996, 297754, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_297754_982996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297754 ⟨982996, by decide⟩ :=
  accepted_of_selected 12 297754 ⟨982996, by decide⟩ ⟨12, 2, 0, 982996, 297754, 2665, 65536⟩
    (by decide) selected_cut_36880

theorem selected_cut_36881 : selected 9 ⟨983051, by decide⟩
    (prefixPartial 12 297755) = some ⟨12, 2, 0, 983051, 297755, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_297755_983051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297755 ⟨983051, by decide⟩ :=
  accepted_of_selected 12 297755 ⟨983051, by decide⟩ ⟨12, 2, 0, 983051, 297755, 2889, 65536⟩
    (by decide) selected_cut_36881

theorem unmarked_context_11_74438_983052 : frontier 10 ⟨983052, by decide⟩
    (prefixCache 11 74438) (prefixPartial 11 74438) = false := by
  decide +kernel

theorem node_context_11_74438_983052 : EJMOriginalGlobalDAGData.nodes 10 ⟨983052, by decide⟩ =
    .split (coordinate 11) (![⟨982887, by decide⟩,⟨982943, by decide⟩,⟨982996, by decide⟩,⟨983051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74438_983052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74438 ⟨983052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74438
    ⟨983052, by decide⟩ (by decide) (![⟨982887, by decide⟩,⟨982943, by decide⟩,⟨982996, by decide⟩,⟨983051, by decide⟩]) unmarked_context_11_74438_983052 node_context_11_74438_983052
  intro a
  fin_cases a
  · exact context_12_297752_982887
  · exact context_12_297753_982943
  · exact context_12_297754_982996
  · exact context_12_297755_983051

theorem selected_cut_36882 : selected 9 ⟨983108, by decide⟩
    (prefixPartial 12 297756) = some ⟨12, 2, 0, 983108, 297756, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_297756_983108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297756 ⟨983108, by decide⟩ :=
  accepted_of_selected 12 297756 ⟨983108, by decide⟩ ⟨12, 2, 0, 983108, 297756, 1453, 65536⟩
    (by decide) selected_cut_36882

theorem selected_cut_36883 : selected 9 ⟨983163, by decide⟩
    (prefixPartial 12 297757) = some ⟨12, 2, 0, 983163, 297757, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_297757_983163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297757 ⟨983163, by decide⟩ :=
  accepted_of_selected 12 297757 ⟨983163, by decide⟩ ⟨12, 2, 0, 983163, 297757, 2493, 65536⟩
    (by decide) selected_cut_36883

theorem selected_cut_36884 : selected 9 ⟨983222, by decide⟩
    (prefixPartial 12 297758) = some ⟨12, 2, 0, 983222, 297758, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_297758_983222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297758 ⟨983222, by decide⟩ :=
  accepted_of_selected 12 297758 ⟨983222, by decide⟩ ⟨12, 2, 0, 983222, 297758, 2449, 65536⟩
    (by decide) selected_cut_36884

theorem selected_cut_36885 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 297759) = some ⟨12, 1, 0, 903806, 297759, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297759_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297759 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 297759 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 297759, 1, 65536⟩
    (by decide) selected_cut_36885

theorem unmarked_context_11_74439_983223 : frontier 10 ⟨983223, by decide⟩
    (prefixCache 11 74439) (prefixPartial 11 74439) = false := by
  decide +kernel

theorem node_context_11_74439_983223 : EJMOriginalGlobalDAGData.nodes 10 ⟨983223, by decide⟩ =
    .split (coordinate 11) (![⟨983108, by decide⟩,⟨983163, by decide⟩,⟨983222, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74439_983223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74439 ⟨983223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74439
    ⟨983223, by decide⟩ (by decide) (![⟨983108, by decide⟩,⟨983163, by decide⟩,⟨983222, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_74439_983223 node_context_11_74439_983223
  intro a
  fin_cases a
  · exact context_12_297756_983108
  · exact context_12_297757_983163
  · exact context_12_297758_983222
  · exact context_12_297759_903806

theorem unmarked_context_10_18609_983224 : frontier 11 ⟨983224, by decide⟩
    (prefixCache 10 18609) (prefixPartial 10 18609) = false := by
  decide +kernel

theorem node_context_10_18609_983224 : EJMOriginalGlobalDAGData.nodes 11 ⟨983224, by decide⟩ =
    .split (coordinate 10) (![⟨982577, by decide⟩,⟨982830, by decide⟩,⟨983052, by decide⟩,⟨983223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18609_983224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18609 ⟨983224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18609
    ⟨983224, by decide⟩ (by decide) (![⟨982577, by decide⟩,⟨982830, by decide⟩,⟨983052, by decide⟩,⟨983223, by decide⟩]) unmarked_context_10_18609_983224 node_context_10_18609_983224
  intro a
  fin_cases a
  · exact context_11_74436_982577
  · exact context_11_74437_982830
  · exact context_11_74438_983052
  · exact context_11_74439_983223

theorem selected_cut_36886 : selected 10 ⟨983370, by decide⟩
    (prefixPartial 11 74440) = some ⟨11, 2, 0, 983370, 74440, 3729, 262144⟩ := by
  decide +kernel

theorem context_11_74440_983370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74440 ⟨983370, by decide⟩ :=
  accepted_of_selected 11 74440 ⟨983370, by decide⟩ ⟨11, 2, 0, 983370, 74440, 3729, 262144⟩
    (by decide) selected_cut_36886

theorem selected_cut_36887 : selected 9 ⟨983428, by decide⟩
    (prefixPartial 12 297764) = some ⟨12, 2, 0, 983428, 297764, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_297764_983428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297764 ⟨983428, by decide⟩ :=
  accepted_of_selected 12 297764 ⟨983428, by decide⟩ ⟨12, 2, 0, 983428, 297764, 1977, 65536⟩
    (by decide) selected_cut_36887

theorem selected_cut_36888 : selected 9 ⟨983481, by decide⟩
    (prefixPartial 12 297765) = some ⟨12, 2, 0, 983481, 297765, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_297765_983481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297765 ⟨983481, by decide⟩ :=
  accepted_of_selected 12 297765 ⟨983481, by decide⟩ ⟨12, 2, 0, 983481, 297765, 2073, 65536⟩
    (by decide) selected_cut_36888

theorem selected_cut_36889 : selected 9 ⟨983544, by decide⟩
    (prefixPartial 12 297766) = some ⟨12, 2, 0, 983544, 297766, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_297766_983544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297766 ⟨983544, by decide⟩ :=
  accepted_of_selected 12 297766 ⟨983544, by decide⟩ ⟨12, 2, 0, 983544, 297766, 2037, 65536⟩
    (by decide) selected_cut_36889

theorem selected_cut_36890 : selected 9 ⟨983594, by decide⟩
    (prefixPartial 12 297767) = some ⟨12, 2, 0, 983594, 297767, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_297767_983594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297767 ⟨983594, by decide⟩ :=
  accepted_of_selected 12 297767 ⟨983594, by decide⟩ ⟨12, 2, 0, 983594, 297767, 2109, 65536⟩
    (by decide) selected_cut_36890

theorem unmarked_context_11_74441_983595 : frontier 10 ⟨983595, by decide⟩
    (prefixCache 11 74441) (prefixPartial 11 74441) = false := by
  decide +kernel

theorem node_context_11_74441_983595 : EJMOriginalGlobalDAGData.nodes 10 ⟨983595, by decide⟩ =
    .split (coordinate 11) (![⟨983428, by decide⟩,⟨983481, by decide⟩,⟨983544, by decide⟩,⟨983594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74441_983595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74441 ⟨983595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74441
    ⟨983595, by decide⟩ (by decide) (![⟨983428, by decide⟩,⟨983481, by decide⟩,⟨983544, by decide⟩,⟨983594, by decide⟩]) unmarked_context_11_74441_983595 node_context_11_74441_983595
  intro a
  fin_cases a
  · exact context_12_297764_983428
  · exact context_12_297765_983481
  · exact context_12_297766_983544
  · exact context_12_297767_983594

theorem selected_cut_36891 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 74442) = some ⟨11, 1, 0, 900587, 74442, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74442_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74442 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 74442 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 74442, 1, 262144⟩
    (by decide) selected_cut_36891

theorem selected_cut_36892 : selected 10 ⟨983684, by decide⟩
    (prefixPartial 11 74443) = some ⟨11, 2, 0, 983684, 74443, 3697, 262144⟩ := by
  decide +kernel

theorem context_11_74443_983684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74443 ⟨983684, by decide⟩ :=
  accepted_of_selected 11 74443 ⟨983684, by decide⟩ ⟨11, 2, 0, 983684, 74443, 3697, 262144⟩
    (by decide) selected_cut_36892

theorem unmarked_context_10_18610_983685 : frontier 11 ⟨983685, by decide⟩
    (prefixCache 10 18610) (prefixPartial 10 18610) = false := by
  decide +kernel

theorem node_context_10_18610_983685 : EJMOriginalGlobalDAGData.nodes 11 ⟨983685, by decide⟩ =
    .split (coordinate 10) (![⟨983370, by decide⟩,⟨983595, by decide⟩,⟨900587, by decide⟩,⟨983684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18610_983685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18610 ⟨983685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18610
    ⟨983685, by decide⟩ (by decide) (![⟨983370, by decide⟩,⟨983595, by decide⟩,⟨900587, by decide⟩,⟨983684, by decide⟩]) unmarked_context_10_18610_983685 node_context_10_18610_983685
  intro a
  fin_cases a
  · exact context_11_74440_983370
  · exact context_11_74441_983595
  · exact context_11_74442_900587
  · exact context_11_74443_983684

theorem selected_cut_36893 : selected 10 ⟨983759, by decide⟩
    (prefixPartial 11 74444) = some ⟨11, 2, 0, 983759, 74444, 1265, 262144⟩ := by
  decide +kernel

theorem context_11_74444_983759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74444 ⟨983759, by decide⟩ :=
  accepted_of_selected 11 74444 ⟨983759, by decide⟩ ⟨11, 2, 0, 983759, 74444, 1265, 262144⟩
    (by decide) selected_cut_36893

theorem selected_cut_36894 : selected 9 ⟨983801, by decide⟩
    (prefixPartial 12 297780) = some ⟨12, 2, 0, 983801, 297780, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_297780_983801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297780 ⟨983801, by decide⟩ :=
  accepted_of_selected 12 297780 ⟨983801, by decide⟩ ⟨12, 2, 0, 983801, 297780, 1109, 65536⟩
    (by decide) selected_cut_36894

theorem selected_cut_36895 : selected 9 ⟨983853, by decide⟩
    (prefixPartial 12 297781) = some ⟨12, 2, 0, 983853, 297781, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_297781_983853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297781 ⟨983853, by decide⟩ :=
  accepted_of_selected 12 297781 ⟨983853, by decide⟩ ⟨12, 2, 0, 983853, 297781, 1657, 65536⟩
    (by decide) selected_cut_36895

theorem selected_cut_36896 : selected 9 ⟨983900, by decide⟩
    (prefixPartial 12 297782) = some ⟨12, 2, 0, 983900, 297782, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_297782_983900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297782 ⟨983900, by decide⟩ :=
  accepted_of_selected 12 297782 ⟨983900, by decide⟩ ⟨12, 2, 0, 983900, 297782, 1669, 65536⟩
    (by decide) selected_cut_36896

theorem selected_cut_36897 : selected 9 ⟨983950, by decide⟩
    (prefixPartial 12 297783) = some ⟨12, 2, 0, 983950, 297783, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_297783_983950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297783 ⟨983950, by decide⟩ :=
  accepted_of_selected 12 297783 ⟨983950, by decide⟩ ⟨12, 2, 0, 983950, 297783, 1533, 65536⟩
    (by decide) selected_cut_36897

theorem unmarked_context_11_74445_983951 : frontier 10 ⟨983951, by decide⟩
    (prefixCache 11 74445) (prefixPartial 11 74445) = false := by
  decide +kernel

theorem node_context_11_74445_983951 : EJMOriginalGlobalDAGData.nodes 10 ⟨983951, by decide⟩ =
    .split (coordinate 11) (![⟨983801, by decide⟩,⟨983853, by decide⟩,⟨983900, by decide⟩,⟨983950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74445_983951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74445 ⟨983951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74445
    ⟨983951, by decide⟩ (by decide) (![⟨983801, by decide⟩,⟨983853, by decide⟩,⟨983900, by decide⟩,⟨983950, by decide⟩]) unmarked_context_11_74445_983951 node_context_11_74445_983951
  intro a
  fin_cases a
  · exact context_12_297780_983801
  · exact context_12_297781_983853
  · exact context_12_297782_983900
  · exact context_12_297783_983950

theorem selected_cut_36898 : selected 9 ⟨982328, by decide⟩
    (prefixPartial 12 297784) = some ⟨12, 1, 0, 982328, 297784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297784_982328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297784 ⟨982328, by decide⟩ :=
  accepted_of_selected 12 297784 ⟨982328, by decide⟩ ⟨12, 1, 0, 982328, 297784, 1, 65536⟩
    (by decide) selected_cut_36898

theorem selected_cut_36899 : selected 9 ⟨984001, by decide⟩
    (prefixPartial 12 297785) = some ⟨12, 2, 0, 984001, 297785, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_297785_984001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297785 ⟨984001, by decide⟩ :=
  accepted_of_selected 12 297785 ⟨984001, by decide⟩ ⟨12, 2, 0, 984001, 297785, 1529, 65536⟩
    (by decide) selected_cut_36899

theorem selected_cut_36900 : selected 9 ⟨984039, by decide⟩
    (prefixPartial 12 297786) = some ⟨12, 2, 0, 984039, 297786, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_297786_984039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297786 ⟨984039, by decide⟩ :=
  accepted_of_selected 12 297786 ⟨984039, by decide⟩ ⟨12, 2, 0, 984039, 297786, 1409, 65536⟩
    (by decide) selected_cut_36900

theorem selected_cut_36901 : selected 9 ⟨984080, by decide⟩
    (prefixPartial 12 297787) = some ⟨12, 2, 0, 984080, 297787, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_297787_984080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297787 ⟨984080, by decide⟩ :=
  accepted_of_selected 12 297787 ⟨984080, by decide⟩ ⟨12, 2, 0, 984080, 297787, 1365, 65536⟩
    (by decide) selected_cut_36901

theorem unmarked_context_11_74446_984081 : frontier 10 ⟨984081, by decide⟩
    (prefixCache 11 74446) (prefixPartial 11 74446) = false := by
  decide +kernel

theorem node_context_11_74446_984081 : EJMOriginalGlobalDAGData.nodes 10 ⟨984081, by decide⟩ =
    .split (coordinate 11) (![⟨982328, by decide⟩,⟨984001, by decide⟩,⟨984039, by decide⟩,⟨984080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74446_984081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74446 ⟨984081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74446
    ⟨984081, by decide⟩ (by decide) (![⟨982328, by decide⟩,⟨984001, by decide⟩,⟨984039, by decide⟩,⟨984080, by decide⟩]) unmarked_context_11_74446_984081 node_context_11_74446_984081
  intro a
  fin_cases a
  · exact context_12_297784_982328
  · exact context_12_297785_984001
  · exact context_12_297786_984039
  · exact context_12_297787_984080

theorem selected_cut_36902 : selected 10 ⟨984155, by decide⟩
    (prefixPartial 11 74447) = some ⟨11, 2, 0, 984155, 74447, 2345, 262144⟩ := by
  decide +kernel

theorem context_11_74447_984155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74447 ⟨984155, by decide⟩ :=
  accepted_of_selected 11 74447 ⟨984155, by decide⟩ ⟨11, 2, 0, 984155, 74447, 2345, 262144⟩
    (by decide) selected_cut_36902

theorem unmarked_context_10_18611_984156 : frontier 11 ⟨984156, by decide⟩
    (prefixCache 10 18611) (prefixPartial 10 18611) = false := by
  decide +kernel

theorem node_context_10_18611_984156 : EJMOriginalGlobalDAGData.nodes 11 ⟨984156, by decide⟩ =
    .split (coordinate 10) (![⟨983759, by decide⟩,⟨983951, by decide⟩,⟨984081, by decide⟩,⟨984155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18611_984156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18611 ⟨984156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18611
    ⟨984156, by decide⟩ (by decide) (![⟨983759, by decide⟩,⟨983951, by decide⟩,⟨984081, by decide⟩,⟨984155, by decide⟩]) unmarked_context_10_18611_984156 node_context_10_18611_984156
  intro a
  fin_cases a
  · exact context_11_74444_983759
  · exact context_11_74445_983951
  · exact context_11_74446_984081
  · exact context_11_74447_984155

theorem unmarked_context_9_4652_984157 : frontier 12 ⟨984157, by decide⟩
    (prefixCache 9 4652) (prefixPartial 9 4652) = false := by
  decide +kernel

theorem node_context_9_4652_984157 : EJMOriginalGlobalDAGData.nodes 12 ⟨984157, by decide⟩ =
    .split (coordinate 9) (![⟨982327, by decide⟩,⟨983224, by decide⟩,⟨983685, by decide⟩,⟨984156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4652_984157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4652 ⟨984157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4652
    ⟨984157, by decide⟩ (by decide) (![⟨982327, by decide⟩,⟨983224, by decide⟩,⟨983685, by decide⟩,⟨984156, by decide⟩]) unmarked_context_9_4652_984157 node_context_9_4652_984157
  intro a
  fin_cases a
  · exact context_10_18608_982327
  · exact context_10_18609_983224
  · exact context_10_18610_983685
  · exact context_10_18611_984156

theorem selected_cut_36903 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 18612) = some ⟨10, 1, 0, 3442, 18612, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18612_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18612 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 18612 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 18612, 1, 1048576⟩
    (by decide) selected_cut_36903

theorem selected_cut_36904 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18613) = some ⟨10, 1, 0, 893098, 18613, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18613_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18613 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18613 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18613, 1, 1048576⟩
    (by decide) selected_cut_36904

theorem selected_cut_36905 : selected 10 ⟨984158, by decide⟩
    (prefixPartial 11 74456) = some ⟨11, 1, 0, 984158, 74456, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74456_984158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74456 ⟨984158, by decide⟩ :=
  accepted_of_selected 11 74456 ⟨984158, by decide⟩ ⟨11, 1, 0, 984158, 74456, 1, 262144⟩
    (by decide) selected_cut_36905

theorem selected_cut_36906 : selected 10 ⟨984333, by decide⟩
    (prefixPartial 11 74457) = some ⟨11, 2, 0, 984333, 74457, 2801, 262144⟩ := by
  decide +kernel

theorem context_11_74457_984333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74457 ⟨984333, by decide⟩ :=
  accepted_of_selected 11 74457 ⟨984333, by decide⟩ ⟨11, 2, 0, 984333, 74457, 2801, 262144⟩
    (by decide) selected_cut_36906

theorem selected_cut_36907 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 74458) = some ⟨11, 1, 0, 900587, 74458, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74458_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74458 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 74458 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 74458, 1, 262144⟩
    (by decide) selected_cut_36907

theorem selected_cut_36908 : selected 10 ⟨984438, by decide⟩
    (prefixPartial 11 74459) = some ⟨11, 2, 0, 984438, 74459, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_74459_984438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74459 ⟨984438, by decide⟩ :=
  accepted_of_selected 11 74459 ⟨984438, by decide⟩ ⟨11, 2, 0, 984438, 74459, 1397, 262144⟩
    (by decide) selected_cut_36908

theorem unmarked_context_10_18614_984439 : frontier 11 ⟨984439, by decide⟩
    (prefixCache 10 18614) (prefixPartial 10 18614) = false := by
  decide +kernel

theorem node_context_10_18614_984439 : EJMOriginalGlobalDAGData.nodes 11 ⟨984439, by decide⟩ =
    .split (coordinate 10) (![⟨984158, by decide⟩,⟨984333, by decide⟩,⟨900587, by decide⟩,⟨984438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18614_984439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18614 ⟨984439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18614
    ⟨984439, by decide⟩ (by decide) (![⟨984158, by decide⟩,⟨984333, by decide⟩,⟨900587, by decide⟩,⟨984438, by decide⟩]) unmarked_context_10_18614_984439 node_context_10_18614_984439
  intro a
  fin_cases a
  · exact context_11_74456_984158
  · exact context_11_74457_984333
  · exact context_11_74458_900587
  · exact context_11_74459_984438

theorem selected_cut_36909 : selected 11 ⟨984628, by decide⟩
    (prefixPartial 10 18615) = some ⟨10, 2, 0, 984628, 18615, 2525, 1048576⟩ := by
  decide +kernel

theorem context_10_18615_984628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18615 ⟨984628, by decide⟩ :=
  accepted_of_selected 10 18615 ⟨984628, by decide⟩ ⟨10, 2, 0, 984628, 18615, 2525, 1048576⟩
    (by decide) selected_cut_36909

theorem unmarked_context_9_4653_984629 : frontier 12 ⟨984629, by decide⟩
    (prefixCache 9 4653) (prefixPartial 9 4653) = false := by
  decide +kernel

theorem node_context_9_4653_984629 : EJMOriginalGlobalDAGData.nodes 12 ⟨984629, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨984439, by decide⟩,⟨984628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4653_984629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4653 ⟨984629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4653
    ⟨984629, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨984439, by decide⟩,⟨984628, by decide⟩]) unmarked_context_9_4653_984629 node_context_9_4653_984629
  intro a
  fin_cases a
  · exact context_10_18612_3442
  · exact context_10_18613_893098
  · exact context_10_18614_984439
  · exact context_10_18615_984628

theorem selected_cut_36910 : selected 12 ⟨984693, by decide⟩
    (prefixPartial 9 4654) = some ⟨9, 2, 0, 984693, 4654, 377, 4194304⟩ := by
  decide +kernel

theorem context_9_4654_984693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4654 ⟨984693, by decide⟩ :=
  accepted_of_selected 9 4654 ⟨984693, by decide⟩ ⟨9, 2, 0, 984693, 4654, 377, 4194304⟩
    (by decide) selected_cut_36910

theorem selected_cut_36911 : selected 12 ⟨984700, by decide⟩
    (prefixPartial 9 4655) = some ⟨9, 2, 0, 984700, 4655, 37, 4194304⟩ := by
  decide +kernel

theorem context_9_4655_984700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4655 ⟨984700, by decide⟩ :=
  accepted_of_selected 9 4655 ⟨984700, by decide⟩ ⟨9, 2, 0, 984700, 4655, 37, 4194304⟩
    (by decide) selected_cut_36911

theorem unmarked_context_8_1163_984701 : frontier 13 ⟨984701, by decide⟩
    (prefixCache 8 1163) (prefixPartial 8 1163) = false := by
  decide +kernel

theorem node_context_8_1163_984701 : EJMOriginalGlobalDAGData.nodes 13 ⟨984701, by decide⟩ =
    .split (coordinate 8) (![⟨984157, by decide⟩,⟨984629, by decide⟩,⟨984693, by decide⟩,⟨984700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1163_984701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1163 ⟨984701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1163
    ⟨984701, by decide⟩ (by decide) (![⟨984157, by decide⟩,⟨984629, by decide⟩,⟨984693, by decide⟩,⟨984700, by decide⟩]) unmarked_context_8_1163_984701 node_context_8_1163_984701
  intro a
  fin_cases a
  · exact context_9_4652_984157
  · exact context_9_4653_984629
  · exact context_9_4654_984693
  · exact context_9_4655_984700

theorem unmarked_context_7_290_984702 : frontier 14 ⟨984702, by decide⟩
    (prefixCache 7 290) (prefixPartial 7 290) = false := by
  decide +kernel

theorem node_context_7_290_984702 : EJMOriginalGlobalDAGData.nodes 14 ⟨984702, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨981762, by decide⟩,⟨979897, by decide⟩,⟨984701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_290_984702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 290 ⟨984702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 290
    ⟨984702, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨981762, by decide⟩,⟨979897, by decide⟩,⟨984701, by decide⟩]) unmarked_context_7_290_984702 node_context_7_290_984702
  intro a
  fin_cases a
  · exact context_8_1160_979897
  · exact context_8_1161_981762
  · exact context_8_1162_979897
  · exact context_8_1163_984701

theorem selected_cut_36912 : selected 14 ⟨984703, by decide⟩
    (prefixPartial 7 291) = some ⟨7, 2, 0, 984703, 291, 5, 67108864⟩ := by
  decide +kernel

theorem context_7_291_984703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 291 ⟨984703, by decide⟩ :=
  accepted_of_selected 7 291 ⟨984703, by decide⟩ ⟨7, 2, 0, 984703, 291, 5, 67108864⟩
    (by decide) selected_cut_36912

theorem unmarked_context_6_72_984704 : frontier 15 ⟨984704, by decide⟩
    (prefixCache 6 72) (prefixPartial 6 72) = false := by
  decide +kernel

theorem node_context_6_72_984704 : EJMOriginalGlobalDAGData.nodes 15 ⟨984704, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨116316, by decide⟩,⟨984702, by decide⟩,⟨984703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_72_984704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 72 ⟨984704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 72
    ⟨984704, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨116316, by decide⟩,⟨984702, by decide⟩,⟨984703, by decide⟩]) unmarked_context_6_72_984704 node_context_6_72_984704
  intro a
  fin_cases a
  · exact context_7_288_116316
  · exact context_7_289_116316
  · exact context_7_290_984702
  · exact context_7_291_984703

theorem selected_cut_36913 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 74752) = some ⟨11, 1, 0, 167448, 74752, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74752_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74752 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 74752 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 74752, 1, 262144⟩
    (by decide) selected_cut_36913

theorem selected_cut_36914 : selected 9 ⟨984786, by decide⟩
    (prefixPartial 12 299012) = some ⟨12, 2, 0, 984786, 299012, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_299012_984786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299012 ⟨984786, by decide⟩ :=
  accepted_of_selected 12 299012 ⟨984786, by decide⟩ ⟨12, 2, 0, 984786, 299012, 3361, 65536⟩
    (by decide) selected_cut_36914

theorem selected_cut_36915 : selected 9 ⟨984848, by decide⟩
    (prefixPartial 12 299013) = some ⟨12, 2, 0, 984848, 299013, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_299013_984848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299013 ⟨984848, by decide⟩ :=
  accepted_of_selected 12 299013 ⟨984848, by decide⟩ ⟨12, 2, 0, 984848, 299013, 3077, 65536⟩
    (by decide) selected_cut_36915

theorem selected_cut_36916 : selected 9 ⟨984906, by decide⟩
    (prefixPartial 12 299014) = some ⟨12, 2, 0, 984906, 299014, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_299014_984906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299014 ⟨984906, by decide⟩ :=
  accepted_of_selected 12 299014 ⟨984906, by decide⟩ ⟨12, 2, 0, 984906, 299014, 3249, 65536⟩
    (by decide) selected_cut_36916

theorem selected_cut_36917 : selected 9 ⟨984965, by decide⟩
    (prefixPartial 12 299015) = some ⟨12, 2, 0, 984965, 299015, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_299015_984965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299015 ⟨984965, by decide⟩ :=
  accepted_of_selected 12 299015 ⟨984965, by decide⟩ ⟨12, 2, 0, 984965, 299015, 3381, 65536⟩
    (by decide) selected_cut_36917

theorem unmarked_context_11_74753_984966 : frontier 10 ⟨984966, by decide⟩
    (prefixCache 11 74753) (prefixPartial 11 74753) = false := by
  decide +kernel

theorem node_context_11_74753_984966 : EJMOriginalGlobalDAGData.nodes 10 ⟨984966, by decide⟩ =
    .split (coordinate 11) (![⟨984786, by decide⟩,⟨984848, by decide⟩,⟨984906, by decide⟩,⟨984965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74753_984966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74753 ⟨984966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74753
    ⟨984966, by decide⟩ (by decide) (![⟨984786, by decide⟩,⟨984848, by decide⟩,⟨984906, by decide⟩,⟨984965, by decide⟩]) unmarked_context_11_74753_984966 node_context_11_74753_984966
  intro a
  fin_cases a
  · exact context_12_299012_984786
  · exact context_12_299013_984848
  · exact context_12_299014_984906
  · exact context_12_299015_984965

theorem selected_cut_36918 : selected 9 ⟨985021, by decide⟩
    (prefixPartial 12 299016) = some ⟨12, 2, 0, 985021, 299016, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_299016_985021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299016 ⟨985021, by decide⟩ :=
  accepted_of_selected 12 299016 ⟨985021, by decide⟩ ⟨12, 2, 0, 985021, 299016, 1801, 65536⟩
    (by decide) selected_cut_36918

theorem selected_cut_36919 : selected 9 ⟨985067, by decide⟩
    (prefixPartial 12 299017) = some ⟨12, 2, 0, 985067, 299017, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_299017_985067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299017 ⟨985067, by decide⟩ :=
  accepted_of_selected 12 299017 ⟨985067, by decide⟩ ⟨12, 2, 0, 985067, 299017, 3197, 65536⟩
    (by decide) selected_cut_36919

theorem selected_cut_36920 : selected 9 ⟨985115, by decide⟩
    (prefixPartial 12 299018) = some ⟨12, 2, 0, 985115, 299018, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_299018_985115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299018 ⟨985115, by decide⟩ :=
  accepted_of_selected 12 299018 ⟨985115, by decide⟩ ⟨12, 2, 0, 985115, 299018, 3029, 65536⟩
    (by decide) selected_cut_36920

theorem selected_cut_36921 : selected 9 ⟨985165, by decide⟩
    (prefixPartial 12 299019) = some ⟨12, 2, 0, 985165, 299019, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_299019_985165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299019 ⟨985165, by decide⟩ :=
  accepted_of_selected 12 299019 ⟨985165, by decide⟩ ⟨12, 2, 0, 985165, 299019, 3329, 65536⟩
    (by decide) selected_cut_36921

theorem unmarked_context_11_74754_985166 : frontier 10 ⟨985166, by decide⟩
    (prefixCache 11 74754) (prefixPartial 11 74754) = false := by
  decide +kernel

theorem node_context_11_74754_985166 : EJMOriginalGlobalDAGData.nodes 10 ⟨985166, by decide⟩ =
    .split (coordinate 11) (![⟨985021, by decide⟩,⟨985067, by decide⟩,⟨985115, by decide⟩,⟨985165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74754_985166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74754 ⟨985166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74754
    ⟨985166, by decide⟩ (by decide) (![⟨985021, by decide⟩,⟨985067, by decide⟩,⟨985115, by decide⟩,⟨985165, by decide⟩]) unmarked_context_11_74754_985166 node_context_11_74754_985166
  intro a
  fin_cases a
  · exact context_12_299016_985021
  · exact context_12_299017_985067
  · exact context_12_299018_985115
  · exact context_12_299019_985165

theorem selected_cut_36922 : selected 9 ⟨985230, by decide⟩
    (prefixPartial 12 299020) = some ⟨12, 2, 0, 985230, 299020, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_299020_985230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299020 ⟨985230, by decide⟩ :=
  accepted_of_selected 12 299020 ⟨985230, by decide⟩ ⟨12, 2, 0, 985230, 299020, 3077, 65536⟩
    (by decide) selected_cut_36922

theorem selected_cut_36923 : selected 9 ⟨985284, by decide⟩
    (prefixPartial 12 299021) = some ⟨12, 2, 0, 985284, 299021, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_299021_985284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299021 ⟨985284, by decide⟩ :=
  accepted_of_selected 12 299021 ⟨985284, by decide⟩ ⟨12, 2, 0, 985284, 299021, 3257, 65536⟩
    (by decide) selected_cut_36923

theorem selected_cut_36924 : selected 9 ⟨985339, by decide⟩
    (prefixPartial 12 299022) = some ⟨12, 2, 0, 985339, 299022, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_299022_985339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299022 ⟨985339, by decide⟩ :=
  accepted_of_selected 12 299022 ⟨985339, by decide⟩ ⟨12, 2, 0, 985339, 299022, 3301, 65536⟩
    (by decide) selected_cut_36924

theorem selected_cut_36925 : selected 9 ⟨985387, by decide⟩
    (prefixPartial 12 299023) = some ⟨12, 2, 0, 985387, 299023, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_299023_985387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299023 ⟨985387, by decide⟩ :=
  accepted_of_selected 12 299023 ⟨985387, by decide⟩ ⟨12, 2, 0, 985387, 299023, 3029, 65536⟩
    (by decide) selected_cut_36925

theorem unmarked_context_11_74755_985388 : frontier 10 ⟨985388, by decide⟩
    (prefixCache 11 74755) (prefixPartial 11 74755) = false := by
  decide +kernel

theorem node_context_11_74755_985388 : EJMOriginalGlobalDAGData.nodes 10 ⟨985388, by decide⟩ =
    .split (coordinate 11) (![⟨985230, by decide⟩,⟨985284, by decide⟩,⟨985339, by decide⟩,⟨985387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74755_985388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74755 ⟨985388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74755
    ⟨985388, by decide⟩ (by decide) (![⟨985230, by decide⟩,⟨985284, by decide⟩,⟨985339, by decide⟩,⟨985387, by decide⟩]) unmarked_context_11_74755_985388 node_context_11_74755_985388
  intro a
  fin_cases a
  · exact context_12_299020_985230
  · exact context_12_299021_985284
  · exact context_12_299022_985339
  · exact context_12_299023_985387

theorem unmarked_context_10_18688_985389 : frontier 11 ⟨985389, by decide⟩
    (prefixCache 10 18688) (prefixPartial 10 18688) = false := by
  decide +kernel

theorem node_context_10_18688_985389 : EJMOriginalGlobalDAGData.nodes 11 ⟨985389, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨984966, by decide⟩,⟨985166, by decide⟩,⟨985388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18688_985389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18688 ⟨985389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18688
    ⟨985389, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨984966, by decide⟩,⟨985166, by decide⟩,⟨985388, by decide⟩]) unmarked_context_10_18688_985389 node_context_10_18688_985389
  intro a
  fin_cases a
  · exact context_11_74752_167448
  · exact context_11_74753_984966
  · exact context_11_74754_985166
  · exact context_11_74755_985388

theorem selected_cut_36926 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 299024) = some ⟨12, 1, 0, 985390, 299024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299024_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299024 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 299024 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 299024, 1, 65536⟩
    (by decide) selected_cut_36926

theorem selected_cut_36927 : selected 9 ⟨985429, by decide⟩
    (prefixPartial 12 299025) = some ⟨12, 2, 0, 985429, 299025, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_299025_985429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299025 ⟨985429, by decide⟩ :=
  accepted_of_selected 12 299025 ⟨985429, by decide⟩ ⟨12, 2, 0, 985429, 299025, 2077, 65536⟩
    (by decide) selected_cut_36927

theorem selected_cut_36928 : selected 9 ⟨985474, by decide⟩
    (prefixPartial 12 299026) = some ⟨12, 2, 0, 985474, 299026, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_299026_985474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299026 ⟨985474, by decide⟩ :=
  accepted_of_selected 12 299026 ⟨985474, by decide⟩ ⟨12, 2, 0, 985474, 299026, 1857, 65536⟩
    (by decide) selected_cut_36928

theorem selected_cut_36929 : selected 9 ⟨985515, by decide⟩
    (prefixPartial 12 299027) = some ⟨12, 2, 0, 985515, 299027, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_299027_985515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299027 ⟨985515, by decide⟩ :=
  accepted_of_selected 12 299027 ⟨985515, by decide⟩ ⟨12, 2, 0, 985515, 299027, 2073, 65536⟩
    (by decide) selected_cut_36929

theorem unmarked_context_11_74756_985516 : frontier 10 ⟨985516, by decide⟩
    (prefixCache 11 74756) (prefixPartial 11 74756) = false := by
  decide +kernel

theorem node_context_11_74756_985516 : EJMOriginalGlobalDAGData.nodes 10 ⟨985516, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨985429, by decide⟩,⟨985474, by decide⟩,⟨985515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74756_985516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74756 ⟨985516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74756
    ⟨985516, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨985429, by decide⟩,⟨985474, by decide⟩,⟨985515, by decide⟩]) unmarked_context_11_74756_985516 node_context_11_74756_985516
  intro a
  fin_cases a
  · exact context_12_299024_985390
  · exact context_12_299025_985429
  · exact context_12_299026_985474
  · exact context_12_299027_985515

theorem selected_cut_36930 : selected 9 ⟨985568, by decide⟩
    (prefixPartial 12 299028) = some ⟨12, 2, 0, 985568, 299028, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_299028_985568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299028 ⟨985568, by decide⟩ :=
  accepted_of_selected 12 299028 ⟨985568, by decide⟩ ⟨12, 2, 0, 985568, 299028, 2745, 65536⟩
    (by decide) selected_cut_36930

theorem selected_cut_36931 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 299029) = some ⟨12, 1, 0, 124308, 299029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299029_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299029 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 299029 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 299029, 1, 65536⟩
    (by decide) selected_cut_36931

theorem selected_cut_36932 : selected 9 ⟨985611, by decide⟩
    (prefixPartial 12 299030) = some ⟨12, 2, 0, 985611, 299030, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_299030_985611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299030 ⟨985611, by decide⟩ :=
  accepted_of_selected 12 299030 ⟨985611, by decide⟩ ⟨12, 2, 0, 985611, 299030, 2685, 65536⟩
    (by decide) selected_cut_36932

theorem selected_cut_36933 : selected 9 ⟨985656, by decide⟩
    (prefixPartial 12 299031) = some ⟨12, 2, 0, 985656, 299031, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_299031_985656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299031 ⟨985656, by decide⟩ :=
  accepted_of_selected 12 299031 ⟨985656, by decide⟩ ⟨12, 2, 0, 985656, 299031, 2853, 65536⟩
    (by decide) selected_cut_36933

theorem unmarked_context_11_74757_985657 : frontier 10 ⟨985657, by decide⟩
    (prefixCache 11 74757) (prefixPartial 11 74757) = false := by
  decide +kernel

theorem node_context_11_74757_985657 : EJMOriginalGlobalDAGData.nodes 10 ⟨985657, by decide⟩ =
    .split (coordinate 11) (![⟨985568, by decide⟩,⟨124308, by decide⟩,⟨985611, by decide⟩,⟨985656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74757_985657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74757 ⟨985657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74757
    ⟨985657, by decide⟩ (by decide) (![⟨985568, by decide⟩,⟨124308, by decide⟩,⟨985611, by decide⟩,⟨985656, by decide⟩]) unmarked_context_11_74757_985657 node_context_11_74757_985657
  intro a
  fin_cases a
  · exact context_12_299028_985568
  · exact context_12_299029_124308
  · exact context_12_299030_985611
  · exact context_12_299031_985656

theorem selected_cut_36934 : selected 9 ⟨985693, by decide⟩
    (prefixPartial 12 299032) = some ⟨12, 2, 0, 985693, 299032, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_299032_985693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299032 ⟨985693, by decide⟩ :=
  accepted_of_selected 12 299032 ⟨985693, by decide⟩ ⟨12, 2, 0, 985693, 299032, 2593, 65536⟩
    (by decide) selected_cut_36934

theorem selected_cut_36935 : selected 9 ⟨985737, by decide⟩
    (prefixPartial 12 299033) = some ⟨12, 2, 0, 985737, 299033, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_299033_985737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299033 ⟨985737, by decide⟩ :=
  accepted_of_selected 12 299033 ⟨985737, by decide⟩ ⟨12, 2, 0, 985737, 299033, 2741, 65536⟩
    (by decide) selected_cut_36935

theorem selected_cut_36936 : selected 9 ⟨985774, by decide⟩
    (prefixPartial 12 299034) = some ⟨12, 2, 0, 985774, 299034, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_299034_985774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299034 ⟨985774, by decide⟩ :=
  accepted_of_selected 12 299034 ⟨985774, by decide⟩ ⟨12, 2, 0, 985774, 299034, 2521, 65536⟩
    (by decide) selected_cut_36936

theorem selected_cut_36937 : selected 9 ⟨985817, by decide⟩
    (prefixPartial 12 299035) = some ⟨12, 2, 0, 985817, 299035, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_299035_985817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299035 ⟨985817, by decide⟩ :=
  accepted_of_selected 12 299035 ⟨985817, by decide⟩ ⟨12, 2, 0, 985817, 299035, 2909, 65536⟩
    (by decide) selected_cut_36937

theorem unmarked_context_11_74758_985818 : frontier 10 ⟨985818, by decide⟩
    (prefixCache 11 74758) (prefixPartial 11 74758) = false := by
  decide +kernel

theorem node_context_11_74758_985818 : EJMOriginalGlobalDAGData.nodes 10 ⟨985818, by decide⟩ =
    .split (coordinate 11) (![⟨985693, by decide⟩,⟨985737, by decide⟩,⟨985774, by decide⟩,⟨985817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74758_985818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74758 ⟨985818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74758
    ⟨985818, by decide⟩ (by decide) (![⟨985693, by decide⟩,⟨985737, by decide⟩,⟨985774, by decide⟩,⟨985817, by decide⟩]) unmarked_context_11_74758_985818 node_context_11_74758_985818
  intro a
  fin_cases a
  · exact context_12_299032_985693
  · exact context_12_299033_985737
  · exact context_12_299034_985774
  · exact context_12_299035_985817

theorem selected_cut_36938 : selected 9 ⟨985866, by decide⟩
    (prefixPartial 12 299036) = some ⟨12, 2, 0, 985866, 299036, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_299036_985866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299036 ⟨985866, by decide⟩ :=
  accepted_of_selected 12 299036 ⟨985866, by decide⟩ ⟨12, 2, 0, 985866, 299036, 2925, 65536⟩
    (by decide) selected_cut_36938

theorem selected_cut_36939 : selected 9 ⟨985926, by decide⟩
    (prefixPartial 12 299037) = some ⟨12, 2, 0, 985926, 299037, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_299037_985926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299037 ⟨985926, by decide⟩ :=
  accepted_of_selected 12 299037 ⟨985926, by decide⟩ ⟨12, 2, 0, 985926, 299037, 3077, 65536⟩
    (by decide) selected_cut_36939

theorem selected_cut_36940 : selected 9 ⟨985971, by decide⟩
    (prefixPartial 12 299038) = some ⟨12, 2, 0, 985971, 299038, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_299038_985971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299038 ⟨985971, by decide⟩ :=
  accepted_of_selected 12 299038 ⟨985971, by decide⟩ ⟨12, 2, 0, 985971, 299038, 2997, 65536⟩
    (by decide) selected_cut_36940

theorem selected_cut_36941 : selected 9 ⟨986007, by decide⟩
    (prefixPartial 12 299039) = some ⟨12, 2, 0, 986007, 299039, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_299039_986007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299039 ⟨986007, by decide⟩ :=
  accepted_of_selected 12 299039 ⟨986007, by decide⟩ ⟨12, 2, 0, 986007, 299039, 2829, 65536⟩
    (by decide) selected_cut_36941

theorem unmarked_context_11_74759_986008 : frontier 10 ⟨986008, by decide⟩
    (prefixCache 11 74759) (prefixPartial 11 74759) = false := by
  decide +kernel

theorem node_context_11_74759_986008 : EJMOriginalGlobalDAGData.nodes 10 ⟨986008, by decide⟩ =
    .split (coordinate 11) (![⟨985866, by decide⟩,⟨985926, by decide⟩,⟨985971, by decide⟩,⟨986007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74759_986008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74759 ⟨986008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74759
    ⟨986008, by decide⟩ (by decide) (![⟨985866, by decide⟩,⟨985926, by decide⟩,⟨985971, by decide⟩,⟨986007, by decide⟩]) unmarked_context_11_74759_986008 node_context_11_74759_986008
  intro a
  fin_cases a
  · exact context_12_299036_985866
  · exact context_12_299037_985926
  · exact context_12_299038_985971
  · exact context_12_299039_986007

theorem unmarked_context_10_18689_986009 : frontier 11 ⟨986009, by decide⟩
    (prefixCache 10 18689) (prefixPartial 10 18689) = false := by
  decide +kernel

theorem node_context_10_18689_986009 : EJMOriginalGlobalDAGData.nodes 11 ⟨986009, by decide⟩ =
    .split (coordinate 10) (![⟨985516, by decide⟩,⟨985657, by decide⟩,⟨985818, by decide⟩,⟨986008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18689_986009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18689 ⟨986009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18689
    ⟨986009, by decide⟩ (by decide) (![⟨985516, by decide⟩,⟨985657, by decide⟩,⟨985818, by decide⟩,⟨986008, by decide⟩]) unmarked_context_10_18689_986009 node_context_10_18689_986009
  intro a
  fin_cases a
  · exact context_11_74756_985516
  · exact context_11_74757_985657
  · exact context_11_74758_985818
  · exact context_11_74759_986008

theorem selected_cut_36942 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 299040) = some ⟨12, 1, 0, 985390, 299040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299040_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299040 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 299040 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 299040, 1, 65536⟩
    (by decide) selected_cut_36942

theorem selected_cut_36943 : selected 9 ⟨986035, by decide⟩
    (prefixPartial 12 299041) = some ⟨12, 2, 0, 986035, 299041, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_299041_986035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299041 ⟨986035, by decide⟩ :=
  accepted_of_selected 12 299041 ⟨986035, by decide⟩ ⟨12, 2, 0, 986035, 299041, 2209, 65536⟩
    (by decide) selected_cut_36943

theorem selected_cut_36944 : selected 9 ⟨986066, by decide⟩
    (prefixPartial 12 299042) = some ⟨12, 2, 0, 986066, 299042, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_299042_986066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299042 ⟨986066, by decide⟩ :=
  accepted_of_selected 12 299042 ⟨986066, by decide⟩ ⟨12, 2, 0, 986066, 299042, 2085, 65536⟩
    (by decide) selected_cut_36944

theorem selected_cut_36945 : selected 9 ⟨986095, by decide⟩
    (prefixPartial 12 299043) = some ⟨12, 2, 0, 986095, 299043, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_299043_986095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299043 ⟨986095, by decide⟩ :=
  accepted_of_selected 12 299043 ⟨986095, by decide⟩ ⟨12, 2, 0, 986095, 299043, 2225, 65536⟩
    (by decide) selected_cut_36945

theorem unmarked_context_11_74760_986096 : frontier 10 ⟨986096, by decide⟩
    (prefixCache 11 74760) (prefixPartial 11 74760) = false := by
  decide +kernel

theorem node_context_11_74760_986096 : EJMOriginalGlobalDAGData.nodes 10 ⟨986096, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨986035, by decide⟩,⟨986066, by decide⟩,⟨986095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74760_986096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74760 ⟨986096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74760
    ⟨986096, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨986035, by decide⟩,⟨986066, by decide⟩,⟨986095, by decide⟩]) unmarked_context_11_74760_986096 node_context_11_74760_986096
  intro a
  fin_cases a
  · exact context_12_299040_985390
  · exact context_12_299041_986035
  · exact context_12_299042_986066
  · exact context_12_299043_986095

theorem selected_cut_36946 : selected 9 ⟨986142, by decide⟩
    (prefixPartial 12 299044) = some ⟨12, 2, 0, 986142, 299044, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_299044_986142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299044 ⟨986142, by decide⟩ :=
  accepted_of_selected 12 299044 ⟨986142, by decide⟩ ⟨12, 2, 0, 986142, 299044, 2777, 65536⟩
    (by decide) selected_cut_36946

theorem selected_cut_36947 : selected 9 ⟨986180, by decide⟩
    (prefixPartial 12 299045) = some ⟨12, 2, 0, 986180, 299045, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_299045_986180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299045 ⟨986180, by decide⟩ :=
  accepted_of_selected 12 299045 ⟨986180, by decide⟩ ⟨12, 2, 0, 986180, 299045, 2637, 65536⟩
    (by decide) selected_cut_36947

theorem selected_cut_36948 : selected 9 ⟨986224, by decide⟩
    (prefixPartial 12 299046) = some ⟨12, 2, 0, 986224, 299046, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_299046_986224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299046 ⟨986224, by decide⟩ :=
  accepted_of_selected 12 299046 ⟨986224, by decide⟩ ⟨12, 2, 0, 986224, 299046, 2733, 65536⟩
    (by decide) selected_cut_36948

theorem selected_cut_36949 : selected 9 ⟨986265, by decide⟩
    (prefixPartial 12 299047) = some ⟨12, 2, 0, 986265, 299047, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_299047_986265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299047 ⟨986265, by decide⟩ :=
  accepted_of_selected 12 299047 ⟨986265, by decide⟩ ⟨12, 2, 0, 986265, 299047, 2865, 65536⟩
    (by decide) selected_cut_36949

theorem unmarked_context_11_74761_986266 : frontier 10 ⟨986266, by decide⟩
    (prefixCache 11 74761) (prefixPartial 11 74761) = false := by
  decide +kernel

theorem node_context_11_74761_986266 : EJMOriginalGlobalDAGData.nodes 10 ⟨986266, by decide⟩ =
    .split (coordinate 11) (![⟨986142, by decide⟩,⟨986180, by decide⟩,⟨986224, by decide⟩,⟨986265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74761_986266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74761 ⟨986266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74761
    ⟨986266, by decide⟩ (by decide) (![⟨986142, by decide⟩,⟨986180, by decide⟩,⟨986224, by decide⟩,⟨986265, by decide⟩]) unmarked_context_11_74761_986266 node_context_11_74761_986266
  intro a
  fin_cases a
  · exact context_12_299044_986142
  · exact context_12_299045_986180
  · exact context_12_299046_986224
  · exact context_12_299047_986265

theorem selected_cut_36950 : selected 9 ⟨986303, by decide⟩
    (prefixPartial 12 299048) = some ⟨12, 2, 0, 986303, 299048, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_299048_986303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299048 ⟨986303, by decide⟩ :=
  accepted_of_selected 12 299048 ⟨986303, by decide⟩ ⟨12, 2, 0, 986303, 299048, 2621, 65536⟩
    (by decide) selected_cut_36950

theorem selected_cut_36951 : selected 9 ⟨986345, by decide⟩
    (prefixPartial 12 299049) = some ⟨12, 2, 0, 986345, 299049, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_299049_986345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299049 ⟨986345, by decide⟩ :=
  accepted_of_selected 12 299049 ⟨986345, by decide⟩ ⟨12, 2, 0, 986345, 299049, 2673, 65536⟩
    (by decide) selected_cut_36951

theorem selected_cut_36952 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 299050) = some ⟨12, 1, 0, 242157, 299050, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299050_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299050 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 299050 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 299050, 1, 65536⟩
    (by decide) selected_cut_36952

theorem selected_cut_36953 : selected 9 ⟨986386, by decide⟩
    (prefixPartial 12 299051) = some ⟨12, 2, 0, 986386, 299051, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_299051_986386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299051 ⟨986386, by decide⟩ :=
  accepted_of_selected 12 299051 ⟨986386, by decide⟩ ⟨12, 2, 0, 986386, 299051, 2881, 65536⟩
    (by decide) selected_cut_36953

theorem unmarked_context_11_74762_986387 : frontier 10 ⟨986387, by decide⟩
    (prefixCache 11 74762) (prefixPartial 11 74762) = false := by
  decide +kernel

theorem node_context_11_74762_986387 : EJMOriginalGlobalDAGData.nodes 10 ⟨986387, by decide⟩ =
    .split (coordinate 11) (![⟨986303, by decide⟩,⟨986345, by decide⟩,⟨242157, by decide⟩,⟨986386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74762_986387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74762 ⟨986387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74762
    ⟨986387, by decide⟩ (by decide) (![⟨986303, by decide⟩,⟨986345, by decide⟩,⟨242157, by decide⟩,⟨986386, by decide⟩]) unmarked_context_11_74762_986387 node_context_11_74762_986387
  intro a
  fin_cases a
  · exact context_12_299048_986303
  · exact context_12_299049_986345
  · exact context_12_299050_242157
  · exact context_12_299051_986386

theorem selected_cut_36954 : selected 9 ⟨986428, by decide⟩
    (prefixPartial 12 299052) = some ⟨12, 2, 0, 986428, 299052, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_299052_986428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299052 ⟨986428, by decide⟩ :=
  accepted_of_selected 12 299052 ⟨986428, by decide⟩ ⟨12, 2, 0, 986428, 299052, 2641, 65536⟩
    (by decide) selected_cut_36954

theorem selected_cut_36955 : selected 9 ⟨986477, by decide⟩
    (prefixPartial 12 299053) = some ⟨12, 2, 0, 986477, 299053, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_299053_986477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299053 ⟨986477, by decide⟩ :=
  accepted_of_selected 12 299053 ⟨986477, by decide⟩ ⟨12, 2, 0, 986477, 299053, 2857, 65536⟩
    (by decide) selected_cut_36955

theorem selected_cut_36956 : selected 9 ⟨986527, by decide⟩
    (prefixPartial 12 299054) = some ⟨12, 2, 0, 986527, 299054, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_299054_986527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299054 ⟨986527, by decide⟩ :=
  accepted_of_selected 12 299054 ⟨986527, by decide⟩ ⟨12, 2, 0, 986527, 299054, 2949, 65536⟩
    (by decide) selected_cut_36956

theorem selected_cut_36957 : selected 9 ⟨986568, by decide⟩
    (prefixPartial 12 299055) = some ⟨12, 2, 0, 986568, 299055, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_299055_986568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299055 ⟨986568, by decide⟩ :=
  accepted_of_selected 12 299055 ⟨986568, by decide⟩ ⟨12, 2, 0, 986568, 299055, 2677, 65536⟩
    (by decide) selected_cut_36957

theorem unmarked_context_11_74763_986569 : frontier 10 ⟨986569, by decide⟩
    (prefixCache 11 74763) (prefixPartial 11 74763) = false := by
  decide +kernel

theorem node_context_11_74763_986569 : EJMOriginalGlobalDAGData.nodes 10 ⟨986569, by decide⟩ =
    .split (coordinate 11) (![⟨986428, by decide⟩,⟨986477, by decide⟩,⟨986527, by decide⟩,⟨986568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74763_986569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74763 ⟨986569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74763
    ⟨986569, by decide⟩ (by decide) (![⟨986428, by decide⟩,⟨986477, by decide⟩,⟨986527, by decide⟩,⟨986568, by decide⟩]) unmarked_context_11_74763_986569 node_context_11_74763_986569
  intro a
  fin_cases a
  · exact context_12_299052_986428
  · exact context_12_299053_986477
  · exact context_12_299054_986527
  · exact context_12_299055_986568

theorem unmarked_context_10_18690_986570 : frontier 11 ⟨986570, by decide⟩
    (prefixCache 10 18690) (prefixPartial 10 18690) = false := by
  decide +kernel

theorem node_context_10_18690_986570 : EJMOriginalGlobalDAGData.nodes 11 ⟨986570, by decide⟩ =
    .split (coordinate 10) (![⟨986096, by decide⟩,⟨986266, by decide⟩,⟨986387, by decide⟩,⟨986569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18690_986570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18690 ⟨986570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18690
    ⟨986570, by decide⟩ (by decide) (![⟨986096, by decide⟩,⟨986266, by decide⟩,⟨986387, by decide⟩,⟨986569, by decide⟩]) unmarked_context_10_18690_986570 node_context_10_18690_986570
  intro a
  fin_cases a
  · exact context_11_74760_986096
  · exact context_11_74761_986266
  · exact context_11_74762_986387
  · exact context_11_74763_986569

theorem selected_cut_36958 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 299056) = some ⟨12, 1, 0, 985390, 299056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299056_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299056 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 299056 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 299056, 1, 65536⟩
    (by decide) selected_cut_36958

theorem selected_cut_36959 : selected 9 ⟨986601, by decide⟩
    (prefixPartial 12 299057) = some ⟨12, 2, 0, 986601, 299057, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_299057_986601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299057 ⟨986601, by decide⟩ :=
  accepted_of_selected 12 299057 ⟨986601, by decide⟩ ⟨12, 2, 0, 986601, 299057, 2129, 65536⟩
    (by decide) selected_cut_36959

theorem selected_cut_36960 : selected 9 ⟨986630, by decide⟩
    (prefixPartial 12 299058) = some ⟨12, 2, 0, 986630, 299058, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_299058_986630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299058 ⟨986630, by decide⟩ :=
  accepted_of_selected 12 299058 ⟨986630, by decide⟩ ⟨12, 2, 0, 986630, 299058, 1853, 65536⟩
    (by decide) selected_cut_36960

theorem selected_cut_36961 : selected 9 ⟨986665, by decide⟩
    (prefixPartial 12 299059) = some ⟨12, 2, 0, 986665, 299059, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_299059_986665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299059 ⟨986665, by decide⟩ :=
  accepted_of_selected 12 299059 ⟨986665, by decide⟩ ⟨12, 2, 0, 986665, 299059, 2117, 65536⟩
    (by decide) selected_cut_36961

theorem unmarked_context_11_74764_986666 : frontier 10 ⟨986666, by decide⟩
    (prefixCache 11 74764) (prefixPartial 11 74764) = false := by
  decide +kernel

theorem node_context_11_74764_986666 : EJMOriginalGlobalDAGData.nodes 10 ⟨986666, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨986601, by decide⟩,⟨986630, by decide⟩,⟨986665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74764_986666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74764 ⟨986666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74764
    ⟨986666, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨986601, by decide⟩,⟨986630, by decide⟩,⟨986665, by decide⟩]) unmarked_context_11_74764_986666 node_context_11_74764_986666
  intro a
  fin_cases a
  · exact context_12_299056_985390
  · exact context_12_299057_986601
  · exact context_12_299058_986630
  · exact context_12_299059_986665

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
