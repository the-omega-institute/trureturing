/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover081
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07874 : selected 8 ⟨225165, by decide⟩
    (prefixPartial 13 91142) = some ⟨13, 2, 0, 225165, 91142, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_91142_225165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91142 ⟨225165, by decide⟩ :=
  accepted_of_selected 13 91142 ⟨225165, by decide⟩ ⟨13, 2, 0, 225165, 91142, 2017, 16384⟩
    (by decide) selected_cut_07874

theorem selected_cut_07875 : selected 8 ⟨225172, by decide⟩
    (prefixPartial 13 91143) = some ⟨13, 2, 0, 225172, 91143, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_91143_225172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91143 ⟨225172, by decide⟩ :=
  accepted_of_selected 13 91143 ⟨225172, by decide⟩ ⟨13, 2, 0, 225172, 91143, 1161, 16384⟩
    (by decide) selected_cut_07875

theorem unmarked_context_12_22785_225173 : frontier 9 ⟨225173, by decide⟩
    (prefixCache 12 22785) (prefixPartial 12 22785) = false := by
  decide +kernel

theorem node_context_12_22785_225173 : EJMOriginalGlobalDAGData.nodes 9 ⟨225173, by decide⟩ =
    .split (coordinate 12) (![⟨225127, by decide⟩,⟨225147, by decide⟩,⟨225165, by decide⟩,⟨225172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22785_225173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22785 ⟨225173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22785
    ⟨225173, by decide⟩ (by decide) (![⟨225127, by decide⟩,⟨225147, by decide⟩,⟨225165, by decide⟩,⟨225172, by decide⟩]) unmarked_context_12_22785_225173 node_context_12_22785_225173
  intro a
  fin_cases a
  · exact context_13_91140_225127
  · exact context_13_91141_225147
  · exact context_13_91142_225165
  · exact context_13_91143_225172

theorem selected_cut_07876 : selected 7 ⟨225213, by decide⟩
    (prefixPartial 14 364576) = some ⟨14, 2, 0, 225213, 364576, 1721, 4096⟩ := by
  decide +kernel

theorem context_14_364576_225213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364576 ⟨225213, by decide⟩ :=
  accepted_of_selected 14 364576 ⟨225213, by decide⟩ ⟨14, 2, 0, 225213, 364576, 1721, 4096⟩
    (by decide) selected_cut_07876

theorem selected_cut_07877 : selected 7 ⟨225228, by decide⟩
    (prefixPartial 14 364577) = some ⟨14, 2, 0, 225228, 364577, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_364577_225228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364577 ⟨225228, by decide⟩ :=
  accepted_of_selected 14 364577 ⟨225228, by decide⟩ ⟨14, 2, 0, 225228, 364577, 1105, 4096⟩
    (by decide) selected_cut_07877

theorem selected_cut_07878 : selected 7 ⟨225248, by decide⟩
    (prefixPartial 14 364578) = some ⟨14, 2, 0, 225248, 364578, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_364578_225248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364578 ⟨225248, by decide⟩ :=
  accepted_of_selected 14 364578 ⟨225248, by decide⟩ ⟨14, 2, 0, 225248, 364578, 1289, 4096⟩
    (by decide) selected_cut_07878

theorem selected_cut_07879 : selected 7 ⟨225265, by decide⟩
    (prefixPartial 14 364579) = some ⟨14, 2, 0, 225265, 364579, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_364579_225265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364579 ⟨225265, by decide⟩ :=
  accepted_of_selected 14 364579 ⟨225265, by decide⟩ ⟨14, 2, 0, 225265, 364579, 1125, 4096⟩
    (by decide) selected_cut_07879

theorem unmarked_context_13_91144_225266 : frontier 8 ⟨225266, by decide⟩
    (prefixCache 13 91144) (prefixPartial 13 91144) = false := by
  decide +kernel

theorem node_context_13_91144_225266 : EJMOriginalGlobalDAGData.nodes 8 ⟨225266, by decide⟩ =
    .split (coordinate 13) (![⟨225213, by decide⟩,⟨225228, by decide⟩,⟨225248, by decide⟩,⟨225265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91144_225266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91144 ⟨225266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91144
    ⟨225266, by decide⟩ (by decide) (![⟨225213, by decide⟩,⟨225228, by decide⟩,⟨225248, by decide⟩,⟨225265, by decide⟩]) unmarked_context_13_91144_225266 node_context_13_91144_225266
  intro a
  fin_cases a
  · exact context_14_364576_225213
  · exact context_14_364577_225228
  · exact context_14_364578_225248
  · exact context_14_364579_225265

theorem selected_cut_07880 : selected 7 ⟨225280, by decide⟩
    (prefixPartial 14 364580) = some ⟨14, 2, 0, 225280, 364580, 1001, 4096⟩ := by
  decide +kernel

theorem context_14_364580_225280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364580 ⟨225280, by decide⟩ :=
  accepted_of_selected 14 364580 ⟨225280, by decide⟩ ⟨14, 2, 0, 225280, 364580, 1001, 4096⟩
    (by decide) selected_cut_07880

theorem selected_cut_07881 : selected 7 ⟨225298, by decide⟩
    (prefixPartial 14 364581) = some ⟨14, 2, 0, 225298, 364581, 977, 4096⟩ := by
  decide +kernel

theorem context_14_364581_225298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364581 ⟨225298, by decide⟩ :=
  accepted_of_selected 14 364581 ⟨225298, by decide⟩ ⟨14, 2, 0, 225298, 364581, 977, 4096⟩
    (by decide) selected_cut_07881

theorem selected_cut_07882 : selected 7 ⟨225330, by decide⟩
    (prefixPartial 14 364582) = some ⟨14, 2, 0, 225330, 364582, 1349, 4096⟩ := by
  decide +kernel

theorem context_14_364582_225330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364582 ⟨225330, by decide⟩ :=
  accepted_of_selected 14 364582 ⟨225330, by decide⟩ ⟨14, 2, 0, 225330, 364582, 1349, 4096⟩
    (by decide) selected_cut_07882

theorem selected_cut_07883 : selected 7 ⟨225346, by decide⟩
    (prefixPartial 14 364583) = some ⟨14, 2, 0, 225346, 364583, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_364583_225346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364583 ⟨225346, by decide⟩ :=
  accepted_of_selected 14 364583 ⟨225346, by decide⟩ ⟨14, 2, 0, 225346, 364583, 1021, 4096⟩
    (by decide) selected_cut_07883

theorem unmarked_context_13_91145_225347 : frontier 8 ⟨225347, by decide⟩
    (prefixCache 13 91145) (prefixPartial 13 91145) = false := by
  decide +kernel

theorem node_context_13_91145_225347 : EJMOriginalGlobalDAGData.nodes 8 ⟨225347, by decide⟩ =
    .split (coordinate 13) (![⟨225280, by decide⟩,⟨225298, by decide⟩,⟨225330, by decide⟩,⟨225346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91145_225347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91145 ⟨225347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91145
    ⟨225347, by decide⟩ (by decide) (![⟨225280, by decide⟩,⟨225298, by decide⟩,⟨225330, by decide⟩,⟨225346, by decide⟩]) unmarked_context_13_91145_225347 node_context_13_91145_225347
  intro a
  fin_cases a
  · exact context_14_364580_225280
  · exact context_14_364581_225298
  · exact context_14_364582_225330
  · exact context_14_364583_225346

theorem selected_cut_07884 : selected 8 ⟨225384, by decide⟩
    (prefixPartial 13 91146) = some ⟨13, 2, 0, 225384, 91146, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_91146_225384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91146 ⟨225384, by decide⟩ :=
  accepted_of_selected 13 91146 ⟨225384, by decide⟩ ⟨13, 2, 0, 225384, 91146, 2585, 16384⟩
    (by decide) selected_cut_07884

theorem selected_cut_07885 : selected 8 ⟨225406, by decide⟩
    (prefixPartial 13 91147) = some ⟨13, 2, 0, 225406, 91147, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_91147_225406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91147 ⟨225406, by decide⟩ :=
  accepted_of_selected 13 91147 ⟨225406, by decide⟩ ⟨13, 2, 0, 225406, 91147, 1469, 16384⟩
    (by decide) selected_cut_07885

theorem unmarked_context_12_22786_225407 : frontier 9 ⟨225407, by decide⟩
    (prefixCache 12 22786) (prefixPartial 12 22786) = false := by
  decide +kernel

theorem node_context_12_22786_225407 : EJMOriginalGlobalDAGData.nodes 9 ⟨225407, by decide⟩ =
    .split (coordinate 12) (![⟨225266, by decide⟩,⟨225347, by decide⟩,⟨225384, by decide⟩,⟨225406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22786_225407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22786 ⟨225407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22786
    ⟨225407, by decide⟩ (by decide) (![⟨225266, by decide⟩,⟨225347, by decide⟩,⟨225384, by decide⟩,⟨225406, by decide⟩]) unmarked_context_12_22786_225407 node_context_12_22786_225407
  intro a
  fin_cases a
  · exact context_13_91144_225266
  · exact context_13_91145_225347
  · exact context_13_91146_225384
  · exact context_13_91147_225406

theorem selected_cut_07886 : selected 7 ⟨225436, by decide⟩
    (prefixPartial 14 364592) = some ⟨14, 2, 0, 225436, 364592, 1597, 4096⟩ := by
  decide +kernel

theorem context_14_364592_225436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364592 ⟨225436, by decide⟩ :=
  accepted_of_selected 14 364592 ⟨225436, by decide⟩ ⟨14, 2, 0, 225436, 364592, 1597, 4096⟩
    (by decide) selected_cut_07886

theorem selected_cut_07887 : selected 7 ⟨225455, by decide⟩
    (prefixPartial 14 364593) = some ⟨14, 2, 0, 225455, 364593, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_364593_225455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364593 ⟨225455, by decide⟩ :=
  accepted_of_selected 14 364593 ⟨225455, by decide⟩ ⟨14, 2, 0, 225455, 364593, 1209, 4096⟩
    (by decide) selected_cut_07887

theorem selected_cut_07888 : selected 7 ⟨225478, by decide⟩
    (prefixPartial 14 364594) = some ⟨14, 2, 0, 225478, 364594, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_364594_225478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364594 ⟨225478, by decide⟩ :=
  accepted_of_selected 14 364594 ⟨225478, by decide⟩ ⟨14, 2, 0, 225478, 364594, 1341, 4096⟩
    (by decide) selected_cut_07888

theorem selected_cut_07889 : selected 7 ⟨225498, by decide⟩
    (prefixPartial 14 364595) = some ⟨14, 2, 0, 225498, 364595, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_364595_225498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364595 ⟨225498, by decide⟩ :=
  accepted_of_selected 14 364595 ⟨225498, by decide⟩ ⟨14, 2, 0, 225498, 364595, 1181, 4096⟩
    (by decide) selected_cut_07889

theorem unmarked_context_13_91148_225499 : frontier 8 ⟨225499, by decide⟩
    (prefixCache 13 91148) (prefixPartial 13 91148) = false := by
  decide +kernel

theorem node_context_13_91148_225499 : EJMOriginalGlobalDAGData.nodes 8 ⟨225499, by decide⟩ =
    .split (coordinate 13) (![⟨225436, by decide⟩,⟨225455, by decide⟩,⟨225478, by decide⟩,⟨225498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91148_225499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91148 ⟨225499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91148
    ⟨225499, by decide⟩ (by decide) (![⟨225436, by decide⟩,⟨225455, by decide⟩,⟨225478, by decide⟩,⟨225498, by decide⟩]) unmarked_context_13_91148_225499 node_context_13_91148_225499
  intro a
  fin_cases a
  · exact context_14_364592_225436
  · exact context_14_364593_225455
  · exact context_14_364594_225478
  · exact context_14_364595_225498

theorem selected_cut_07890 : selected 7 ⟨225517, by decide⟩
    (prefixPartial 14 364596) = some ⟨14, 2, 0, 225517, 364596, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_364596_225517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364596 ⟨225517, by decide⟩ :=
  accepted_of_selected 14 364596 ⟨225517, by decide⟩ ⟨14, 2, 0, 225517, 364596, 1081, 4096⟩
    (by decide) selected_cut_07890

theorem selected_cut_07891 : selected 7 ⟨225535, by decide⟩
    (prefixPartial 14 364597) = some ⟨14, 2, 0, 225535, 364597, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_364597_225535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364597 ⟨225535, by decide⟩ :=
  accepted_of_selected 14 364597 ⟨225535, by decide⟩ ⟨14, 2, 0, 225535, 364597, 1121, 4096⟩
    (by decide) selected_cut_07891

theorem selected_cut_07892 : selected 7 ⟨225558, by decide⟩
    (prefixPartial 14 364598) = some ⟨14, 2, 0, 225558, 364598, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_364598_225558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364598 ⟨225558, by decide⟩ :=
  accepted_of_selected 14 364598 ⟨225558, by decide⟩ ⟨14, 2, 0, 225558, 364598, 1313, 4096⟩
    (by decide) selected_cut_07892

theorem selected_cut_07893 : selected 7 ⟨225581, by decide⟩
    (prefixPartial 14 364599) = some ⟨14, 2, 0, 225581, 364599, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_364599_225581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364599 ⟨225581, by decide⟩ :=
  accepted_of_selected 14 364599 ⟨225581, by decide⟩ ⟨14, 2, 0, 225581, 364599, 1153, 4096⟩
    (by decide) selected_cut_07893

theorem unmarked_context_13_91149_225582 : frontier 8 ⟨225582, by decide⟩
    (prefixCache 13 91149) (prefixPartial 13 91149) = false := by
  decide +kernel

theorem node_context_13_91149_225582 : EJMOriginalGlobalDAGData.nodes 8 ⟨225582, by decide⟩ =
    .split (coordinate 13) (![⟨225517, by decide⟩,⟨225535, by decide⟩,⟨225558, by decide⟩,⟨225581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91149_225582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91149 ⟨225582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91149
    ⟨225582, by decide⟩ (by decide) (![⟨225517, by decide⟩,⟨225535, by decide⟩,⟨225558, by decide⟩,⟨225581, by decide⟩]) unmarked_context_13_91149_225582 node_context_13_91149_225582
  intro a
  fin_cases a
  · exact context_14_364596_225517
  · exact context_14_364597_225535
  · exact context_14_364598_225558
  · exact context_14_364599_225581

theorem selected_cut_07894 : selected 8 ⟨225621, by decide⟩
    (prefixPartial 13 91150) = some ⟨13, 2, 0, 225621, 91150, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_91150_225621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91150 ⟨225621, by decide⟩ :=
  accepted_of_selected 13 91150 ⟨225621, by decide⟩ ⟨13, 2, 0, 225621, 91150, 2493, 16384⟩
    (by decide) selected_cut_07894

theorem selected_cut_07895 : selected 8 ⟨225639, by decide⟩
    (prefixPartial 13 91151) = some ⟨13, 2, 0, 225639, 91151, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_91151_225639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91151 ⟨225639, by decide⟩ :=
  accepted_of_selected 13 91151 ⟨225639, by decide⟩ ⟨13, 2, 0, 225639, 91151, 1341, 16384⟩
    (by decide) selected_cut_07895

theorem unmarked_context_12_22787_225640 : frontier 9 ⟨225640, by decide⟩
    (prefixCache 12 22787) (prefixPartial 12 22787) = false := by
  decide +kernel

theorem node_context_12_22787_225640 : EJMOriginalGlobalDAGData.nodes 9 ⟨225640, by decide⟩ =
    .split (coordinate 12) (![⟨225499, by decide⟩,⟨225582, by decide⟩,⟨225621, by decide⟩,⟨225639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22787_225640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22787 ⟨225640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22787
    ⟨225640, by decide⟩ (by decide) (![⟨225499, by decide⟩,⟨225582, by decide⟩,⟨225621, by decide⟩,⟨225639, by decide⟩]) unmarked_context_12_22787_225640 node_context_12_22787_225640
  intro a
  fin_cases a
  · exact context_13_91148_225499
  · exact context_13_91149_225582
  · exact context_13_91150_225621
  · exact context_13_91151_225639

theorem unmarked_context_11_5696_225641 : frontier 10 ⟨225641, by decide⟩
    (prefixCache 11 5696) (prefixPartial 11 5696) = false := by
  decide +kernel

theorem node_context_11_5696_225641 : EJMOriginalGlobalDAGData.nodes 10 ⟨225641, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨225173, by decide⟩,⟨225407, by decide⟩,⟨225640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5696_225641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5696 ⟨225641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5696
    ⟨225641, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨225173, by decide⟩,⟨225407, by decide⟩,⟨225640, by decide⟩]) unmarked_context_11_5696_225641 node_context_11_5696_225641
  intro a
  fin_cases a
  · exact context_12_22784_34034
  · exact context_12_22785_225173
  · exact context_12_22786_225407
  · exact context_12_22787_225640

theorem selected_cut_07896 : selected 8 ⟨225705, by decide⟩
    (prefixPartial 13 91152) = some ⟨13, 2, 0, 225705, 91152, 3445, 16384⟩ := by
  decide +kernel

theorem context_13_91152_225705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91152 ⟨225705, by decide⟩ :=
  accepted_of_selected 13 91152 ⟨225705, by decide⟩ ⟨13, 2, 0, 225705, 91152, 3445, 16384⟩
    (by decide) selected_cut_07896

theorem selected_cut_07897 : selected 8 ⟨225753, by decide⟩
    (prefixPartial 13 91153) = some ⟨13, 2, 0, 225753, 91153, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_91153_225753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91153 ⟨225753, by decide⟩ :=
  accepted_of_selected 13 91153 ⟨225753, by decide⟩ ⟨13, 2, 0, 225753, 91153, 3225, 16384⟩
    (by decide) selected_cut_07897

theorem selected_cut_07898 : selected 8 ⟨225774, by decide⟩
    (prefixPartial 13 91154) = some ⟨13, 2, 0, 225774, 91154, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_91154_225774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91154 ⟨225774, by decide⟩ :=
  accepted_of_selected 13 91154 ⟨225774, by decide⟩ ⟨13, 2, 0, 225774, 91154, 1733, 16384⟩
    (by decide) selected_cut_07898

theorem selected_cut_07899 : selected 8 ⟨225791, by decide⟩
    (prefixPartial 13 91155) = some ⟨13, 2, 0, 225791, 91155, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_91155_225791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91155 ⟨225791, by decide⟩ :=
  accepted_of_selected 13 91155 ⟨225791, by decide⟩ ⟨13, 2, 0, 225791, 91155, 1173, 16384⟩
    (by decide) selected_cut_07899

theorem unmarked_context_12_22788_225792 : frontier 9 ⟨225792, by decide⟩
    (prefixCache 12 22788) (prefixPartial 12 22788) = false := by
  decide +kernel

theorem node_context_12_22788_225792 : EJMOriginalGlobalDAGData.nodes 9 ⟨225792, by decide⟩ =
    .split (coordinate 12) (![⟨225705, by decide⟩,⟨225753, by decide⟩,⟨225774, by decide⟩,⟨225791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22788_225792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22788 ⟨225792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22788
    ⟨225792, by decide⟩ (by decide) (![⟨225705, by decide⟩,⟨225753, by decide⟩,⟨225774, by decide⟩,⟨225791, by decide⟩]) unmarked_context_12_22788_225792 node_context_12_22788_225792
  intro a
  fin_cases a
  · exact context_13_91152_225705
  · exact context_13_91153_225753
  · exact context_13_91154_225774
  · exact context_13_91155_225791

theorem selected_cut_07900 : selected 7 ⟨225833, by decide⟩
    (prefixPartial 14 364624) = some ⟨14, 2, 0, 225833, 364624, 1913, 4096⟩ := by
  decide +kernel

theorem context_14_364624_225833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364624 ⟨225833, by decide⟩ :=
  accepted_of_selected 14 364624 ⟨225833, by decide⟩ ⟨14, 2, 0, 225833, 364624, 1913, 4096⟩
    (by decide) selected_cut_07900

theorem selected_cut_07901 : selected 7 ⟨225852, by decide⟩
    (prefixPartial 14 364625) = some ⟨14, 2, 0, 225852, 364625, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_364625_225852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364625 ⟨225852, by decide⟩ :=
  accepted_of_selected 14 364625 ⟨225852, by decide⟩ ⟨14, 2, 0, 225852, 364625, 1105, 4096⟩
    (by decide) selected_cut_07901

theorem selected_cut_07902 : selected 7 ⟨225872, by decide⟩
    (prefixPartial 14 364626) = some ⟨14, 2, 0, 225872, 364626, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_364626_225872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364626 ⟨225872, by decide⟩ :=
  accepted_of_selected 14 364626 ⟨225872, by decide⟩ ⟨14, 2, 0, 225872, 364626, 1313, 4096⟩
    (by decide) selected_cut_07902

theorem selected_cut_07903 : selected 7 ⟨225892, by decide⟩
    (prefixPartial 14 364627) = some ⟨14, 2, 0, 225892, 364627, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_364627_225892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364627 ⟨225892, by decide⟩ :=
  accepted_of_selected 14 364627 ⟨225892, by decide⟩ ⟨14, 2, 0, 225892, 364627, 1201, 4096⟩
    (by decide) selected_cut_07903

theorem unmarked_context_13_91156_225893 : frontier 8 ⟨225893, by decide⟩
    (prefixCache 13 91156) (prefixPartial 13 91156) = false := by
  decide +kernel

theorem node_context_13_91156_225893 : EJMOriginalGlobalDAGData.nodes 8 ⟨225893, by decide⟩ =
    .split (coordinate 13) (![⟨225833, by decide⟩,⟨225852, by decide⟩,⟨225872, by decide⟩,⟨225892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91156_225893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91156 ⟨225893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91156
    ⟨225893, by decide⟩ (by decide) (![⟨225833, by decide⟩,⟨225852, by decide⟩,⟨225872, by decide⟩,⟨225892, by decide⟩]) unmarked_context_13_91156_225893 node_context_13_91156_225893
  intro a
  fin_cases a
  · exact context_14_364624_225833
  · exact context_14_364625_225852
  · exact context_14_364626_225872
  · exact context_14_364627_225892

theorem selected_cut_07904 : selected 7 ⟨225906, by decide⟩
    (prefixPartial 14 364628) = some ⟨14, 2, 0, 225906, 364628, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_364628_225906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364628 ⟨225906, by decide⟩ :=
  accepted_of_selected 14 364628 ⟨225906, by decide⟩ ⟨14, 2, 0, 225906, 364628, 1093, 4096⟩
    (by decide) selected_cut_07904

theorem selected_cut_07905 : selected 7 ⟨225926, by decide⟩
    (prefixPartial 14 364629) = some ⟨14, 2, 0, 225926, 364629, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_364629_225926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364629 ⟨225926, by decide⟩ :=
  accepted_of_selected 14 364629 ⟨225926, by decide⟩ ⟨14, 2, 0, 225926, 364629, 1069, 4096⟩
    (by decide) selected_cut_07905

theorem selected_cut_07906 : selected 7 ⟨225959, by decide⟩
    (prefixPartial 14 364630) = some ⟨14, 2, 0, 225959, 364630, 1401, 4096⟩ := by
  decide +kernel

theorem context_14_364630_225959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364630 ⟨225959, by decide⟩ :=
  accepted_of_selected 14 364630 ⟨225959, by decide⟩ ⟨14, 2, 0, 225959, 364630, 1401, 4096⟩
    (by decide) selected_cut_07906

theorem selected_cut_07907 : selected 7 ⟨225984, by decide⟩
    (prefixPartial 14 364631) = some ⟨14, 2, 0, 225984, 364631, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_364631_225984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364631 ⟨225984, by decide⟩ :=
  accepted_of_selected 14 364631 ⟨225984, by decide⟩ ⟨14, 2, 0, 225984, 364631, 1085, 4096⟩
    (by decide) selected_cut_07907

theorem unmarked_context_13_91157_225985 : frontier 8 ⟨225985, by decide⟩
    (prefixCache 13 91157) (prefixPartial 13 91157) = false := by
  decide +kernel

theorem node_context_13_91157_225985 : EJMOriginalGlobalDAGData.nodes 8 ⟨225985, by decide⟩ =
    .split (coordinate 13) (![⟨225906, by decide⟩,⟨225926, by decide⟩,⟨225959, by decide⟩,⟨225984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91157_225985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91157 ⟨225985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91157
    ⟨225985, by decide⟩ (by decide) (![⟨225906, by decide⟩,⟨225926, by decide⟩,⟨225959, by decide⟩,⟨225984, by decide⟩]) unmarked_context_13_91157_225985 node_context_13_91157_225985
  intro a
  fin_cases a
  · exact context_14_364628_225906
  · exact context_14_364629_225926
  · exact context_14_364630_225959
  · exact context_14_364631_225984

theorem selected_cut_07908 : selected 8 ⟨226010, by decide⟩
    (prefixPartial 13 91158) = some ⟨13, 2, 0, 226010, 91158, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_91158_226010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91158 ⟨226010, by decide⟩ :=
  accepted_of_selected 13 91158 ⟨226010, by decide⟩ ⟨13, 2, 0, 226010, 91158, 2377, 16384⟩
    (by decide) selected_cut_07908

theorem selected_cut_07909 : selected 8 ⟨226038, by decide⟩
    (prefixPartial 13 91159) = some ⟨13, 2, 0, 226038, 91159, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_91159_226038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91159 ⟨226038, by decide⟩ :=
  accepted_of_selected 13 91159 ⟨226038, by decide⟩ ⟨13, 2, 0, 226038, 91159, 1497, 16384⟩
    (by decide) selected_cut_07909

theorem unmarked_context_12_22789_226039 : frontier 9 ⟨226039, by decide⟩
    (prefixCache 12 22789) (prefixPartial 12 22789) = false := by
  decide +kernel

theorem node_context_12_22789_226039 : EJMOriginalGlobalDAGData.nodes 9 ⟨226039, by decide⟩ =
    .split (coordinate 12) (![⟨225893, by decide⟩,⟨225985, by decide⟩,⟨226010, by decide⟩,⟨226038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22789_226039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22789 ⟨226039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22789
    ⟨226039, by decide⟩ (by decide) (![⟨225893, by decide⟩,⟨225985, by decide⟩,⟨226010, by decide⟩,⟨226038, by decide⟩]) unmarked_context_12_22789_226039 node_context_12_22789_226039
  intro a
  fin_cases a
  · exact context_13_91156_225893
  · exact context_13_91157_225985
  · exact context_13_91158_226010
  · exact context_13_91159_226038

theorem selected_cut_07910 : selected 7 ⟨226063, by decide⟩
    (prefixPartial 14 364640) = some ⟨14, 2, 0, 226063, 364640, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_364640_226063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364640 ⟨226063, by decide⟩ :=
  accepted_of_selected 14 364640 ⟨226063, by decide⟩ ⟨14, 2, 0, 226063, 364640, 1293, 4096⟩
    (by decide) selected_cut_07910

theorem selected_cut_07911 : selected 7 ⟨226077, by decide⟩
    (prefixPartial 14 364641) = some ⟨14, 2, 0, 226077, 364641, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_364641_226077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364641 ⟨226077, by decide⟩ :=
  accepted_of_selected 14 364641 ⟨226077, by decide⟩ ⟨14, 2, 0, 226077, 364641, 1025, 4096⟩
    (by decide) selected_cut_07911

theorem selected_cut_07912 : selected 7 ⟨226094, by decide⟩
    (prefixPartial 14 364642) = some ⟨14, 2, 0, 226094, 364642, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_364642_226094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364642 ⟨226094, by decide⟩ :=
  accepted_of_selected 14 364642 ⟨226094, by decide⟩ ⟨14, 2, 0, 226094, 364642, 1177, 4096⟩
    (by decide) selected_cut_07912

theorem selected_cut_07913 : selected 7 ⟨226106, by decide⟩
    (prefixPartial 14 364643) = some ⟨14, 2, 0, 226106, 364643, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_364643_226106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364643 ⟨226106, by decide⟩ :=
  accepted_of_selected 14 364643 ⟨226106, by decide⟩ ⟨14, 2, 0, 226106, 364643, 1041, 4096⟩
    (by decide) selected_cut_07913

theorem unmarked_context_13_91160_226107 : frontier 8 ⟨226107, by decide⟩
    (prefixCache 13 91160) (prefixPartial 13 91160) = false := by
  decide +kernel

theorem node_context_13_91160_226107 : EJMOriginalGlobalDAGData.nodes 8 ⟨226107, by decide⟩ =
    .split (coordinate 13) (![⟨226063, by decide⟩,⟨226077, by decide⟩,⟨226094, by decide⟩,⟨226106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91160_226107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91160 ⟨226107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91160
    ⟨226107, by decide⟩ (by decide) (![⟨226063, by decide⟩,⟨226077, by decide⟩,⟨226094, by decide⟩,⟨226106, by decide⟩]) unmarked_context_13_91160_226107 node_context_13_91160_226107
  intro a
  fin_cases a
  · exact context_14_364640_226063
  · exact context_14_364641_226077
  · exact context_14_364642_226094
  · exact context_14_364643_226106

theorem selected_cut_07914 : selected 8 ⟨226168, by decide⟩
    (prefixPartial 13 91161) = some ⟨13, 2, 0, 226168, 91161, 3617, 16384⟩ := by
  decide +kernel

theorem context_13_91161_226168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91161 ⟨226168, by decide⟩ :=
  accepted_of_selected 13 91161 ⟨226168, by decide⟩ ⟨13, 2, 0, 226168, 91161, 3617, 16384⟩
    (by decide) selected_cut_07914

theorem selected_cut_07915 : selected 8 ⟨226190, by decide⟩
    (prefixPartial 13 91162) = some ⟨13, 2, 0, 226190, 91162, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_91162_226190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91162 ⟨226190, by decide⟩ :=
  accepted_of_selected 13 91162 ⟨226190, by decide⟩ ⟨13, 2, 0, 226190, 91162, 2097, 16384⟩
    (by decide) selected_cut_07915

theorem selected_cut_07916 : selected 8 ⟨226205, by decide⟩
    (prefixPartial 13 91163) = some ⟨13, 2, 0, 226205, 91163, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_91163_226205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91163 ⟨226205, by decide⟩ :=
  accepted_of_selected 13 91163 ⟨226205, by decide⟩ ⟨13, 2, 0, 226205, 91163, 1345, 16384⟩
    (by decide) selected_cut_07916

theorem unmarked_context_12_22790_226206 : frontier 9 ⟨226206, by decide⟩
    (prefixCache 12 22790) (prefixPartial 12 22790) = false := by
  decide +kernel

theorem node_context_12_22790_226206 : EJMOriginalGlobalDAGData.nodes 9 ⟨226206, by decide⟩ =
    .split (coordinate 12) (![⟨226107, by decide⟩,⟨226168, by decide⟩,⟨226190, by decide⟩,⟨226205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22790_226206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22790 ⟨226206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22790
    ⟨226206, by decide⟩ (by decide) (![⟨226107, by decide⟩,⟨226168, by decide⟩,⟨226190, by decide⟩,⟨226205, by decide⟩]) unmarked_context_12_22790_226206 node_context_12_22790_226206
  intro a
  fin_cases a
  · exact context_13_91160_226107
  · exact context_13_91161_226168
  · exact context_13_91162_226190
  · exact context_13_91163_226205

theorem selected_cut_07917 : selected 7 ⟨226229, by decide⟩
    (prefixPartial 14 364656) = some ⟨14, 2, 0, 226229, 364656, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_364656_226229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364656 ⟨226229, by decide⟩ :=
  accepted_of_selected 14 364656 ⟨226229, by decide⟩ ⟨14, 2, 0, 226229, 364656, 1189, 4096⟩
    (by decide) selected_cut_07917

theorem selected_cut_07918 : selected 7 ⟨226244, by decide⟩
    (prefixPartial 14 364657) = some ⟨14, 2, 0, 226244, 364657, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_364657_226244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364657 ⟨226244, by decide⟩ :=
  accepted_of_selected 14 364657 ⟨226244, by decide⟩ ⟨14, 2, 0, 226244, 364657, 1077, 4096⟩
    (by decide) selected_cut_07918

theorem selected_cut_07919 : selected 7 ⟨226261, by decide⟩
    (prefixPartial 14 364658) = some ⟨14, 2, 0, 226261, 364658, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_364658_226261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364658 ⟨226261, by decide⟩ :=
  accepted_of_selected 14 364658 ⟨226261, by decide⟩ ⟨14, 2, 0, 226261, 364658, 1201, 4096⟩
    (by decide) selected_cut_07919

theorem selected_cut_07920 : selected 7 ⟨226273, by decide⟩
    (prefixPartial 14 364659) = some ⟨14, 2, 0, 226273, 364659, 1001, 4096⟩ := by
  decide +kernel

theorem context_14_364659_226273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364659 ⟨226273, by decide⟩ :=
  accepted_of_selected 14 364659 ⟨226273, by decide⟩ ⟨14, 2, 0, 226273, 364659, 1001, 4096⟩
    (by decide) selected_cut_07920

theorem unmarked_context_13_91164_226274 : frontier 8 ⟨226274, by decide⟩
    (prefixCache 13 91164) (prefixPartial 13 91164) = false := by
  decide +kernel

theorem node_context_13_91164_226274 : EJMOriginalGlobalDAGData.nodes 8 ⟨226274, by decide⟩ =
    .split (coordinate 13) (![⟨226229, by decide⟩,⟨226244, by decide⟩,⟨226261, by decide⟩,⟨226273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91164_226274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91164 ⟨226274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91164
    ⟨226274, by decide⟩ (by decide) (![⟨226229, by decide⟩,⟨226244, by decide⟩,⟨226261, by decide⟩,⟨226273, by decide⟩]) unmarked_context_13_91164_226274 node_context_13_91164_226274
  intro a
  fin_cases a
  · exact context_14_364656_226229
  · exact context_14_364657_226244
  · exact context_14_364658_226261
  · exact context_14_364659_226273

theorem selected_cut_07921 : selected 8 ⟨226338, by decide⟩
    (prefixPartial 13 91165) = some ⟨13, 2, 0, 226338, 91165, 3717, 16384⟩ := by
  decide +kernel

theorem context_13_91165_226338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91165 ⟨226338, by decide⟩ :=
  accepted_of_selected 13 91165 ⟨226338, by decide⟩ ⟨13, 2, 0, 226338, 91165, 3717, 16384⟩
    (by decide) selected_cut_07921

theorem selected_cut_07922 : selected 8 ⟨226357, by decide⟩
    (prefixPartial 13 91166) = some ⟨13, 2, 0, 226357, 91166, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_91166_226357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91166 ⟨226357, by decide⟩ :=
  accepted_of_selected 13 91166 ⟨226357, by decide⟩ ⟨13, 2, 0, 226357, 91166, 2077, 16384⟩
    (by decide) selected_cut_07922

theorem selected_cut_07923 : selected 8 ⟨226366, by decide⟩
    (prefixPartial 13 91167) = some ⟨13, 2, 0, 226366, 91167, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_91167_226366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91167 ⟨226366, by decide⟩ :=
  accepted_of_selected 13 91167 ⟨226366, by decide⟩ ⟨13, 2, 0, 226366, 91167, 1217, 16384⟩
    (by decide) selected_cut_07923

theorem unmarked_context_12_22791_226367 : frontier 9 ⟨226367, by decide⟩
    (prefixCache 12 22791) (prefixPartial 12 22791) = false := by
  decide +kernel

theorem node_context_12_22791_226367 : EJMOriginalGlobalDAGData.nodes 9 ⟨226367, by decide⟩ =
    .split (coordinate 12) (![⟨226274, by decide⟩,⟨226338, by decide⟩,⟨226357, by decide⟩,⟨226366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22791_226367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22791 ⟨226367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22791
    ⟨226367, by decide⟩ (by decide) (![⟨226274, by decide⟩,⟨226338, by decide⟩,⟨226357, by decide⟩,⟨226366, by decide⟩]) unmarked_context_12_22791_226367 node_context_12_22791_226367
  intro a
  fin_cases a
  · exact context_13_91164_226274
  · exact context_13_91165_226338
  · exact context_13_91166_226357
  · exact context_13_91167_226366

theorem unmarked_context_11_5697_226368 : frontier 10 ⟨226368, by decide⟩
    (prefixCache 11 5697) (prefixPartial 11 5697) = false := by
  decide +kernel

theorem node_context_11_5697_226368 : EJMOriginalGlobalDAGData.nodes 10 ⟨226368, by decide⟩ =
    .split (coordinate 11) (![⟨225792, by decide⟩,⟨226039, by decide⟩,⟨226206, by decide⟩,⟨226367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5697_226368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5697 ⟨226368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5697
    ⟨226368, by decide⟩ (by decide) (![⟨225792, by decide⟩,⟨226039, by decide⟩,⟨226206, by decide⟩,⟨226367, by decide⟩]) unmarked_context_11_5697_226368 node_context_11_5697_226368
  intro a
  fin_cases a
  · exact context_12_22788_225792
  · exact context_12_22789_226039
  · exact context_12_22790_226206
  · exact context_12_22791_226367

theorem selected_cut_07924 : selected 8 ⟨226407, by decide⟩
    (prefixPartial 13 91168) = some ⟨13, 2, 0, 226407, 91168, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_91168_226407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91168 ⟨226407, by decide⟩ :=
  accepted_of_selected 13 91168 ⟨226407, by decide⟩ ⟨13, 2, 0, 226407, 91168, 2993, 16384⟩
    (by decide) selected_cut_07924

theorem selected_cut_07925 : selected 8 ⟨226456, by decide⟩
    (prefixPartial 13 91169) = some ⟨13, 2, 0, 226456, 91169, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_91169_226456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91169 ⟨226456, by decide⟩ :=
  accepted_of_selected 13 91169 ⟨226456, by decide⟩ ⟨13, 2, 0, 226456, 91169, 3477, 16384⟩
    (by decide) selected_cut_07925

theorem selected_cut_07926 : selected 8 ⟨226478, by decide⟩
    (prefixPartial 13 91170) = some ⟨13, 2, 0, 226478, 91170, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_91170_226478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91170 ⟨226478, by decide⟩ :=
  accepted_of_selected 13 91170 ⟨226478, by decide⟩ ⟨13, 2, 0, 226478, 91170, 2185, 16384⟩
    (by decide) selected_cut_07926

theorem selected_cut_07927 : selected 8 ⟨226487, by decide⟩
    (prefixPartial 13 91171) = some ⟨13, 2, 0, 226487, 91171, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_91171_226487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91171 ⟨226487, by decide⟩ :=
  accepted_of_selected 13 91171 ⟨226487, by decide⟩ ⟨13, 2, 0, 226487, 91171, 1177, 16384⟩
    (by decide) selected_cut_07927

theorem unmarked_context_12_22792_226488 : frontier 9 ⟨226488, by decide⟩
    (prefixCache 12 22792) (prefixPartial 12 22792) = false := by
  decide +kernel

theorem node_context_12_22792_226488 : EJMOriginalGlobalDAGData.nodes 9 ⟨226488, by decide⟩ =
    .split (coordinate 12) (![⟨226407, by decide⟩,⟨226456, by decide⟩,⟨226478, by decide⟩,⟨226487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22792_226488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22792 ⟨226488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22792
    ⟨226488, by decide⟩ (by decide) (![⟨226407, by decide⟩,⟨226456, by decide⟩,⟨226478, by decide⟩,⟨226487, by decide⟩]) unmarked_context_12_22792_226488 node_context_12_22792_226488
  intro a
  fin_cases a
  · exact context_13_91168_226407
  · exact context_13_91169_226456
  · exact context_13_91170_226478
  · exact context_13_91171_226487

theorem selected_cut_07928 : selected 8 ⟨226527, by decide⟩
    (prefixPartial 13 91172) = some ⟨13, 2, 0, 226527, 91172, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_91172_226527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91172 ⟨226527, by decide⟩ :=
  accepted_of_selected 13 91172 ⟨226527, by decide⟩ ⟨13, 2, 0, 226527, 91172, 3041, 16384⟩
    (by decide) selected_cut_07928

theorem selected_cut_07929 : selected 8 ⟨226549, by decide⟩
    (prefixPartial 13 91173) = some ⟨13, 2, 0, 226549, 91173, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_91173_226549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91173 ⟨226549, by decide⟩ :=
  accepted_of_selected 13 91173 ⟨226549, by decide⟩ ⟨13, 2, 0, 226549, 91173, 2861, 16384⟩
    (by decide) selected_cut_07929

theorem selected_cut_07930 : selected 8 ⟨226568, by decide⟩
    (prefixPartial 13 91174) = some ⟨13, 2, 0, 226568, 91174, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_91174_226568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91174 ⟨226568, by decide⟩ :=
  accepted_of_selected 13 91174 ⟨226568, by decide⟩ ⟨13, 2, 0, 226568, 91174, 2145, 16384⟩
    (by decide) selected_cut_07930

theorem selected_cut_07931 : selected 8 ⟨226575, by decide⟩
    (prefixPartial 13 91175) = some ⟨13, 2, 0, 226575, 91175, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_91175_226575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91175 ⟨226575, by decide⟩ :=
  accepted_of_selected 13 91175 ⟨226575, by decide⟩ ⟨13, 2, 0, 226575, 91175, 1161, 16384⟩
    (by decide) selected_cut_07931

theorem unmarked_context_12_22793_226576 : frontier 9 ⟨226576, by decide⟩
    (prefixCache 12 22793) (prefixPartial 12 22793) = false := by
  decide +kernel

theorem node_context_12_22793_226576 : EJMOriginalGlobalDAGData.nodes 9 ⟨226576, by decide⟩ =
    .split (coordinate 12) (![⟨226527, by decide⟩,⟨226549, by decide⟩,⟨226568, by decide⟩,⟨226575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22793_226576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22793 ⟨226576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22793
    ⟨226576, by decide⟩ (by decide) (![⟨226527, by decide⟩,⟨226549, by decide⟩,⟨226568, by decide⟩,⟨226575, by decide⟩]) unmarked_context_12_22793_226576 node_context_12_22793_226576
  intro a
  fin_cases a
  · exact context_13_91172_226527
  · exact context_13_91173_226549
  · exact context_13_91174_226568
  · exact context_13_91175_226575

theorem selected_cut_07932 : selected 7 ⟨226595, by decide⟩
    (prefixPartial 14 364704) = some ⟨14, 2, 0, 226595, 364704, 941, 4096⟩ := by
  decide +kernel

theorem context_14_364704_226595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364704 ⟨226595, by decide⟩ :=
  accepted_of_selected 14 364704 ⟨226595, by decide⟩ ⟨14, 2, 0, 226595, 364704, 941, 4096⟩
    (by decide) selected_cut_07932

theorem selected_cut_07933 : selected 7 ⟨226609, by decide⟩
    (prefixPartial 14 364705) = some ⟨14, 2, 0, 226609, 364705, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_364705_226609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364705 ⟨226609, by decide⟩ :=
  accepted_of_selected 14 364705 ⟨226609, by decide⟩ ⟨14, 2, 0, 226609, 364705, 1073, 4096⟩
    (by decide) selected_cut_07933

theorem selected_cut_07934 : selected 7 ⟨226624, by decide⟩
    (prefixPartial 14 364706) = some ⟨14, 2, 0, 226624, 364706, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_364706_226624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364706 ⟨226624, by decide⟩ :=
  accepted_of_selected 14 364706 ⟨226624, by decide⟩ ⟨14, 2, 0, 226624, 364706, 1169, 4096⟩
    (by decide) selected_cut_07934

theorem selected_cut_07935 : selected 7 ⟨226638, by decide⟩
    (prefixPartial 14 364707) = some ⟨14, 2, 0, 226638, 364707, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_364707_226638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364707 ⟨226638, by decide⟩ :=
  accepted_of_selected 14 364707 ⟨226638, by decide⟩ ⟨14, 2, 0, 226638, 364707, 1181, 4096⟩
    (by decide) selected_cut_07935

theorem unmarked_context_13_91176_226639 : frontier 8 ⟨226639, by decide⟩
    (prefixCache 13 91176) (prefixPartial 13 91176) = false := by
  decide +kernel

theorem node_context_13_91176_226639 : EJMOriginalGlobalDAGData.nodes 8 ⟨226639, by decide⟩ =
    .split (coordinate 13) (![⟨226595, by decide⟩,⟨226609, by decide⟩,⟨226624, by decide⟩,⟨226638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91176_226639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91176 ⟨226639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91176
    ⟨226639, by decide⟩ (by decide) (![⟨226595, by decide⟩,⟨226609, by decide⟩,⟨226624, by decide⟩,⟨226638, by decide⟩]) unmarked_context_13_91176_226639 node_context_13_91176_226639
  intro a
  fin_cases a
  · exact context_14_364704_226595
  · exact context_14_364705_226609
  · exact context_14_364706_226624
  · exact context_14_364707_226638

theorem selected_cut_07936 : selected 8 ⟨226694, by decide⟩
    (prefixPartial 13 91177) = some ⟨13, 2, 0, 226694, 91177, 3845, 16384⟩ := by
  decide +kernel

theorem context_13_91177_226694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91177 ⟨226694, by decide⟩ :=
  accepted_of_selected 13 91177 ⟨226694, by decide⟩ ⟨13, 2, 0, 226694, 91177, 3845, 16384⟩
    (by decide) selected_cut_07936

theorem selected_cut_07937 : selected 8 ⟨226724, by decide⟩
    (prefixPartial 13 91178) = some ⟨13, 2, 0, 226724, 91178, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_91178_226724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91178 ⟨226724, by decide⟩ :=
  accepted_of_selected 13 91178 ⟨226724, by decide⟩ ⟨13, 2, 0, 226724, 91178, 2481, 16384⟩
    (by decide) selected_cut_07937

theorem selected_cut_07938 : selected 8 ⟨226741, by decide⟩
    (prefixPartial 13 91179) = some ⟨13, 2, 0, 226741, 91179, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_91179_226741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91179 ⟨226741, by decide⟩ :=
  accepted_of_selected 13 91179 ⟨226741, by decide⟩ ⟨13, 2, 0, 226741, 91179, 1285, 16384⟩
    (by decide) selected_cut_07938

theorem unmarked_context_12_22794_226742 : frontier 9 ⟨226742, by decide⟩
    (prefixCache 12 22794) (prefixPartial 12 22794) = false := by
  decide +kernel

theorem node_context_12_22794_226742 : EJMOriginalGlobalDAGData.nodes 9 ⟨226742, by decide⟩ =
    .split (coordinate 12) (![⟨226639, by decide⟩,⟨226694, by decide⟩,⟨226724, by decide⟩,⟨226741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22794_226742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22794 ⟨226742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22794
    ⟨226742, by decide⟩ (by decide) (![⟨226639, by decide⟩,⟨226694, by decide⟩,⟨226724, by decide⟩,⟨226741, by decide⟩]) unmarked_context_12_22794_226742 node_context_12_22794_226742
  intro a
  fin_cases a
  · exact context_13_91176_226639
  · exact context_13_91177_226694
  · exact context_13_91178_226724
  · exact context_13_91179_226741

theorem selected_cut_07939 : selected 7 ⟨226756, by decide⟩
    (prefixPartial 14 364720) = some ⟨14, 2, 0, 226756, 364720, 781, 4096⟩ := by
  decide +kernel

theorem context_14_364720_226756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364720 ⟨226756, by decide⟩ :=
  accepted_of_selected 14 364720 ⟨226756, by decide⟩ ⟨14, 2, 0, 226756, 364720, 781, 4096⟩
    (by decide) selected_cut_07939

theorem selected_cut_07940 : selected 7 ⟨226772, by decide⟩
    (prefixPartial 14 364721) = some ⟨14, 2, 0, 226772, 364721, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_364721_226772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364721 ⟨226772, by decide⟩ :=
  accepted_of_selected 14 364721 ⟨226772, by decide⟩ ⟨14, 2, 0, 226772, 364721, 1169, 4096⟩
    (by decide) selected_cut_07940

theorem selected_cut_07941 : selected 7 ⟨226791, by decide⟩
    (prefixPartial 14 364722) = some ⟨14, 2, 0, 226791, 364722, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_364722_226791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364722 ⟨226791, by decide⟩ :=
  accepted_of_selected 14 364722 ⟨226791, by decide⟩ ⟨14, 2, 0, 226791, 364722, 1197, 4096⟩
    (by decide) selected_cut_07941

theorem selected_cut_07942 : selected 7 ⟨226806, by decide⟩
    (prefixPartial 14 364723) = some ⟨14, 2, 0, 226806, 364723, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_364723_226806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364723 ⟨226806, by decide⟩ :=
  accepted_of_selected 14 364723 ⟨226806, by decide⟩ ⟨14, 2, 0, 226806, 364723, 1213, 4096⟩
    (by decide) selected_cut_07942

theorem unmarked_context_13_91180_226807 : frontier 8 ⟨226807, by decide⟩
    (prefixCache 13 91180) (prefixPartial 13 91180) = false := by
  decide +kernel

theorem node_context_13_91180_226807 : EJMOriginalGlobalDAGData.nodes 8 ⟨226807, by decide⟩ =
    .split (coordinate 13) (![⟨226756, by decide⟩,⟨226772, by decide⟩,⟨226791, by decide⟩,⟨226806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91180_226807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91180 ⟨226807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91180
    ⟨226807, by decide⟩ (by decide) (![⟨226756, by decide⟩,⟨226772, by decide⟩,⟨226791, by decide⟩,⟨226806, by decide⟩]) unmarked_context_13_91180_226807 node_context_13_91180_226807
  intro a
  fin_cases a
  · exact context_14_364720_226756
  · exact context_14_364721_226772
  · exact context_14_364722_226791
  · exact context_14_364723_226806

theorem selected_cut_07943 : selected 7 ⟨226826, by decide⟩
    (prefixPartial 14 364724) = some ⟨14, 2, 0, 226826, 364724, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_364724_226826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364724 ⟨226826, by decide⟩ :=
  accepted_of_selected 14 364724 ⟨226826, by decide⟩ ⟨14, 2, 0, 226826, 364724, 1105, 4096⟩
    (by decide) selected_cut_07943

theorem selected_cut_07944 : selected 7 ⟨226841, by decide⟩
    (prefixPartial 14 364725) = some ⟨14, 2, 0, 226841, 364725, 917, 4096⟩ := by
  decide +kernel

theorem context_14_364725_226841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364725 ⟨226841, by decide⟩ :=
  accepted_of_selected 14 364725 ⟨226841, by decide⟩ ⟨14, 2, 0, 226841, 364725, 917, 4096⟩
    (by decide) selected_cut_07944

theorem selected_cut_07945 : selected 7 ⟨226863, by decide⟩
    (prefixPartial 14 364726) = some ⟨14, 2, 0, 226863, 364726, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_364726_226863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364726 ⟨226863, by decide⟩ :=
  accepted_of_selected 14 364726 ⟨226863, by decide⟩ ⟨14, 2, 0, 226863, 364726, 1133, 4096⟩
    (by decide) selected_cut_07945

theorem selected_cut_07946 : selected 7 ⟨226876, by decide⟩
    (prefixPartial 14 364727) = some ⟨14, 2, 0, 226876, 364727, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_364727_226876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364727 ⟨226876, by decide⟩ :=
  accepted_of_selected 14 364727 ⟨226876, by decide⟩ ⟨14, 2, 0, 226876, 364727, 1041, 4096⟩
    (by decide) selected_cut_07946

theorem unmarked_context_13_91181_226877 : frontier 8 ⟨226877, by decide⟩
    (prefixCache 13 91181) (prefixPartial 13 91181) = false := by
  decide +kernel

theorem node_context_13_91181_226877 : EJMOriginalGlobalDAGData.nodes 8 ⟨226877, by decide⟩ =
    .split (coordinate 13) (![⟨226826, by decide⟩,⟨226841, by decide⟩,⟨226863, by decide⟩,⟨226876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91181_226877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91181 ⟨226877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91181
    ⟨226877, by decide⟩ (by decide) (![⟨226826, by decide⟩,⟨226841, by decide⟩,⟨226863, by decide⟩,⟨226876, by decide⟩]) unmarked_context_13_91181_226877 node_context_13_91181_226877
  intro a
  fin_cases a
  · exact context_14_364724_226826
  · exact context_14_364725_226841
  · exact context_14_364726_226863
  · exact context_14_364727_226876

theorem selected_cut_07947 : selected 8 ⟨226908, by decide⟩
    (prefixPartial 13 91182) = some ⟨13, 2, 0, 226908, 91182, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_91182_226908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91182 ⟨226908, by decide⟩ :=
  accepted_of_selected 13 91182 ⟨226908, by decide⟩ ⟨13, 2, 0, 226908, 91182, 2569, 16384⟩
    (by decide) selected_cut_07947

theorem selected_cut_07948 : selected 8 ⟨226922, by decide⟩
    (prefixPartial 13 91183) = some ⟨13, 2, 0, 226922, 91183, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_91183_226922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91183 ⟨226922, by decide⟩ :=
  accepted_of_selected 13 91183 ⟨226922, by decide⟩ ⟨13, 2, 0, 226922, 91183, 1273, 16384⟩
    (by decide) selected_cut_07948

theorem unmarked_context_12_22795_226923 : frontier 9 ⟨226923, by decide⟩
    (prefixCache 12 22795) (prefixPartial 12 22795) = false := by
  decide +kernel

theorem node_context_12_22795_226923 : EJMOriginalGlobalDAGData.nodes 9 ⟨226923, by decide⟩ =
    .split (coordinate 12) (![⟨226807, by decide⟩,⟨226877, by decide⟩,⟨226908, by decide⟩,⟨226922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22795_226923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22795 ⟨226923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22795
    ⟨226923, by decide⟩ (by decide) (![⟨226807, by decide⟩,⟨226877, by decide⟩,⟨226908, by decide⟩,⟨226922, by decide⟩]) unmarked_context_12_22795_226923 node_context_12_22795_226923
  intro a
  fin_cases a
  · exact context_13_91180_226807
  · exact context_13_91181_226877
  · exact context_13_91182_226908
  · exact context_13_91183_226922

theorem unmarked_context_11_5698_226924 : frontier 10 ⟨226924, by decide⟩
    (prefixCache 11 5698) (prefixPartial 11 5698) = false := by
  decide +kernel

theorem node_context_11_5698_226924 : EJMOriginalGlobalDAGData.nodes 10 ⟨226924, by decide⟩ =
    .split (coordinate 11) (![⟨226488, by decide⟩,⟨226576, by decide⟩,⟨226742, by decide⟩,⟨226923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5698_226924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5698 ⟨226924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5698
    ⟨226924, by decide⟩ (by decide) (![⟨226488, by decide⟩,⟨226576, by decide⟩,⟨226742, by decide⟩,⟨226923, by decide⟩]) unmarked_context_11_5698_226924 node_context_11_5698_226924
  intro a
  fin_cases a
  · exact context_12_22792_226488
  · exact context_12_22793_226576
  · exact context_12_22794_226742
  · exact context_12_22795_226923

theorem selected_cut_07949 : selected 8 ⟨226962, by decide⟩
    (prefixPartial 13 91184) = some ⟨13, 2, 0, 226962, 91184, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_91184_226962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91184 ⟨226962, by decide⟩ :=
  accepted_of_selected 13 91184 ⟨226962, by decide⟩ ⟨13, 2, 0, 226962, 91184, 2761, 16384⟩
    (by decide) selected_cut_07949

theorem selected_cut_07950 : selected 8 ⟨227005, by decide⟩
    (prefixPartial 13 91185) = some ⟨13, 2, 0, 227005, 91185, 3589, 16384⟩ := by
  decide +kernel

theorem context_13_91185_227005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91185 ⟨227005, by decide⟩ :=
  accepted_of_selected 13 91185 ⟨227005, by decide⟩ ⟨13, 2, 0, 227005, 91185, 3589, 16384⟩
    (by decide) selected_cut_07950

theorem selected_cut_07951 : selected 8 ⟨227025, by decide⟩
    (prefixPartial 13 91186) = some ⟨13, 2, 0, 227025, 91186, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_91186_227025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91186 ⟨227025, by decide⟩ :=
  accepted_of_selected 13 91186 ⟨227025, by decide⟩ ⟨13, 2, 0, 227025, 91186, 1989, 16384⟩
    (by decide) selected_cut_07951

theorem selected_cut_07952 : selected 8 ⟨227041, by decide⟩
    (prefixPartial 13 91187) = some ⟨13, 2, 0, 227041, 91187, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_91187_227041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91187 ⟨227041, by decide⟩ :=
  accepted_of_selected 13 91187 ⟨227041, by decide⟩ ⟨13, 2, 0, 227041, 91187, 1285, 16384⟩
    (by decide) selected_cut_07952

theorem unmarked_context_12_22796_227042 : frontier 9 ⟨227042, by decide⟩
    (prefixCache 12 22796) (prefixPartial 12 22796) = false := by
  decide +kernel

theorem node_context_12_22796_227042 : EJMOriginalGlobalDAGData.nodes 9 ⟨227042, by decide⟩ =
    .split (coordinate 12) (![⟨226962, by decide⟩,⟨227005, by decide⟩,⟨227025, by decide⟩,⟨227041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22796_227042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22796 ⟨227042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22796
    ⟨227042, by decide⟩ (by decide) (![⟨226962, by decide⟩,⟨227005, by decide⟩,⟨227025, by decide⟩,⟨227041, by decide⟩]) unmarked_context_12_22796_227042 node_context_12_22796_227042
  intro a
  fin_cases a
  · exact context_13_91184_226962
  · exact context_13_91185_227005
  · exact context_13_91186_227025
  · exact context_13_91187_227041

theorem selected_cut_07953 : selected 8 ⟨227078, by decide⟩
    (prefixPartial 13 91188) = some ⟨13, 2, 0, 227078, 91188, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_91188_227078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91188 ⟨227078, by decide⟩ :=
  accepted_of_selected 13 91188 ⟨227078, by decide⟩ ⟨13, 2, 0, 227078, 91188, 2813, 16384⟩
    (by decide) selected_cut_07953

theorem selected_cut_07954 : selected 8 ⟨227108, by decide⟩
    (prefixPartial 13 91189) = some ⟨13, 2, 0, 227108, 91189, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_91189_227108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91189 ⟨227108, by decide⟩ :=
  accepted_of_selected 13 91189 ⟨227108, by decide⟩ ⟨13, 2, 0, 227108, 91189, 2865, 16384⟩
    (by decide) selected_cut_07954

theorem selected_cut_07955 : selected 8 ⟨227122, by decide⟩
    (prefixPartial 13 91190) = some ⟨13, 2, 0, 227122, 91190, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_91190_227122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91190 ⟨227122, by decide⟩ :=
  accepted_of_selected 13 91190 ⟨227122, by decide⟩ ⟨13, 2, 0, 227122, 91190, 1993, 16384⟩
    (by decide) selected_cut_07955

theorem selected_cut_07956 : selected 8 ⟨227127, by decide⟩
    (prefixPartial 13 91191) = some ⟨13, 2, 0, 227127, 91191, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_91191_227127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91191 ⟨227127, by decide⟩ :=
  accepted_of_selected 13 91191 ⟨227127, by decide⟩ ⟨13, 2, 0, 227127, 91191, 1177, 16384⟩
    (by decide) selected_cut_07956

theorem unmarked_context_12_22797_227128 : frontier 9 ⟨227128, by decide⟩
    (prefixCache 12 22797) (prefixPartial 12 22797) = false := by
  decide +kernel

theorem node_context_12_22797_227128 : EJMOriginalGlobalDAGData.nodes 9 ⟨227128, by decide⟩ =
    .split (coordinate 12) (![⟨227078, by decide⟩,⟨227108, by decide⟩,⟨227122, by decide⟩,⟨227127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22797_227128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22797 ⟨227128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22797
    ⟨227128, by decide⟩ (by decide) (![⟨227078, by decide⟩,⟨227108, by decide⟩,⟨227122, by decide⟩,⟨227127, by decide⟩]) unmarked_context_12_22797_227128 node_context_12_22797_227128
  intro a
  fin_cases a
  · exact context_13_91188_227078
  · exact context_13_91189_227108
  · exact context_13_91190_227122
  · exact context_13_91191_227127

theorem selected_cut_07957 : selected 7 ⟨227135, by decide⟩
    (prefixPartial 14 364768) = some ⟨14, 2, 0, 227135, 364768, 353, 4096⟩ := by
  decide +kernel

theorem context_14_364768_227135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364768 ⟨227135, by decide⟩ :=
  accepted_of_selected 14 364768 ⟨227135, by decide⟩ ⟨14, 2, 0, 227135, 364768, 353, 4096⟩
    (by decide) selected_cut_07957

theorem selected_cut_07958 : selected 7 ⟨227154, by decide⟩
    (prefixPartial 14 364769) = some ⟨14, 2, 0, 227154, 364769, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_364769_227154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364769 ⟨227154, by decide⟩ :=
  accepted_of_selected 14 364769 ⟨227154, by decide⟩ ⟨14, 2, 0, 227154, 364769, 1229, 4096⟩
    (by decide) selected_cut_07958

theorem selected_cut_07959 : selected 7 ⟨227175, by decide⟩
    (prefixPartial 14 364770) = some ⟨14, 2, 0, 227175, 364770, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_364770_227175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364770 ⟨227175, by decide⟩ :=
  accepted_of_selected 14 364770 ⟨227175, by decide⟩ ⟨14, 2, 0, 227175, 364770, 1393, 4096⟩
    (by decide) selected_cut_07959

theorem selected_cut_07960 : selected 7 ⟨227190, by decide⟩
    (prefixPartial 14 364771) = some ⟨14, 2, 0, 227190, 364771, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_364771_227190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364771 ⟨227190, by decide⟩ :=
  accepted_of_selected 14 364771 ⟨227190, by decide⟩ ⟨14, 2, 0, 227190, 364771, 1157, 4096⟩
    (by decide) selected_cut_07960

theorem unmarked_context_13_91192_227191 : frontier 8 ⟨227191, by decide⟩
    (prefixCache 13 91192) (prefixPartial 13 91192) = false := by
  decide +kernel

theorem node_context_13_91192_227191 : EJMOriginalGlobalDAGData.nodes 8 ⟨227191, by decide⟩ =
    .split (coordinate 13) (![⟨227135, by decide⟩,⟨227154, by decide⟩,⟨227175, by decide⟩,⟨227190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91192_227191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91192 ⟨227191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91192
    ⟨227191, by decide⟩ (by decide) (![⟨227135, by decide⟩,⟨227154, by decide⟩,⟨227175, by decide⟩,⟨227190, by decide⟩]) unmarked_context_13_91192_227191 node_context_13_91192_227191
  intro a
  fin_cases a
  · exact context_14_364768_227135
  · exact context_14_364769_227154
  · exact context_14_364770_227175
  · exact context_14_364771_227190

theorem selected_cut_07961 : selected 8 ⟨227248, by decide⟩
    (prefixPartial 13 91193) = some ⟨13, 2, 0, 227248, 91193, 4073, 16384⟩ := by
  decide +kernel

theorem context_13_91193_227248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91193 ⟨227248, by decide⟩ :=
  accepted_of_selected 13 91193 ⟨227248, by decide⟩ ⟨13, 2, 0, 227248, 91193, 4073, 16384⟩
    (by decide) selected_cut_07961

theorem selected_cut_07962 : selected 8 ⟨227272, by decide⟩
    (prefixPartial 13 91194) = some ⟨13, 2, 0, 227272, 91194, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_91194_227272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91194 ⟨227272, by decide⟩ :=
  accepted_of_selected 13 91194 ⟨227272, by decide⟩ ⟨13, 2, 0, 227272, 91194, 2353, 16384⟩
    (by decide) selected_cut_07962

theorem selected_cut_07963 : selected 8 ⟨227285, by decide⟩
    (prefixPartial 13 91195) = some ⟨13, 2, 0, 227285, 91195, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_91195_227285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91195 ⟨227285, by decide⟩ :=
  accepted_of_selected 13 91195 ⟨227285, by decide⟩ ⟨13, 2, 0, 227285, 91195, 1289, 16384⟩
    (by decide) selected_cut_07963

theorem unmarked_context_12_22798_227286 : frontier 9 ⟨227286, by decide⟩
    (prefixCache 12 22798) (prefixPartial 12 22798) = false := by
  decide +kernel

theorem node_context_12_22798_227286 : EJMOriginalGlobalDAGData.nodes 9 ⟨227286, by decide⟩ =
    .split (coordinate 12) (![⟨227191, by decide⟩,⟨227248, by decide⟩,⟨227272, by decide⟩,⟨227285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22798_227286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22798 ⟨227286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22798
    ⟨227286, by decide⟩ (by decide) (![⟨227191, by decide⟩,⟨227248, by decide⟩,⟨227272, by decide⟩,⟨227285, by decide⟩]) unmarked_context_12_22798_227286 node_context_12_22798_227286
  intro a
  fin_cases a
  · exact context_13_91192_227191
  · exact context_13_91193_227248
  · exact context_13_91194_227272
  · exact context_13_91195_227285

theorem selected_cut_07964 : selected 8 ⟨227344, by decide⟩
    (prefixPartial 13 91196) = some ⟨13, 2, 0, 227344, 91196, 3925, 16384⟩ := by
  decide +kernel

theorem context_13_91196_227344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91196 ⟨227344, by decide⟩ :=
  accepted_of_selected 13 91196 ⟨227344, by decide⟩ ⟨13, 2, 0, 227344, 91196, 3925, 16384⟩
    (by decide) selected_cut_07964

theorem selected_cut_07965 : selected 7 ⟨227352, by decide⟩
    (prefixPartial 14 364788) = some ⟨14, 2, 0, 227352, 364788, 1029, 4096⟩ := by
  decide +kernel

theorem context_14_364788_227352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364788 ⟨227352, by decide⟩ :=
  accepted_of_selected 14 364788 ⟨227352, by decide⟩ ⟨14, 2, 0, 227352, 364788, 1029, 4096⟩
    (by decide) selected_cut_07965

theorem selected_cut_07966 : selected 7 ⟨227367, by decide⟩
    (prefixPartial 14 364789) = some ⟨14, 2, 0, 227367, 364789, 945, 4096⟩ := by
  decide +kernel

theorem context_14_364789_227367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364789 ⟨227367, by decide⟩ :=
  accepted_of_selected 14 364789 ⟨227367, by decide⟩ ⟨14, 2, 0, 227367, 364789, 945, 4096⟩
    (by decide) selected_cut_07966

theorem selected_cut_07967 : selected 7 ⟨227387, by decide⟩
    (prefixPartial 14 364790) = some ⟨14, 2, 0, 227387, 364790, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_364790_227387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364790 ⟨227387, by decide⟩ :=
  accepted_of_selected 14 364790 ⟨227387, by decide⟩ ⟨14, 2, 0, 227387, 364790, 1125, 4096⟩
    (by decide) selected_cut_07967

theorem selected_cut_07968 : selected 7 ⟨227403, by decide⟩
    (prefixPartial 14 364791) = some ⟨14, 2, 0, 227403, 364791, 997, 4096⟩ := by
  decide +kernel

theorem context_14_364791_227403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 364791 ⟨227403, by decide⟩ :=
  accepted_of_selected 14 364791 ⟨227403, by decide⟩ ⟨14, 2, 0, 227403, 364791, 997, 4096⟩
    (by decide) selected_cut_07968

theorem unmarked_context_13_91197_227404 : frontier 8 ⟨227404, by decide⟩
    (prefixCache 13 91197) (prefixPartial 13 91197) = false := by
  decide +kernel

theorem node_context_13_91197_227404 : EJMOriginalGlobalDAGData.nodes 8 ⟨227404, by decide⟩ =
    .split (coordinate 13) (![⟨227352, by decide⟩,⟨227367, by decide⟩,⟨227387, by decide⟩,⟨227403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_91197_227404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91197 ⟨227404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 91197
    ⟨227404, by decide⟩ (by decide) (![⟨227352, by decide⟩,⟨227367, by decide⟩,⟨227387, by decide⟩,⟨227403, by decide⟩]) unmarked_context_13_91197_227404 node_context_13_91197_227404
  intro a
  fin_cases a
  · exact context_14_364788_227352
  · exact context_14_364789_227367
  · exact context_14_364790_227387
  · exact context_14_364791_227403

theorem selected_cut_07969 : selected 8 ⟨227418, by decide⟩
    (prefixPartial 13 91198) = some ⟨13, 2, 0, 227418, 91198, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_91198_227418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91198 ⟨227418, by decide⟩ :=
  accepted_of_selected 13 91198 ⟨227418, by decide⟩ ⟨13, 2, 0, 227418, 91198, 2217, 16384⟩
    (by decide) selected_cut_07969

theorem selected_cut_07970 : selected 8 ⟨227426, by decide⟩
    (prefixPartial 13 91199) = some ⟨13, 2, 0, 227426, 91199, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_91199_227426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91199 ⟨227426, by decide⟩ :=
  accepted_of_selected 13 91199 ⟨227426, by decide⟩ ⟨13, 2, 0, 227426, 91199, 1281, 16384⟩
    (by decide) selected_cut_07970

theorem unmarked_context_12_22799_227427 : frontier 9 ⟨227427, by decide⟩
    (prefixCache 12 22799) (prefixPartial 12 22799) = false := by
  decide +kernel

theorem node_context_12_22799_227427 : EJMOriginalGlobalDAGData.nodes 9 ⟨227427, by decide⟩ =
    .split (coordinate 12) (![⟨227344, by decide⟩,⟨227404, by decide⟩,⟨227418, by decide⟩,⟨227426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22799_227427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22799 ⟨227427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22799
    ⟨227427, by decide⟩ (by decide) (![⟨227344, by decide⟩,⟨227404, by decide⟩,⟨227418, by decide⟩,⟨227426, by decide⟩]) unmarked_context_12_22799_227427 node_context_12_22799_227427
  intro a
  fin_cases a
  · exact context_13_91196_227344
  · exact context_13_91197_227404
  · exact context_13_91198_227418
  · exact context_13_91199_227426

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
