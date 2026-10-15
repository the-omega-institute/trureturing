/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover278
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26787 : selected 8 ⟨676997, by decide⟩
    (prefixPartial 13 364575) = some ⟨13, 2, 0, 676997, 364575, 145, 16384⟩ := by
  decide +kernel

theorem context_13_364575_676997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364575 ⟨676997, by decide⟩ :=
  accepted_of_selected 13 364575 ⟨676997, by decide⟩ ⟨13, 2, 0, 676997, 364575, 145, 16384⟩
    (by decide) selected_cut_26787

theorem unmarked_context_12_91143_676998 : frontier 9 ⟨676998, by decide⟩
    (prefixCache 12 91143) (prefixPartial 12 91143) = false := by
  decide +kernel

theorem node_context_12_91143_676998 : EJMOriginalGlobalDAGData.nodes 9 ⟨676998, by decide⟩ =
    .split (coordinate 12) (![⟨676944, by decide⟩,⟨676981, by decide⟩,⟨676993, by decide⟩,⟨676997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91143_676998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91143 ⟨676998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91143
    ⟨676998, by decide⟩ (by decide) (![⟨676944, by decide⟩,⟨676981, by decide⟩,⟨676993, by decide⟩,⟨676997, by decide⟩]) unmarked_context_12_91143_676998 node_context_12_91143_676998
  intro a
  fin_cases a
  · exact context_13_364572_676944
  · exact context_13_364573_676981
  · exact context_13_364574_676993
  · exact context_13_364575_676997

theorem unmarked_context_11_22785_676999 : frontier 10 ⟨676999, by decide⟩
    (prefixCache 11 22785) (prefixPartial 11 22785) = false := by
  decide +kernel

theorem node_context_11_22785_676999 : EJMOriginalGlobalDAGData.nodes 10 ⟨676999, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨676865, by decide⟩,⟨676998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22785_676999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22785 ⟨676999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22785
    ⟨676999, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨676865, by decide⟩,⟨676998, by decide⟩]) unmarked_context_11_22785_676999 node_context_11_22785_676999
  intro a
  fin_cases a
  · exact context_12_91140_448748
  · exact context_12_91141_34034
  · exact context_12_91142_676865
  · exact context_12_91143_676998

theorem selected_cut_26788 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91144) = some ⟨12, 1, 0, 448748, 91144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91144_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91144 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91144 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91144, 1, 65536⟩
    (by decide) selected_cut_26788

theorem selected_cut_26789 : selected 7 ⟨677027, by decide⟩
    (prefixPartial 14 1458320) = some ⟨14, 2, 0, 677027, 1458320, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_1458320_677027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1458320 ⟨677027, by decide⟩ :=
  accepted_of_selected 14 1458320 ⟨677027, by decide⟩ ⟨14, 2, 0, 677027, 1458320, 1057, 4096⟩
    (by decide) selected_cut_26789

theorem selected_cut_26790 : selected 7 ⟨677057, by decide⟩
    (prefixPartial 14 1458321) = some ⟨14, 2, 0, 677057, 1458321, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_1458321_677057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1458321 ⟨677057, by decide⟩ :=
  accepted_of_selected 14 1458321 ⟨677057, by decide⟩ ⟨14, 2, 0, 677057, 1458321, 1133, 4096⟩
    (by decide) selected_cut_26790

theorem selected_cut_26791 : selected 7 ⟨677080, by decide⟩
    (prefixPartial 14 1458322) = some ⟨14, 2, 0, 677080, 1458322, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_1458322_677080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1458322 ⟨677080, by decide⟩ :=
  accepted_of_selected 14 1458322 ⟨677080, by decide⟩ ⟨14, 2, 0, 677080, 1458322, 1037, 4096⟩
    (by decide) selected_cut_26791

theorem selected_cut_26792 : selected 7 ⟨677109, by decide⟩
    (prefixPartial 14 1458323) = some ⟨14, 2, 0, 677109, 1458323, 1397, 4096⟩ := by
  decide +kernel

theorem context_14_1458323_677109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1458323 ⟨677109, by decide⟩ :=
  accepted_of_selected 14 1458323 ⟨677109, by decide⟩ ⟨14, 2, 0, 677109, 1458323, 1397, 4096⟩
    (by decide) selected_cut_26792

theorem unmarked_context_13_364580_677110 : frontier 8 ⟨677110, by decide⟩
    (prefixCache 13 364580) (prefixPartial 13 364580) = false := by
  decide +kernel

theorem node_context_13_364580_677110 : EJMOriginalGlobalDAGData.nodes 8 ⟨677110, by decide⟩ =
    .split (coordinate 13) (![⟨677027, by decide⟩,⟨677057, by decide⟩,⟨677080, by decide⟩,⟨677109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_364580_677110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364580 ⟨677110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 364580
    ⟨677110, by decide⟩ (by decide) (![⟨677027, by decide⟩,⟨677057, by decide⟩,⟨677080, by decide⟩,⟨677109, by decide⟩]) unmarked_context_13_364580_677110 node_context_13_364580_677110
  intro a
  fin_cases a
  · exact context_14_1458320_677027
  · exact context_14_1458321_677057
  · exact context_14_1458322_677080
  · exact context_14_1458323_677109

theorem selected_cut_26793 : selected 8 ⟨677203, by decide⟩
    (prefixPartial 13 364581) = some ⟨13, 2, 0, 677203, 364581, 3817, 16384⟩ := by
  decide +kernel

theorem context_13_364581_677203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364581 ⟨677203, by decide⟩ :=
  accepted_of_selected 13 364581 ⟨677203, by decide⟩ ⟨13, 2, 0, 677203, 364581, 3817, 16384⟩
    (by decide) selected_cut_26793

theorem selected_cut_26794 : selected 8 ⟨677251, by decide⟩
    (prefixPartial 13 364582) = some ⟨13, 2, 0, 677251, 364582, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_364582_677251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364582 ⟨677251, by decide⟩ :=
  accepted_of_selected 13 364582 ⟨677251, by decide⟩ ⟨13, 2, 0, 677251, 364582, 2633, 16384⟩
    (by decide) selected_cut_26794

theorem selected_cut_26795 : selected 8 ⟨677267, by decide⟩
    (prefixPartial 13 364583) = some ⟨13, 2, 0, 677267, 364583, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_364583_677267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364583 ⟨677267, by decide⟩ :=
  accepted_of_selected 13 364583 ⟨677267, by decide⟩ ⟨13, 2, 0, 677267, 364583, 1085, 16384⟩
    (by decide) selected_cut_26795

theorem unmarked_context_12_91145_677268 : frontier 9 ⟨677268, by decide⟩
    (prefixCache 12 91145) (prefixPartial 12 91145) = false := by
  decide +kernel

theorem node_context_12_91145_677268 : EJMOriginalGlobalDAGData.nodes 9 ⟨677268, by decide⟩ =
    .split (coordinate 12) (![⟨677110, by decide⟩,⟨677203, by decide⟩,⟨677251, by decide⟩,⟨677267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91145_677268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91145 ⟨677268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91145
    ⟨677268, by decide⟩ (by decide) (![⟨677110, by decide⟩,⟨677203, by decide⟩,⟨677251, by decide⟩,⟨677267, by decide⟩]) unmarked_context_12_91145_677268 node_context_12_91145_677268
  intro a
  fin_cases a
  · exact context_13_364580_677110
  · exact context_13_364581_677203
  · exact context_13_364582_677251
  · exact context_13_364583_677267

theorem selected_cut_26796 : selected 8 ⟨677346, by decide⟩
    (prefixPartial 13 364584) = some ⟨13, 2, 0, 677346, 364584, 3325, 16384⟩ := by
  decide +kernel

theorem context_13_364584_677346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364584 ⟨677346, by decide⟩ :=
  accepted_of_selected 13 364584 ⟨677346, by decide⟩ ⟨13, 2, 0, 677346, 364584, 3325, 16384⟩
    (by decide) selected_cut_26796

theorem selected_cut_26797 : selected 8 ⟨677414, by decide⟩
    (prefixPartial 13 364585) = some ⟨13, 2, 0, 677414, 364585, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_364585_677414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364585 ⟨677414, by decide⟩ :=
  accepted_of_selected 13 364585 ⟨677414, by decide⟩ ⟨13, 2, 0, 677414, 364585, 3185, 16384⟩
    (by decide) selected_cut_26797

theorem selected_cut_26798 : selected 8 ⟨677438, by decide⟩
    (prefixPartial 13 364586) = some ⟨13, 2, 0, 677438, 364586, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_364586_677438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364586 ⟨677438, by decide⟩ :=
  accepted_of_selected 13 364586 ⟨677438, by decide⟩ ⟨13, 2, 0, 677438, 364586, 1981, 16384⟩
    (by decide) selected_cut_26798

theorem selected_cut_26799 : selected 8 ⟨677455, by decide⟩
    (prefixPartial 13 364587) = some ⟨13, 2, 0, 677455, 364587, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_364587_677455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364587 ⟨677455, by decide⟩ :=
  accepted_of_selected 13 364587 ⟨677455, by decide⟩ ⟨13, 2, 0, 677455, 364587, 1193, 16384⟩
    (by decide) selected_cut_26799

theorem unmarked_context_12_91146_677456 : frontier 9 ⟨677456, by decide⟩
    (prefixCache 12 91146) (prefixPartial 12 91146) = false := by
  decide +kernel

theorem node_context_12_91146_677456 : EJMOriginalGlobalDAGData.nodes 9 ⟨677456, by decide⟩ =
    .split (coordinate 12) (![⟨677346, by decide⟩,⟨677414, by decide⟩,⟨677438, by decide⟩,⟨677455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91146_677456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91146 ⟨677456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91146
    ⟨677456, by decide⟩ (by decide) (![⟨677346, by decide⟩,⟨677414, by decide⟩,⟨677438, by decide⟩,⟨677455, by decide⟩]) unmarked_context_12_91146_677456 node_context_12_91146_677456
  intro a
  fin_cases a
  · exact context_13_364584_677346
  · exact context_13_364585_677414
  · exact context_13_364586_677438
  · exact context_13_364587_677455

theorem selected_cut_26800 : selected 8 ⟨677540, by decide⟩
    (prefixPartial 13 364588) = some ⟨13, 2, 0, 677540, 364588, 4009, 16384⟩ := by
  decide +kernel

theorem context_13_364588_677540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364588 ⟨677540, by decide⟩ :=
  accepted_of_selected 13 364588 ⟨677540, by decide⟩ ⟨13, 2, 0, 677540, 364588, 4009, 16384⟩
    (by decide) selected_cut_26800

theorem selected_cut_26801 : selected 8 ⟨677625, by decide⟩
    (prefixPartial 13 364589) = some ⟨13, 2, 0, 677625, 364589, 4041, 16384⟩ := by
  decide +kernel

theorem context_13_364589_677625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364589 ⟨677625, by decide⟩ :=
  accepted_of_selected 13 364589 ⟨677625, by decide⟩ ⟨13, 2, 0, 677625, 364589, 4041, 16384⟩
    (by decide) selected_cut_26801

theorem selected_cut_26802 : selected 8 ⟨677660, by decide⟩
    (prefixPartial 13 364590) = some ⟨13, 2, 0, 677660, 364590, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_364590_677660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364590 ⟨677660, by decide⟩ :=
  accepted_of_selected 13 364590 ⟨677660, by decide⟩ ⟨13, 2, 0, 677660, 364590, 2561, 16384⟩
    (by decide) selected_cut_26802

theorem selected_cut_26803 : selected 8 ⟨677670, by decide⟩
    (prefixPartial 13 364591) = some ⟨13, 2, 0, 677670, 364591, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_364591_677670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364591 ⟨677670, by decide⟩ :=
  accepted_of_selected 13 364591 ⟨677670, by decide⟩ ⟨13, 2, 0, 677670, 364591, 1073, 16384⟩
    (by decide) selected_cut_26803

theorem unmarked_context_12_91147_677671 : frontier 9 ⟨677671, by decide⟩
    (prefixCache 12 91147) (prefixPartial 12 91147) = false := by
  decide +kernel

theorem node_context_12_91147_677671 : EJMOriginalGlobalDAGData.nodes 9 ⟨677671, by decide⟩ =
    .split (coordinate 12) (![⟨677540, by decide⟩,⟨677625, by decide⟩,⟨677660, by decide⟩,⟨677670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91147_677671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91147 ⟨677671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91147
    ⟨677671, by decide⟩ (by decide) (![⟨677540, by decide⟩,⟨677625, by decide⟩,⟨677660, by decide⟩,⟨677670, by decide⟩]) unmarked_context_12_91147_677671 node_context_12_91147_677671
  intro a
  fin_cases a
  · exact context_13_364588_677540
  · exact context_13_364589_677625
  · exact context_13_364590_677660
  · exact context_13_364591_677670

theorem unmarked_context_11_22786_677672 : frontier 10 ⟨677672, by decide⟩
    (prefixCache 11 22786) (prefixPartial 11 22786) = false := by
  decide +kernel

theorem node_context_11_22786_677672 : EJMOriginalGlobalDAGData.nodes 10 ⟨677672, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨677268, by decide⟩,⟨677456, by decide⟩,⟨677671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22786_677672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22786 ⟨677672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22786
    ⟨677672, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨677268, by decide⟩,⟨677456, by decide⟩,⟨677671, by decide⟩]) unmarked_context_11_22786_677672 node_context_11_22786_677672
  intro a
  fin_cases a
  · exact context_12_91144_448748
  · exact context_12_91145_677268
  · exact context_12_91146_677456
  · exact context_12_91147_677671

theorem selected_cut_26804 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91148) = some ⟨12, 1, 0, 448748, 91148, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91148_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91148 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91148 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91148, 1, 65536⟩
    (by decide) selected_cut_26804

theorem selected_cut_26805 : selected 8 ⟨677718, by decide⟩
    (prefixPartial 13 364596) = some ⟨13, 2, 0, 677718, 364596, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_364596_677718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364596 ⟨677718, by decide⟩ :=
  accepted_of_selected 13 364596 ⟨677718, by decide⟩ ⟨13, 2, 0, 677718, 364596, 1685, 16384⟩
    (by decide) selected_cut_26805

theorem selected_cut_26806 : selected 8 ⟨677781, by decide⟩
    (prefixPartial 13 364597) = some ⟨13, 2, 0, 677781, 364597, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_364597_677781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364597 ⟨677781, by decide⟩ :=
  accepted_of_selected 13 364597 ⟨677781, by decide⟩ ⟨13, 2, 0, 677781, 364597, 1957, 16384⟩
    (by decide) selected_cut_26806

theorem selected_cut_26807 : selected 8 ⟨677845, by decide⟩
    (prefixPartial 13 364598) = some ⟨13, 2, 0, 677845, 364598, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_364598_677845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364598 ⟨677845, by decide⟩ :=
  accepted_of_selected 13 364598 ⟨677845, by decide⟩ ⟨13, 2, 0, 677845, 364598, 1845, 16384⟩
    (by decide) selected_cut_26807

theorem selected_cut_26808 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 364599) = some ⟨13, 1, 0, 265883, 364599, 1, 16384⟩ := by
  decide +kernel

theorem context_13_364599_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364599 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 364599 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 364599, 1, 16384⟩
    (by decide) selected_cut_26808

theorem unmarked_context_12_91149_677846 : frontier 9 ⟨677846, by decide⟩
    (prefixCache 12 91149) (prefixPartial 12 91149) = false := by
  decide +kernel

theorem node_context_12_91149_677846 : EJMOriginalGlobalDAGData.nodes 9 ⟨677846, by decide⟩ =
    .split (coordinate 12) (![⟨677718, by decide⟩,⟨677781, by decide⟩,⟨677845, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91149_677846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91149 ⟨677846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91149
    ⟨677846, by decide⟩ (by decide) (![⟨677718, by decide⟩,⟨677781, by decide⟩,⟨677845, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_91149_677846 node_context_12_91149_677846
  intro a
  fin_cases a
  · exact context_13_364596_677718
  · exact context_13_364597_677781
  · exact context_13_364598_677845
  · exact context_13_364599_265883

theorem selected_cut_26809 : selected 8 ⟨677913, by decide⟩
    (prefixPartial 13 364600) = some ⟨13, 2, 0, 677913, 364600, 3281, 16384⟩ := by
  decide +kernel

theorem context_13_364600_677913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364600 ⟨677913, by decide⟩ :=
  accepted_of_selected 13 364600 ⟨677913, by decide⟩ ⟨13, 2, 0, 677913, 364600, 3281, 16384⟩
    (by decide) selected_cut_26809

theorem selected_cut_26810 : selected 8 ⟨677987, by decide⟩
    (prefixPartial 13 364601) = some ⟨13, 2, 0, 677987, 364601, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_364601_677987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364601 ⟨677987, by decide⟩ :=
  accepted_of_selected 13 364601 ⟨677987, by decide⟩ ⟨13, 2, 0, 677987, 364601, 3425, 16384⟩
    (by decide) selected_cut_26810

theorem selected_cut_26811 : selected 8 ⟨678013, by decide⟩
    (prefixPartial 13 364602) = some ⟨13, 2, 0, 678013, 364602, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_364602_678013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364602 ⟨678013, by decide⟩ :=
  accepted_of_selected 13 364602 ⟨678013, by decide⟩ ⟨13, 2, 0, 678013, 364602, 1913, 16384⟩
    (by decide) selected_cut_26811

theorem selected_cut_26812 : selected 8 ⟨678031, by decide⟩
    (prefixPartial 13 364603) = some ⟨13, 2, 0, 678031, 364603, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_364603_678031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364603 ⟨678031, by decide⟩ :=
  accepted_of_selected 13 364603 ⟨678031, by decide⟩ ⟨13, 2, 0, 678031, 364603, 1205, 16384⟩
    (by decide) selected_cut_26812

theorem unmarked_context_12_91150_678032 : frontier 9 ⟨678032, by decide⟩
    (prefixCache 12 91150) (prefixPartial 12 91150) = false := by
  decide +kernel

theorem node_context_12_91150_678032 : EJMOriginalGlobalDAGData.nodes 9 ⟨678032, by decide⟩ =
    .split (coordinate 12) (![⟨677913, by decide⟩,⟨677987, by decide⟩,⟨678013, by decide⟩,⟨678031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91150_678032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91150 ⟨678032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91150
    ⟨678032, by decide⟩ (by decide) (![⟨677913, by decide⟩,⟨677987, by decide⟩,⟨678013, by decide⟩,⟨678031, by decide⟩]) unmarked_context_12_91150_678032 node_context_12_91150_678032
  intro a
  fin_cases a
  · exact context_13_364600_677913
  · exact context_13_364601_677987
  · exact context_13_364602_678013
  · exact context_13_364603_678031

theorem selected_cut_26813 : selected 8 ⟨678113, by decide⟩
    (prefixPartial 13 364604) = some ⟨13, 2, 0, 678113, 364604, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_364604_678113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364604 ⟨678113, by decide⟩ :=
  accepted_of_selected 13 364604 ⟨678113, by decide⟩ ⟨13, 2, 0, 678113, 364604, 3109, 16384⟩
    (by decide) selected_cut_26813

theorem selected_cut_26814 : selected 8 ⟨678194, by decide⟩
    (prefixPartial 13 364605) = some ⟨13, 2, 0, 678194, 364605, 3585, 16384⟩ := by
  decide +kernel

theorem context_13_364605_678194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364605 ⟨678194, by decide⟩ :=
  accepted_of_selected 13 364605 ⟨678194, by decide⟩ ⟨13, 2, 0, 678194, 364605, 3585, 16384⟩
    (by decide) selected_cut_26814

theorem selected_cut_26815 : selected 8 ⟨678225, by decide⟩
    (prefixPartial 13 364606) = some ⟨13, 2, 0, 678225, 364606, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_364606_678225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364606 ⟨678225, by decide⟩ :=
  accepted_of_selected 13 364606 ⟨678225, by decide⟩ ⟨13, 2, 0, 678225, 364606, 2221, 16384⟩
    (by decide) selected_cut_26815

theorem selected_cut_26816 : selected 8 ⟨678234, by decide⟩
    (prefixPartial 13 364607) = some ⟨13, 2, 0, 678234, 364607, 953, 16384⟩ := by
  decide +kernel

theorem context_13_364607_678234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364607 ⟨678234, by decide⟩ :=
  accepted_of_selected 13 364607 ⟨678234, by decide⟩ ⟨13, 2, 0, 678234, 364607, 953, 16384⟩
    (by decide) selected_cut_26816

theorem unmarked_context_12_91151_678235 : frontier 9 ⟨678235, by decide⟩
    (prefixCache 12 91151) (prefixPartial 12 91151) = false := by
  decide +kernel

theorem node_context_12_91151_678235 : EJMOriginalGlobalDAGData.nodes 9 ⟨678235, by decide⟩ =
    .split (coordinate 12) (![⟨678113, by decide⟩,⟨678194, by decide⟩,⟨678225, by decide⟩,⟨678234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91151_678235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91151 ⟨678235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91151
    ⟨678235, by decide⟩ (by decide) (![⟨678113, by decide⟩,⟨678194, by decide⟩,⟨678225, by decide⟩,⟨678234, by decide⟩]) unmarked_context_12_91151_678235 node_context_12_91151_678235
  intro a
  fin_cases a
  · exact context_13_364604_678113
  · exact context_13_364605_678194
  · exact context_13_364606_678225
  · exact context_13_364607_678234

theorem unmarked_context_11_22787_678236 : frontier 10 ⟨678236, by decide⟩
    (prefixCache 11 22787) (prefixPartial 11 22787) = false := by
  decide +kernel

theorem node_context_11_22787_678236 : EJMOriginalGlobalDAGData.nodes 10 ⟨678236, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨677846, by decide⟩,⟨678032, by decide⟩,⟨678235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22787_678236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22787 ⟨678236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22787
    ⟨678236, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨677846, by decide⟩,⟨678032, by decide⟩,⟨678235, by decide⟩]) unmarked_context_11_22787_678236 node_context_11_22787_678236
  intro a
  fin_cases a
  · exact context_12_91148_448748
  · exact context_12_91149_677846
  · exact context_12_91150_678032
  · exact context_12_91151_678235

theorem unmarked_context_10_5696_678237 : frontier 11 ⟨678237, by decide⟩
    (prefixCache 10 5696) (prefixPartial 10 5696) = false := by
  decide +kernel

theorem node_context_10_5696_678237 : EJMOriginalGlobalDAGData.nodes 11 ⟨678237, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨676999, by decide⟩,⟨677672, by decide⟩,⟨678236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5696_678237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5696 ⟨678237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5696
    ⟨678237, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨676999, by decide⟩,⟨677672, by decide⟩,⟨678236, by decide⟩]) unmarked_context_10_5696_678237 node_context_10_5696_678237
  intro a
  fin_cases a
  · exact context_11_22784_434745
  · exact context_11_22785_676999
  · exact context_11_22786_677672
  · exact context_11_22787_678236

theorem selected_cut_26817 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 91152) = some ⟨12, 1, 0, 307381, 91152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91152_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91152 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 91152 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 91152, 1, 65536⟩
    (by decide) selected_cut_26817

theorem selected_cut_26818 : selected 8 ⟨678277, by decide⟩
    (prefixPartial 13 364612) = some ⟨13, 2, 0, 678277, 364612, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_364612_678277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364612 ⟨678277, by decide⟩ :=
  accepted_of_selected 13 364612 ⟨678277, by decide⟩ ⟨13, 2, 0, 678277, 364612, 1697, 16384⟩
    (by decide) selected_cut_26818

theorem selected_cut_26819 : selected 8 ⟨678299, by decide⟩
    (prefixPartial 13 364613) = some ⟨13, 2, 0, 678299, 364613, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_364613_678299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364613 ⟨678299, by decide⟩ :=
  accepted_of_selected 13 364613 ⟨678299, by decide⟩ ⟨13, 2, 0, 678299, 364613, 1297, 16384⟩
    (by decide) selected_cut_26819

theorem selected_cut_26820 : selected 8 ⟨678317, by decide⟩
    (prefixPartial 13 364614) = some ⟨13, 2, 0, 678317, 364614, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_364614_678317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364614 ⟨678317, by decide⟩ :=
  accepted_of_selected 13 364614 ⟨678317, by decide⟩ ⟨13, 2, 0, 678317, 364614, 1317, 16384⟩
    (by decide) selected_cut_26820

theorem selected_cut_26821 : selected 8 ⟨678323, by decide⟩
    (prefixPartial 13 364615) = some ⟨13, 2, 0, 678323, 364615, 717, 16384⟩ := by
  decide +kernel

theorem context_13_364615_678323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364615 ⟨678323, by decide⟩ :=
  accepted_of_selected 13 364615 ⟨678323, by decide⟩ ⟨13, 2, 0, 678323, 364615, 717, 16384⟩
    (by decide) selected_cut_26821

theorem unmarked_context_12_91153_678324 : frontier 9 ⟨678324, by decide⟩
    (prefixCache 12 91153) (prefixPartial 12 91153) = false := by
  decide +kernel

theorem node_context_12_91153_678324 : EJMOriginalGlobalDAGData.nodes 9 ⟨678324, by decide⟩ =
    .split (coordinate 12) (![⟨678277, by decide⟩,⟨678299, by decide⟩,⟨678317, by decide⟩,⟨678323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91153_678324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91153 ⟨678324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91153
    ⟨678324, by decide⟩ (by decide) (![⟨678277, by decide⟩,⟨678299, by decide⟩,⟨678317, by decide⟩,⟨678323, by decide⟩]) unmarked_context_12_91153_678324 node_context_12_91153_678324
  intro a
  fin_cases a
  · exact context_13_364612_678277
  · exact context_13_364613_678299
  · exact context_13_364614_678317
  · exact context_13_364615_678323

theorem selected_cut_26822 : selected 8 ⟨678355, by decide⟩
    (prefixPartial 13 364616) = some ⟨13, 2, 0, 678355, 364616, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_364616_678355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364616 ⟨678355, by decide⟩ :=
  accepted_of_selected 13 364616 ⟨678355, by decide⟩ ⟨13, 2, 0, 678355, 364616, 1445, 16384⟩
    (by decide) selected_cut_26822

theorem selected_cut_26823 : selected 8 ⟨678375, by decide⟩
    (prefixPartial 13 364617) = some ⟨13, 2, 0, 678375, 364617, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_364617_678375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364617 ⟨678375, by decide⟩ :=
  accepted_of_selected 13 364617 ⟨678375, by decide⟩ ⟨13, 2, 0, 678375, 364617, 1349, 16384⟩
    (by decide) selected_cut_26823

theorem selected_cut_26824 : selected 8 ⟨678389, by decide⟩
    (prefixPartial 13 364618) = some ⟨13, 2, 0, 678389, 364618, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_364618_678389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364618 ⟨678389, by decide⟩ :=
  accepted_of_selected 13 364618 ⟨678389, by decide⟩ ⟨13, 2, 0, 678389, 364618, 1157, 16384⟩
    (by decide) selected_cut_26824

theorem selected_cut_26825 : selected 8 ⟨678395, by decide⟩
    (prefixPartial 13 364619) = some ⟨13, 2, 0, 678395, 364619, 841, 16384⟩ := by
  decide +kernel

theorem context_13_364619_678395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364619 ⟨678395, by decide⟩ :=
  accepted_of_selected 13 364619 ⟨678395, by decide⟩ ⟨13, 2, 0, 678395, 364619, 841, 16384⟩
    (by decide) selected_cut_26825

theorem unmarked_context_12_91154_678396 : frontier 9 ⟨678396, by decide⟩
    (prefixCache 12 91154) (prefixPartial 12 91154) = false := by
  decide +kernel

theorem node_context_12_91154_678396 : EJMOriginalGlobalDAGData.nodes 9 ⟨678396, by decide⟩ =
    .split (coordinate 12) (![⟨678355, by decide⟩,⟨678375, by decide⟩,⟨678389, by decide⟩,⟨678395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91154_678396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91154 ⟨678396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91154
    ⟨678396, by decide⟩ (by decide) (![⟨678355, by decide⟩,⟨678375, by decide⟩,⟨678389, by decide⟩,⟨678395, by decide⟩]) unmarked_context_12_91154_678396 node_context_12_91154_678396
  intro a
  fin_cases a
  · exact context_13_364616_678355
  · exact context_13_364617_678375
  · exact context_13_364618_678389
  · exact context_13_364619_678395

theorem selected_cut_26826 : selected 8 ⟨678431, by decide⟩
    (prefixPartial 13 364620) = some ⟨13, 2, 0, 678431, 364620, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_364620_678431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364620 ⟨678431, by decide⟩ :=
  accepted_of_selected 13 364620 ⟨678431, by decide⟩ ⟨13, 2, 0, 678431, 364620, 1521, 16384⟩
    (by decide) selected_cut_26826

theorem selected_cut_26827 : selected 8 ⟨678455, by decide⟩
    (prefixPartial 13 364621) = some ⟨13, 2, 0, 678455, 364621, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_364621_678455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364621 ⟨678455, by decide⟩ :=
  accepted_of_selected 13 364621 ⟨678455, by decide⟩ ⟨13, 2, 0, 678455, 364621, 1589, 16384⟩
    (by decide) selected_cut_26827

theorem selected_cut_26828 : selected 8 ⟨678478, by decide⟩
    (prefixPartial 13 364622) = some ⟨13, 2, 0, 678478, 364622, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_364622_678478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364622 ⟨678478, by decide⟩ :=
  accepted_of_selected 13 364622 ⟨678478, by decide⟩ ⟨13, 2, 0, 678478, 364622, 1457, 16384⟩
    (by decide) selected_cut_26828

theorem selected_cut_26829 : selected 8 ⟨678483, by decide⟩
    (prefixPartial 13 364623) = some ⟨13, 2, 0, 678483, 364623, 669, 16384⟩ := by
  decide +kernel

theorem context_13_364623_678483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364623 ⟨678483, by decide⟩ :=
  accepted_of_selected 13 364623 ⟨678483, by decide⟩ ⟨13, 2, 0, 678483, 364623, 669, 16384⟩
    (by decide) selected_cut_26829

theorem unmarked_context_12_91155_678484 : frontier 9 ⟨678484, by decide⟩
    (prefixCache 12 91155) (prefixPartial 12 91155) = false := by
  decide +kernel

theorem node_context_12_91155_678484 : EJMOriginalGlobalDAGData.nodes 9 ⟨678484, by decide⟩ =
    .split (coordinate 12) (![⟨678431, by decide⟩,⟨678455, by decide⟩,⟨678478, by decide⟩,⟨678483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91155_678484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91155 ⟨678484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91155
    ⟨678484, by decide⟩ (by decide) (![⟨678431, by decide⟩,⟨678455, by decide⟩,⟨678478, by decide⟩,⟨678483, by decide⟩]) unmarked_context_12_91155_678484 node_context_12_91155_678484
  intro a
  fin_cases a
  · exact context_13_364620_678431
  · exact context_13_364621_678455
  · exact context_13_364622_678478
  · exact context_13_364623_678483

theorem unmarked_context_11_22788_678485 : frontier 10 ⟨678485, by decide⟩
    (prefixCache 11 22788) (prefixPartial 11 22788) = false := by
  decide +kernel

theorem node_context_11_22788_678485 : EJMOriginalGlobalDAGData.nodes 10 ⟨678485, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨678324, by decide⟩,⟨678396, by decide⟩,⟨678484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22788_678485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22788 ⟨678485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22788
    ⟨678485, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨678324, by decide⟩,⟨678396, by decide⟩,⟨678484, by decide⟩]) unmarked_context_11_22788_678485 node_context_11_22788_678485
  intro a
  fin_cases a
  · exact context_12_91152_307381
  · exact context_12_91153_678324
  · exact context_12_91154_678396
  · exact context_12_91155_678484

theorem selected_cut_26830 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 91156) = some ⟨12, 1, 0, 308705, 91156, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91156_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91156 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 91156 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 91156, 1, 65536⟩
    (by decide) selected_cut_26830

theorem selected_cut_26831 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 91157) = some ⟨12, 1, 0, 308705, 91157, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91157_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91157 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 91157 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 91157, 1, 65536⟩
    (by decide) selected_cut_26831

theorem selected_cut_26832 : selected 8 ⟨678560, by decide⟩
    (prefixPartial 13 364632) = some ⟨13, 2, 0, 678560, 364632, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_364632_678560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364632 ⟨678560, by decide⟩ :=
  accepted_of_selected 13 364632 ⟨678560, by decide⟩ ⟨13, 2, 0, 678560, 364632, 2357, 16384⟩
    (by decide) selected_cut_26832

theorem selected_cut_26833 : selected 8 ⟨678666, by decide⟩
    (prefixPartial 13 364633) = some ⟨13, 2, 0, 678666, 364633, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_364633_678666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364633 ⟨678666, by decide⟩ :=
  accepted_of_selected 13 364633 ⟨678666, by decide⟩ ⟨13, 2, 0, 678666, 364633, 2621, 16384⟩
    (by decide) selected_cut_26833

theorem selected_cut_26834 : selected 8 ⟨678726, by decide⟩
    (prefixPartial 13 364634) = some ⟨13, 2, 0, 678726, 364634, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_364634_678726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364634 ⟨678726, by decide⟩ :=
  accepted_of_selected 13 364634 ⟨678726, by decide⟩ ⟨13, 2, 0, 678726, 364634, 1681, 16384⟩
    (by decide) selected_cut_26834

theorem selected_cut_26835 : selected 8 ⟨678752, by decide⟩
    (prefixPartial 13 364635) = some ⟨13, 2, 0, 678752, 364635, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_364635_678752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364635 ⟨678752, by decide⟩ :=
  accepted_of_selected 13 364635 ⟨678752, by decide⟩ ⟨13, 2, 0, 678752, 364635, 1069, 16384⟩
    (by decide) selected_cut_26835

theorem unmarked_context_12_91158_678753 : frontier 9 ⟨678753, by decide⟩
    (prefixCache 12 91158) (prefixPartial 12 91158) = false := by
  decide +kernel

theorem node_context_12_91158_678753 : EJMOriginalGlobalDAGData.nodes 9 ⟨678753, by decide⟩ =
    .split (coordinate 12) (![⟨678560, by decide⟩,⟨678666, by decide⟩,⟨678726, by decide⟩,⟨678752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91158_678753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91158 ⟨678753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91158
    ⟨678753, by decide⟩ (by decide) (![⟨678560, by decide⟩,⟨678666, by decide⟩,⟨678726, by decide⟩,⟨678752, by decide⟩]) unmarked_context_12_91158_678753 node_context_12_91158_678753
  intro a
  fin_cases a
  · exact context_13_364632_678560
  · exact context_13_364633_678666
  · exact context_13_364634_678726
  · exact context_13_364635_678752

theorem selected_cut_26836 : selected 8 ⟨678836, by decide⟩
    (prefixPartial 13 364636) = some ⟨13, 2, 0, 678836, 364636, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_364636_678836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364636 ⟨678836, by decide⟩ :=
  accepted_of_selected 13 364636 ⟨678836, by decide⟩ ⟨13, 2, 0, 678836, 364636, 2565, 16384⟩
    (by decide) selected_cut_26836

theorem selected_cut_26837 : selected 8 ⟨678959, by decide⟩
    (prefixPartial 13 364637) = some ⟨13, 2, 0, 678959, 364637, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_364637_678959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364637 ⟨678959, by decide⟩ :=
  accepted_of_selected 13 364637 ⟨678959, by decide⟩ ⟨13, 2, 0, 678959, 364637, 2969, 16384⟩
    (by decide) selected_cut_26837

theorem selected_cut_26838 : selected 8 ⟨679035, by decide⟩
    (prefixPartial 13 364638) = some ⟨13, 2, 0, 679035, 364638, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_364638_679035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364638 ⟨679035, by decide⟩ :=
  accepted_of_selected 13 364638 ⟨679035, by decide⟩ ⟨13, 2, 0, 679035, 364638, 2133, 16384⟩
    (by decide) selected_cut_26838

theorem selected_cut_26839 : selected 8 ⟨679056, by decide⟩
    (prefixPartial 13 364639) = some ⟨13, 2, 0, 679056, 364639, 985, 16384⟩ := by
  decide +kernel

theorem context_13_364639_679056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364639 ⟨679056, by decide⟩ :=
  accepted_of_selected 13 364639 ⟨679056, by decide⟩ ⟨13, 2, 0, 679056, 364639, 985, 16384⟩
    (by decide) selected_cut_26839

theorem unmarked_context_12_91159_679057 : frontier 9 ⟨679057, by decide⟩
    (prefixCache 12 91159) (prefixPartial 12 91159) = false := by
  decide +kernel

theorem node_context_12_91159_679057 : EJMOriginalGlobalDAGData.nodes 9 ⟨679057, by decide⟩ =
    .split (coordinate 12) (![⟨678836, by decide⟩,⟨678959, by decide⟩,⟨679035, by decide⟩,⟨679056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91159_679057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91159 ⟨679057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91159
    ⟨679057, by decide⟩ (by decide) (![⟨678836, by decide⟩,⟨678959, by decide⟩,⟨679035, by decide⟩,⟨679056, by decide⟩]) unmarked_context_12_91159_679057 node_context_12_91159_679057
  intro a
  fin_cases a
  · exact context_13_364636_678836
  · exact context_13_364637_678959
  · exact context_13_364638_679035
  · exact context_13_364639_679056

theorem unmarked_context_11_22789_679058 : frontier 10 ⟨679058, by decide⟩
    (prefixCache 11 22789) (prefixPartial 11 22789) = false := by
  decide +kernel

theorem node_context_11_22789_679058 : EJMOriginalGlobalDAGData.nodes 10 ⟨679058, by decide⟩ =
    .split (coordinate 11) (![⟨308705, by decide⟩,⟨308705, by decide⟩,⟨678753, by decide⟩,⟨679057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22789_679058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22789 ⟨679058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22789
    ⟨679058, by decide⟩ (by decide) (![⟨308705, by decide⟩,⟨308705, by decide⟩,⟨678753, by decide⟩,⟨679057, by decide⟩]) unmarked_context_11_22789_679058 node_context_11_22789_679058
  intro a
  fin_cases a
  · exact context_12_91156_308705
  · exact context_12_91157_308705
  · exact context_12_91158_678753
  · exact context_12_91159_679057

theorem selected_cut_26840 : selected 8 ⟨679080, by decide⟩
    (prefixPartial 13 364640) = some ⟨13, 2, 0, 679080, 364640, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_364640_679080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364640 ⟨679080, by decide⟩ :=
  accepted_of_selected 13 364640 ⟨679080, by decide⟩ ⟨13, 2, 0, 679080, 364640, 1109, 16384⟩
    (by decide) selected_cut_26840

theorem selected_cut_26841 : selected 8 ⟨679114, by decide⟩
    (prefixPartial 13 364641) = some ⟨13, 2, 0, 679114, 364641, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_364641_679114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364641 ⟨679114, by decide⟩ :=
  accepted_of_selected 13 364641 ⟨679114, by decide⟩ ⟨13, 2, 0, 679114, 364641, 1641, 16384⟩
    (by decide) selected_cut_26841

theorem selected_cut_26842 : selected 8 ⟨679129, by decide⟩
    (prefixPartial 13 364642) = some ⟨13, 2, 0, 679129, 364642, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_364642_679129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364642 ⟨679129, by decide⟩ :=
  accepted_of_selected 13 364642 ⟨679129, by decide⟩ ⟨13, 2, 0, 679129, 364642, 1269, 16384⟩
    (by decide) selected_cut_26842

theorem selected_cut_26843 : selected 8 ⟨679135, by decide⟩
    (prefixPartial 13 364643) = some ⟨13, 2, 0, 679135, 364643, 801, 16384⟩ := by
  decide +kernel

theorem context_13_364643_679135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364643 ⟨679135, by decide⟩ :=
  accepted_of_selected 13 364643 ⟨679135, by decide⟩ ⟨13, 2, 0, 679135, 364643, 801, 16384⟩
    (by decide) selected_cut_26843

theorem unmarked_context_12_91160_679136 : frontier 9 ⟨679136, by decide⟩
    (prefixCache 12 91160) (prefixPartial 12 91160) = false := by
  decide +kernel

theorem node_context_12_91160_679136 : EJMOriginalGlobalDAGData.nodes 9 ⟨679136, by decide⟩ =
    .split (coordinate 12) (![⟨679080, by decide⟩,⟨679114, by decide⟩,⟨679129, by decide⟩,⟨679135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91160_679136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91160 ⟨679136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91160
    ⟨679136, by decide⟩ (by decide) (![⟨679080, by decide⟩,⟨679114, by decide⟩,⟨679129, by decide⟩,⟨679135, by decide⟩]) unmarked_context_12_91160_679136 node_context_12_91160_679136
  intro a
  fin_cases a
  · exact context_13_364640_679080
  · exact context_13_364641_679114
  · exact context_13_364642_679129
  · exact context_13_364643_679135

theorem selected_cut_26844 : selected 8 ⟨679174, by decide⟩
    (prefixPartial 13 364644) = some ⟨13, 2, 0, 679174, 364644, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_364644_679174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364644 ⟨679174, by decide⟩ :=
  accepted_of_selected 13 364644 ⟨679174, by decide⟩ ⟨13, 2, 0, 679174, 364644, 1825, 16384⟩
    (by decide) selected_cut_26844

theorem selected_cut_26845 : selected 8 ⟨679212, by decide⟩
    (prefixPartial 13 364645) = some ⟨13, 2, 0, 679212, 364645, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_364645_679212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364645 ⟨679212, by decide⟩ :=
  accepted_of_selected 13 364645 ⟨679212, by decide⟩ ⟨13, 2, 0, 679212, 364645, 1789, 16384⟩
    (by decide) selected_cut_26845

theorem selected_cut_26846 : selected 8 ⟨679239, by decide⟩
    (prefixPartial 13 364646) = some ⟨13, 2, 0, 679239, 364646, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_364646_679239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364646 ⟨679239, by decide⟩ :=
  accepted_of_selected 13 364646 ⟨679239, by decide⟩ ⟨13, 2, 0, 679239, 364646, 1661, 16384⟩
    (by decide) selected_cut_26846

theorem selected_cut_26847 : selected 8 ⟨679246, by decide⟩
    (prefixPartial 13 364647) = some ⟨13, 2, 0, 679246, 364647, 845, 16384⟩ := by
  decide +kernel

theorem context_13_364647_679246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364647 ⟨679246, by decide⟩ :=
  accepted_of_selected 13 364647 ⟨679246, by decide⟩ ⟨13, 2, 0, 679246, 364647, 845, 16384⟩
    (by decide) selected_cut_26847

theorem unmarked_context_12_91161_679247 : frontier 9 ⟨679247, by decide⟩
    (prefixCache 12 91161) (prefixPartial 12 91161) = false := by
  decide +kernel

theorem node_context_12_91161_679247 : EJMOriginalGlobalDAGData.nodes 9 ⟨679247, by decide⟩ =
    .split (coordinate 12) (![⟨679174, by decide⟩,⟨679212, by decide⟩,⟨679239, by decide⟩,⟨679246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91161_679247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91161 ⟨679247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91161
    ⟨679247, by decide⟩ (by decide) (![⟨679174, by decide⟩,⟨679212, by decide⟩,⟨679239, by decide⟩,⟨679246, by decide⟩]) unmarked_context_12_91161_679247 node_context_12_91161_679247
  intro a
  fin_cases a
  · exact context_13_364644_679174
  · exact context_13_364645_679212
  · exact context_13_364646_679239
  · exact context_13_364647_679246

theorem selected_cut_26848 : selected 8 ⟨679271, by decide⟩
    (prefixPartial 13 364648) = some ⟨13, 2, 0, 679271, 364648, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_364648_679271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364648 ⟨679271, by decide⟩ :=
  accepted_of_selected 13 364648 ⟨679271, by decide⟩ ⟨13, 2, 0, 679271, 364648, 1353, 16384⟩
    (by decide) selected_cut_26848

theorem selected_cut_26849 : selected 8 ⟨679299, by decide⟩
    (prefixPartial 13 364649) = some ⟨13, 2, 0, 679299, 364649, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_364649_679299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364649 ⟨679299, by decide⟩ :=
  accepted_of_selected 13 364649 ⟨679299, by decide⟩ ⟨13, 2, 0, 679299, 364649, 1561, 16384⟩
    (by decide) selected_cut_26849

theorem selected_cut_26850 : selected 8 ⟨679315, by decide⟩
    (prefixPartial 13 364650) = some ⟨13, 2, 0, 679315, 364650, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_364650_679315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364650 ⟨679315, by decide⟩ :=
  accepted_of_selected 13 364650 ⟨679315, by decide⟩ ⟨13, 2, 0, 679315, 364650, 1233, 16384⟩
    (by decide) selected_cut_26850

theorem selected_cut_26851 : selected 8 ⟨679322, by decide⟩
    (prefixPartial 13 364651) = some ⟨13, 2, 0, 679322, 364651, 913, 16384⟩ := by
  decide +kernel

theorem context_13_364651_679322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364651 ⟨679322, by decide⟩ :=
  accepted_of_selected 13 364651 ⟨679322, by decide⟩ ⟨13, 2, 0, 679322, 364651, 913, 16384⟩
    (by decide) selected_cut_26851

theorem unmarked_context_12_91162_679323 : frontier 9 ⟨679323, by decide⟩
    (prefixCache 12 91162) (prefixPartial 12 91162) = false := by
  decide +kernel

theorem node_context_12_91162_679323 : EJMOriginalGlobalDAGData.nodes 9 ⟨679323, by decide⟩ =
    .split (coordinate 12) (![⟨679271, by decide⟩,⟨679299, by decide⟩,⟨679315, by decide⟩,⟨679322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91162_679323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91162 ⟨679323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91162
    ⟨679323, by decide⟩ (by decide) (![⟨679271, by decide⟩,⟨679299, by decide⟩,⟨679315, by decide⟩,⟨679322, by decide⟩]) unmarked_context_12_91162_679323 node_context_12_91162_679323
  intro a
  fin_cases a
  · exact context_13_364648_679271
  · exact context_13_364649_679299
  · exact context_13_364650_679315
  · exact context_13_364651_679322

theorem selected_cut_26852 : selected 8 ⟨679348, by decide⟩
    (prefixPartial 13 364652) = some ⟨13, 2, 0, 679348, 364652, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_364652_679348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364652 ⟨679348, by decide⟩ :=
  accepted_of_selected 13 364652 ⟨679348, by decide⟩ ⟨13, 2, 0, 679348, 364652, 1565, 16384⟩
    (by decide) selected_cut_26852

theorem selected_cut_26853 : selected 8 ⟨679388, by decide⟩
    (prefixPartial 13 364653) = some ⟨13, 2, 0, 679388, 364653, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_364653_679388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364653 ⟨679388, by decide⟩ :=
  accepted_of_selected 13 364653 ⟨679388, by decide⟩ ⟨13, 2, 0, 679388, 364653, 2093, 16384⟩
    (by decide) selected_cut_26853

theorem selected_cut_26854 : selected 8 ⟨679410, by decide⟩
    (prefixPartial 13 364654) = some ⟨13, 2, 0, 679410, 364654, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_364654_679410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364654 ⟨679410, by decide⟩ :=
  accepted_of_selected 13 364654 ⟨679410, by decide⟩ ⟨13, 2, 0, 679410, 364654, 1681, 16384⟩
    (by decide) selected_cut_26854

theorem selected_cut_26855 : selected 8 ⟨679416, by decide⟩
    (prefixPartial 13 364655) = some ⟨13, 2, 0, 679416, 364655, 777, 16384⟩ := by
  decide +kernel

theorem context_13_364655_679416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364655 ⟨679416, by decide⟩ :=
  accepted_of_selected 13 364655 ⟨679416, by decide⟩ ⟨13, 2, 0, 679416, 364655, 777, 16384⟩
    (by decide) selected_cut_26855

theorem unmarked_context_12_91163_679417 : frontier 9 ⟨679417, by decide⟩
    (prefixCache 12 91163) (prefixPartial 12 91163) = false := by
  decide +kernel

theorem node_context_12_91163_679417 : EJMOriginalGlobalDAGData.nodes 9 ⟨679417, by decide⟩ =
    .split (coordinate 12) (![⟨679348, by decide⟩,⟨679388, by decide⟩,⟨679410, by decide⟩,⟨679416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91163_679417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91163 ⟨679417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91163
    ⟨679417, by decide⟩ (by decide) (![⟨679348, by decide⟩,⟨679388, by decide⟩,⟨679410, by decide⟩,⟨679416, by decide⟩]) unmarked_context_12_91163_679417 node_context_12_91163_679417
  intro a
  fin_cases a
  · exact context_13_364652_679348
  · exact context_13_364653_679388
  · exact context_13_364654_679410
  · exact context_13_364655_679416

theorem unmarked_context_11_22790_679418 : frontier 10 ⟨679418, by decide⟩
    (prefixCache 11 22790) (prefixPartial 11 22790) = false := by
  decide +kernel

theorem node_context_11_22790_679418 : EJMOriginalGlobalDAGData.nodes 10 ⟨679418, by decide⟩ =
    .split (coordinate 11) (![⟨679136, by decide⟩,⟨679247, by decide⟩,⟨679323, by decide⟩,⟨679417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22790_679418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22790 ⟨679418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22790
    ⟨679418, by decide⟩ (by decide) (![⟨679136, by decide⟩,⟨679247, by decide⟩,⟨679323, by decide⟩,⟨679417, by decide⟩]) unmarked_context_11_22790_679418 node_context_11_22790_679418
  intro a
  fin_cases a
  · exact context_12_91160_679136
  · exact context_12_91161_679247
  · exact context_12_91162_679323
  · exact context_12_91163_679417

theorem selected_cut_26856 : selected 8 ⟨679438, by decide⟩
    (prefixPartial 13 364656) = some ⟨13, 2, 0, 679438, 364656, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_364656_679438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364656 ⟨679438, by decide⟩ :=
  accepted_of_selected 13 364656 ⟨679438, by decide⟩ ⟨13, 2, 0, 679438, 364656, 1009, 16384⟩
    (by decide) selected_cut_26856

theorem selected_cut_26857 : selected 8 ⟨679466, by decide⟩
    (prefixPartial 13 364657) = some ⟨13, 2, 0, 679466, 364657, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_364657_679466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364657 ⟨679466, by decide⟩ :=
  accepted_of_selected 13 364657 ⟨679466, by decide⟩ ⟨13, 2, 0, 679466, 364657, 1545, 16384⟩
    (by decide) selected_cut_26857

theorem selected_cut_26858 : selected 8 ⟨679483, by decide⟩
    (prefixPartial 13 364658) = some ⟨13, 2, 0, 679483, 364658, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_364658_679483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364658 ⟨679483, by decide⟩ :=
  accepted_of_selected 13 364658 ⟨679483, by decide⟩ ⟨13, 2, 0, 679483, 364658, 1077, 16384⟩
    (by decide) selected_cut_26858

theorem selected_cut_26859 : selected 8 ⟨679491, by decide⟩
    (prefixPartial 13 364659) = some ⟨13, 2, 0, 679491, 364659, 673, 16384⟩ := by
  decide +kernel

theorem context_13_364659_679491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364659 ⟨679491, by decide⟩ :=
  accepted_of_selected 13 364659 ⟨679491, by decide⟩ ⟨13, 2, 0, 679491, 364659, 673, 16384⟩
    (by decide) selected_cut_26859

theorem unmarked_context_12_91164_679492 : frontier 9 ⟨679492, by decide⟩
    (prefixCache 12 91164) (prefixPartial 12 91164) = false := by
  decide +kernel

theorem node_context_12_91164_679492 : EJMOriginalGlobalDAGData.nodes 9 ⟨679492, by decide⟩ =
    .split (coordinate 12) (![⟨679438, by decide⟩,⟨679466, by decide⟩,⟨679483, by decide⟩,⟨679491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91164_679492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91164 ⟨679492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91164
    ⟨679492, by decide⟩ (by decide) (![⟨679438, by decide⟩,⟨679466, by decide⟩,⟨679483, by decide⟩,⟨679491, by decide⟩]) unmarked_context_12_91164_679492 node_context_12_91164_679492
  intro a
  fin_cases a
  · exact context_13_364656_679438
  · exact context_13_364657_679466
  · exact context_13_364658_679483
  · exact context_13_364659_679491

theorem selected_cut_26860 : selected 8 ⟨679518, by decide⟩
    (prefixPartial 13 364660) = some ⟨13, 2, 0, 679518, 364660, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_364660_679518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364660 ⟨679518, by decide⟩ :=
  accepted_of_selected 13 364660 ⟨679518, by decide⟩ ⟨13, 2, 0, 679518, 364660, 1469, 16384⟩
    (by decide) selected_cut_26860

theorem selected_cut_26861 : selected 8 ⟨679554, by decide⟩
    (prefixPartial 13 364661) = some ⟨13, 2, 0, 679554, 364661, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_364661_679554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364661 ⟨679554, by decide⟩ :=
  accepted_of_selected 13 364661 ⟨679554, by decide⟩ ⟨13, 2, 0, 679554, 364661, 1869, 16384⟩
    (by decide) selected_cut_26861

theorem selected_cut_26862 : selected 8 ⟨679573, by decide⟩
    (prefixPartial 13 364662) = some ⟨13, 2, 0, 679573, 364662, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_364662_679573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364662 ⟨679573, by decide⟩ :=
  accepted_of_selected 13 364662 ⟨679573, by decide⟩ ⟨13, 2, 0, 679573, 364662, 1437, 16384⟩
    (by decide) selected_cut_26862

theorem selected_cut_26863 : selected 8 ⟨679578, by decide⟩
    (prefixPartial 13 364663) = some ⟨13, 2, 0, 679578, 364663, 697, 16384⟩ := by
  decide +kernel

theorem context_13_364663_679578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364663 ⟨679578, by decide⟩ :=
  accepted_of_selected 13 364663 ⟨679578, by decide⟩ ⟨13, 2, 0, 679578, 364663, 697, 16384⟩
    (by decide) selected_cut_26863

theorem unmarked_context_12_91165_679579 : frontier 9 ⟨679579, by decide⟩
    (prefixCache 12 91165) (prefixPartial 12 91165) = false := by
  decide +kernel

theorem node_context_12_91165_679579 : EJMOriginalGlobalDAGData.nodes 9 ⟨679579, by decide⟩ =
    .split (coordinate 12) (![⟨679518, by decide⟩,⟨679554, by decide⟩,⟨679573, by decide⟩,⟨679578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91165_679579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91165 ⟨679579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91165
    ⟨679579, by decide⟩ (by decide) (![⟨679518, by decide⟩,⟨679554, by decide⟩,⟨679573, by decide⟩,⟨679578, by decide⟩]) unmarked_context_12_91165_679579 node_context_12_91165_679579
  intro a
  fin_cases a
  · exact context_13_364660_679518
  · exact context_13_364661_679554
  · exact context_13_364662_679573
  · exact context_13_364663_679578

theorem selected_cut_26864 : selected 8 ⟨679597, by decide⟩
    (prefixPartial 13 364664) = some ⟨13, 2, 0, 679597, 364664, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_364664_679597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364664 ⟨679597, by decide⟩ :=
  accepted_of_selected 13 364664 ⟨679597, by decide⟩ ⟨13, 2, 0, 679597, 364664, 1249, 16384⟩
    (by decide) selected_cut_26864

theorem selected_cut_26865 : selected 8 ⟨679620, by decide⟩
    (prefixPartial 13 364665) = some ⟨13, 2, 0, 679620, 364665, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_364665_679620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364665 ⟨679620, by decide⟩ :=
  accepted_of_selected 13 364665 ⟨679620, by decide⟩ ⟨13, 2, 0, 679620, 364665, 1761, 16384⟩
    (by decide) selected_cut_26865

theorem selected_cut_26866 : selected 8 ⟨679636, by decide⟩
    (prefixPartial 13 364666) = some ⟨13, 2, 0, 679636, 364666, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_364666_679636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364666 ⟨679636, by decide⟩ :=
  accepted_of_selected 13 364666 ⟨679636, by decide⟩ ⟨13, 2, 0, 679636, 364666, 1221, 16384⟩
    (by decide) selected_cut_26866

theorem selected_cut_26867 : selected 8 ⟨679641, by decide⟩
    (prefixPartial 13 364667) = some ⟨13, 2, 0, 679641, 364667, 881, 16384⟩ := by
  decide +kernel

theorem context_13_364667_679641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364667 ⟨679641, by decide⟩ :=
  accepted_of_selected 13 364667 ⟨679641, by decide⟩ ⟨13, 2, 0, 679641, 364667, 881, 16384⟩
    (by decide) selected_cut_26867

theorem unmarked_context_12_91166_679642 : frontier 9 ⟨679642, by decide⟩
    (prefixCache 12 91166) (prefixPartial 12 91166) = false := by
  decide +kernel

theorem node_context_12_91166_679642 : EJMOriginalGlobalDAGData.nodes 9 ⟨679642, by decide⟩ =
    .split (coordinate 12) (![⟨679597, by decide⟩,⟨679620, by decide⟩,⟨679636, by decide⟩,⟨679641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91166_679642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91166 ⟨679642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91166
    ⟨679642, by decide⟩ (by decide) (![⟨679597, by decide⟩,⟨679620, by decide⟩,⟨679636, by decide⟩,⟨679641, by decide⟩]) unmarked_context_12_91166_679642 node_context_12_91166_679642
  intro a
  fin_cases a
  · exact context_13_364664_679597
  · exact context_13_364665_679620
  · exact context_13_364666_679636
  · exact context_13_364667_679641

theorem selected_cut_26868 : selected 8 ⟨679663, by decide⟩
    (prefixPartial 13 364668) = some ⟨13, 2, 0, 679663, 364668, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_364668_679663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364668 ⟨679663, by decide⟩ :=
  accepted_of_selected 13 364668 ⟨679663, by decide⟩ ⟨13, 2, 0, 679663, 364668, 1197, 16384⟩
    (by decide) selected_cut_26868

theorem selected_cut_26869 : selected 8 ⟨679696, by decide⟩
    (prefixPartial 13 364669) = some ⟨13, 2, 0, 679696, 364669, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_364669_679696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364669 ⟨679696, by decide⟩ :=
  accepted_of_selected 13 364669 ⟨679696, by decide⟩ ⟨13, 2, 0, 679696, 364669, 1917, 16384⟩
    (by decide) selected_cut_26869

theorem selected_cut_26870 : selected 8 ⟨679719, by decide⟩
    (prefixPartial 13 364670) = some ⟨13, 2, 0, 679719, 364670, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_364670_679719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364670 ⟨679719, by decide⟩ :=
  accepted_of_selected 13 364670 ⟨679719, by decide⟩ ⟨13, 2, 0, 679719, 364670, 1413, 16384⟩
    (by decide) selected_cut_26870

theorem selected_cut_26871 : selected 8 ⟨679727, by decide⟩
    (prefixPartial 13 364671) = some ⟨13, 2, 0, 679727, 364671, 705, 16384⟩ := by
  decide +kernel

theorem context_13_364671_679727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364671 ⟨679727, by decide⟩ :=
  accepted_of_selected 13 364671 ⟨679727, by decide⟩ ⟨13, 2, 0, 679727, 364671, 705, 16384⟩
    (by decide) selected_cut_26871

theorem unmarked_context_12_91167_679728 : frontier 9 ⟨679728, by decide⟩
    (prefixCache 12 91167) (prefixPartial 12 91167) = false := by
  decide +kernel

theorem node_context_12_91167_679728 : EJMOriginalGlobalDAGData.nodes 9 ⟨679728, by decide⟩ =
    .split (coordinate 12) (![⟨679663, by decide⟩,⟨679696, by decide⟩,⟨679719, by decide⟩,⟨679727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91167_679728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91167 ⟨679728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91167
    ⟨679728, by decide⟩ (by decide) (![⟨679663, by decide⟩,⟨679696, by decide⟩,⟨679719, by decide⟩,⟨679727, by decide⟩]) unmarked_context_12_91167_679728 node_context_12_91167_679728
  intro a
  fin_cases a
  · exact context_13_364668_679663
  · exact context_13_364669_679696
  · exact context_13_364670_679719
  · exact context_13_364671_679727

theorem unmarked_context_11_22791_679729 : frontier 10 ⟨679729, by decide⟩
    (prefixCache 11 22791) (prefixPartial 11 22791) = false := by
  decide +kernel

theorem node_context_11_22791_679729 : EJMOriginalGlobalDAGData.nodes 10 ⟨679729, by decide⟩ =
    .split (coordinate 11) (![⟨679492, by decide⟩,⟨679579, by decide⟩,⟨679642, by decide⟩,⟨679728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22791_679729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22791 ⟨679729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22791
    ⟨679729, by decide⟩ (by decide) (![⟨679492, by decide⟩,⟨679579, by decide⟩,⟨679642, by decide⟩,⟨679728, by decide⟩]) unmarked_context_11_22791_679729 node_context_11_22791_679729
  intro a
  fin_cases a
  · exact context_12_91164_679492
  · exact context_12_91165_679579
  · exact context_12_91166_679642
  · exact context_12_91167_679728

theorem unmarked_context_10_5697_679730 : frontier 11 ⟨679730, by decide⟩
    (prefixCache 10 5697) (prefixPartial 10 5697) = false := by
  decide +kernel

theorem node_context_10_5697_679730 : EJMOriginalGlobalDAGData.nodes 11 ⟨679730, by decide⟩ =
    .split (coordinate 10) (![⟨678485, by decide⟩,⟨679058, by decide⟩,⟨679418, by decide⟩,⟨679729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5697_679730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5697 ⟨679730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5697
    ⟨679730, by decide⟩ (by decide) (![⟨678485, by decide⟩,⟨679058, by decide⟩,⟨679418, by decide⟩,⟨679729, by decide⟩]) unmarked_context_10_5697_679730 node_context_10_5697_679730
  intro a
  fin_cases a
  · exact context_11_22788_678485
  · exact context_11_22789_679058
  · exact context_11_22790_679418
  · exact context_11_22791_679729

theorem selected_cut_26872 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 91168) = some ⟨12, 1, 0, 641337, 91168, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91168_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91168 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 91168 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 91168, 1, 65536⟩
    (by decide) selected_cut_26872

theorem selected_cut_26873 : selected 8 ⟨679756, by decide⟩
    (prefixPartial 13 364676) = some ⟨13, 2, 0, 679756, 364676, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_364676_679756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364676 ⟨679756, by decide⟩ :=
  accepted_of_selected 13 364676 ⟨679756, by decide⟩ ⟨13, 2, 0, 679756, 364676, 1205, 16384⟩
    (by decide) selected_cut_26873

theorem selected_cut_26874 : selected 8 ⟨679793, by decide⟩
    (prefixPartial 13 364677) = some ⟨13, 2, 0, 679793, 364677, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_364677_679793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364677 ⟨679793, by decide⟩ :=
  accepted_of_selected 13 364677 ⟨679793, by decide⟩ ⟨13, 2, 0, 679793, 364677, 1565, 16384⟩
    (by decide) selected_cut_26874

theorem selected_cut_26875 : selected 8 ⟨679809, by decide⟩
    (prefixPartial 13 364678) = some ⟨13, 2, 0, 679809, 364678, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_364678_679809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364678 ⟨679809, by decide⟩ :=
  accepted_of_selected 13 364678 ⟨679809, by decide⟩ ⟨13, 2, 0, 679809, 364678, 1261, 16384⟩
    (by decide) selected_cut_26875

theorem selected_cut_26876 : selected 8 ⟨679816, by decide⟩
    (prefixPartial 13 364679) = some ⟨13, 2, 0, 679816, 364679, 773, 16384⟩ := by
  decide +kernel

theorem context_13_364679_679816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364679 ⟨679816, by decide⟩ :=
  accepted_of_selected 13 364679 ⟨679816, by decide⟩ ⟨13, 2, 0, 679816, 364679, 773, 16384⟩
    (by decide) selected_cut_26876

theorem unmarked_context_12_91169_679817 : frontier 9 ⟨679817, by decide⟩
    (prefixCache 12 91169) (prefixPartial 12 91169) = false := by
  decide +kernel

theorem node_context_12_91169_679817 : EJMOriginalGlobalDAGData.nodes 9 ⟨679817, by decide⟩ =
    .split (coordinate 12) (![⟨679756, by decide⟩,⟨679793, by decide⟩,⟨679809, by decide⟩,⟨679816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91169_679817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91169 ⟨679817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91169
    ⟨679817, by decide⟩ (by decide) (![⟨679756, by decide⟩,⟨679793, by decide⟩,⟨679809, by decide⟩,⟨679816, by decide⟩]) unmarked_context_12_91169_679817 node_context_12_91169_679817
  intro a
  fin_cases a
  · exact context_13_364676_679756
  · exact context_13_364677_679793
  · exact context_13_364678_679809
  · exact context_13_364679_679816

theorem selected_cut_26877 : selected 8 ⟨679835, by decide⟩
    (prefixPartial 13 364680) = some ⟨13, 2, 0, 679835, 364680, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_364680_679835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364680 ⟨679835, by decide⟩ :=
  accepted_of_selected 13 364680 ⟨679835, by decide⟩ ⟨13, 2, 0, 679835, 364680, 1061, 16384⟩
    (by decide) selected_cut_26877

theorem selected_cut_26878 : selected 8 ⟨679861, by decide⟩
    (prefixPartial 13 364681) = some ⟨13, 2, 0, 679861, 364681, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_364681_679861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364681 ⟨679861, by decide⟩ :=
  accepted_of_selected 13 364681 ⟨679861, by decide⟩ ⟨13, 2, 0, 679861, 364681, 1521, 16384⟩
    (by decide) selected_cut_26878

theorem selected_cut_26879 : selected 8 ⟨679874, by decide⟩
    (prefixPartial 13 364682) = some ⟨13, 2, 0, 679874, 364682, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_364682_679874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364682 ⟨679874, by decide⟩ :=
  accepted_of_selected 13 364682 ⟨679874, by decide⟩ ⟨13, 2, 0, 679874, 364682, 1245, 16384⟩
    (by decide) selected_cut_26879

theorem selected_cut_26880 : selected 8 ⟨679883, by decide⟩
    (prefixPartial 13 364683) = some ⟨13, 2, 0, 679883, 364683, 817, 16384⟩ := by
  decide +kernel

theorem context_13_364683_679883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364683 ⟨679883, by decide⟩ :=
  accepted_of_selected 13 364683 ⟨679883, by decide⟩ ⟨13, 2, 0, 679883, 364683, 817, 16384⟩
    (by decide) selected_cut_26880

theorem unmarked_context_12_91170_679884 : frontier 9 ⟨679884, by decide⟩
    (prefixCache 12 91170) (prefixPartial 12 91170) = false := by
  decide +kernel

theorem node_context_12_91170_679884 : EJMOriginalGlobalDAGData.nodes 9 ⟨679884, by decide⟩ =
    .split (coordinate 12) (![⟨679835, by decide⟩,⟨679861, by decide⟩,⟨679874, by decide⟩,⟨679883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91170_679884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91170 ⟨679884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91170
    ⟨679884, by decide⟩ (by decide) (![⟨679835, by decide⟩,⟨679861, by decide⟩,⟨679874, by decide⟩,⟨679883, by decide⟩]) unmarked_context_12_91170_679884 node_context_12_91170_679884
  intro a
  fin_cases a
  · exact context_13_364680_679835
  · exact context_13_364681_679861
  · exact context_13_364682_679874
  · exact context_13_364683_679883

theorem selected_cut_26881 : selected 8 ⟨679905, by decide⟩
    (prefixPartial 13 364684) = some ⟨13, 2, 0, 679905, 364684, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_364684_679905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364684 ⟨679905, by decide⟩ :=
  accepted_of_selected 13 364684 ⟨679905, by decide⟩ ⟨13, 2, 0, 679905, 364684, 1009, 16384⟩
    (by decide) selected_cut_26881

theorem selected_cut_26882 : selected 8 ⟨679937, by decide⟩
    (prefixPartial 13 364685) = some ⟨13, 2, 0, 679937, 364685, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_364685_679937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364685 ⟨679937, by decide⟩ :=
  accepted_of_selected 13 364685 ⟨679937, by decide⟩ ⟨13, 2, 0, 679937, 364685, 1825, 16384⟩
    (by decide) selected_cut_26882

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
