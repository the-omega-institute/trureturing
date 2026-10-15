/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover062
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_13_84201_183477 : frontier 8 ⟨183477, by decide⟩
    (prefixCache 13 84201) (prefixPartial 13 84201) = false := by
  decide +kernel

theorem node_context_13_84201_183477 : EJMOriginalGlobalDAGData.nodes 8 ⟨183477, by decide⟩ =
    .split (coordinate 13) (![⟨183429, by decide⟩,⟨183450, by decide⟩,⟨183465, by decide⟩,⟨183476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_84201_183477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84201 ⟨183477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 84201
    ⟨183477, by decide⟩ (by decide) (![⟨183429, by decide⟩,⟨183450, by decide⟩,⟨183465, by decide⟩,⟨183476, by decide⟩]) unmarked_context_13_84201_183477 node_context_13_84201_183477
  intro a
  fin_cases a
  · exact context_14_336804_183429
  · exact context_14_336805_183450
  · exact context_14_336806_183465
  · exact context_14_336807_183476

theorem selected_cut_06052 : selected 8 ⟨183517, by decide⟩
    (prefixPartial 13 84202) = some ⟨13, 2, 0, 183517, 84202, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_84202_183517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84202 ⟨183517, by decide⟩ :=
  accepted_of_selected 13 84202 ⟨183517, by decide⟩ ⟨13, 2, 0, 183517, 84202, 2469, 16384⟩
    (by decide) selected_cut_06052

theorem selected_cut_06053 : selected 8 ⟨183525, by decide⟩
    (prefixPartial 13 84203) = some ⟨13, 2, 0, 183525, 84203, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_84203_183525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84203 ⟨183525, by decide⟩ :=
  accepted_of_selected 13 84203 ⟨183525, by decide⟩ ⟨13, 2, 0, 183525, 84203, 1053, 16384⟩
    (by decide) selected_cut_06053

theorem unmarked_context_12_21050_183526 : frontier 9 ⟨183526, by decide⟩
    (prefixCache 12 21050) (prefixPartial 12 21050) = false := by
  decide +kernel

theorem node_context_12_21050_183526 : EJMOriginalGlobalDAGData.nodes 9 ⟨183526, by decide⟩ =
    .split (coordinate 12) (![⟨183408, by decide⟩,⟨183477, by decide⟩,⟨183517, by decide⟩,⟨183525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21050_183526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21050 ⟨183526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21050
    ⟨183526, by decide⟩ (by decide) (![⟨183408, by decide⟩,⟨183477, by decide⟩,⟨183517, by decide⟩,⟨183525, by decide⟩]) unmarked_context_12_21050_183526 node_context_12_21050_183526
  intro a
  fin_cases a
  · exact context_13_84200_183408
  · exact context_13_84201_183477
  · exact context_13_84202_183517
  · exact context_13_84203_183525

theorem selected_cut_06054 : selected 8 ⟨183533, by decide⟩
    (prefixPartial 13 84204) = some ⟨13, 2, 0, 183533, 84204, 265, 16384⟩ := by
  decide +kernel

theorem context_13_84204_183533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84204 ⟨183533, by decide⟩ :=
  accepted_of_selected 13 84204 ⟨183533, by decide⟩ ⟨13, 2, 0, 183533, 84204, 265, 16384⟩
    (by decide) selected_cut_06054

theorem selected_cut_06055 : selected 8 ⟨183574, by decide⟩
    (prefixPartial 13 84205) = some ⟨13, 2, 0, 183574, 84205, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_84205_183574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84205 ⟨183574, by decide⟩ :=
  accepted_of_selected 13 84205 ⟨183574, by decide⟩ ⟨13, 2, 0, 183574, 84205, 2893, 16384⟩
    (by decide) selected_cut_06055

theorem selected_cut_06056 : selected 8 ⟨183594, by decide⟩
    (prefixPartial 13 84206) = some ⟨13, 2, 0, 183594, 84206, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_84206_183594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84206 ⟨183594, by decide⟩ :=
  accepted_of_selected 13 84206 ⟨183594, by decide⟩ ⟨13, 2, 0, 183594, 84206, 1529, 16384⟩
    (by decide) selected_cut_06056

theorem selected_cut_06057 : selected 8 ⟨183601, by decide⟩
    (prefixPartial 13 84207) = some ⟨13, 2, 0, 183601, 84207, 801, 16384⟩ := by
  decide +kernel

theorem context_13_84207_183601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84207 ⟨183601, by decide⟩ :=
  accepted_of_selected 13 84207 ⟨183601, by decide⟩ ⟨13, 2, 0, 183601, 84207, 801, 16384⟩
    (by decide) selected_cut_06057

theorem unmarked_context_12_21051_183602 : frontier 9 ⟨183602, by decide⟩
    (prefixCache 12 21051) (prefixPartial 12 21051) = false := by
  decide +kernel

theorem node_context_12_21051_183602 : EJMOriginalGlobalDAGData.nodes 9 ⟨183602, by decide⟩ =
    .split (coordinate 12) (![⟨183533, by decide⟩,⟨183574, by decide⟩,⟨183594, by decide⟩,⟨183601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21051_183602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21051 ⟨183602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21051
    ⟨183602, by decide⟩ (by decide) (![⟨183533, by decide⟩,⟨183574, by decide⟩,⟨183594, by decide⟩,⟨183601, by decide⟩]) unmarked_context_12_21051_183602 node_context_12_21051_183602
  intro a
  fin_cases a
  · exact context_13_84204_183533
  · exact context_13_84205_183574
  · exact context_13_84206_183594
  · exact context_13_84207_183601

theorem unmarked_context_11_5262_183603 : frontier 10 ⟨183603, by decide⟩
    (prefixCache 11 5262) (prefixPartial 11 5262) = false := by
  decide +kernel

theorem node_context_11_5262_183603 : EJMOriginalGlobalDAGData.nodes 10 ⟨183603, by decide⟩ =
    .split (coordinate 11) (![⟨183332, by decide⟩,⟨183398, by decide⟩,⟨183526, by decide⟩,⟨183602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5262_183603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5262 ⟨183603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5262
    ⟨183603, by decide⟩ (by decide) (![⟨183332, by decide⟩,⟨183398, by decide⟩,⟨183526, by decide⟩,⟨183602, by decide⟩]) unmarked_context_11_5262_183603 node_context_11_5262_183603
  intro a
  fin_cases a
  · exact context_12_21048_183332
  · exact context_12_21049_183398
  · exact context_12_21050_183526
  · exact context_12_21051_183602

theorem selected_cut_06058 : selected 8 ⟨183606, by decide⟩
    (prefixPartial 13 84208) = some ⟨13, 2, 0, 183606, 84208, 149, 16384⟩ := by
  decide +kernel

theorem context_13_84208_183606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84208 ⟨183606, by decide⟩ :=
  accepted_of_selected 13 84208 ⟨183606, by decide⟩ ⟨13, 2, 0, 183606, 84208, 149, 16384⟩
    (by decide) selected_cut_06058

theorem selected_cut_06059 : selected 8 ⟨183634, by decide⟩
    (prefixPartial 13 84209) = some ⟨13, 2, 0, 183634, 84209, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_84209_183634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84209 ⟨183634, by decide⟩ :=
  accepted_of_selected 13 84209 ⟨183634, by decide⟩ ⟨13, 2, 0, 183634, 84209, 2261, 16384⟩
    (by decide) selected_cut_06059

theorem selected_cut_06060 : selected 8 ⟨183654, by decide⟩
    (prefixPartial 13 84210) = some ⟨13, 2, 0, 183654, 84210, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_84210_183654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84210 ⟨183654, by decide⟩ :=
  accepted_of_selected 13 84210 ⟨183654, by decide⟩ ⟨13, 2, 0, 183654, 84210, 1405, 16384⟩
    (by decide) selected_cut_06060

theorem selected_cut_06061 : selected 8 ⟨183662, by decide⟩
    (prefixPartial 13 84211) = some ⟨13, 2, 0, 183662, 84211, 757, 16384⟩ := by
  decide +kernel

theorem context_13_84211_183662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84211 ⟨183662, by decide⟩ :=
  accepted_of_selected 13 84211 ⟨183662, by decide⟩ ⟨13, 2, 0, 183662, 84211, 757, 16384⟩
    (by decide) selected_cut_06061

theorem unmarked_context_12_21052_183663 : frontier 9 ⟨183663, by decide⟩
    (prefixCache 12 21052) (prefixPartial 12 21052) = false := by
  decide +kernel

theorem node_context_12_21052_183663 : EJMOriginalGlobalDAGData.nodes 9 ⟨183663, by decide⟩ =
    .split (coordinate 12) (![⟨183606, by decide⟩,⟨183634, by decide⟩,⟨183654, by decide⟩,⟨183662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21052_183663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21052 ⟨183663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21052
    ⟨183663, by decide⟩ (by decide) (![⟨183606, by decide⟩,⟨183634, by decide⟩,⟨183654, by decide⟩,⟨183662, by decide⟩]) unmarked_context_12_21052_183663 node_context_12_21052_183663
  intro a
  fin_cases a
  · exact context_13_84208_183606
  · exact context_13_84209_183634
  · exact context_13_84210_183654
  · exact context_13_84211_183662

theorem selected_cut_06062 : selected 8 ⟨183666, by decide⟩
    (prefixPartial 13 84212) = some ⟨13, 2, 0, 183666, 84212, 121, 16384⟩ := by
  decide +kernel

theorem context_13_84212_183666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84212 ⟨183666, by decide⟩ :=
  accepted_of_selected 13 84212 ⟨183666, by decide⟩ ⟨13, 2, 0, 183666, 84212, 121, 16384⟩
    (by decide) selected_cut_06062

theorem selected_cut_06063 : selected 8 ⟨183702, by decide⟩
    (prefixPartial 13 84213) = some ⟨13, 2, 0, 183702, 84213, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_84213_183702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84213 ⟨183702, by decide⟩ :=
  accepted_of_selected 13 84213 ⟨183702, by decide⟩ ⟨13, 2, 0, 183702, 84213, 2493, 16384⟩
    (by decide) selected_cut_06063

theorem selected_cut_06064 : selected 8 ⟨183726, by decide⟩
    (prefixPartial 13 84214) = some ⟨13, 2, 0, 183726, 84214, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_84214_183726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84214 ⟨183726, by decide⟩ :=
  accepted_of_selected 13 84214 ⟨183726, by decide⟩ ⟨13, 2, 0, 183726, 84214, 1617, 16384⟩
    (by decide) selected_cut_06064

theorem selected_cut_06065 : selected 8 ⟨183733, by decide⟩
    (prefixPartial 13 84215) = some ⟨13, 2, 0, 183733, 84215, 753, 16384⟩ := by
  decide +kernel

theorem context_13_84215_183733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84215 ⟨183733, by decide⟩ :=
  accepted_of_selected 13 84215 ⟨183733, by decide⟩ ⟨13, 2, 0, 183733, 84215, 753, 16384⟩
    (by decide) selected_cut_06065

theorem unmarked_context_12_21053_183734 : frontier 9 ⟨183734, by decide⟩
    (prefixCache 12 21053) (prefixPartial 12 21053) = false := by
  decide +kernel

theorem node_context_12_21053_183734 : EJMOriginalGlobalDAGData.nodes 9 ⟨183734, by decide⟩ =
    .split (coordinate 12) (![⟨183666, by decide⟩,⟨183702, by decide⟩,⟨183726, by decide⟩,⟨183733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21053_183734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21053 ⟨183734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21053
    ⟨183734, by decide⟩ (by decide) (![⟨183666, by decide⟩,⟨183702, by decide⟩,⟨183726, by decide⟩,⟨183733, by decide⟩]) unmarked_context_12_21053_183734 node_context_12_21053_183734
  intro a
  fin_cases a
  · exact context_13_84212_183666
  · exact context_13_84213_183702
  · exact context_13_84214_183726
  · exact context_13_84215_183733

theorem selected_cut_06066 : selected 8 ⟨183737, by decide⟩
    (prefixPartial 13 84216) = some ⟨13, 2, 0, 183737, 84216, 89, 16384⟩ := by
  decide +kernel

theorem context_13_84216_183737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84216 ⟨183737, by decide⟩ :=
  accepted_of_selected 13 84216 ⟨183737, by decide⟩ ⟨13, 2, 0, 183737, 84216, 89, 16384⟩
    (by decide) selected_cut_06066

theorem selected_cut_06067 : selected 8 ⟨183782, by decide⟩
    (prefixPartial 13 84217) = some ⟨13, 2, 0, 183782, 84217, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_84217_183782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84217 ⟨183782, by decide⟩ :=
  accepted_of_selected 13 84217 ⟨183782, by decide⟩ ⟨13, 2, 0, 183782, 84217, 2933, 16384⟩
    (by decide) selected_cut_06067

theorem selected_cut_06068 : selected 8 ⟨183805, by decide⟩
    (prefixPartial 13 84218) = some ⟨13, 2, 0, 183805, 84218, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_84218_183805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84218 ⟨183805, by decide⟩ :=
  accepted_of_selected 13 84218 ⟨183805, by decide⟩ ⟨13, 2, 0, 183805, 84218, 1497, 16384⟩
    (by decide) selected_cut_06068

theorem selected_cut_06069 : selected 8 ⟨183811, by decide⟩
    (prefixPartial 13 84219) = some ⟨13, 2, 0, 183811, 84219, 729, 16384⟩ := by
  decide +kernel

theorem context_13_84219_183811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84219 ⟨183811, by decide⟩ :=
  accepted_of_selected 13 84219 ⟨183811, by decide⟩ ⟨13, 2, 0, 183811, 84219, 729, 16384⟩
    (by decide) selected_cut_06069

theorem unmarked_context_12_21054_183812 : frontier 9 ⟨183812, by decide⟩
    (prefixCache 12 21054) (prefixPartial 12 21054) = false := by
  decide +kernel

theorem node_context_12_21054_183812 : EJMOriginalGlobalDAGData.nodes 9 ⟨183812, by decide⟩ =
    .split (coordinate 12) (![⟨183737, by decide⟩,⟨183782, by decide⟩,⟨183805, by decide⟩,⟨183811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21054_183812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21054 ⟨183812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21054
    ⟨183812, by decide⟩ (by decide) (![⟨183737, by decide⟩,⟨183782, by decide⟩,⟨183805, by decide⟩,⟨183811, by decide⟩]) unmarked_context_12_21054_183812 node_context_12_21054_183812
  intro a
  fin_cases a
  · exact context_13_84216_183737
  · exact context_13_84217_183782
  · exact context_13_84218_183805
  · exact context_13_84219_183811

theorem selected_cut_06070 : selected 8 ⟨183816, by decide⟩
    (prefixPartial 13 84220) = some ⟨13, 2, 0, 183816, 84220, 73, 16384⟩ := by
  decide +kernel

theorem context_13_84220_183816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84220 ⟨183816, by decide⟩ :=
  accepted_of_selected 13 84220 ⟨183816, by decide⟩ ⟨13, 2, 0, 183816, 84220, 73, 16384⟩
    (by decide) selected_cut_06070

theorem selected_cut_06071 : selected 8 ⟨183859, by decide⟩
    (prefixPartial 13 84221) = some ⟨13, 2, 0, 183859, 84221, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_84221_183859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84221 ⟨183859, by decide⟩ :=
  accepted_of_selected 13 84221 ⟨183859, by decide⟩ ⟨13, 2, 0, 183859, 84221, 2857, 16384⟩
    (by decide) selected_cut_06071

theorem selected_cut_06072 : selected 8 ⟨183878, by decide⟩
    (prefixPartial 13 84222) = some ⟨13, 2, 0, 183878, 84222, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_84222_183878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84222 ⟨183878, by decide⟩ :=
  accepted_of_selected 13 84222 ⟨183878, by decide⟩ ⟨13, 2, 0, 183878, 84222, 1561, 16384⟩
    (by decide) selected_cut_06072

theorem selected_cut_06073 : selected 8 ⟨183888, by decide⟩
    (prefixPartial 13 84223) = some ⟨13, 2, 0, 183888, 84223, 801, 16384⟩ := by
  decide +kernel

theorem context_13_84223_183888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84223 ⟨183888, by decide⟩ :=
  accepted_of_selected 13 84223 ⟨183888, by decide⟩ ⟨13, 2, 0, 183888, 84223, 801, 16384⟩
    (by decide) selected_cut_06073

theorem unmarked_context_12_21055_183889 : frontier 9 ⟨183889, by decide⟩
    (prefixCache 12 21055) (prefixPartial 12 21055) = false := by
  decide +kernel

theorem node_context_12_21055_183889 : EJMOriginalGlobalDAGData.nodes 9 ⟨183889, by decide⟩ =
    .split (coordinate 12) (![⟨183816, by decide⟩,⟨183859, by decide⟩,⟨183878, by decide⟩,⟨183888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21055_183889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21055 ⟨183889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21055
    ⟨183889, by decide⟩ (by decide) (![⟨183816, by decide⟩,⟨183859, by decide⟩,⟨183878, by decide⟩,⟨183888, by decide⟩]) unmarked_context_12_21055_183889 node_context_12_21055_183889
  intro a
  fin_cases a
  · exact context_13_84220_183816
  · exact context_13_84221_183859
  · exact context_13_84222_183878
  · exact context_13_84223_183888

theorem unmarked_context_11_5263_183890 : frontier 10 ⟨183890, by decide⟩
    (prefixCache 11 5263) (prefixPartial 11 5263) = false := by
  decide +kernel

theorem node_context_11_5263_183890 : EJMOriginalGlobalDAGData.nodes 10 ⟨183890, by decide⟩ =
    .split (coordinate 11) (![⟨183663, by decide⟩,⟨183734, by decide⟩,⟨183812, by decide⟩,⟨183889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5263_183890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5263 ⟨183890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5263
    ⟨183890, by decide⟩ (by decide) (![⟨183663, by decide⟩,⟨183734, by decide⟩,⟨183812, by decide⟩,⟨183889, by decide⟩]) unmarked_context_11_5263_183890 node_context_11_5263_183890
  intro a
  fin_cases a
  · exact context_12_21052_183663
  · exact context_12_21053_183734
  · exact context_12_21054_183812
  · exact context_12_21055_183889

theorem unmarked_context_10_1315_183891 : frontier 11 ⟨183891, by decide⟩
    (prefixCache 10 1315) (prefixPartial 10 1315) = false := by
  decide +kernel

theorem node_context_10_1315_183891 : EJMOriginalGlobalDAGData.nodes 11 ⟨183891, by decide⟩ =
    .split (coordinate 10) (![⟨183025, by decide⟩,⟨183274, by decide⟩,⟨183603, by decide⟩,⟨183890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1315_183891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1315 ⟨183891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1315
    ⟨183891, by decide⟩ (by decide) (![⟨183025, by decide⟩,⟨183274, by decide⟩,⟨183603, by decide⟩,⟨183890, by decide⟩]) unmarked_context_10_1315_183891 node_context_10_1315_183891
  intro a
  fin_cases a
  · exact context_11_5260_183025
  · exact context_11_5261_183274
  · exact context_11_5262_183603
  · exact context_11_5263_183890

theorem unmarked_context_9_328_183892 : frontier 12 ⟨183892, by decide⟩
    (prefixCache 9 328) (prefixPartial 9 328) = false := by
  decide +kernel

theorem node_context_9_328_183892 : EJMOriginalGlobalDAGData.nodes 12 ⟨183892, by decide⟩ =
    .split (coordinate 9) (![⟨180176, by decide⟩,⟨181549, by decide⟩,⟨182778, by decide⟩,⟨183891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_328_183892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 328 ⟨183892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 328
    ⟨183892, by decide⟩ (by decide) (![⟨180176, by decide⟩,⟨181549, by decide⟩,⟨182778, by decide⟩,⟨183891, by decide⟩]) unmarked_context_9_328_183892 node_context_9_328_183892
  intro a
  fin_cases a
  · exact context_10_1312_180176
  · exact context_10_1313_181549
  · exact context_10_1314_182778
  · exact context_10_1315_183891

theorem selected_cut_06074 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84224) = some ⟨13, 1, 0, 3444, 84224, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84224_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84224 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84224 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84224, 1, 16384⟩
    (by decide) selected_cut_06074

theorem selected_cut_06075 : selected 8 ⟨183927, by decide⟩
    (prefixPartial 13 84225) = some ⟨13, 2, 0, 183927, 84225, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_84225_183927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84225 ⟨183927, by decide⟩ :=
  accepted_of_selected 13 84225 ⟨183927, by decide⟩ ⟨13, 2, 0, 183927, 84225, 2637, 16384⟩
    (by decide) selected_cut_06075

theorem selected_cut_06076 : selected 8 ⟨183946, by decide⟩
    (prefixPartial 13 84226) = some ⟨13, 2, 0, 183946, 84226, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_84226_183946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84226 ⟨183946, by decide⟩ :=
  accepted_of_selected 13 84226 ⟨183946, by decide⟩ ⟨13, 2, 0, 183946, 84226, 1481, 16384⟩
    (by decide) selected_cut_06076

theorem selected_cut_06077 : selected 8 ⟨183954, by decide⟩
    (prefixPartial 13 84227) = some ⟨13, 2, 0, 183954, 84227, 797, 16384⟩ := by
  decide +kernel

theorem context_13_84227_183954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84227 ⟨183954, by decide⟩ :=
  accepted_of_selected 13 84227 ⟨183954, by decide⟩ ⟨13, 2, 0, 183954, 84227, 797, 16384⟩
    (by decide) selected_cut_06077

theorem unmarked_context_12_21056_183955 : frontier 9 ⟨183955, by decide⟩
    (prefixCache 12 21056) (prefixPartial 12 21056) = false := by
  decide +kernel

theorem node_context_12_21056_183955 : EJMOriginalGlobalDAGData.nodes 9 ⟨183955, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨183927, by decide⟩,⟨183946, by decide⟩,⟨183954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21056_183955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21056 ⟨183955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21056
    ⟨183955, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨183927, by decide⟩,⟨183946, by decide⟩,⟨183954, by decide⟩]) unmarked_context_12_21056_183955 node_context_12_21056_183955
  intro a
  fin_cases a
  · exact context_13_84224_3444
  · exact context_13_84225_183927
  · exact context_13_84226_183946
  · exact context_13_84227_183954

theorem selected_cut_06078 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84228) = some ⟨13, 1, 0, 3444, 84228, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84228_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84228 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84228 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84228, 1, 16384⟩
    (by decide) selected_cut_06078

theorem selected_cut_06079 : selected 7 ⟨183987, by decide⟩
    (prefixPartial 14 336916) = some ⟨14, 2, 0, 183987, 336916, 1693, 4096⟩ := by
  decide +kernel

theorem context_14_336916_183987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336916 ⟨183987, by decide⟩ :=
  accepted_of_selected 14 336916 ⟨183987, by decide⟩ ⟨14, 2, 0, 183987, 336916, 1693, 4096⟩
    (by decide) selected_cut_06079

theorem selected_cut_06080 : selected 7 ⟨184007, by decide⟩
    (prefixPartial 14 336917) = some ⟨14, 2, 0, 184007, 336917, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_336917_184007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336917 ⟨184007, by decide⟩ :=
  accepted_of_selected 14 336917 ⟨184007, by decide⟩ ⟨14, 2, 0, 184007, 336917, 1089, 4096⟩
    (by decide) selected_cut_06080

theorem selected_cut_06081 : selected 7 ⟨184030, by decide⟩
    (prefixPartial 14 336918) = some ⟨14, 2, 0, 184030, 336918, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_336918_184030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336918 ⟨184030, by decide⟩ :=
  accepted_of_selected 14 336918 ⟨184030, by decide⟩ ⟨14, 2, 0, 184030, 336918, 1297, 4096⟩
    (by decide) selected_cut_06081

theorem selected_cut_06082 : selected 7 ⟨184048, by decide⟩
    (prefixPartial 14 336919) = some ⟨14, 2, 0, 184048, 336919, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_336919_184048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336919 ⟨184048, by decide⟩ :=
  accepted_of_selected 14 336919 ⟨184048, by decide⟩ ⟨14, 2, 0, 184048, 336919, 1105, 4096⟩
    (by decide) selected_cut_06082

theorem unmarked_context_13_84229_184049 : frontier 8 ⟨184049, by decide⟩
    (prefixCache 13 84229) (prefixPartial 13 84229) = false := by
  decide +kernel

theorem node_context_13_84229_184049 : EJMOriginalGlobalDAGData.nodes 8 ⟨184049, by decide⟩ =
    .split (coordinate 13) (![⟨183987, by decide⟩,⟨184007, by decide⟩,⟨184030, by decide⟩,⟨184048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_84229_184049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84229 ⟨184049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 84229
    ⟨184049, by decide⟩ (by decide) (![⟨183987, by decide⟩,⟨184007, by decide⟩,⟨184030, by decide⟩,⟨184048, by decide⟩]) unmarked_context_13_84229_184049 node_context_13_84229_184049
  intro a
  fin_cases a
  · exact context_14_336916_183987
  · exact context_14_336917_184007
  · exact context_14_336918_184030
  · exact context_14_336919_184048

theorem selected_cut_06083 : selected 8 ⟨184076, by decide⟩
    (prefixPartial 13 84230) = some ⟨13, 2, 0, 184076, 84230, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_84230_184076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84230 ⟨184076, by decide⟩ :=
  accepted_of_selected 13 84230 ⟨184076, by decide⟩ ⟨13, 2, 0, 184076, 84230, 2349, 16384⟩
    (by decide) selected_cut_06083

theorem selected_cut_06084 : selected 8 ⟨184095, by decide⟩
    (prefixPartial 13 84231) = some ⟨13, 2, 0, 184095, 84231, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_84231_184095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84231 ⟨184095, by decide⟩ :=
  accepted_of_selected 13 84231 ⟨184095, by decide⟩ ⟨13, 2, 0, 184095, 84231, 1337, 16384⟩
    (by decide) selected_cut_06084

theorem unmarked_context_12_21057_184096 : frontier 9 ⟨184096, by decide⟩
    (prefixCache 12 21057) (prefixPartial 12 21057) = false := by
  decide +kernel

theorem node_context_12_21057_184096 : EJMOriginalGlobalDAGData.nodes 9 ⟨184096, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184049, by decide⟩,⟨184076, by decide⟩,⟨184095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21057_184096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21057 ⟨184096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21057
    ⟨184096, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184049, by decide⟩,⟨184076, by decide⟩,⟨184095, by decide⟩]) unmarked_context_12_21057_184096 node_context_12_21057_184096
  intro a
  fin_cases a
  · exact context_13_84228_3444
  · exact context_13_84229_184049
  · exact context_13_84230_184076
  · exact context_13_84231_184095

theorem selected_cut_06085 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84232) = some ⟨13, 1, 0, 3444, 84232, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84232_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84232 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84232 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84232, 1, 16384⟩
    (by decide) selected_cut_06085

theorem selected_cut_06086 : selected 8 ⟨184156, by decide⟩
    (prefixPartial 13 84233) = some ⟨13, 2, 0, 184156, 84233, 3689, 16384⟩ := by
  decide +kernel

theorem context_13_84233_184156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84233 ⟨184156, by decide⟩ :=
  accepted_of_selected 13 84233 ⟨184156, by decide⟩ ⟨13, 2, 0, 184156, 84233, 3689, 16384⟩
    (by decide) selected_cut_06086

theorem selected_cut_06087 : selected 8 ⟨184177, by decide⟩
    (prefixPartial 13 84234) = some ⟨13, 2, 0, 184177, 84234, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_84234_184177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84234 ⟨184177, by decide⟩ :=
  accepted_of_selected 13 84234 ⟨184177, by decide⟩ ⟨13, 2, 0, 184177, 84234, 1929, 16384⟩
    (by decide) selected_cut_06087

theorem selected_cut_06088 : selected 8 ⟨184187, by decide⟩
    (prefixPartial 13 84235) = some ⟨13, 2, 0, 184187, 84235, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_84235_184187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84235 ⟨184187, by decide⟩ :=
  accepted_of_selected 13 84235 ⟨184187, by decide⟩ ⟨13, 2, 0, 184187, 84235, 1029, 16384⟩
    (by decide) selected_cut_06088

theorem unmarked_context_12_21058_184188 : frontier 9 ⟨184188, by decide⟩
    (prefixCache 12 21058) (prefixPartial 12 21058) = false := by
  decide +kernel

theorem node_context_12_21058_184188 : EJMOriginalGlobalDAGData.nodes 9 ⟨184188, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184156, by decide⟩,⟨184177, by decide⟩,⟨184187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21058_184188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21058 ⟨184188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21058
    ⟨184188, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184156, by decide⟩,⟨184177, by decide⟩,⟨184187, by decide⟩]) unmarked_context_12_21058_184188 node_context_12_21058_184188
  intro a
  fin_cases a
  · exact context_13_84232_3444
  · exact context_13_84233_184156
  · exact context_13_84234_184177
  · exact context_13_84235_184187

theorem selected_cut_06089 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84236) = some ⟨13, 1, 0, 3444, 84236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84236, 1, 16384⟩
    (by decide) selected_cut_06089

theorem selected_cut_06090 : selected 8 ⟨184239, by decide⟩
    (prefixPartial 13 84237) = some ⟨13, 2, 0, 184239, 84237, 3637, 16384⟩ := by
  decide +kernel

theorem context_13_84237_184239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84237 ⟨184239, by decide⟩ :=
  accepted_of_selected 13 84237 ⟨184239, by decide⟩ ⟨13, 2, 0, 184239, 84237, 3637, 16384⟩
    (by decide) selected_cut_06090

theorem selected_cut_06091 : selected 8 ⟨184261, by decide⟩
    (prefixPartial 13 84238) = some ⟨13, 2, 0, 184261, 84238, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_84238_184261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84238 ⟨184261, by decide⟩ :=
  accepted_of_selected 13 84238 ⟨184261, by decide⟩ ⟨13, 2, 0, 184261, 84238, 1909, 16384⟩
    (by decide) selected_cut_06091

theorem selected_cut_06092 : selected 8 ⟨184274, by decide⟩
    (prefixPartial 13 84239) = some ⟨13, 2, 0, 184274, 84239, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_84239_184274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84239 ⟨184274, by decide⟩ :=
  accepted_of_selected 13 84239 ⟨184274, by decide⟩ ⟨13, 2, 0, 184274, 84239, 1117, 16384⟩
    (by decide) selected_cut_06092

theorem unmarked_context_12_21059_184275 : frontier 9 ⟨184275, by decide⟩
    (prefixCache 12 21059) (prefixPartial 12 21059) = false := by
  decide +kernel

theorem node_context_12_21059_184275 : EJMOriginalGlobalDAGData.nodes 9 ⟨184275, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184239, by decide⟩,⟨184261, by decide⟩,⟨184274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21059_184275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21059 ⟨184275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21059
    ⟨184275, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184239, by decide⟩,⟨184261, by decide⟩,⟨184274, by decide⟩]) unmarked_context_12_21059_184275 node_context_12_21059_184275
  intro a
  fin_cases a
  · exact context_13_84236_3444
  · exact context_13_84237_184239
  · exact context_13_84238_184261
  · exact context_13_84239_184274

theorem unmarked_context_11_5264_184276 : frontier 10 ⟨184276, by decide⟩
    (prefixCache 11 5264) (prefixPartial 11 5264) = false := by
  decide +kernel

theorem node_context_11_5264_184276 : EJMOriginalGlobalDAGData.nodes 10 ⟨184276, by decide⟩ =
    .split (coordinate 11) (![⟨183955, by decide⟩,⟨184096, by decide⟩,⟨184188, by decide⟩,⟨184275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5264_184276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5264 ⟨184276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5264
    ⟨184276, by decide⟩ (by decide) (![⟨183955, by decide⟩,⟨184096, by decide⟩,⟨184188, by decide⟩,⟨184275, by decide⟩]) unmarked_context_11_5264_184276 node_context_11_5264_184276
  intro a
  fin_cases a
  · exact context_12_21056_183955
  · exact context_12_21057_184096
  · exact context_12_21058_184188
  · exact context_12_21059_184275

theorem selected_cut_06093 : selected 9 ⟨184322, by decide⟩
    (prefixPartial 12 21060) = some ⟨12, 2, 0, 184322, 21060, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_21060_184322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21060 ⟨184322, by decide⟩ :=
  accepted_of_selected 12 21060 ⟨184322, by decide⟩ ⟨12, 2, 0, 184322, 21060, 3577, 65536⟩
    (by decide) selected_cut_06093

theorem selected_cut_06094 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84244) = some ⟨13, 1, 0, 3444, 84244, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84244_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84244 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84244 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84244, 1, 16384⟩
    (by decide) selected_cut_06094

theorem selected_cut_06095 : selected 8 ⟨184365, by decide⟩
    (prefixPartial 13 84245) = some ⟨13, 2, 0, 184365, 84245, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_84245_184365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84245 ⟨184365, by decide⟩ :=
  accepted_of_selected 13 84245 ⟨184365, by decide⟩ ⟨13, 2, 0, 184365, 84245, 3029, 16384⟩
    (by decide) selected_cut_06095

theorem selected_cut_06096 : selected 8 ⟨184389, by decide⟩
    (prefixPartial 13 84246) = some ⟨13, 2, 0, 184389, 84246, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_84246_184389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84246 ⟨184389, by decide⟩ :=
  accepted_of_selected 13 84246 ⟨184389, by decide⟩ ⟨13, 2, 0, 184389, 84246, 1889, 16384⟩
    (by decide) selected_cut_06096

theorem selected_cut_06097 : selected 8 ⟨184396, by decide⟩
    (prefixPartial 13 84247) = some ⟨13, 2, 0, 184396, 84247, 921, 16384⟩ := by
  decide +kernel

theorem context_13_84247_184396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84247 ⟨184396, by decide⟩ :=
  accepted_of_selected 13 84247 ⟨184396, by decide⟩ ⟨13, 2, 0, 184396, 84247, 921, 16384⟩
    (by decide) selected_cut_06097

theorem unmarked_context_12_21061_184397 : frontier 9 ⟨184397, by decide⟩
    (prefixCache 12 21061) (prefixPartial 12 21061) = false := by
  decide +kernel

theorem node_context_12_21061_184397 : EJMOriginalGlobalDAGData.nodes 9 ⟨184397, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184365, by decide⟩,⟨184389, by decide⟩,⟨184396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21061_184397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21061 ⟨184397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21061
    ⟨184397, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184365, by decide⟩,⟨184389, by decide⟩,⟨184396, by decide⟩]) unmarked_context_12_21061_184397 node_context_12_21061_184397
  intro a
  fin_cases a
  · exact context_13_84244_3444
  · exact context_13_84245_184365
  · exact context_13_84246_184389
  · exact context_13_84247_184396

theorem selected_cut_06098 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84248) = some ⟨13, 1, 0, 3444, 84248, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84248_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84248 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84248 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84248, 1, 16384⟩
    (by decide) selected_cut_06098

theorem selected_cut_06099 : selected 8 ⟨184427, by decide⟩
    (prefixPartial 13 84249) = some ⟨13, 2, 0, 184427, 84249, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_84249_184427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84249 ⟨184427, by decide⟩ :=
  accepted_of_selected 13 84249 ⟨184427, by decide⟩ ⟨13, 2, 0, 184427, 84249, 2161, 16384⟩
    (by decide) selected_cut_06099

theorem selected_cut_06100 : selected 8 ⟨184448, by decide⟩
    (prefixPartial 13 84250) = some ⟨13, 2, 0, 184448, 84250, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_84250_184448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84250 ⟨184448, by decide⟩ :=
  accepted_of_selected 13 84250 ⟨184448, by decide⟩ ⟨13, 2, 0, 184448, 84250, 1333, 16384⟩
    (by decide) selected_cut_06100

theorem selected_cut_06101 : selected 8 ⟨184457, by decide⟩
    (prefixPartial 13 84251) = some ⟨13, 2, 0, 184457, 84251, 729, 16384⟩ := by
  decide +kernel

theorem context_13_84251_184457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84251 ⟨184457, by decide⟩ :=
  accepted_of_selected 13 84251 ⟨184457, by decide⟩ ⟨13, 2, 0, 184457, 84251, 729, 16384⟩
    (by decide) selected_cut_06101

theorem unmarked_context_12_21062_184458 : frontier 9 ⟨184458, by decide⟩
    (prefixCache 12 21062) (prefixPartial 12 21062) = false := by
  decide +kernel

theorem node_context_12_21062_184458 : EJMOriginalGlobalDAGData.nodes 9 ⟨184458, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184427, by decide⟩,⟨184448, by decide⟩,⟨184457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21062_184458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21062 ⟨184458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21062
    ⟨184458, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184427, by decide⟩,⟨184448, by decide⟩,⟨184457, by decide⟩]) unmarked_context_12_21062_184458 node_context_12_21062_184458
  intro a
  fin_cases a
  · exact context_13_84248_3444
  · exact context_13_84249_184427
  · exact context_13_84250_184448
  · exact context_13_84251_184457

theorem selected_cut_06102 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84252) = some ⟨13, 1, 0, 3444, 84252, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84252_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84252 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84252 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84252, 1, 16384⟩
    (by decide) selected_cut_06102

theorem selected_cut_06103 : selected 8 ⟨184486, by decide⟩
    (prefixPartial 13 84253) = some ⟨13, 2, 0, 184486, 84253, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_84253_184486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84253 ⟨184486, by decide⟩ :=
  accepted_of_selected 13 84253 ⟨184486, by decide⟩ ⟨13, 2, 0, 184486, 84253, 2185, 16384⟩
    (by decide) selected_cut_06103

theorem selected_cut_06104 : selected 8 ⟨184508, by decide⟩
    (prefixPartial 13 84254) = some ⟨13, 2, 0, 184508, 84254, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_84254_184508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84254 ⟨184508, by decide⟩ :=
  accepted_of_selected 13 84254 ⟨184508, by decide⟩ ⟨13, 2, 0, 184508, 84254, 1581, 16384⟩
    (by decide) selected_cut_06104

theorem selected_cut_06105 : selected 8 ⟨184516, by decide⟩
    (prefixPartial 13 84255) = some ⟨13, 2, 0, 184516, 84255, 797, 16384⟩ := by
  decide +kernel

theorem context_13_84255_184516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84255 ⟨184516, by decide⟩ :=
  accepted_of_selected 13 84255 ⟨184516, by decide⟩ ⟨13, 2, 0, 184516, 84255, 797, 16384⟩
    (by decide) selected_cut_06105

theorem unmarked_context_12_21063_184517 : frontier 9 ⟨184517, by decide⟩
    (prefixCache 12 21063) (prefixPartial 12 21063) = false := by
  decide +kernel

theorem node_context_12_21063_184517 : EJMOriginalGlobalDAGData.nodes 9 ⟨184517, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184486, by decide⟩,⟨184508, by decide⟩,⟨184516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21063_184517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21063 ⟨184517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21063
    ⟨184517, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184486, by decide⟩,⟨184508, by decide⟩,⟨184516, by decide⟩]) unmarked_context_12_21063_184517 node_context_12_21063_184517
  intro a
  fin_cases a
  · exact context_13_84252_3444
  · exact context_13_84253_184486
  · exact context_13_84254_184508
  · exact context_13_84255_184516

theorem unmarked_context_11_5265_184518 : frontier 10 ⟨184518, by decide⟩
    (prefixCache 11 5265) (prefixPartial 11 5265) = false := by
  decide +kernel

theorem node_context_11_5265_184518 : EJMOriginalGlobalDAGData.nodes 10 ⟨184518, by decide⟩ =
    .split (coordinate 11) (![⟨184322, by decide⟩,⟨184397, by decide⟩,⟨184458, by decide⟩,⟨184517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5265_184518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5265 ⟨184518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5265
    ⟨184518, by decide⟩ (by decide) (![⟨184322, by decide⟩,⟨184397, by decide⟩,⟨184458, by decide⟩,⟨184517, by decide⟩]) unmarked_context_11_5265_184518 node_context_11_5265_184518
  intro a
  fin_cases a
  · exact context_12_21060_184322
  · exact context_12_21061_184397
  · exact context_12_21062_184458
  · exact context_12_21063_184517

theorem selected_cut_06106 : selected 9 ⟨184560, by decide⟩
    (prefixPartial 12 21064) = some ⟨12, 2, 0, 184560, 21064, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_21064_184560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21064 ⟨184560, by decide⟩ :=
  accepted_of_selected 12 21064 ⟨184560, by decide⟩ ⟨12, 2, 0, 184560, 21064, 3121, 65536⟩
    (by decide) selected_cut_06106

theorem selected_cut_06107 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84260) = some ⟨13, 1, 0, 3444, 84260, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84260_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84260 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84260 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84260, 1, 16384⟩
    (by decide) selected_cut_06107

theorem selected_cut_06108 : selected 8 ⟨184589, by decide⟩
    (prefixPartial 13 84261) = some ⟨13, 2, 0, 184589, 84261, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_84261_184589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84261 ⟨184589, by decide⟩ :=
  accepted_of_selected 13 84261 ⟨184589, by decide⟩ ⟨13, 2, 0, 184589, 84261, 2577, 16384⟩
    (by decide) selected_cut_06108

theorem selected_cut_06109 : selected 8 ⟨184609, by decide⟩
    (prefixPartial 13 84262) = some ⟨13, 2, 0, 184609, 84262, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_84262_184609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84262 ⟨184609, by decide⟩ :=
  accepted_of_selected 13 84262 ⟨184609, by decide⟩ ⟨13, 2, 0, 184609, 84262, 2109, 16384⟩
    (by decide) selected_cut_06109

theorem selected_cut_06110 : selected 8 ⟨184617, by decide⟩
    (prefixPartial 13 84263) = some ⟨13, 2, 0, 184617, 84263, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_84263_184617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84263 ⟨184617, by decide⟩ :=
  accepted_of_selected 13 84263 ⟨184617, by decide⟩ ⟨13, 2, 0, 184617, 84263, 1109, 16384⟩
    (by decide) selected_cut_06110

theorem unmarked_context_12_21065_184618 : frontier 9 ⟨184618, by decide⟩
    (prefixCache 12 21065) (prefixPartial 12 21065) = false := by
  decide +kernel

theorem node_context_12_21065_184618 : EJMOriginalGlobalDAGData.nodes 9 ⟨184618, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184589, by decide⟩,⟨184609, by decide⟩,⟨184617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21065_184618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21065 ⟨184618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21065
    ⟨184618, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184589, by decide⟩,⟨184609, by decide⟩,⟨184617, by decide⟩]) unmarked_context_12_21065_184618 node_context_12_21065_184618
  intro a
  fin_cases a
  · exact context_13_84260_3444
  · exact context_13_84261_184589
  · exact context_13_84262_184609
  · exact context_13_84263_184617

theorem selected_cut_06111 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84264) = some ⟨13, 1, 0, 3444, 84264, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84264_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84264 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84264 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84264, 1, 16384⟩
    (by decide) selected_cut_06111

theorem selected_cut_06112 : selected 8 ⟨184659, by decide⟩
    (prefixPartial 13 84265) = some ⟨13, 2, 0, 184659, 84265, 3241, 16384⟩ := by
  decide +kernel

theorem context_13_84265_184659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84265 ⟨184659, by decide⟩ :=
  accepted_of_selected 13 84265 ⟨184659, by decide⟩ ⟨13, 2, 0, 184659, 84265, 3241, 16384⟩
    (by decide) selected_cut_06112

theorem selected_cut_06113 : selected 8 ⟨184693, by decide⟩
    (prefixPartial 13 84266) = some ⟨13, 2, 0, 184693, 84266, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_84266_184693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84266 ⟨184693, by decide⟩ :=
  accepted_of_selected 13 84266 ⟨184693, by decide⟩ ⟨13, 2, 0, 184693, 84266, 2721, 16384⟩
    (by decide) selected_cut_06113

theorem selected_cut_06114 : selected 8 ⟨184699, by decide⟩
    (prefixPartial 13 84267) = some ⟨13, 2, 0, 184699, 84267, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_84267_184699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84267 ⟨184699, by decide⟩ :=
  accepted_of_selected 13 84267 ⟨184699, by decide⟩ ⟨13, 2, 0, 184699, 84267, 1201, 16384⟩
    (by decide) selected_cut_06114

theorem unmarked_context_12_21066_184700 : frontier 9 ⟨184700, by decide⟩
    (prefixCache 12 21066) (prefixPartial 12 21066) = false := by
  decide +kernel

theorem node_context_12_21066_184700 : EJMOriginalGlobalDAGData.nodes 9 ⟨184700, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184659, by decide⟩,⟨184693, by decide⟩,⟨184699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21066_184700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21066 ⟨184700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21066
    ⟨184700, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184659, by decide⟩,⟨184693, by decide⟩,⟨184699, by decide⟩]) unmarked_context_12_21066_184700 node_context_12_21066_184700
  intro a
  fin_cases a
  · exact context_13_84264_3444
  · exact context_13_84265_184659
  · exact context_13_84266_184693
  · exact context_13_84267_184699

theorem selected_cut_06115 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84268) = some ⟨13, 1, 0, 3444, 84268, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84268_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84268 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84268 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84268, 1, 16384⟩
    (by decide) selected_cut_06115

theorem selected_cut_06116 : selected 8 ⟨184724, by decide⟩
    (prefixPartial 13 84269) = some ⟨13, 2, 0, 184724, 84269, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_84269_184724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84269 ⟨184724, by decide⟩ :=
  accepted_of_selected 13 84269 ⟨184724, by decide⟩ ⟨13, 2, 0, 184724, 84269, 1933, 16384⟩
    (by decide) selected_cut_06116

theorem selected_cut_06117 : selected 8 ⟨184746, by decide⟩
    (prefixPartial 13 84270) = some ⟨13, 2, 0, 184746, 84270, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_84270_184746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84270 ⟨184746, by decide⟩ :=
  accepted_of_selected 13 84270 ⟨184746, by decide⟩ ⟨13, 2, 0, 184746, 84270, 1609, 16384⟩
    (by decide) selected_cut_06117

theorem selected_cut_06118 : selected 8 ⟨184756, by decide⟩
    (prefixPartial 13 84271) = some ⟨13, 2, 0, 184756, 84271, 897, 16384⟩ := by
  decide +kernel

theorem context_13_84271_184756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84271 ⟨184756, by decide⟩ :=
  accepted_of_selected 13 84271 ⟨184756, by decide⟩ ⟨13, 2, 0, 184756, 84271, 897, 16384⟩
    (by decide) selected_cut_06118

theorem unmarked_context_12_21067_184757 : frontier 9 ⟨184757, by decide⟩
    (prefixCache 12 21067) (prefixPartial 12 21067) = false := by
  decide +kernel

theorem node_context_12_21067_184757 : EJMOriginalGlobalDAGData.nodes 9 ⟨184757, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184724, by decide⟩,⟨184746, by decide⟩,⟨184756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21067_184757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21067 ⟨184757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21067
    ⟨184757, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184724, by decide⟩,⟨184746, by decide⟩,⟨184756, by decide⟩]) unmarked_context_12_21067_184757 node_context_12_21067_184757
  intro a
  fin_cases a
  · exact context_13_84268_3444
  · exact context_13_84269_184724
  · exact context_13_84270_184746
  · exact context_13_84271_184756

theorem unmarked_context_11_5266_184758 : frontier 10 ⟨184758, by decide⟩
    (prefixCache 11 5266) (prefixPartial 11 5266) = false := by
  decide +kernel

theorem node_context_11_5266_184758 : EJMOriginalGlobalDAGData.nodes 10 ⟨184758, by decide⟩ =
    .split (coordinate 11) (![⟨184560, by decide⟩,⟨184618, by decide⟩,⟨184700, by decide⟩,⟨184757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5266_184758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5266 ⟨184758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5266
    ⟨184758, by decide⟩ (by decide) (![⟨184560, by decide⟩,⟨184618, by decide⟩,⟨184700, by decide⟩,⟨184757, by decide⟩]) unmarked_context_11_5266_184758 node_context_11_5266_184758
  intro a
  fin_cases a
  · exact context_12_21064_184560
  · exact context_12_21065_184618
  · exact context_12_21066_184700
  · exact context_12_21067_184757

theorem selected_cut_06119 : selected 9 ⟨184804, by decide⟩
    (prefixPartial 12 21068) = some ⟨12, 2, 0, 184804, 21068, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_21068_184804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21068 ⟨184804, by decide⟩ :=
  accepted_of_selected 12 21068 ⟨184804, by decide⟩ ⟨12, 2, 0, 184804, 21068, 3633, 65536⟩
    (by decide) selected_cut_06119

theorem selected_cut_06120 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84276) = some ⟨13, 1, 0, 3444, 84276, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84276_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84276 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84276 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84276, 1, 16384⟩
    (by decide) selected_cut_06120

theorem selected_cut_06121 : selected 8 ⟨184830, by decide⟩
    (prefixPartial 13 84277) = some ⟨13, 2, 0, 184830, 84277, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_84277_184830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84277 ⟨184830, by decide⟩ :=
  accepted_of_selected 13 84277 ⟨184830, by decide⟩ ⟨13, 2, 0, 184830, 84277, 2557, 16384⟩
    (by decide) selected_cut_06121

theorem selected_cut_06122 : selected 8 ⟨184860, by decide⟩
    (prefixPartial 13 84278) = some ⟨13, 2, 0, 184860, 84278, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_84278_184860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84278 ⟨184860, by decide⟩ :=
  accepted_of_selected 13 84278 ⟨184860, by decide⟩ ⟨13, 2, 0, 184860, 84278, 2469, 16384⟩
    (by decide) selected_cut_06122

theorem selected_cut_06123 : selected 8 ⟨184870, by decide⟩
    (prefixPartial 13 84279) = some ⟨13, 2, 0, 184870, 84279, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_84279_184870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84279 ⟨184870, by decide⟩ :=
  accepted_of_selected 13 84279 ⟨184870, by decide⟩ ⟨13, 2, 0, 184870, 84279, 1125, 16384⟩
    (by decide) selected_cut_06123

theorem unmarked_context_12_21069_184871 : frontier 9 ⟨184871, by decide⟩
    (prefixCache 12 21069) (prefixPartial 12 21069) = false := by
  decide +kernel

theorem node_context_12_21069_184871 : EJMOriginalGlobalDAGData.nodes 9 ⟨184871, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184830, by decide⟩,⟨184860, by decide⟩,⟨184870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21069_184871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21069 ⟨184871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21069
    ⟨184871, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184830, by decide⟩,⟨184860, by decide⟩,⟨184870, by decide⟩]) unmarked_context_12_21069_184871 node_context_12_21069_184871
  intro a
  fin_cases a
  · exact context_13_84276_3444
  · exact context_13_84277_184830
  · exact context_13_84278_184860
  · exact context_13_84279_184870

theorem selected_cut_06124 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84280) = some ⟨13, 1, 0, 3444, 84280, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84280_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84280 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84280 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84280, 1, 16384⟩
    (by decide) selected_cut_06124

theorem selected_cut_06125 : selected 8 ⟨184892, by decide⟩
    (prefixPartial 13 84281) = some ⟨13, 2, 0, 184892, 84281, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_84281_184892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84281 ⟨184892, by decide⟩ :=
  accepted_of_selected 13 84281 ⟨184892, by decide⟩ ⟨13, 2, 0, 184892, 84281, 2045, 16384⟩
    (by decide) selected_cut_06125

theorem selected_cut_06126 : selected 8 ⟨184914, by decide⟩
    (prefixPartial 13 84282) = some ⟨13, 2, 0, 184914, 84282, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_84282_184914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84282 ⟨184914, by decide⟩ :=
  accepted_of_selected 13 84282 ⟨184914, by decide⟩ ⟨13, 2, 0, 184914, 84282, 1893, 16384⟩
    (by decide) selected_cut_06126

theorem selected_cut_06127 : selected 8 ⟨184924, by decide⟩
    (prefixPartial 13 84283) = some ⟨13, 2, 0, 184924, 84283, 873, 16384⟩ := by
  decide +kernel

theorem context_13_84283_184924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84283 ⟨184924, by decide⟩ :=
  accepted_of_selected 13 84283 ⟨184924, by decide⟩ ⟨13, 2, 0, 184924, 84283, 873, 16384⟩
    (by decide) selected_cut_06127

theorem unmarked_context_12_21070_184925 : frontier 9 ⟨184925, by decide⟩
    (prefixCache 12 21070) (prefixPartial 12 21070) = false := by
  decide +kernel

theorem node_context_12_21070_184925 : EJMOriginalGlobalDAGData.nodes 9 ⟨184925, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184892, by decide⟩,⟨184914, by decide⟩,⟨184924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21070_184925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21070 ⟨184925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21070
    ⟨184925, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184892, by decide⟩,⟨184914, by decide⟩,⟨184924, by decide⟩]) unmarked_context_12_21070_184925 node_context_12_21070_184925
  intro a
  fin_cases a
  · exact context_13_84280_3444
  · exact context_13_84281_184892
  · exact context_13_84282_184914
  · exact context_13_84283_184924

theorem selected_cut_06128 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84284) = some ⟨13, 1, 0, 3444, 84284, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84284_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84284 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84284 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84284, 1, 16384⟩
    (by decide) selected_cut_06128

theorem selected_cut_06129 : selected 8 ⟨184945, by decide⟩
    (prefixPartial 13 84285) = some ⟨13, 2, 0, 184945, 84285, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_84285_184945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84285 ⟨184945, by decide⟩ :=
  accepted_of_selected 13 84285 ⟨184945, by decide⟩ ⟨13, 2, 0, 184945, 84285, 1877, 16384⟩
    (by decide) selected_cut_06129

theorem selected_cut_06130 : selected 8 ⟨184968, by decide⟩
    (prefixPartial 13 84286) = some ⟨13, 2, 0, 184968, 84286, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_84286_184968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84286 ⟨184968, by decide⟩ :=
  accepted_of_selected 13 84286 ⟨184968, by decide⟩ ⟨13, 2, 0, 184968, 84286, 1777, 16384⟩
    (by decide) selected_cut_06130

theorem selected_cut_06131 : selected 8 ⟨184978, by decide⟩
    (prefixPartial 13 84287) = some ⟨13, 2, 0, 184978, 84287, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_84287_184978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84287 ⟨184978, by decide⟩ :=
  accepted_of_selected 13 84287 ⟨184978, by decide⟩ ⟨13, 2, 0, 184978, 84287, 1021, 16384⟩
    (by decide) selected_cut_06131

theorem unmarked_context_12_21071_184979 : frontier 9 ⟨184979, by decide⟩
    (prefixCache 12 21071) (prefixPartial 12 21071) = false := by
  decide +kernel

theorem node_context_12_21071_184979 : EJMOriginalGlobalDAGData.nodes 9 ⟨184979, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨184945, by decide⟩,⟨184968, by decide⟩,⟨184978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21071_184979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21071 ⟨184979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21071
    ⟨184979, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨184945, by decide⟩,⟨184968, by decide⟩,⟨184978, by decide⟩]) unmarked_context_12_21071_184979 node_context_12_21071_184979
  intro a
  fin_cases a
  · exact context_13_84284_3444
  · exact context_13_84285_184945
  · exact context_13_84286_184968
  · exact context_13_84287_184978

theorem unmarked_context_11_5267_184980 : frontier 10 ⟨184980, by decide⟩
    (prefixCache 11 5267) (prefixPartial 11 5267) = false := by
  decide +kernel

theorem node_context_11_5267_184980 : EJMOriginalGlobalDAGData.nodes 10 ⟨184980, by decide⟩ =
    .split (coordinate 11) (![⟨184804, by decide⟩,⟨184871, by decide⟩,⟨184925, by decide⟩,⟨184979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5267_184980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5267 ⟨184980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5267
    ⟨184980, by decide⟩ (by decide) (![⟨184804, by decide⟩,⟨184871, by decide⟩,⟨184925, by decide⟩,⟨184979, by decide⟩]) unmarked_context_11_5267_184980 node_context_11_5267_184980
  intro a
  fin_cases a
  · exact context_12_21068_184804
  · exact context_12_21069_184871
  · exact context_12_21070_184925
  · exact context_12_21071_184979

theorem unmarked_context_10_1316_184981 : frontier 11 ⟨184981, by decide⟩
    (prefixCache 10 1316) (prefixPartial 10 1316) = false := by
  decide +kernel

theorem node_context_10_1316_184981 : EJMOriginalGlobalDAGData.nodes 11 ⟨184981, by decide⟩ =
    .split (coordinate 10) (![⟨184276, by decide⟩,⟨184518, by decide⟩,⟨184758, by decide⟩,⟨184980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1316_184981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1316 ⟨184981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1316
    ⟨184981, by decide⟩ (by decide) (![⟨184276, by decide⟩,⟨184518, by decide⟩,⟨184758, by decide⟩,⟨184980, by decide⟩]) unmarked_context_10_1316_184981 node_context_10_1316_184981
  intro a
  fin_cases a
  · exact context_11_5264_184276
  · exact context_11_5265_184518
  · exact context_11_5266_184758
  · exact context_11_5267_184980

theorem selected_cut_06132 : selected 9 ⟨185013, by decide⟩
    (prefixPartial 12 21072) = some ⟨12, 2, 0, 185013, 21072, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_21072_185013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21072 ⟨185013, by decide⟩ :=
  accepted_of_selected 12 21072 ⟨185013, by decide⟩ ⟨12, 2, 0, 185013, 21072, 2673, 65536⟩
    (by decide) selected_cut_06132

theorem selected_cut_06133 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84292) = some ⟨13, 1, 0, 3444, 84292, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84292_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84292 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84292 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84292, 1, 16384⟩
    (by decide) selected_cut_06133

theorem selected_cut_06134 : selected 8 ⟨185036, by decide⟩
    (prefixPartial 13 84293) = some ⟨13, 2, 0, 185036, 84293, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_84293_185036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84293 ⟨185036, by decide⟩ :=
  accepted_of_selected 13 84293 ⟨185036, by decide⟩ ⟨13, 2, 0, 185036, 84293, 2093, 16384⟩
    (by decide) selected_cut_06134

theorem selected_cut_06135 : selected 8 ⟨185059, by decide⟩
    (prefixPartial 13 84294) = some ⟨13, 2, 0, 185059, 84294, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_84294_185059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84294 ⟨185059, by decide⟩ :=
  accepted_of_selected 13 84294 ⟨185059, by decide⟩ ⟨13, 2, 0, 185059, 84294, 1833, 16384⟩
    (by decide) selected_cut_06135

theorem selected_cut_06136 : selected 8 ⟨185070, by decide⟩
    (prefixPartial 13 84295) = some ⟨13, 2, 0, 185070, 84295, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_84295_185070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84295 ⟨185070, by decide⟩ :=
  accepted_of_selected 13 84295 ⟨185070, by decide⟩ ⟨13, 2, 0, 185070, 84295, 1017, 16384⟩
    (by decide) selected_cut_06136

theorem unmarked_context_12_21073_185071 : frontier 9 ⟨185071, by decide⟩
    (prefixCache 12 21073) (prefixPartial 12 21073) = false := by
  decide +kernel

theorem node_context_12_21073_185071 : EJMOriginalGlobalDAGData.nodes 9 ⟨185071, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185036, by decide⟩,⟨185059, by decide⟩,⟨185070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21073_185071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21073 ⟨185071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21073
    ⟨185071, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185036, by decide⟩,⟨185059, by decide⟩,⟨185070, by decide⟩]) unmarked_context_12_21073_185071 node_context_12_21073_185071
  intro a
  fin_cases a
  · exact context_13_84292_3444
  · exact context_13_84293_185036
  · exact context_13_84294_185059
  · exact context_13_84295_185070

theorem selected_cut_06137 : selected 9 ⟨185119, by decide⟩
    (prefixPartial 12 21074) = some ⟨12, 2, 0, 185119, 21074, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_21074_185119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21074 ⟨185119, by decide⟩ :=
  accepted_of_selected 12 21074 ⟨185119, by decide⟩ ⟨12, 2, 0, 185119, 21074, 3897, 65536⟩
    (by decide) selected_cut_06137

theorem selected_cut_06138 : selected 9 ⟨185165, by decide⟩
    (prefixPartial 12 21075) = some ⟨12, 2, 0, 185165, 21075, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_21075_185165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21075 ⟨185165, by decide⟩ :=
  accepted_of_selected 12 21075 ⟨185165, by decide⟩ ⟨12, 2, 0, 185165, 21075, 4065, 65536⟩
    (by decide) selected_cut_06138

theorem unmarked_context_11_5268_185166 : frontier 10 ⟨185166, by decide⟩
    (prefixCache 11 5268) (prefixPartial 11 5268) = false := by
  decide +kernel

theorem node_context_11_5268_185166 : EJMOriginalGlobalDAGData.nodes 10 ⟨185166, by decide⟩ =
    .split (coordinate 11) (![⟨185013, by decide⟩,⟨185071, by decide⟩,⟨185119, by decide⟩,⟨185165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5268_185166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5268 ⟨185166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5268
    ⟨185166, by decide⟩ (by decide) (![⟨185013, by decide⟩,⟨185071, by decide⟩,⟨185119, by decide⟩,⟨185165, by decide⟩]) unmarked_context_11_5268_185166 node_context_11_5268_185166
  intro a
  fin_cases a
  · exact context_12_21072_185013
  · exact context_12_21073_185071
  · exact context_12_21074_185119
  · exact context_12_21075_185165

theorem selected_cut_06139 : selected 9 ⟨185201, by decide⟩
    (prefixPartial 12 21076) = some ⟨12, 2, 0, 185201, 21076, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_21076_185201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21076 ⟨185201, by decide⟩ :=
  accepted_of_selected 12 21076 ⟨185201, by decide⟩ ⟨12, 2, 0, 185201, 21076, 2945, 65536⟩
    (by decide) selected_cut_06139

theorem selected_cut_06140 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 21077) = some ⟨12, 1, 0, 170504, 21077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21077_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21077 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 21077 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 21077, 1, 65536⟩
    (by decide) selected_cut_06140

theorem selected_cut_06141 : selected 9 ⟨185249, by decide⟩
    (prefixPartial 12 21078) = some ⟨12, 2, 0, 185249, 21078, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_21078_185249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21078 ⟨185249, by decide⟩ :=
  accepted_of_selected 12 21078 ⟨185249, by decide⟩ ⟨12, 2, 0, 185249, 21078, 3733, 65536⟩
    (by decide) selected_cut_06141

theorem selected_cut_06142 : selected 9 ⟨185300, by decide⟩
    (prefixPartial 12 21079) = some ⟨12, 2, 0, 185300, 21079, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_21079_185300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21079 ⟨185300, by decide⟩ :=
  accepted_of_selected 12 21079 ⟨185300, by decide⟩ ⟨12, 2, 0, 185300, 21079, 4041, 65536⟩
    (by decide) selected_cut_06142

theorem unmarked_context_11_5269_185301 : frontier 10 ⟨185301, by decide⟩
    (prefixCache 11 5269) (prefixPartial 11 5269) = false := by
  decide +kernel

theorem node_context_11_5269_185301 : EJMOriginalGlobalDAGData.nodes 10 ⟨185301, by decide⟩ =
    .split (coordinate 11) (![⟨185201, by decide⟩,⟨170504, by decide⟩,⟨185249, by decide⟩,⟨185300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5269_185301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5269 ⟨185301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5269
    ⟨185301, by decide⟩ (by decide) (![⟨185201, by decide⟩,⟨170504, by decide⟩,⟨185249, by decide⟩,⟨185300, by decide⟩]) unmarked_context_11_5269_185301 node_context_11_5269_185301
  intro a
  fin_cases a
  · exact context_12_21076_185201
  · exact context_12_21077_170504
  · exact context_12_21078_185249
  · exact context_12_21079_185300

theorem selected_cut_06143 : selected 9 ⟨185335, by decide⟩
    (prefixPartial 12 21080) = some ⟨12, 2, 0, 185335, 21080, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_21080_185335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21080 ⟨185335, by decide⟩ :=
  accepted_of_selected 12 21080 ⟨185335, by decide⟩ ⟨12, 2, 0, 185335, 21080, 2693, 65536⟩
    (by decide) selected_cut_06143

theorem selected_cut_06144 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84324) = some ⟨13, 1, 0, 3444, 84324, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84324_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84324 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84324 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84324, 1, 16384⟩
    (by decide) selected_cut_06144

theorem selected_cut_06145 : selected 8 ⟨185358, by decide⟩
    (prefixPartial 13 84325) = some ⟨13, 2, 0, 185358, 84325, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_84325_185358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84325 ⟨185358, by decide⟩ :=
  accepted_of_selected 13 84325 ⟨185358, by decide⟩ ⟨13, 2, 0, 185358, 84325, 1653, 16384⟩
    (by decide) selected_cut_06145

theorem selected_cut_06146 : selected 8 ⟨185386, by decide⟩
    (prefixPartial 13 84326) = some ⟨13, 2, 0, 185386, 84326, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_84326_185386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84326 ⟨185386, by decide⟩ :=
  accepted_of_selected 13 84326 ⟨185386, by decide⟩ ⟨13, 2, 0, 185386, 84326, 2157, 16384⟩
    (by decide) selected_cut_06146

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
