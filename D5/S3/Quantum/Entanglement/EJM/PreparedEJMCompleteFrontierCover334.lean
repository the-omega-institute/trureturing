/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover333
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32068 : selected 8 ⟨823851, by decide⟩
    (prefixPartial 13 431275) = some ⟨13, 2, 0, 823851, 431275, 925, 16384⟩ := by
  decide +kernel

theorem context_13_431275_823851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431275 ⟨823851, by decide⟩ :=
  accepted_of_selected 13 431275 ⟨823851, by decide⟩ ⟨13, 2, 0, 823851, 431275, 925, 16384⟩
    (by decide) selected_cut_32068

theorem unmarked_context_12_107818_823852 : frontier 9 ⟨823852, by decide⟩
    (prefixCache 12 107818) (prefixPartial 12 107818) = false := by
  decide +kernel

theorem node_context_12_107818_823852 : EJMOriginalGlobalDAGData.nodes 9 ⟨823852, by decide⟩ =
    .split (coordinate 12) (![⟨823799, by decide⟩,⟨823819, by decide⟩,⟨823840, by decide⟩,⟨823851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107818_823852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107818 ⟨823852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107818
    ⟨823852, by decide⟩ (by decide) (![⟨823799, by decide⟩,⟨823819, by decide⟩,⟨823840, by decide⟩,⟨823851, by decide⟩]) unmarked_context_12_107818_823852 node_context_12_107818_823852
  intro a
  fin_cases a
  · exact context_13_431272_823799
  · exact context_13_431273_823819
  · exact context_13_431274_823840
  · exact context_13_431275_823851

theorem selected_cut_32069 : selected 8 ⟨823875, by decide⟩
    (prefixPartial 13 431276) = some ⟨13, 2, 0, 823875, 431276, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_431276_823875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431276 ⟨823875, by decide⟩ :=
  accepted_of_selected 13 431276 ⟨823875, by decide⟩ ⟨13, 2, 0, 823875, 431276, 1321, 16384⟩
    (by decide) selected_cut_32069

theorem selected_cut_32070 : selected 8 ⟨823899, by decide⟩
    (prefixPartial 13 431277) = some ⟨13, 2, 0, 823899, 431277, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_431277_823899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431277 ⟨823899, by decide⟩ :=
  accepted_of_selected 13 431277 ⟨823899, by decide⟩ ⟨13, 2, 0, 823899, 431277, 2537, 16384⟩
    (by decide) selected_cut_32070

theorem selected_cut_32071 : selected 8 ⟨823931, by decide⟩
    (prefixPartial 13 431278) = some ⟨13, 2, 0, 823931, 431278, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_431278_823931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431278 ⟨823931, by decide⟩ :=
  accepted_of_selected 13 431278 ⟨823931, by decide⟩ ⟨13, 2, 0, 823931, 431278, 1629, 16384⟩
    (by decide) selected_cut_32071

theorem selected_cut_32072 : selected 8 ⟨823942, by decide⟩
    (prefixPartial 13 431279) = some ⟨13, 2, 0, 823942, 431279, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_431279_823942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431279 ⟨823942, by decide⟩ :=
  accepted_of_selected 13 431279 ⟨823942, by decide⟩ ⟨13, 2, 0, 823942, 431279, 1005, 16384⟩
    (by decide) selected_cut_32072

theorem unmarked_context_12_107819_823943 : frontier 9 ⟨823943, by decide⟩
    (prefixCache 12 107819) (prefixPartial 12 107819) = false := by
  decide +kernel

theorem node_context_12_107819_823943 : EJMOriginalGlobalDAGData.nodes 9 ⟨823943, by decide⟩ =
    .split (coordinate 12) (![⟨823875, by decide⟩,⟨823899, by decide⟩,⟨823931, by decide⟩,⟨823942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107819_823943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107819 ⟨823943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107819
    ⟨823943, by decide⟩ (by decide) (![⟨823875, by decide⟩,⟨823899, by decide⟩,⟨823931, by decide⟩,⟨823942, by decide⟩]) unmarked_context_12_107819_823943 node_context_12_107819_823943
  intro a
  fin_cases a
  · exact context_13_431276_823875
  · exact context_13_431277_823899
  · exact context_13_431278_823931
  · exact context_13_431279_823942

theorem unmarked_context_11_26954_823944 : frontier 10 ⟨823944, by decide⟩
    (prefixCache 11 26954) (prefixPartial 11 26954) = false := by
  decide +kernel

theorem node_context_11_26954_823944 : EJMOriginalGlobalDAGData.nodes 10 ⟨823944, by decide⟩ =
    .split (coordinate 11) (![⟨823712, by decide⟩,⟨823786, by decide⟩,⟨823852, by decide⟩,⟨823943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26954_823944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26954 ⟨823944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26954
    ⟨823944, by decide⟩ (by decide) (![⟨823712, by decide⟩,⟨823786, by decide⟩,⟨823852, by decide⟩,⟨823943, by decide⟩]) unmarked_context_11_26954_823944 node_context_11_26954_823944
  intro a
  fin_cases a
  · exact context_12_107816_823712
  · exact context_12_107817_823786
  · exact context_12_107818_823852
  · exact context_12_107819_823943

theorem selected_cut_32073 : selected 8 ⟨823967, by decide⟩
    (prefixPartial 13 431280) = some ⟨13, 2, 0, 823967, 431280, 961, 16384⟩ := by
  decide +kernel

theorem context_13_431280_823967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431280 ⟨823967, by decide⟩ :=
  accepted_of_selected 13 431280 ⟨823967, by decide⟩ ⟨13, 2, 0, 823967, 431280, 961, 16384⟩
    (by decide) selected_cut_32073

theorem selected_cut_32074 : selected 8 ⟨824018, by decide⟩
    (prefixPartial 13 431281) = some ⟨13, 2, 0, 824018, 431281, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_431281_824018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431281 ⟨824018, by decide⟩ :=
  accepted_of_selected 13 431281 ⟨824018, by decide⟩ ⟨13, 2, 0, 824018, 431281, 3041, 16384⟩
    (by decide) selected_cut_32074

theorem selected_cut_32075 : selected 8 ⟨824052, by decide⟩
    (prefixPartial 13 431282) = some ⟨13, 2, 0, 824052, 431282, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_431282_824052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431282 ⟨824052, by decide⟩ :=
  accepted_of_selected 13 431282 ⟨824052, by decide⟩ ⟨13, 2, 0, 824052, 431282, 1697, 16384⟩
    (by decide) selected_cut_32075

theorem selected_cut_32076 : selected 8 ⟨824061, by decide⟩
    (prefixPartial 13 431283) = some ⟨13, 2, 0, 824061, 431283, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_431283_824061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431283 ⟨824061, by decide⟩ :=
  accepted_of_selected 13 431283 ⟨824061, by decide⟩ ⟨13, 2, 0, 824061, 431283, 1029, 16384⟩
    (by decide) selected_cut_32076

theorem unmarked_context_12_107820_824062 : frontier 9 ⟨824062, by decide⟩
    (prefixCache 12 107820) (prefixPartial 12 107820) = false := by
  decide +kernel

theorem node_context_12_107820_824062 : EJMOriginalGlobalDAGData.nodes 9 ⟨824062, by decide⟩ =
    .split (coordinate 12) (![⟨823967, by decide⟩,⟨824018, by decide⟩,⟨824052, by decide⟩,⟨824061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107820_824062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107820 ⟨824062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107820
    ⟨824062, by decide⟩ (by decide) (![⟨823967, by decide⟩,⟨824018, by decide⟩,⟨824052, by decide⟩,⟨824061, by decide⟩]) unmarked_context_12_107820_824062 node_context_12_107820_824062
  intro a
  fin_cases a
  · exact context_13_431280_823967
  · exact context_13_431281_824018
  · exact context_13_431282_824052
  · exact context_13_431283_824061

theorem selected_cut_32077 : selected 8 ⟨824073, by decide⟩
    (prefixPartial 13 431284) = some ⟨13, 2, 0, 824073, 431284, 997, 16384⟩ := by
  decide +kernel

theorem context_13_431284_824073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431284 ⟨824073, by decide⟩ :=
  accepted_of_selected 13 431284 ⟨824073, by decide⟩ ⟨13, 2, 0, 824073, 431284, 997, 16384⟩
    (by decide) selected_cut_32077

theorem selected_cut_32078 : selected 8 ⟨824104, by decide⟩
    (prefixPartial 13 431285) = some ⟨13, 2, 0, 824104, 431285, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_431285_824104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431285 ⟨824104, by decide⟩ :=
  accepted_of_selected 13 431285 ⟨824104, by decide⟩ ⟨13, 2, 0, 824104, 431285, 2497, 16384⟩
    (by decide) selected_cut_32078

theorem selected_cut_32079 : selected 8 ⟨824136, by decide⟩
    (prefixPartial 13 431286) = some ⟨13, 2, 0, 824136, 431286, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_431286_824136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431286 ⟨824136, by decide⟩ :=
  accepted_of_selected 13 431286 ⟨824136, by decide⟩ ⟨13, 2, 0, 824136, 431286, 1477, 16384⟩
    (by decide) selected_cut_32079

theorem selected_cut_32080 : selected 8 ⟨824145, by decide⟩
    (prefixPartial 13 431287) = some ⟨13, 2, 0, 824145, 431287, 781, 16384⟩ := by
  decide +kernel

theorem context_13_431287_824145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431287 ⟨824145, by decide⟩ :=
  accepted_of_selected 13 431287 ⟨824145, by decide⟩ ⟨13, 2, 0, 824145, 431287, 781, 16384⟩
    (by decide) selected_cut_32080

theorem unmarked_context_12_107821_824146 : frontier 9 ⟨824146, by decide⟩
    (prefixCache 12 107821) (prefixPartial 12 107821) = false := by
  decide +kernel

theorem node_context_12_107821_824146 : EJMOriginalGlobalDAGData.nodes 9 ⟨824146, by decide⟩ =
    .split (coordinate 12) (![⟨824073, by decide⟩,⟨824104, by decide⟩,⟨824136, by decide⟩,⟨824145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107821_824146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107821 ⟨824146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107821
    ⟨824146, by decide⟩ (by decide) (![⟨824073, by decide⟩,⟨824104, by decide⟩,⟨824136, by decide⟩,⟨824145, by decide⟩]) unmarked_context_12_107821_824146 node_context_12_107821_824146
  intro a
  fin_cases a
  · exact context_13_431284_824073
  · exact context_13_431285_824104
  · exact context_13_431286_824136
  · exact context_13_431287_824145

theorem selected_cut_32081 : selected 8 ⟨824159, by decide⟩
    (prefixPartial 13 431288) = some ⟨13, 2, 0, 824159, 431288, 909, 16384⟩ := by
  decide +kernel

theorem context_13_431288_824159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431288 ⟨824159, by decide⟩ :=
  accepted_of_selected 13 431288 ⟨824159, by decide⟩ ⟨13, 2, 0, 824159, 431288, 909, 16384⟩
    (by decide) selected_cut_32081

theorem selected_cut_32082 : selected 8 ⟨824196, by decide⟩
    (prefixPartial 13 431289) = some ⟨13, 2, 0, 824196, 431289, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_431289_824196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431289 ⟨824196, by decide⟩ :=
  accepted_of_selected 13 431289 ⟨824196, by decide⟩ ⟨13, 2, 0, 824196, 431289, 2521, 16384⟩
    (by decide) selected_cut_32082

theorem selected_cut_32083 : selected 8 ⟨824222, by decide⟩
    (prefixPartial 13 431290) = some ⟨13, 2, 0, 824222, 431290, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_431290_824222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431290 ⟨824222, by decide⟩ :=
  accepted_of_selected 13 431290 ⟨824222, by decide⟩ ⟨13, 2, 0, 824222, 431290, 1313, 16384⟩
    (by decide) selected_cut_32083

theorem selected_cut_32084 : selected 8 ⟨824228, by decide⟩
    (prefixPartial 13 431291) = some ⟨13, 2, 0, 824228, 431291, 909, 16384⟩ := by
  decide +kernel

theorem context_13_431291_824228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431291 ⟨824228, by decide⟩ :=
  accepted_of_selected 13 431291 ⟨824228, by decide⟩ ⟨13, 2, 0, 824228, 431291, 909, 16384⟩
    (by decide) selected_cut_32084

theorem unmarked_context_12_107822_824229 : frontier 9 ⟨824229, by decide⟩
    (prefixCache 12 107822) (prefixPartial 12 107822) = false := by
  decide +kernel

theorem node_context_12_107822_824229 : EJMOriginalGlobalDAGData.nodes 9 ⟨824229, by decide⟩ =
    .split (coordinate 12) (![⟨824159, by decide⟩,⟨824196, by decide⟩,⟨824222, by decide⟩,⟨824228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107822_824229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107822 ⟨824229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107822
    ⟨824229, by decide⟩ (by decide) (![⟨824159, by decide⟩,⟨824196, by decide⟩,⟨824222, by decide⟩,⟨824228, by decide⟩]) unmarked_context_12_107822_824229 node_context_12_107822_824229
  intro a
  fin_cases a
  · exact context_13_431288_824159
  · exact context_13_431289_824196
  · exact context_13_431290_824222
  · exact context_13_431291_824228

theorem selected_cut_32085 : selected 8 ⟨824254, by decide⟩
    (prefixPartial 13 431292) = some ⟨13, 2, 0, 824254, 431292, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_431292_824254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431292 ⟨824254, by decide⟩ :=
  accepted_of_selected 13 431292 ⟨824254, by decide⟩ ⟨13, 2, 0, 824254, 431292, 1097, 16384⟩
    (by decide) selected_cut_32085

theorem selected_cut_32086 : selected 8 ⟨824300, by decide⟩
    (prefixPartial 13 431293) = some ⟨13, 2, 0, 824300, 431293, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_431293_824300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431293 ⟨824300, by decide⟩ :=
  accepted_of_selected 13 431293 ⟨824300, by decide⟩ ⟨13, 2, 0, 824300, 431293, 3109, 16384⟩
    (by decide) selected_cut_32086

theorem selected_cut_32087 : selected 8 ⟨824336, by decide⟩
    (prefixPartial 13 431294) = some ⟨13, 2, 0, 824336, 431294, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_431294_824336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431294 ⟨824336, by decide⟩ :=
  accepted_of_selected 13 431294 ⟨824336, by decide⟩ ⟨13, 2, 0, 824336, 431294, 1729, 16384⟩
    (by decide) selected_cut_32087

theorem selected_cut_32088 : selected 8 ⟨824344, by decide⟩
    (prefixPartial 13 431295) = some ⟨13, 2, 0, 824344, 431295, 933, 16384⟩ := by
  decide +kernel

theorem context_13_431295_824344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431295 ⟨824344, by decide⟩ :=
  accepted_of_selected 13 431295 ⟨824344, by decide⟩ ⟨13, 2, 0, 824344, 431295, 933, 16384⟩
    (by decide) selected_cut_32088

theorem unmarked_context_12_107823_824345 : frontier 9 ⟨824345, by decide⟩
    (prefixCache 12 107823) (prefixPartial 12 107823) = false := by
  decide +kernel

theorem node_context_12_107823_824345 : EJMOriginalGlobalDAGData.nodes 9 ⟨824345, by decide⟩ =
    .split (coordinate 12) (![⟨824254, by decide⟩,⟨824300, by decide⟩,⟨824336, by decide⟩,⟨824344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107823_824345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107823 ⟨824345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107823
    ⟨824345, by decide⟩ (by decide) (![⟨824254, by decide⟩,⟨824300, by decide⟩,⟨824336, by decide⟩,⟨824344, by decide⟩]) unmarked_context_12_107823_824345 node_context_12_107823_824345
  intro a
  fin_cases a
  · exact context_13_431292_824254
  · exact context_13_431293_824300
  · exact context_13_431294_824336
  · exact context_13_431295_824344

theorem unmarked_context_11_26955_824346 : frontier 10 ⟨824346, by decide⟩
    (prefixCache 11 26955) (prefixPartial 11 26955) = false := by
  decide +kernel

theorem node_context_11_26955_824346 : EJMOriginalGlobalDAGData.nodes 10 ⟨824346, by decide⟩ =
    .split (coordinate 11) (![⟨824062, by decide⟩,⟨824146, by decide⟩,⟨824229, by decide⟩,⟨824345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26955_824346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26955 ⟨824346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26955
    ⟨824346, by decide⟩ (by decide) (![⟨824062, by decide⟩,⟨824146, by decide⟩,⟨824229, by decide⟩,⟨824345, by decide⟩]) unmarked_context_11_26955_824346 node_context_11_26955_824346
  intro a
  fin_cases a
  · exact context_12_107820_824062
  · exact context_12_107821_824146
  · exact context_12_107822_824229
  · exact context_12_107823_824345

theorem unmarked_context_10_6738_824347 : frontier 11 ⟨824347, by decide⟩
    (prefixCache 10 6738) (prefixPartial 10 6738) = false := by
  decide +kernel

theorem node_context_10_6738_824347 : EJMOriginalGlobalDAGData.nodes 11 ⟨824347, by decide⟩ =
    .split (coordinate 10) (![⟨823346, by decide⟩,⟨823619, by decide⟩,⟨823944, by decide⟩,⟨824346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6738_824347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6738 ⟨824347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6738
    ⟨824347, by decide⟩ (by decide) (![⟨823346, by decide⟩,⟨823619, by decide⟩,⟨823944, by decide⟩,⟨824346, by decide⟩]) unmarked_context_10_6738_824347 node_context_10_6738_824347
  intro a
  fin_cases a
  · exact context_11_26952_823346
  · exact context_11_26953_823619
  · exact context_11_26954_823944
  · exact context_11_26955_824346

theorem selected_cut_32089 : selected 8 ⟨824360, by decide⟩
    (prefixPartial 13 431296) = some ⟨13, 2, 0, 824360, 431296, 873, 16384⟩ := by
  decide +kernel

theorem context_13_431296_824360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431296 ⟨824360, by decide⟩ :=
  accepted_of_selected 13 431296 ⟨824360, by decide⟩ ⟨13, 2, 0, 824360, 431296, 873, 16384⟩
    (by decide) selected_cut_32089

theorem selected_cut_32090 : selected 8 ⟨824394, by decide⟩
    (prefixPartial 13 431297) = some ⟨13, 2, 0, 824394, 431297, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_431297_824394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431297 ⟨824394, by decide⟩ :=
  accepted_of_selected 13 431297 ⟨824394, by decide⟩ ⟨13, 2, 0, 824394, 431297, 2833, 16384⟩
    (by decide) selected_cut_32090

theorem selected_cut_32091 : selected 8 ⟨824424, by decide⟩
    (prefixPartial 13 431298) = some ⟨13, 2, 0, 824424, 431298, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_431298_824424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431298 ⟨824424, by decide⟩ :=
  accepted_of_selected 13 431298 ⟨824424, by decide⟩ ⟨13, 2, 0, 824424, 431298, 1505, 16384⟩
    (by decide) selected_cut_32091

theorem selected_cut_32092 : selected 8 ⟨824432, by decide⟩
    (prefixPartial 13 431299) = some ⟨13, 2, 0, 824432, 431299, 881, 16384⟩ := by
  decide +kernel

theorem context_13_431299_824432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431299 ⟨824432, by decide⟩ :=
  accepted_of_selected 13 431299 ⟨824432, by decide⟩ ⟨13, 2, 0, 824432, 431299, 881, 16384⟩
    (by decide) selected_cut_32092

theorem unmarked_context_12_107824_824433 : frontier 9 ⟨824433, by decide⟩
    (prefixCache 12 107824) (prefixPartial 12 107824) = false := by
  decide +kernel

theorem node_context_12_107824_824433 : EJMOriginalGlobalDAGData.nodes 9 ⟨824433, by decide⟩ =
    .split (coordinate 12) (![⟨824360, by decide⟩,⟨824394, by decide⟩,⟨824424, by decide⟩,⟨824432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107824_824433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107824 ⟨824433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107824
    ⟨824433, by decide⟩ (by decide) (![⟨824360, by decide⟩,⟨824394, by decide⟩,⟨824424, by decide⟩,⟨824432, by decide⟩]) unmarked_context_12_107824_824433 node_context_12_107824_824433
  intro a
  fin_cases a
  · exact context_13_431296_824360
  · exact context_13_431297_824394
  · exact context_13_431298_824424
  · exact context_13_431299_824432

theorem selected_cut_32093 : selected 8 ⟨824447, by decide⟩
    (prefixPartial 13 431300) = some ⟨13, 2, 0, 824447, 431300, 829, 16384⟩ := by
  decide +kernel

theorem context_13_431300_824447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431300 ⟨824447, by decide⟩ :=
  accepted_of_selected 13 431300 ⟨824447, by decide⟩ ⟨13, 2, 0, 824447, 431300, 829, 16384⟩
    (by decide) selected_cut_32093

theorem selected_cut_32094 : selected 8 ⟨824477, by decide⟩
    (prefixPartial 13 431301) = some ⟨13, 2, 0, 824477, 431301, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_431301_824477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431301 ⟨824477, by decide⟩ :=
  accepted_of_selected 13 431301 ⟨824477, by decide⟩ ⟨13, 2, 0, 824477, 431301, 2533, 16384⟩
    (by decide) selected_cut_32094

theorem selected_cut_32095 : selected 8 ⟨824496, by decide⟩
    (prefixPartial 13 431302) = some ⟨13, 2, 0, 824496, 431302, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_431302_824496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431302 ⟨824496, by decide⟩ :=
  accepted_of_selected 13 431302 ⟨824496, by decide⟩ ⟨13, 2, 0, 824496, 431302, 1237, 16384⟩
    (by decide) selected_cut_32095

theorem selected_cut_32096 : selected 8 ⟨824502, by decide⟩
    (prefixPartial 13 431303) = some ⟨13, 2, 0, 824502, 431303, 745, 16384⟩ := by
  decide +kernel

theorem context_13_431303_824502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431303 ⟨824502, by decide⟩ :=
  accepted_of_selected 13 431303 ⟨824502, by decide⟩ ⟨13, 2, 0, 824502, 431303, 745, 16384⟩
    (by decide) selected_cut_32096

theorem unmarked_context_12_107825_824503 : frontier 9 ⟨824503, by decide⟩
    (prefixCache 12 107825) (prefixPartial 12 107825) = false := by
  decide +kernel

theorem node_context_12_107825_824503 : EJMOriginalGlobalDAGData.nodes 9 ⟨824503, by decide⟩ =
    .split (coordinate 12) (![⟨824447, by decide⟩,⟨824477, by decide⟩,⟨824496, by decide⟩,⟨824502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107825_824503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107825 ⟨824503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107825
    ⟨824503, by decide⟩ (by decide) (![⟨824447, by decide⟩,⟨824477, by decide⟩,⟨824496, by decide⟩,⟨824502, by decide⟩]) unmarked_context_12_107825_824503 node_context_12_107825_824503
  intro a
  fin_cases a
  · exact context_13_431300_824447
  · exact context_13_431301_824477
  · exact context_13_431302_824496
  · exact context_13_431303_824502

theorem selected_cut_32097 : selected 8 ⟨824515, by decide⟩
    (prefixPartial 13 431304) = some ⟨13, 2, 0, 824515, 431304, 745, 16384⟩ := by
  decide +kernel

theorem context_13_431304_824515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431304 ⟨824515, by decide⟩ :=
  accepted_of_selected 13 431304 ⟨824515, by decide⟩ ⟨13, 2, 0, 824515, 431304, 745, 16384⟩
    (by decide) selected_cut_32097

theorem selected_cut_32098 : selected 8 ⟨824539, by decide⟩
    (prefixPartial 13 431305) = some ⟨13, 2, 0, 824539, 431305, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_431305_824539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431305 ⟨824539, by decide⟩ :=
  accepted_of_selected 13 431305 ⟨824539, by decide⟩ ⟨13, 2, 0, 824539, 431305, 2493, 16384⟩
    (by decide) selected_cut_32098

theorem selected_cut_32099 : selected 8 ⟨824558, by decide⟩
    (prefixPartial 13 431306) = some ⟨13, 2, 0, 824558, 431306, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_431306_824558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431306 ⟨824558, by decide⟩ :=
  accepted_of_selected 13 431306 ⟨824558, by decide⟩ ⟨13, 2, 0, 824558, 431306, 1185, 16384⟩
    (by decide) selected_cut_32099

theorem selected_cut_32100 : selected 8 ⟨824566, by decide⟩
    (prefixPartial 13 431307) = some ⟨13, 2, 0, 824566, 431307, 853, 16384⟩ := by
  decide +kernel

theorem context_13_431307_824566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431307 ⟨824566, by decide⟩ :=
  accepted_of_selected 13 431307 ⟨824566, by decide⟩ ⟨13, 2, 0, 824566, 431307, 853, 16384⟩
    (by decide) selected_cut_32100

theorem unmarked_context_12_107826_824567 : frontier 9 ⟨824567, by decide⟩
    (prefixCache 12 107826) (prefixPartial 12 107826) = false := by
  decide +kernel

theorem node_context_12_107826_824567 : EJMOriginalGlobalDAGData.nodes 9 ⟨824567, by decide⟩ =
    .split (coordinate 12) (![⟨824515, by decide⟩,⟨824539, by decide⟩,⟨824558, by decide⟩,⟨824566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107826_824567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107826 ⟨824567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107826
    ⟨824567, by decide⟩ (by decide) (![⟨824515, by decide⟩,⟨824539, by decide⟩,⟨824558, by decide⟩,⟨824566, by decide⟩]) unmarked_context_12_107826_824567 node_context_12_107826_824567
  intro a
  fin_cases a
  · exact context_13_431304_824515
  · exact context_13_431305_824539
  · exact context_13_431306_824558
  · exact context_13_431307_824566

theorem selected_cut_32101 : selected 8 ⟨824586, by decide⟩
    (prefixPartial 13 431308) = some ⟨13, 2, 0, 824586, 431308, 961, 16384⟩ := by
  decide +kernel

theorem context_13_431308_824586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431308 ⟨824586, by decide⟩ :=
  accepted_of_selected 13 431308 ⟨824586, by decide⟩ ⟨13, 2, 0, 824586, 431308, 961, 16384⟩
    (by decide) selected_cut_32101

theorem selected_cut_32102 : selected 8 ⟨824633, by decide⟩
    (prefixPartial 13 431309) = some ⟨13, 2, 0, 824633, 431309, 3329, 16384⟩ := by
  decide +kernel

theorem context_13_431309_824633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431309 ⟨824633, by decide⟩ :=
  accepted_of_selected 13 431309 ⟨824633, by decide⟩ ⟨13, 2, 0, 824633, 431309, 3329, 16384⟩
    (by decide) selected_cut_32102

theorem selected_cut_32103 : selected 8 ⟨824658, by decide⟩
    (prefixPartial 13 431310) = some ⟨13, 2, 0, 824658, 431310, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_431310_824658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431310 ⟨824658, by decide⟩ :=
  accepted_of_selected 13 431310 ⟨824658, by decide⟩ ⟨13, 2, 0, 824658, 431310, 1457, 16384⟩
    (by decide) selected_cut_32103

theorem selected_cut_32104 : selected 8 ⟨824666, by decide⟩
    (prefixPartial 13 431311) = some ⟨13, 2, 0, 824666, 431311, 845, 16384⟩ := by
  decide +kernel

theorem context_13_431311_824666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431311 ⟨824666, by decide⟩ :=
  accepted_of_selected 13 431311 ⟨824666, by decide⟩ ⟨13, 2, 0, 824666, 431311, 845, 16384⟩
    (by decide) selected_cut_32104

theorem unmarked_context_12_107827_824667 : frontier 9 ⟨824667, by decide⟩
    (prefixCache 12 107827) (prefixPartial 12 107827) = false := by
  decide +kernel

theorem node_context_12_107827_824667 : EJMOriginalGlobalDAGData.nodes 9 ⟨824667, by decide⟩ =
    .split (coordinate 12) (![⟨824586, by decide⟩,⟨824633, by decide⟩,⟨824658, by decide⟩,⟨824666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107827_824667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107827 ⟨824667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107827
    ⟨824667, by decide⟩ (by decide) (![⟨824586, by decide⟩,⟨824633, by decide⟩,⟨824658, by decide⟩,⟨824666, by decide⟩]) unmarked_context_12_107827_824667 node_context_12_107827_824667
  intro a
  fin_cases a
  · exact context_13_431308_824586
  · exact context_13_431309_824633
  · exact context_13_431310_824658
  · exact context_13_431311_824666

theorem unmarked_context_11_26956_824668 : frontier 10 ⟨824668, by decide⟩
    (prefixCache 11 26956) (prefixPartial 11 26956) = false := by
  decide +kernel

theorem node_context_11_26956_824668 : EJMOriginalGlobalDAGData.nodes 10 ⟨824668, by decide⟩ =
    .split (coordinate 11) (![⟨824433, by decide⟩,⟨824503, by decide⟩,⟨824567, by decide⟩,⟨824667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26956_824668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26956 ⟨824668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26956
    ⟨824668, by decide⟩ (by decide) (![⟨824433, by decide⟩,⟨824503, by decide⟩,⟨824567, by decide⟩,⟨824667, by decide⟩]) unmarked_context_11_26956_824668 node_context_11_26956_824668
  intro a
  fin_cases a
  · exact context_12_107824_824433
  · exact context_12_107825_824503
  · exact context_12_107826_824567
  · exact context_12_107827_824667

theorem selected_cut_32105 : selected 8 ⟨824677, by decide⟩
    (prefixPartial 13 431312) = some ⟨13, 2, 0, 824677, 431312, 589, 16384⟩ := by
  decide +kernel

theorem context_13_431312_824677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431312 ⟨824677, by decide⟩ :=
  accepted_of_selected 13 431312 ⟨824677, by decide⟩ ⟨13, 2, 0, 824677, 431312, 589, 16384⟩
    (by decide) selected_cut_32105

theorem selected_cut_32106 : selected 8 ⟨824714, by decide⟩
    (prefixPartial 13 431313) = some ⟨13, 2, 0, 824714, 431313, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_431313_824714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431313 ⟨824714, by decide⟩ :=
  accepted_of_selected 13 431313 ⟨824714, by decide⟩ ⟨13, 2, 0, 824714, 431313, 2529, 16384⟩
    (by decide) selected_cut_32106

theorem selected_cut_32107 : selected 8 ⟨824735, by decide⟩
    (prefixPartial 13 431314) = some ⟨13, 2, 0, 824735, 431314, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_431314_824735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431314 ⟨824735, by decide⟩ :=
  accepted_of_selected 13 431314 ⟨824735, by decide⟩ ⟨13, 2, 0, 824735, 431314, 1389, 16384⟩
    (by decide) selected_cut_32107

theorem selected_cut_32108 : selected 8 ⟨824742, by decide⟩
    (prefixPartial 13 431315) = some ⟨13, 2, 0, 824742, 431315, 821, 16384⟩ := by
  decide +kernel

theorem context_13_431315_824742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431315 ⟨824742, by decide⟩ :=
  accepted_of_selected 13 431315 ⟨824742, by decide⟩ ⟨13, 2, 0, 824742, 431315, 821, 16384⟩
    (by decide) selected_cut_32108

theorem unmarked_context_12_107828_824743 : frontier 9 ⟨824743, by decide⟩
    (prefixCache 12 107828) (prefixPartial 12 107828) = false := by
  decide +kernel

theorem node_context_12_107828_824743 : EJMOriginalGlobalDAGData.nodes 9 ⟨824743, by decide⟩ =
    .split (coordinate 12) (![⟨824677, by decide⟩,⟨824714, by decide⟩,⟨824735, by decide⟩,⟨824742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107828_824743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107828 ⟨824743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107828
    ⟨824743, by decide⟩ (by decide) (![⟨824677, by decide⟩,⟨824714, by decide⟩,⟨824735, by decide⟩,⟨824742, by decide⟩]) unmarked_context_12_107828_824743 node_context_12_107828_824743
  intro a
  fin_cases a
  · exact context_13_431312_824677
  · exact context_13_431313_824714
  · exact context_13_431314_824735
  · exact context_13_431315_824742

theorem selected_cut_32109 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 107829) = some ⟨12, 1, 0, 689956, 107829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107829_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107829 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 107829 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 107829, 1, 65536⟩
    (by decide) selected_cut_32109

theorem selected_cut_32110 : selected 8 ⟨824754, by decide⟩
    (prefixPartial 13 431320) = some ⟨13, 2, 0, 824754, 431320, 521, 16384⟩ := by
  decide +kernel

theorem context_13_431320_824754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431320 ⟨824754, by decide⟩ :=
  accepted_of_selected 13 431320 ⟨824754, by decide⟩ ⟨13, 2, 0, 824754, 431320, 521, 16384⟩
    (by decide) selected_cut_32110

theorem selected_cut_32111 : selected 8 ⟨824778, by decide⟩
    (prefixPartial 13 431321) = some ⟨13, 2, 0, 824778, 431321, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_431321_824778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431321 ⟨824778, by decide⟩ :=
  accepted_of_selected 13 431321 ⟨824778, by decide⟩ ⟨13, 2, 0, 824778, 431321, 2053, 16384⟩
    (by decide) selected_cut_32111

theorem selected_cut_32112 : selected 8 ⟨824796, by decide⟩
    (prefixPartial 13 431322) = some ⟨13, 2, 0, 824796, 431322, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_431322_824796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431322 ⟨824796, by decide⟩ :=
  accepted_of_selected 13 431322 ⟨824796, by decide⟩ ⟨13, 2, 0, 824796, 431322, 1021, 16384⟩
    (by decide) selected_cut_32112

theorem selected_cut_32113 : selected 8 ⟨824802, by decide⟩
    (prefixPartial 13 431323) = some ⟨13, 2, 0, 824802, 431323, 741, 16384⟩ := by
  decide +kernel

theorem context_13_431323_824802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431323 ⟨824802, by decide⟩ :=
  accepted_of_selected 13 431323 ⟨824802, by decide⟩ ⟨13, 2, 0, 824802, 431323, 741, 16384⟩
    (by decide) selected_cut_32113

theorem unmarked_context_12_107830_824803 : frontier 9 ⟨824803, by decide⟩
    (prefixCache 12 107830) (prefixPartial 12 107830) = false := by
  decide +kernel

theorem node_context_12_107830_824803 : EJMOriginalGlobalDAGData.nodes 9 ⟨824803, by decide⟩ =
    .split (coordinate 12) (![⟨824754, by decide⟩,⟨824778, by decide⟩,⟨824796, by decide⟩,⟨824802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107830_824803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107830 ⟨824803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107830
    ⟨824803, by decide⟩ (by decide) (![⟨824754, by decide⟩,⟨824778, by decide⟩,⟨824796, by decide⟩,⟨824802, by decide⟩]) unmarked_context_12_107830_824803 node_context_12_107830_824803
  intro a
  fin_cases a
  · exact context_13_431320_824754
  · exact context_13_431321_824778
  · exact context_13_431322_824796
  · exact context_13_431323_824802

theorem selected_cut_32114 : selected 8 ⟨824819, by decide⟩
    (prefixPartial 13 431324) = some ⟨13, 2, 0, 824819, 431324, 673, 16384⟩ := by
  decide +kernel

theorem context_13_431324_824819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431324 ⟨824819, by decide⟩ :=
  accepted_of_selected 13 431324 ⟨824819, by decide⟩ ⟨13, 2, 0, 824819, 431324, 673, 16384⟩
    (by decide) selected_cut_32114

theorem selected_cut_32115 : selected 8 ⟨824880, by decide⟩
    (prefixPartial 13 431325) = some ⟨13, 2, 0, 824880, 431325, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_431325_824880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431325 ⟨824880, by decide⟩ :=
  accepted_of_selected 13 431325 ⟨824880, by decide⟩ ⟨13, 2, 0, 824880, 431325, 3009, 16384⟩
    (by decide) selected_cut_32115

theorem selected_cut_32116 : selected 8 ⟨824923, by decide⟩
    (prefixPartial 13 431326) = some ⟨13, 2, 0, 824923, 431326, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_431326_824923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431326 ⟨824923, by decide⟩ :=
  accepted_of_selected 13 431326 ⟨824923, by decide⟩ ⟨13, 2, 0, 824923, 431326, 1449, 16384⟩
    (by decide) selected_cut_32116

theorem selected_cut_32117 : selected 8 ⟨824930, by decide⟩
    (prefixPartial 13 431327) = some ⟨13, 2, 0, 824930, 431327, 705, 16384⟩ := by
  decide +kernel

theorem context_13_431327_824930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431327 ⟨824930, by decide⟩ :=
  accepted_of_selected 13 431327 ⟨824930, by decide⟩ ⟨13, 2, 0, 824930, 431327, 705, 16384⟩
    (by decide) selected_cut_32117

theorem unmarked_context_12_107831_824931 : frontier 9 ⟨824931, by decide⟩
    (prefixCache 12 107831) (prefixPartial 12 107831) = false := by
  decide +kernel

theorem node_context_12_107831_824931 : EJMOriginalGlobalDAGData.nodes 9 ⟨824931, by decide⟩ =
    .split (coordinate 12) (![⟨824819, by decide⟩,⟨824880, by decide⟩,⟨824923, by decide⟩,⟨824930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107831_824931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107831 ⟨824931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107831
    ⟨824931, by decide⟩ (by decide) (![⟨824819, by decide⟩,⟨824880, by decide⟩,⟨824923, by decide⟩,⟨824930, by decide⟩]) unmarked_context_12_107831_824931 node_context_12_107831_824931
  intro a
  fin_cases a
  · exact context_13_431324_824819
  · exact context_13_431325_824880
  · exact context_13_431326_824923
  · exact context_13_431327_824930

theorem unmarked_context_11_26957_824932 : frontier 10 ⟨824932, by decide⟩
    (prefixCache 11 26957) (prefixPartial 11 26957) = false := by
  decide +kernel

theorem node_context_11_26957_824932 : EJMOriginalGlobalDAGData.nodes 10 ⟨824932, by decide⟩ =
    .split (coordinate 11) (![⟨824743, by decide⟩,⟨689956, by decide⟩,⟨824803, by decide⟩,⟨824931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26957_824932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26957 ⟨824932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26957
    ⟨824932, by decide⟩ (by decide) (![⟨824743, by decide⟩,⟨689956, by decide⟩,⟨824803, by decide⟩,⟨824931, by decide⟩]) unmarked_context_11_26957_824932 node_context_11_26957_824932
  intro a
  fin_cases a
  · exact context_12_107828_824743
  · exact context_12_107829_689956
  · exact context_12_107830_824803
  · exact context_12_107831_824931

theorem selected_cut_32118 : selected 8 ⟨824941, by decide⟩
    (prefixPartial 13 431328) = some ⟨13, 2, 0, 824941, 431328, 417, 16384⟩ := by
  decide +kernel

theorem context_13_431328_824941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431328 ⟨824941, by decide⟩ :=
  accepted_of_selected 13 431328 ⟨824941, by decide⟩ ⟨13, 2, 0, 824941, 431328, 417, 16384⟩
    (by decide) selected_cut_32118

theorem selected_cut_32119 : selected 8 ⟨824982, by decide⟩
    (prefixPartial 13 431329) = some ⟨13, 2, 0, 824982, 431329, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_431329_824982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431329 ⟨824982, by decide⟩ :=
  accepted_of_selected 13 431329 ⟨824982, by decide⟩ ⟨13, 2, 0, 824982, 431329, 2733, 16384⟩
    (by decide) selected_cut_32119

theorem selected_cut_32120 : selected 8 ⟨825033, by decide⟩
    (prefixPartial 13 431330) = some ⟨13, 2, 0, 825033, 431330, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_431330_825033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431330 ⟨825033, by decide⟩ :=
  accepted_of_selected 13 431330 ⟨825033, by decide⟩ ⟨13, 2, 0, 825033, 431330, 1841, 16384⟩
    (by decide) selected_cut_32120

theorem selected_cut_32121 : selected 8 ⟨825046, by decide⟩
    (prefixPartial 13 431331) = some ⟨13, 2, 0, 825046, 431331, 993, 16384⟩ := by
  decide +kernel

theorem context_13_431331_825046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431331 ⟨825046, by decide⟩ :=
  accepted_of_selected 13 431331 ⟨825046, by decide⟩ ⟨13, 2, 0, 825046, 431331, 993, 16384⟩
    (by decide) selected_cut_32121

theorem unmarked_context_12_107832_825047 : frontier 9 ⟨825047, by decide⟩
    (prefixCache 12 107832) (prefixPartial 12 107832) = false := by
  decide +kernel

theorem node_context_12_107832_825047 : EJMOriginalGlobalDAGData.nodes 9 ⟨825047, by decide⟩ =
    .split (coordinate 12) (![⟨824941, by decide⟩,⟨824982, by decide⟩,⟨825033, by decide⟩,⟨825046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107832_825047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107832 ⟨825047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107832
    ⟨825047, by decide⟩ (by decide) (![⟨824941, by decide⟩,⟨824982, by decide⟩,⟨825033, by decide⟩,⟨825046, by decide⟩]) unmarked_context_12_107832_825047 node_context_12_107832_825047
  intro a
  fin_cases a
  · exact context_13_431328_824941
  · exact context_13_431329_824982
  · exact context_13_431330_825033
  · exact context_13_431331_825046

theorem selected_cut_32122 : selected 8 ⟨825053, by decide⟩
    (prefixPartial 13 431332) = some ⟨13, 2, 0, 825053, 431332, 453, 16384⟩ := by
  decide +kernel

theorem context_13_431332_825053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431332 ⟨825053, by decide⟩ :=
  accepted_of_selected 13 431332 ⟨825053, by decide⟩ ⟨13, 2, 0, 825053, 431332, 453, 16384⟩
    (by decide) selected_cut_32122

theorem selected_cut_32123 : selected 8 ⟨825080, by decide⟩
    (prefixPartial 13 431333) = some ⟨13, 2, 0, 825080, 431333, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_431333_825080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431333 ⟨825080, by decide⟩ :=
  accepted_of_selected 13 431333 ⟨825080, by decide⟩ ⟨13, 2, 0, 825080, 431333, 2257, 16384⟩
    (by decide) selected_cut_32123

theorem selected_cut_32124 : selected 8 ⟨825108, by decide⟩
    (prefixPartial 13 431334) = some ⟨13, 2, 0, 825108, 431334, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_431334_825108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431334 ⟨825108, by decide⟩ :=
  accepted_of_selected 13 431334 ⟨825108, by decide⟩ ⟨13, 2, 0, 825108, 431334, 1553, 16384⟩
    (by decide) selected_cut_32124

theorem selected_cut_32125 : selected 8 ⟨825114, by decide⟩
    (prefixPartial 13 431335) = some ⟨13, 2, 0, 825114, 431335, 861, 16384⟩ := by
  decide +kernel

theorem context_13_431335_825114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431335 ⟨825114, by decide⟩ :=
  accepted_of_selected 13 431335 ⟨825114, by decide⟩ ⟨13, 2, 0, 825114, 431335, 861, 16384⟩
    (by decide) selected_cut_32125

theorem unmarked_context_12_107833_825115 : frontier 9 ⟨825115, by decide⟩
    (prefixCache 12 107833) (prefixPartial 12 107833) = false := by
  decide +kernel

theorem node_context_12_107833_825115 : EJMOriginalGlobalDAGData.nodes 9 ⟨825115, by decide⟩ =
    .split (coordinate 12) (![⟨825053, by decide⟩,⟨825080, by decide⟩,⟨825108, by decide⟩,⟨825114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107833_825115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107833 ⟨825115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107833
    ⟨825115, by decide⟩ (by decide) (![⟨825053, by decide⟩,⟨825080, by decide⟩,⟨825108, by decide⟩,⟨825114, by decide⟩]) unmarked_context_12_107833_825115 node_context_12_107833_825115
  intro a
  fin_cases a
  · exact context_13_431332_825053
  · exact context_13_431333_825080
  · exact context_13_431334_825108
  · exact context_13_431335_825114

theorem selected_cut_32126 : selected 8 ⟨825120, by decide⟩
    (prefixPartial 13 431336) = some ⟨13, 2, 0, 825120, 431336, 297, 16384⟩ := by
  decide +kernel

theorem context_13_431336_825120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431336 ⟨825120, by decide⟩ :=
  accepted_of_selected 13 431336 ⟨825120, by decide⟩ ⟨13, 2, 0, 825120, 431336, 297, 16384⟩
    (by decide) selected_cut_32126

theorem selected_cut_32127 : selected 8 ⟨825147, by decide⟩
    (prefixPartial 13 431337) = some ⟨13, 2, 0, 825147, 431337, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_431337_825147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431337 ⟨825147, by decide⟩ :=
  accepted_of_selected 13 431337 ⟨825147, by decide⟩ ⟨13, 2, 0, 825147, 431337, 2201, 16384⟩
    (by decide) selected_cut_32127

theorem selected_cut_32128 : selected 8 ⟨825171, by decide⟩
    (prefixPartial 13 431338) = some ⟨13, 2, 0, 825171, 431338, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_431338_825171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431338 ⟨825171, by decide⟩ :=
  accepted_of_selected 13 431338 ⟨825171, by decide⟩ ⟨13, 2, 0, 825171, 431338, 1365, 16384⟩
    (by decide) selected_cut_32128

theorem selected_cut_32129 : selected 8 ⟨825180, by decide⟩
    (prefixPartial 13 431339) = some ⟨13, 2, 0, 825180, 431339, 853, 16384⟩ := by
  decide +kernel

theorem context_13_431339_825180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431339 ⟨825180, by decide⟩ :=
  accepted_of_selected 13 431339 ⟨825180, by decide⟩ ⟨13, 2, 0, 825180, 431339, 853, 16384⟩
    (by decide) selected_cut_32129

theorem unmarked_context_12_107834_825181 : frontier 9 ⟨825181, by decide⟩
    (prefixCache 12 107834) (prefixPartial 12 107834) = false := by
  decide +kernel

theorem node_context_12_107834_825181 : EJMOriginalGlobalDAGData.nodes 9 ⟨825181, by decide⟩ =
    .split (coordinate 12) (![⟨825120, by decide⟩,⟨825147, by decide⟩,⟨825171, by decide⟩,⟨825180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107834_825181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107834 ⟨825181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107834
    ⟨825181, by decide⟩ (by decide) (![⟨825120, by decide⟩,⟨825147, by decide⟩,⟨825171, by decide⟩,⟨825180, by decide⟩]) unmarked_context_12_107834_825181 node_context_12_107834_825181
  intro a
  fin_cases a
  · exact context_13_431336_825120
  · exact context_13_431337_825147
  · exact context_13_431338_825171
  · exact context_13_431339_825180

theorem selected_cut_32130 : selected 8 ⟨825189, by decide⟩
    (prefixPartial 13 431340) = some ⟨13, 2, 0, 825189, 431340, 349, 16384⟩ := by
  decide +kernel

theorem context_13_431340_825189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431340 ⟨825189, by decide⟩ :=
  accepted_of_selected 13 431340 ⟨825189, by decide⟩ ⟨13, 2, 0, 825189, 431340, 349, 16384⟩
    (by decide) selected_cut_32130

theorem selected_cut_32131 : selected 8 ⟨825223, by decide⟩
    (prefixPartial 13 431341) = some ⟨13, 2, 0, 825223, 431341, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_431341_825223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431341 ⟨825223, by decide⟩ :=
  accepted_of_selected 13 431341 ⟨825223, by decide⟩ ⟨13, 2, 0, 825223, 431341, 3085, 16384⟩
    (by decide) selected_cut_32131

theorem selected_cut_32132 : selected 8 ⟨825253, by decide⟩
    (prefixPartial 13 431342) = some ⟨13, 2, 0, 825253, 431342, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_431342_825253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431342 ⟨825253, by decide⟩ :=
  accepted_of_selected 13 431342 ⟨825253, by decide⟩ ⟨13, 2, 0, 825253, 431342, 1765, 16384⟩
    (by decide) selected_cut_32132

theorem selected_cut_32133 : selected 8 ⟨825263, by decide⟩
    (prefixPartial 13 431343) = some ⟨13, 2, 0, 825263, 431343, 877, 16384⟩ := by
  decide +kernel

theorem context_13_431343_825263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431343 ⟨825263, by decide⟩ :=
  accepted_of_selected 13 431343 ⟨825263, by decide⟩ ⟨13, 2, 0, 825263, 431343, 877, 16384⟩
    (by decide) selected_cut_32133

theorem unmarked_context_12_107835_825264 : frontier 9 ⟨825264, by decide⟩
    (prefixCache 12 107835) (prefixPartial 12 107835) = false := by
  decide +kernel

theorem node_context_12_107835_825264 : EJMOriginalGlobalDAGData.nodes 9 ⟨825264, by decide⟩ =
    .split (coordinate 12) (![⟨825189, by decide⟩,⟨825223, by decide⟩,⟨825253, by decide⟩,⟨825263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107835_825264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107835 ⟨825264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107835
    ⟨825264, by decide⟩ (by decide) (![⟨825189, by decide⟩,⟨825223, by decide⟩,⟨825253, by decide⟩,⟨825263, by decide⟩]) unmarked_context_12_107835_825264 node_context_12_107835_825264
  intro a
  fin_cases a
  · exact context_13_431340_825189
  · exact context_13_431341_825223
  · exact context_13_431342_825253
  · exact context_13_431343_825263

theorem unmarked_context_11_26958_825265 : frontier 10 ⟨825265, by decide⟩
    (prefixCache 11 26958) (prefixPartial 11 26958) = false := by
  decide +kernel

theorem node_context_11_26958_825265 : EJMOriginalGlobalDAGData.nodes 10 ⟨825265, by decide⟩ =
    .split (coordinate 11) (![⟨825047, by decide⟩,⟨825115, by decide⟩,⟨825181, by decide⟩,⟨825264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26958_825265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26958 ⟨825265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26958
    ⟨825265, by decide⟩ (by decide) (![⟨825047, by decide⟩,⟨825115, by decide⟩,⟨825181, by decide⟩,⟨825264, by decide⟩]) unmarked_context_11_26958_825265 node_context_11_26958_825265
  intro a
  fin_cases a
  · exact context_12_107832_825047
  · exact context_12_107833_825115
  · exact context_12_107834_825181
  · exact context_12_107835_825264

theorem selected_cut_32134 : selected 8 ⟨825271, by decide⟩
    (prefixPartial 13 431344) = some ⟨13, 2, 0, 825271, 431344, 173, 16384⟩ := by
  decide +kernel

theorem context_13_431344_825271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431344 ⟨825271, by decide⟩ :=
  accepted_of_selected 13 431344 ⟨825271, by decide⟩ ⟨13, 2, 0, 825271, 431344, 173, 16384⟩
    (by decide) selected_cut_32134

theorem selected_cut_32135 : selected 8 ⟨825333, by decide⟩
    (prefixPartial 13 431345) = some ⟨13, 2, 0, 825333, 431345, 3197, 16384⟩ := by
  decide +kernel

theorem context_13_431345_825333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431345 ⟨825333, by decide⟩ :=
  accepted_of_selected 13 431345 ⟨825333, by decide⟩ ⟨13, 2, 0, 825333, 431345, 3197, 16384⟩
    (by decide) selected_cut_32135

theorem selected_cut_32136 : selected 8 ⟨825360, by decide⟩
    (prefixPartial 13 431346) = some ⟨13, 2, 0, 825360, 431346, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_431346_825360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431346 ⟨825360, by decide⟩ :=
  accepted_of_selected 13 431346 ⟨825360, by decide⟩ ⟨13, 2, 0, 825360, 431346, 1601, 16384⟩
    (by decide) selected_cut_32136

theorem selected_cut_32137 : selected 8 ⟨825367, by decide⟩
    (prefixPartial 13 431347) = some ⟨13, 2, 0, 825367, 431347, 897, 16384⟩ := by
  decide +kernel

theorem context_13_431347_825367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431347 ⟨825367, by decide⟩ :=
  accepted_of_selected 13 431347 ⟨825367, by decide⟩ ⟨13, 2, 0, 825367, 431347, 897, 16384⟩
    (by decide) selected_cut_32137

theorem unmarked_context_12_107836_825368 : frontier 9 ⟨825368, by decide⟩
    (prefixCache 12 107836) (prefixPartial 12 107836) = false := by
  decide +kernel

theorem node_context_12_107836_825368 : EJMOriginalGlobalDAGData.nodes 9 ⟨825368, by decide⟩ =
    .split (coordinate 12) (![⟨825271, by decide⟩,⟨825333, by decide⟩,⟨825360, by decide⟩,⟨825367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107836_825368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107836 ⟨825368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107836
    ⟨825368, by decide⟩ (by decide) (![⟨825271, by decide⟩,⟨825333, by decide⟩,⟨825360, by decide⟩,⟨825367, by decide⟩]) unmarked_context_12_107836_825368 node_context_12_107836_825368
  intro a
  fin_cases a
  · exact context_13_431344_825271
  · exact context_13_431345_825333
  · exact context_13_431346_825360
  · exact context_13_431347_825367

theorem selected_cut_32138 : selected 8 ⟨825373, by decide⟩
    (prefixPartial 13 431348) = some ⟨13, 2, 0, 825373, 431348, 141, 16384⟩ := by
  decide +kernel

theorem context_13_431348_825373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431348 ⟨825373, by decide⟩ :=
  accepted_of_selected 13 431348 ⟨825373, by decide⟩ ⟨13, 2, 0, 825373, 431348, 141, 16384⟩
    (by decide) selected_cut_32138

theorem selected_cut_32139 : selected 8 ⟨825415, by decide⟩
    (prefixPartial 13 431349) = some ⟨13, 2, 0, 825415, 431349, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_431349_825415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431349 ⟨825415, by decide⟩ :=
  accepted_of_selected 13 431349 ⟨825415, by decide⟩ ⟨13, 2, 0, 825415, 431349, 2517, 16384⟩
    (by decide) selected_cut_32139

theorem selected_cut_32140 : selected 8 ⟨825436, by decide⟩
    (prefixPartial 13 431350) = some ⟨13, 2, 0, 825436, 431350, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_431350_825436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431350 ⟨825436, by decide⟩ :=
  accepted_of_selected 13 431350 ⟨825436, by decide⟩ ⟨13, 2, 0, 825436, 431350, 1345, 16384⟩
    (by decide) selected_cut_32140

theorem selected_cut_32141 : selected 8 ⟨825442, by decide⟩
    (prefixPartial 13 431351) = some ⟨13, 2, 0, 825442, 431351, 689, 16384⟩ := by
  decide +kernel

theorem context_13_431351_825442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431351 ⟨825442, by decide⟩ :=
  accepted_of_selected 13 431351 ⟨825442, by decide⟩ ⟨13, 2, 0, 825442, 431351, 689, 16384⟩
    (by decide) selected_cut_32141

theorem unmarked_context_12_107837_825443 : frontier 9 ⟨825443, by decide⟩
    (prefixCache 12 107837) (prefixPartial 12 107837) = false := by
  decide +kernel

theorem node_context_12_107837_825443 : EJMOriginalGlobalDAGData.nodes 9 ⟨825443, by decide⟩ =
    .split (coordinate 12) (![⟨825373, by decide⟩,⟨825415, by decide⟩,⟨825436, by decide⟩,⟨825442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107837_825443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107837 ⟨825443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107837
    ⟨825443, by decide⟩ (by decide) (![⟨825373, by decide⟩,⟨825415, by decide⟩,⟨825436, by decide⟩,⟨825442, by decide⟩]) unmarked_context_12_107837_825443 node_context_12_107837_825443
  intro a
  fin_cases a
  · exact context_13_431348_825373
  · exact context_13_431349_825415
  · exact context_13_431350_825436
  · exact context_13_431351_825442

theorem selected_cut_32142 : selected 8 ⟨825446, by decide⟩
    (prefixPartial 13 431352) = some ⟨13, 2, 0, 825446, 431352, 113, 16384⟩ := by
  decide +kernel

theorem context_13_431352_825446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431352 ⟨825446, by decide⟩ :=
  accepted_of_selected 13 431352 ⟨825446, by decide⟩ ⟨13, 2, 0, 825446, 431352, 113, 16384⟩
    (by decide) selected_cut_32142

theorem selected_cut_32143 : selected 8 ⟨825474, by decide⟩
    (prefixPartial 13 431353) = some ⟨13, 2, 0, 825474, 431353, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_431353_825474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431353 ⟨825474, by decide⟩ :=
  accepted_of_selected 13 431353 ⟨825474, by decide⟩ ⟨13, 2, 0, 825474, 431353, 2445, 16384⟩
    (by decide) selected_cut_32143

theorem selected_cut_32144 : selected 8 ⟨825491, by decide⟩
    (prefixPartial 13 431354) = some ⟨13, 2, 0, 825491, 431354, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_431354_825491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431354 ⟨825491, by decide⟩ :=
  accepted_of_selected 13 431354 ⟨825491, by decide⟩ ⟨13, 2, 0, 825491, 431354, 1261, 16384⟩
    (by decide) selected_cut_32144

theorem selected_cut_32145 : selected 8 ⟨825499, by decide⟩
    (prefixPartial 13 431355) = some ⟨13, 2, 0, 825499, 431355, 841, 16384⟩ := by
  decide +kernel

theorem context_13_431355_825499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431355 ⟨825499, by decide⟩ :=
  accepted_of_selected 13 431355 ⟨825499, by decide⟩ ⟨13, 2, 0, 825499, 431355, 841, 16384⟩
    (by decide) selected_cut_32145

theorem unmarked_context_12_107838_825500 : frontier 9 ⟨825500, by decide⟩
    (prefixCache 12 107838) (prefixPartial 12 107838) = false := by
  decide +kernel

theorem node_context_12_107838_825500 : EJMOriginalGlobalDAGData.nodes 9 ⟨825500, by decide⟩ =
    .split (coordinate 12) (![⟨825446, by decide⟩,⟨825474, by decide⟩,⟨825491, by decide⟩,⟨825499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107838_825500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107838 ⟨825500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107838
    ⟨825500, by decide⟩ (by decide) (![⟨825446, by decide⟩,⟨825474, by decide⟩,⟨825491, by decide⟩,⟨825499, by decide⟩]) unmarked_context_12_107838_825500 node_context_12_107838_825500
  intro a
  fin_cases a
  · exact context_13_431352_825446
  · exact context_13_431353_825474
  · exact context_13_431354_825491
  · exact context_13_431355_825499

theorem selected_cut_32146 : selected 8 ⟨825504, by decide⟩
    (prefixPartial 13 431356) = some ⟨13, 2, 0, 825504, 431356, 101, 16384⟩ := by
  decide +kernel

theorem context_13_431356_825504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431356 ⟨825504, by decide⟩ :=
  accepted_of_selected 13 431356 ⟨825504, by decide⟩ ⟨13, 2, 0, 825504, 431356, 101, 16384⟩
    (by decide) selected_cut_32146

theorem selected_cut_32147 : selected 8 ⟨825552, by decide⟩
    (prefixPartial 13 431357) = some ⟨13, 2, 0, 825552, 431357, 3377, 16384⟩ := by
  decide +kernel

theorem context_13_431357_825552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431357 ⟨825552, by decide⟩ :=
  accepted_of_selected 13 431357 ⟨825552, by decide⟩ ⟨13, 2, 0, 825552, 431357, 3377, 16384⟩
    (by decide) selected_cut_32147

theorem selected_cut_32148 : selected 8 ⟨825575, by decide⟩
    (prefixPartial 13 431358) = some ⟨13, 2, 0, 825575, 431358, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_431358_825575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431358 ⟨825575, by decide⟩ :=
  accepted_of_selected 13 431358 ⟨825575, by decide⟩ ⟨13, 2, 0, 825575, 431358, 1557, 16384⟩
    (by decide) selected_cut_32148

theorem selected_cut_32149 : selected 8 ⟨825585, by decide⟩
    (prefixPartial 13 431359) = some ⟨13, 2, 0, 825585, 431359, 785, 16384⟩ := by
  decide +kernel

theorem context_13_431359_825585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431359 ⟨825585, by decide⟩ :=
  accepted_of_selected 13 431359 ⟨825585, by decide⟩ ⟨13, 2, 0, 825585, 431359, 785, 16384⟩
    (by decide) selected_cut_32149

theorem unmarked_context_12_107839_825586 : frontier 9 ⟨825586, by decide⟩
    (prefixCache 12 107839) (prefixPartial 12 107839) = false := by
  decide +kernel

theorem node_context_12_107839_825586 : EJMOriginalGlobalDAGData.nodes 9 ⟨825586, by decide⟩ =
    .split (coordinate 12) (![⟨825504, by decide⟩,⟨825552, by decide⟩,⟨825575, by decide⟩,⟨825585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107839_825586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107839 ⟨825586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107839
    ⟨825586, by decide⟩ (by decide) (![⟨825504, by decide⟩,⟨825552, by decide⟩,⟨825575, by decide⟩,⟨825585, by decide⟩]) unmarked_context_12_107839_825586 node_context_12_107839_825586
  intro a
  fin_cases a
  · exact context_13_431356_825504
  · exact context_13_431357_825552
  · exact context_13_431358_825575
  · exact context_13_431359_825585

theorem unmarked_context_11_26959_825587 : frontier 10 ⟨825587, by decide⟩
    (prefixCache 11 26959) (prefixPartial 11 26959) = false := by
  decide +kernel

theorem node_context_11_26959_825587 : EJMOriginalGlobalDAGData.nodes 10 ⟨825587, by decide⟩ =
    .split (coordinate 11) (![⟨825368, by decide⟩,⟨825443, by decide⟩,⟨825500, by decide⟩,⟨825586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26959_825587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26959 ⟨825587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26959
    ⟨825587, by decide⟩ (by decide) (![⟨825368, by decide⟩,⟨825443, by decide⟩,⟨825500, by decide⟩,⟨825586, by decide⟩]) unmarked_context_11_26959_825587 node_context_11_26959_825587
  intro a
  fin_cases a
  · exact context_12_107836_825368
  · exact context_12_107837_825443
  · exact context_12_107838_825500
  · exact context_12_107839_825586

theorem unmarked_context_10_6739_825588 : frontier 11 ⟨825588, by decide⟩
    (prefixCache 10 6739) (prefixPartial 10 6739) = false := by
  decide +kernel

theorem node_context_10_6739_825588 : EJMOriginalGlobalDAGData.nodes 11 ⟨825588, by decide⟩ =
    .split (coordinate 10) (![⟨824668, by decide⟩,⟨824932, by decide⟩,⟨825265, by decide⟩,⟨825587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6739_825588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6739 ⟨825588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6739
    ⟨825588, by decide⟩ (by decide) (![⟨824668, by decide⟩,⟨824932, by decide⟩,⟨825265, by decide⟩,⟨825587, by decide⟩]) unmarked_context_10_6739_825588 node_context_10_6739_825588
  intro a
  fin_cases a
  · exact context_11_26956_824668
  · exact context_11_26957_824932
  · exact context_11_26958_825265
  · exact context_11_26959_825587

theorem unmarked_context_9_1684_825589 : frontier 12 ⟨825589, by decide⟩
    (prefixCache 9 1684) (prefixPartial 9 1684) = false := by
  decide +kernel

theorem node_context_9_1684_825589 : EJMOriginalGlobalDAGData.nodes 12 ⟨825589, by decide⟩ =
    .split (coordinate 9) (![⟨821773, by decide⟩,⟨822973, by decide⟩,⟨824347, by decide⟩,⟨825588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1684_825589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1684 ⟨825589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1684
    ⟨825589, by decide⟩ (by decide) (![⟨821773, by decide⟩,⟨822973, by decide⟩,⟨824347, by decide⟩,⟨825588, by decide⟩]) unmarked_context_9_1684_825589 node_context_9_1684_825589
  intro a
  fin_cases a
  · exact context_10_6736_821773
  · exact context_10_6737_822973
  · exact context_10_6738_824347
  · exact context_10_6739_825588

theorem selected_cut_32150 : selected 9 ⟨825652, by decide⟩
    (prefixPartial 12 107840) = some ⟨12, 2, 0, 825652, 107840, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_107840_825652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107840 ⟨825652, by decide⟩ :=
  accepted_of_selected 12 107840 ⟨825652, by decide⟩ ⟨12, 2, 0, 825652, 107840, 4093, 65536⟩
    (by decide) selected_cut_32150

theorem selected_cut_32151 : selected 9 ⟨825706, by decide⟩
    (prefixPartial 12 107841) = some ⟨12, 2, 0, 825706, 107841, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_107841_825706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107841 ⟨825706, by decide⟩ :=
  accepted_of_selected 12 107841 ⟨825706, by decide⟩ ⟨12, 2, 0, 825706, 107841, 3437, 65536⟩
    (by decide) selected_cut_32151

theorem selected_cut_32152 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431368) = some ⟨13, 1, 0, 3444, 431368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431368, 1, 16384⟩
    (by decide) selected_cut_32152

theorem selected_cut_32153 : selected 8 ⟨825732, by decide⟩
    (prefixPartial 13 431369) = some ⟨13, 2, 0, 825732, 431369, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_431369_825732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431369 ⟨825732, by decide⟩ :=
  accepted_of_selected 13 431369 ⟨825732, by decide⟩ ⟨13, 2, 0, 825732, 431369, 1941, 16384⟩
    (by decide) selected_cut_32153

theorem selected_cut_32154 : selected 8 ⟨825757, by decide⟩
    (prefixPartial 13 431370) = some ⟨13, 2, 0, 825757, 431370, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_431370_825757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431370 ⟨825757, by decide⟩ :=
  accepted_of_selected 13 431370 ⟨825757, by decide⟩ ⟨13, 2, 0, 825757, 431370, 1421, 16384⟩
    (by decide) selected_cut_32154

theorem selected_cut_32155 : selected 8 ⟨825764, by decide⟩
    (prefixPartial 13 431371) = some ⟨13, 2, 0, 825764, 431371, 813, 16384⟩ := by
  decide +kernel

theorem context_13_431371_825764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431371 ⟨825764, by decide⟩ :=
  accepted_of_selected 13 431371 ⟨825764, by decide⟩ ⟨13, 2, 0, 825764, 431371, 813, 16384⟩
    (by decide) selected_cut_32155

theorem unmarked_context_12_107842_825765 : frontier 9 ⟨825765, by decide⟩
    (prefixCache 12 107842) (prefixPartial 12 107842) = false := by
  decide +kernel

theorem node_context_12_107842_825765 : EJMOriginalGlobalDAGData.nodes 9 ⟨825765, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨825732, by decide⟩,⟨825757, by decide⟩,⟨825764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107842_825765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107842 ⟨825765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107842
    ⟨825765, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨825732, by decide⟩,⟨825757, by decide⟩,⟨825764, by decide⟩]) unmarked_context_12_107842_825765 node_context_12_107842_825765
  intro a
  fin_cases a
  · exact context_13_431368_3444
  · exact context_13_431369_825732
  · exact context_13_431370_825757
  · exact context_13_431371_825764

theorem selected_cut_32156 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431372) = some ⟨13, 1, 0, 3444, 431372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431372, 1, 16384⟩
    (by decide) selected_cut_32156

theorem selected_cut_32157 : selected 8 ⟨825799, by decide⟩
    (prefixPartial 13 431373) = some ⟨13, 2, 0, 825799, 431373, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_431373_825799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431373 ⟨825799, by decide⟩ :=
  accepted_of_selected 13 431373 ⟨825799, by decide⟩ ⟨13, 2, 0, 825799, 431373, 2065, 16384⟩
    (by decide) selected_cut_32157

theorem selected_cut_32158 : selected 8 ⟨825829, by decide⟩
    (prefixPartial 13 431374) = some ⟨13, 2, 0, 825829, 431374, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_431374_825829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431374 ⟨825829, by decide⟩ :=
  accepted_of_selected 13 431374 ⟨825829, by decide⟩ ⟨13, 2, 0, 825829, 431374, 1617, 16384⟩
    (by decide) selected_cut_32158

theorem selected_cut_32159 : selected 8 ⟨825833, by decide⟩
    (prefixPartial 13 431375) = some ⟨13, 2, 0, 825833, 431375, 781, 16384⟩ := by
  decide +kernel

theorem context_13_431375_825833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431375 ⟨825833, by decide⟩ :=
  accepted_of_selected 13 431375 ⟨825833, by decide⟩ ⟨13, 2, 0, 825833, 431375, 781, 16384⟩
    (by decide) selected_cut_32159

theorem unmarked_context_12_107843_825834 : frontier 9 ⟨825834, by decide⟩
    (prefixCache 12 107843) (prefixPartial 12 107843) = false := by
  decide +kernel

theorem node_context_12_107843_825834 : EJMOriginalGlobalDAGData.nodes 9 ⟨825834, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨825799, by decide⟩,⟨825829, by decide⟩,⟨825833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107843_825834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107843 ⟨825834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107843
    ⟨825834, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨825799, by decide⟩,⟨825829, by decide⟩,⟨825833, by decide⟩]) unmarked_context_12_107843_825834 node_context_12_107843_825834
  intro a
  fin_cases a
  · exact context_13_431372_3444
  · exact context_13_431373_825799
  · exact context_13_431374_825829
  · exact context_13_431375_825833

theorem unmarked_context_11_26960_825835 : frontier 10 ⟨825835, by decide⟩
    (prefixCache 11 26960) (prefixPartial 11 26960) = false := by
  decide +kernel

theorem node_context_11_26960_825835 : EJMOriginalGlobalDAGData.nodes 10 ⟨825835, by decide⟩ =
    .split (coordinate 11) (![⟨825652, by decide⟩,⟨825706, by decide⟩,⟨825765, by decide⟩,⟨825834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26960_825835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26960 ⟨825835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26960
    ⟨825835, by decide⟩ (by decide) (![⟨825652, by decide⟩,⟨825706, by decide⟩,⟨825765, by decide⟩,⟨825834, by decide⟩]) unmarked_context_11_26960_825835 node_context_11_26960_825835
  intro a
  fin_cases a
  · exact context_12_107840_825652
  · exact context_12_107841_825706
  · exact context_12_107842_825765
  · exact context_12_107843_825834

theorem selected_cut_32160 : selected 9 ⟨825888, by decide⟩
    (prefixPartial 12 107844) = some ⟨12, 2, 0, 825888, 107844, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_107844_825888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107844 ⟨825888, by decide⟩ :=
  accepted_of_selected 12 107844 ⟨825888, by decide⟩ ⟨12, 2, 0, 825888, 107844, 3437, 65536⟩
    (by decide) selected_cut_32160

theorem selected_cut_32161 : selected 9 ⟨692443, by decide⟩
    (prefixPartial 12 107845) = some ⟨12, 1, 0, 692443, 107845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107845_692443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107845 ⟨692443, by decide⟩ :=
  accepted_of_selected 12 107845 ⟨692443, by decide⟩ ⟨12, 1, 0, 692443, 107845, 1, 65536⟩
    (by decide) selected_cut_32161

theorem selected_cut_32162 : selected 9 ⟨825934, by decide⟩
    (prefixPartial 12 107846) = some ⟨12, 2, 0, 825934, 107846, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_107846_825934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107846 ⟨825934, by decide⟩ :=
  accepted_of_selected 12 107846 ⟨825934, by decide⟩ ⟨12, 2, 0, 825934, 107846, 3349, 65536⟩
    (by decide) selected_cut_32162

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
