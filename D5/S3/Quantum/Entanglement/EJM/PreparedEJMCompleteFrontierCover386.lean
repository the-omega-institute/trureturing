/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover385
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37058 : selected 9 ⟨989211, by decide⟩
    (prefixPartial 12 299270) = some ⟨12, 2, 0, 989211, 299270, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_299270_989211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299270 ⟨989211, by decide⟩ :=
  accepted_of_selected 12 299270 ⟨989211, by decide⟩ ⟨12, 2, 0, 989211, 299270, 3845, 65536⟩
    (by decide) selected_cut_37058

theorem selected_cut_37059 : selected 9 ⟨989282, by decide⟩
    (prefixPartial 12 299271) = some ⟨12, 2, 0, 989282, 299271, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_299271_989282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299271 ⟨989282, by decide⟩ :=
  accepted_of_selected 12 299271 ⟨989282, by decide⟩ ⟨12, 2, 0, 989282, 299271, 3889, 65536⟩
    (by decide) selected_cut_37059

theorem unmarked_context_11_74817_989283 : frontier 10 ⟨989283, by decide⟩
    (prefixCache 11 74817) (prefixPartial 11 74817) = false := by
  decide +kernel

theorem node_context_11_74817_989283 : EJMOriginalGlobalDAGData.nodes 10 ⟨989283, by decide⟩ =
    .split (coordinate 11) (![⟨989139, by decide⟩,⟨891951, by decide⟩,⟨989211, by decide⟩,⟨989282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74817_989283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74817 ⟨989283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74817
    ⟨989283, by decide⟩ (by decide) (![⟨989139, by decide⟩,⟨891951, by decide⟩,⟨989211, by decide⟩,⟨989282, by decide⟩]) unmarked_context_11_74817_989283 node_context_11_74817_989283
  intro a
  fin_cases a
  · exact context_12_299268_989139
  · exact context_12_299269_891951
  · exact context_12_299270_989211
  · exact context_12_299271_989282

theorem selected_cut_37060 : selected 9 ⟨989360, by decide⟩
    (prefixPartial 12 299272) = some ⟨12, 2, 0, 989360, 299272, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_299272_989360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299272 ⟨989360, by decide⟩ :=
  accepted_of_selected 12 299272 ⟨989360, by decide⟩ ⟨12, 2, 0, 989360, 299272, 4077, 65536⟩
    (by decide) selected_cut_37060

theorem selected_cut_37061 : selected 9 ⟨989422, by decide⟩
    (prefixPartial 12 299273) = some ⟨12, 2, 0, 989422, 299273, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_299273_989422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299273 ⟨989422, by decide⟩ :=
  accepted_of_selected 12 299273 ⟨989422, by decide⟩ ⟨12, 2, 0, 989422, 299273, 3669, 65536⟩
    (by decide) selected_cut_37061

theorem selected_cut_37062 : selected 9 ⟨989490, by decide⟩
    (prefixPartial 12 299274) = some ⟨12, 2, 0, 989490, 299274, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_299274_989490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299274 ⟨989490, by decide⟩ :=
  accepted_of_selected 12 299274 ⟨989490, by decide⟩ ⟨12, 2, 0, 989490, 299274, 3693, 65536⟩
    (by decide) selected_cut_37062

theorem selected_cut_37063 : selected 9 ⟨989557, by decide⟩
    (prefixPartial 12 299275) = some ⟨12, 2, 0, 989557, 299275, 3645, 65536⟩ := by
  decide +kernel

theorem context_12_299275_989557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299275 ⟨989557, by decide⟩ :=
  accepted_of_selected 12 299275 ⟨989557, by decide⟩ ⟨12, 2, 0, 989557, 299275, 3645, 65536⟩
    (by decide) selected_cut_37063

theorem unmarked_context_11_74818_989558 : frontier 10 ⟨989558, by decide⟩
    (prefixCache 11 74818) (prefixPartial 11 74818) = false := by
  decide +kernel

theorem node_context_11_74818_989558 : EJMOriginalGlobalDAGData.nodes 10 ⟨989558, by decide⟩ =
    .split (coordinate 11) (![⟨989360, by decide⟩,⟨989422, by decide⟩,⟨989490, by decide⟩,⟨989557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74818_989558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74818 ⟨989558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74818
    ⟨989558, by decide⟩ (by decide) (![⟨989360, by decide⟩,⟨989422, by decide⟩,⟨989490, by decide⟩,⟨989557, by decide⟩]) unmarked_context_11_74818_989558 node_context_11_74818_989558
  intro a
  fin_cases a
  · exact context_12_299272_989360
  · exact context_12_299273_989422
  · exact context_12_299274_989490
  · exact context_12_299275_989557

theorem selected_cut_37064 : selected 8 ⟨989589, by decide⟩
    (prefixPartial 13 1197104) = some ⟨13, 2, 0, 989589, 1197104, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_1197104_989589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197104 ⟨989589, by decide⟩ :=
  accepted_of_selected 13 1197104 ⟨989589, by decide⟩ ⟨13, 2, 0, 989589, 1197104, 1469, 16384⟩
    (by decide) selected_cut_37064

theorem selected_cut_37065 : selected 8 ⟨989611, by decide⟩
    (prefixPartial 13 1197105) = some ⟨13, 2, 0, 989611, 1197105, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_1197105_989611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197105 ⟨989611, by decide⟩ :=
  accepted_of_selected 13 1197105 ⟨989611, by decide⟩ ⟨13, 2, 0, 989611, 1197105, 1293, 16384⟩
    (by decide) selected_cut_37065

theorem selected_cut_37066 : selected 8 ⟨989626, by decide⟩
    (prefixPartial 13 1197106) = some ⟨13, 2, 0, 989626, 1197106, 773, 16384⟩ := by
  decide +kernel

theorem context_13_1197106_989626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197106 ⟨989626, by decide⟩ :=
  accepted_of_selected 13 1197106 ⟨989626, by decide⟩ ⟨13, 2, 0, 989626, 1197106, 773, 16384⟩
    (by decide) selected_cut_37066

theorem selected_cut_37067 : selected 8 ⟨989631, by decide⟩
    (prefixPartial 13 1197107) = some ⟨13, 2, 0, 989631, 1197107, 565, 16384⟩ := by
  decide +kernel

theorem context_13_1197107_989631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197107 ⟨989631, by decide⟩ :=
  accepted_of_selected 13 1197107 ⟨989631, by decide⟩ ⟨13, 2, 0, 989631, 1197107, 565, 16384⟩
    (by decide) selected_cut_37067

theorem unmarked_context_12_299276_989632 : frontier 9 ⟨989632, by decide⟩
    (prefixCache 12 299276) (prefixPartial 12 299276) = false := by
  decide +kernel

theorem node_context_12_299276_989632 : EJMOriginalGlobalDAGData.nodes 9 ⟨989632, by decide⟩ =
    .split (coordinate 12) (![⟨989589, by decide⟩,⟨989611, by decide⟩,⟨989626, by decide⟩,⟨989631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299276_989632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299276 ⟨989632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299276
    ⟨989632, by decide⟩ (by decide) (![⟨989589, by decide⟩,⟨989611, by decide⟩,⟨989626, by decide⟩,⟨989631, by decide⟩]) unmarked_context_12_299276_989632 node_context_12_299276_989632
  intro a
  fin_cases a
  · exact context_13_1197104_989589
  · exact context_13_1197105_989611
  · exact context_13_1197106_989626
  · exact context_13_1197107_989631

theorem selected_cut_37068 : selected 9 ⟨989699, by decide⟩
    (prefixPartial 12 299277) = some ⟨12, 2, 0, 989699, 299277, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_299277_989699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299277 ⟨989699, by decide⟩ :=
  accepted_of_selected 12 299277 ⟨989699, by decide⟩ ⟨12, 2, 0, 989699, 299277, 3741, 65536⟩
    (by decide) selected_cut_37068

theorem selected_cut_37069 : selected 9 ⟨989757, by decide⟩
    (prefixPartial 12 299278) = some ⟨12, 2, 0, 989757, 299278, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_299278_989757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299278 ⟨989757, by decide⟩ :=
  accepted_of_selected 12 299278 ⟨989757, by decide⟩ ⟨12, 2, 0, 989757, 299278, 3469, 65536⟩
    (by decide) selected_cut_37069

theorem selected_cut_37070 : selected 9 ⟨989811, by decide⟩
    (prefixPartial 12 299279) = some ⟨12, 2, 0, 989811, 299279, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_299279_989811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299279 ⟨989811, by decide⟩ :=
  accepted_of_selected 12 299279 ⟨989811, by decide⟩ ⟨12, 2, 0, 989811, 299279, 3693, 65536⟩
    (by decide) selected_cut_37070

theorem unmarked_context_11_74819_989812 : frontier 10 ⟨989812, by decide⟩
    (prefixCache 11 74819) (prefixPartial 11 74819) = false := by
  decide +kernel

theorem node_context_11_74819_989812 : EJMOriginalGlobalDAGData.nodes 10 ⟨989812, by decide⟩ =
    .split (coordinate 11) (![⟨989632, by decide⟩,⟨989699, by decide⟩,⟨989757, by decide⟩,⟨989811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74819_989812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74819 ⟨989812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74819
    ⟨989812, by decide⟩ (by decide) (![⟨989632, by decide⟩,⟨989699, by decide⟩,⟨989757, by decide⟩,⟨989811, by decide⟩]) unmarked_context_11_74819_989812 node_context_11_74819_989812
  intro a
  fin_cases a
  · exact context_12_299276_989632
  · exact context_12_299277_989699
  · exact context_12_299278_989757
  · exact context_12_299279_989811

theorem unmarked_context_10_18704_989813 : frontier 11 ⟨989813, by decide⟩
    (prefixCache 10 18704) (prefixPartial 10 18704) = false := by
  decide +kernel

theorem node_context_10_18704_989813 : EJMOriginalGlobalDAGData.nodes 11 ⟨989813, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨989283, by decide⟩,⟨989558, by decide⟩,⟨989812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18704_989813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18704 ⟨989813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18704
    ⟨989813, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨989283, by decide⟩,⟨989558, by decide⟩,⟨989812, by decide⟩]) unmarked_context_10_18704_989813 node_context_10_18704_989813
  intro a
  fin_cases a
  · exact context_11_74816_167448
  · exact context_11_74817_989283
  · exact context_11_74818_989558
  · exact context_11_74819_989812

theorem selected_cut_37071 : selected 9 ⟨989875, by decide⟩
    (prefixPartial 12 299280) = some ⟨12, 2, 0, 989875, 299280, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_299280_989875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299280 ⟨989875, by decide⟩ :=
  accepted_of_selected 12 299280 ⟨989875, by decide⟩ ⟨12, 2, 0, 989875, 299280, 1833, 65536⟩
    (by decide) selected_cut_37071

theorem selected_cut_37072 : selected 9 ⟨989912, by decide⟩
    (prefixPartial 12 299281) = some ⟨12, 2, 0, 989912, 299281, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_299281_989912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299281 ⟨989912, by decide⟩ :=
  accepted_of_selected 12 299281 ⟨989912, by decide⟩ ⟨12, 2, 0, 989912, 299281, 2245, 65536⟩
    (by decide) selected_cut_37072

theorem selected_cut_37073 : selected 9 ⟨989953, by decide⟩
    (prefixPartial 12 299282) = some ⟨12, 2, 0, 989953, 299282, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_299282_989953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299282 ⟨989953, by decide⟩ :=
  accepted_of_selected 12 299282 ⟨989953, by decide⟩ ⟨12, 2, 0, 989953, 299282, 2237, 65536⟩
    (by decide) selected_cut_37073

theorem selected_cut_37074 : selected 9 ⟨989991, by decide⟩
    (prefixPartial 12 299283) = some ⟨12, 2, 0, 989991, 299283, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_299283_989991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299283 ⟨989991, by decide⟩ :=
  accepted_of_selected 12 299283 ⟨989991, by decide⟩ ⟨12, 2, 0, 989991, 299283, 2505, 65536⟩
    (by decide) selected_cut_37074

theorem unmarked_context_11_74820_989992 : frontier 10 ⟨989992, by decide⟩
    (prefixCache 11 74820) (prefixPartial 11 74820) = false := by
  decide +kernel

theorem node_context_11_74820_989992 : EJMOriginalGlobalDAGData.nodes 10 ⟨989992, by decide⟩ =
    .split (coordinate 11) (![⟨989875, by decide⟩,⟨989912, by decide⟩,⟨989953, by decide⟩,⟨989991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74820_989992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74820 ⟨989992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74820
    ⟨989992, by decide⟩ (by decide) (![⟨989875, by decide⟩,⟨989912, by decide⟩,⟨989953, by decide⟩,⟨989991, by decide⟩]) unmarked_context_11_74820_989992 node_context_11_74820_989992
  intro a
  fin_cases a
  · exact context_12_299280_989875
  · exact context_12_299281_989912
  · exact context_12_299282_989953
  · exact context_12_299283_989991

theorem selected_cut_37075 : selected 9 ⟨990046, by decide⟩
    (prefixPartial 12 299284) = some ⟨12, 2, 0, 990046, 299284, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_299284_990046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299284 ⟨990046, by decide⟩ :=
  accepted_of_selected 12 299284 ⟨990046, by decide⟩ ⟨12, 2, 0, 990046, 299284, 3289, 65536⟩
    (by decide) selected_cut_37075

theorem selected_cut_37076 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 299285) = some ⟨12, 1, 0, 124308, 299285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299285_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299285 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 299285 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 299285, 1, 65536⟩
    (by decide) selected_cut_37076

theorem selected_cut_37077 : selected 9 ⟨990088, by decide⟩
    (prefixPartial 12 299286) = some ⟨12, 2, 0, 990088, 299286, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_299286_990088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299286 ⟨990088, by decide⟩ :=
  accepted_of_selected 12 299286 ⟨990088, by decide⟩ ⟨12, 2, 0, 990088, 299286, 2865, 65536⟩
    (by decide) selected_cut_37077

theorem selected_cut_37078 : selected 9 ⟨990131, by decide⟩
    (prefixPartial 12 299287) = some ⟨12, 2, 0, 990131, 299287, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_299287_990131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299287 ⟨990131, by decide⟩ :=
  accepted_of_selected 12 299287 ⟨990131, by decide⟩ ⟨12, 2, 0, 990131, 299287, 3101, 65536⟩
    (by decide) selected_cut_37078

theorem unmarked_context_11_74821_990132 : frontier 10 ⟨990132, by decide⟩
    (prefixCache 11 74821) (prefixPartial 11 74821) = false := by
  decide +kernel

theorem node_context_11_74821_990132 : EJMOriginalGlobalDAGData.nodes 10 ⟨990132, by decide⟩ =
    .split (coordinate 11) (![⟨990046, by decide⟩,⟨124308, by decide⟩,⟨990088, by decide⟩,⟨990131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74821_990132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74821 ⟨990132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74821
    ⟨990132, by decide⟩ (by decide) (![⟨990046, by decide⟩,⟨124308, by decide⟩,⟨990088, by decide⟩,⟨990131, by decide⟩]) unmarked_context_11_74821_990132 node_context_11_74821_990132
  intro a
  fin_cases a
  · exact context_12_299284_990046
  · exact context_12_299285_124308
  · exact context_12_299286_990088
  · exact context_12_299287_990131

theorem selected_cut_37079 : selected 9 ⟨990179, by decide⟩
    (prefixPartial 12 299288) = some ⟨12, 2, 0, 990179, 299288, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_299288_990179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299288 ⟨990179, by decide⟩ :=
  accepted_of_selected 12 299288 ⟨990179, by decide⟩ ⟨12, 2, 0, 990179, 299288, 3057, 65536⟩
    (by decide) selected_cut_37079

theorem selected_cut_37080 : selected 9 ⟨990213, by decide⟩
    (prefixPartial 12 299289) = some ⟨12, 2, 0, 990213, 299289, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_299289_990213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299289 ⟨990213, by decide⟩ :=
  accepted_of_selected 12 299289 ⟨990213, by decide⟩ ⟨12, 2, 0, 990213, 299289, 2661, 65536⟩
    (by decide) selected_cut_37080

theorem selected_cut_37081 : selected 9 ⟨990246, by decide⟩
    (prefixPartial 12 299290) = some ⟨12, 2, 0, 990246, 299290, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_299290_990246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299290 ⟨990246, by decide⟩ :=
  accepted_of_selected 12 299290 ⟨990246, by decide⟩ ⟨12, 2, 0, 990246, 299290, 2693, 65536⟩
    (by decide) selected_cut_37081

theorem selected_cut_37082 : selected 9 ⟨990285, by decide⟩
    (prefixPartial 12 299291) = some ⟨12, 2, 0, 990285, 299291, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_299291_990285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299291 ⟨990285, by decide⟩ :=
  accepted_of_selected 12 299291 ⟨990285, by decide⟩ ⟨12, 2, 0, 990285, 299291, 2829, 65536⟩
    (by decide) selected_cut_37082

theorem unmarked_context_11_74822_990286 : frontier 10 ⟨990286, by decide⟩
    (prefixCache 11 74822) (prefixPartial 11 74822) = false := by
  decide +kernel

theorem node_context_11_74822_990286 : EJMOriginalGlobalDAGData.nodes 10 ⟨990286, by decide⟩ =
    .split (coordinate 11) (![⟨990179, by decide⟩,⟨990213, by decide⟩,⟨990246, by decide⟩,⟨990285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74822_990286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74822 ⟨990286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74822
    ⟨990286, by decide⟩ (by decide) (![⟨990179, by decide⟩,⟨990213, by decide⟩,⟨990246, by decide⟩,⟨990285, by decide⟩]) unmarked_context_11_74822_990286 node_context_11_74822_990286
  intro a
  fin_cases a
  · exact context_12_299288_990179
  · exact context_12_299289_990213
  · exact context_12_299290_990246
  · exact context_12_299291_990285

theorem selected_cut_37083 : selected 9 ⟨990340, by decide⟩
    (prefixPartial 12 299292) = some ⟨12, 2, 0, 990340, 299292, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_299292_990340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299292 ⟨990340, by decide⟩ :=
  accepted_of_selected 12 299292 ⟨990340, by decide⟩ ⟨12, 2, 0, 990340, 299292, 3413, 65536⟩
    (by decide) selected_cut_37083

theorem selected_cut_37084 : selected 9 ⟨990387, by decide⟩
    (prefixPartial 12 299293) = some ⟨12, 2, 0, 990387, 299293, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_299293_990387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299293 ⟨990387, by decide⟩ :=
  accepted_of_selected 12 299293 ⟨990387, by decide⟩ ⟨12, 2, 0, 990387, 299293, 2929, 65536⟩
    (by decide) selected_cut_37084

theorem selected_cut_37085 : selected 9 ⟨990434, by decide⟩
    (prefixPartial 12 299294) = some ⟨12, 2, 0, 990434, 299294, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_299294_990434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299294 ⟨990434, by decide⟩ :=
  accepted_of_selected 12 299294 ⟨990434, by decide⟩ ⟨12, 2, 0, 990434, 299294, 2897, 65536⟩
    (by decide) selected_cut_37085

theorem selected_cut_37086 : selected 9 ⟨990473, by decide⟩
    (prefixPartial 12 299295) = some ⟨12, 2, 0, 990473, 299295, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_299295_990473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299295 ⟨990473, by decide⟩ :=
  accepted_of_selected 12 299295 ⟨990473, by decide⟩ ⟨12, 2, 0, 990473, 299295, 3021, 65536⟩
    (by decide) selected_cut_37086

theorem unmarked_context_11_74823_990474 : frontier 10 ⟨990474, by decide⟩
    (prefixCache 11 74823) (prefixPartial 11 74823) = false := by
  decide +kernel

theorem node_context_11_74823_990474 : EJMOriginalGlobalDAGData.nodes 10 ⟨990474, by decide⟩ =
    .split (coordinate 11) (![⟨990340, by decide⟩,⟨990387, by decide⟩,⟨990434, by decide⟩,⟨990473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74823_990474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74823 ⟨990474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74823
    ⟨990474, by decide⟩ (by decide) (![⟨990340, by decide⟩,⟨990387, by decide⟩,⟨990434, by decide⟩,⟨990473, by decide⟩]) unmarked_context_11_74823_990474 node_context_11_74823_990474
  intro a
  fin_cases a
  · exact context_12_299292_990340
  · exact context_12_299293_990387
  · exact context_12_299294_990434
  · exact context_12_299295_990473

theorem unmarked_context_10_18705_990475 : frontier 11 ⟨990475, by decide⟩
    (prefixCache 10 18705) (prefixPartial 10 18705) = false := by
  decide +kernel

theorem node_context_10_18705_990475 : EJMOriginalGlobalDAGData.nodes 11 ⟨990475, by decide⟩ =
    .split (coordinate 10) (![⟨989992, by decide⟩,⟨990132, by decide⟩,⟨990286, by decide⟩,⟨990474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18705_990475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18705 ⟨990475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18705
    ⟨990475, by decide⟩ (by decide) (![⟨989992, by decide⟩,⟨990132, by decide⟩,⟨990286, by decide⟩,⟨990474, by decide⟩]) unmarked_context_10_18705_990475 node_context_10_18705_990475
  intro a
  fin_cases a
  · exact context_11_74820_989992
  · exact context_11_74821_990132
  · exact context_11_74822_990286
  · exact context_11_74823_990474

theorem selected_cut_37087 : selected 9 ⟨990521, by decide⟩
    (prefixPartial 12 299296) = some ⟨12, 2, 0, 990521, 299296, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_299296_990521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299296 ⟨990521, by decide⟩ :=
  accepted_of_selected 12 299296 ⟨990521, by decide⟩ ⟨12, 2, 0, 990521, 299296, 3009, 65536⟩
    (by decide) selected_cut_37087

theorem selected_cut_37088 : selected 9 ⟨990560, by decide⟩
    (prefixPartial 12 299297) = some ⟨12, 2, 0, 990560, 299297, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_299297_990560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299297 ⟨990560, by decide⟩ :=
  accepted_of_selected 12 299297 ⟨990560, by decide⟩ ⟨12, 2, 0, 990560, 299297, 2749, 65536⟩
    (by decide) selected_cut_37088

theorem selected_cut_37089 : selected 9 ⟨990599, by decide⟩
    (prefixPartial 12 299298) = some ⟨12, 2, 0, 990599, 299298, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_299298_990599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299298 ⟨990599, by decide⟩ :=
  accepted_of_selected 12 299298 ⟨990599, by decide⟩ ⟨12, 2, 0, 990599, 299298, 2449, 65536⟩
    (by decide) selected_cut_37089

theorem selected_cut_37090 : selected 9 ⟨990631, by decide⟩
    (prefixPartial 12 299299) = some ⟨12, 2, 0, 990631, 299299, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_299299_990631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299299 ⟨990631, by decide⟩ :=
  accepted_of_selected 12 299299 ⟨990631, by decide⟩ ⟨12, 2, 0, 990631, 299299, 2765, 65536⟩
    (by decide) selected_cut_37090

theorem unmarked_context_11_74824_990632 : frontier 10 ⟨990632, by decide⟩
    (prefixCache 11 74824) (prefixPartial 11 74824) = false := by
  decide +kernel

theorem node_context_11_74824_990632 : EJMOriginalGlobalDAGData.nodes 10 ⟨990632, by decide⟩ =
    .split (coordinate 11) (![⟨990521, by decide⟩,⟨990560, by decide⟩,⟨990599, by decide⟩,⟨990631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74824_990632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74824 ⟨990632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74824
    ⟨990632, by decide⟩ (by decide) (![⟨990521, by decide⟩,⟨990560, by decide⟩,⟨990599, by decide⟩,⟨990631, by decide⟩]) unmarked_context_11_74824_990632 node_context_11_74824_990632
  intro a
  fin_cases a
  · exact context_12_299296_990521
  · exact context_12_299297_990560
  · exact context_12_299298_990599
  · exact context_12_299299_990631

theorem selected_cut_37091 : selected 9 ⟨990706, by decide⟩
    (prefixPartial 12 299300) = some ⟨12, 2, 0, 990706, 299300, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_299300_990706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299300 ⟨990706, by decide⟩ :=
  accepted_of_selected 12 299300 ⟨990706, by decide⟩ ⟨12, 2, 0, 990706, 299300, 3805, 65536⟩
    (by decide) selected_cut_37091

theorem selected_cut_37092 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 299301) = some ⟨12, 1, 0, 891951, 299301, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299301_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299301 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 299301 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 299301, 1, 65536⟩
    (by decide) selected_cut_37092

theorem selected_cut_37093 : selected 9 ⟨990756, by decide⟩
    (prefixPartial 12 299302) = some ⟨12, 2, 0, 990756, 299302, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_299302_990756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299302 ⟨990756, by decide⟩ :=
  accepted_of_selected 12 299302 ⟨990756, by decide⟩ ⟨12, 2, 0, 990756, 299302, 3069, 65536⟩
    (by decide) selected_cut_37093

theorem selected_cut_37094 : selected 9 ⟨990811, by decide⟩
    (prefixPartial 12 299303) = some ⟨12, 2, 0, 990811, 299303, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_299303_990811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299303 ⟨990811, by decide⟩ :=
  accepted_of_selected 12 299303 ⟨990811, by decide⟩ ⟨12, 2, 0, 990811, 299303, 3341, 65536⟩
    (by decide) selected_cut_37094

theorem unmarked_context_11_74825_990812 : frontier 10 ⟨990812, by decide⟩
    (prefixCache 11 74825) (prefixPartial 11 74825) = false := by
  decide +kernel

theorem node_context_11_74825_990812 : EJMOriginalGlobalDAGData.nodes 10 ⟨990812, by decide⟩ =
    .split (coordinate 11) (![⟨990706, by decide⟩,⟨891951, by decide⟩,⟨990756, by decide⟩,⟨990811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74825_990812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74825 ⟨990812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74825
    ⟨990812, by decide⟩ (by decide) (![⟨990706, by decide⟩,⟨891951, by decide⟩,⟨990756, by decide⟩,⟨990811, by decide⟩]) unmarked_context_11_74825_990812 node_context_11_74825_990812
  intro a
  fin_cases a
  · exact context_12_299300_990706
  · exact context_12_299301_891951
  · exact context_12_299302_990756
  · exact context_12_299303_990811

theorem selected_cut_37095 : selected 9 ⟨990859, by decide⟩
    (prefixPartial 12 299304) = some ⟨12, 2, 0, 990859, 299304, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_299304_990859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299304 ⟨990859, by decide⟩ :=
  accepted_of_selected 12 299304 ⟨990859, by decide⟩ ⟨12, 2, 0, 990859, 299304, 3205, 65536⟩
    (by decide) selected_cut_37095

theorem selected_cut_37096 : selected 9 ⟨990903, by decide⟩
    (prefixPartial 12 299305) = some ⟨12, 2, 0, 990903, 299305, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_299305_990903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299305 ⟨990903, by decide⟩ :=
  accepted_of_selected 12 299305 ⟨990903, by decide⟩ ⟨12, 2, 0, 990903, 299305, 2957, 65536⟩
    (by decide) selected_cut_37096

theorem selected_cut_37097 : selected 9 ⟨990942, by decide⟩
    (prefixPartial 12 299306) = some ⟨12, 2, 0, 990942, 299306, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_299306_990942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299306 ⟨990942, by decide⟩ :=
  accepted_of_selected 12 299306 ⟨990942, by decide⟩ ⟨12, 2, 0, 990942, 299306, 2761, 65536⟩
    (by decide) selected_cut_37097

theorem selected_cut_37098 : selected 9 ⟨990981, by decide⟩
    (prefixPartial 12 299307) = some ⟨12, 2, 0, 990981, 299307, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_299307_990981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299307 ⟨990981, by decide⟩ :=
  accepted_of_selected 12 299307 ⟨990981, by decide⟩ ⟨12, 2, 0, 990981, 299307, 2841, 65536⟩
    (by decide) selected_cut_37098

theorem unmarked_context_11_74826_990982 : frontier 10 ⟨990982, by decide⟩
    (prefixCache 11 74826) (prefixPartial 11 74826) = false := by
  decide +kernel

theorem node_context_11_74826_990982 : EJMOriginalGlobalDAGData.nodes 10 ⟨990982, by decide⟩ =
    .split (coordinate 11) (![⟨990859, by decide⟩,⟨990903, by decide⟩,⟨990942, by decide⟩,⟨990981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74826_990982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74826 ⟨990982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74826
    ⟨990982, by decide⟩ (by decide) (![⟨990859, by decide⟩,⟨990903, by decide⟩,⟨990942, by decide⟩,⟨990981, by decide⟩]) unmarked_context_11_74826_990982 node_context_11_74826_990982
  intro a
  fin_cases a
  · exact context_12_299304_990859
  · exact context_12_299305_990903
  · exact context_12_299306_990942
  · exact context_12_299307_990981

theorem selected_cut_37099 : selected 9 ⟨991022, by decide⟩
    (prefixPartial 12 299308) = some ⟨12, 2, 0, 991022, 299308, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_299308_991022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299308 ⟨991022, by decide⟩ :=
  accepted_of_selected 12 299308 ⟨991022, by decide⟩ ⟨12, 2, 0, 991022, 299308, 3153, 65536⟩
    (by decide) selected_cut_37099

theorem selected_cut_37100 : selected 9 ⟨991073, by decide⟩
    (prefixPartial 12 299309) = some ⟨12, 2, 0, 991073, 299309, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_299309_991073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299309 ⟨991073, by decide⟩ :=
  accepted_of_selected 12 299309 ⟨991073, by decide⟩ ⟨12, 2, 0, 991073, 299309, 3061, 65536⟩
    (by decide) selected_cut_37100

theorem selected_cut_37101 : selected 9 ⟨991115, by decide⟩
    (prefixPartial 12 299310) = some ⟨12, 2, 0, 991115, 299310, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_299310_991115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299310 ⟨991115, by decide⟩ :=
  accepted_of_selected 12 299310 ⟨991115, by decide⟩ ⟨12, 2, 0, 991115, 299310, 2845, 65536⟩
    (by decide) selected_cut_37101

theorem selected_cut_37102 : selected 9 ⟨991166, by decide⟩
    (prefixPartial 12 299311) = some ⟨12, 2, 0, 991166, 299311, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_299311_991166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299311 ⟨991166, by decide⟩ :=
  accepted_of_selected 12 299311 ⟨991166, by decide⟩ ⟨12, 2, 0, 991166, 299311, 3149, 65536⟩
    (by decide) selected_cut_37102

theorem unmarked_context_11_74827_991167 : frontier 10 ⟨991167, by decide⟩
    (prefixCache 11 74827) (prefixPartial 11 74827) = false := by
  decide +kernel

theorem node_context_11_74827_991167 : EJMOriginalGlobalDAGData.nodes 10 ⟨991167, by decide⟩ =
    .split (coordinate 11) (![⟨991022, by decide⟩,⟨991073, by decide⟩,⟨991115, by decide⟩,⟨991166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74827_991167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74827 ⟨991167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74827
    ⟨991167, by decide⟩ (by decide) (![⟨991022, by decide⟩,⟨991073, by decide⟩,⟨991115, by decide⟩,⟨991166, by decide⟩]) unmarked_context_11_74827_991167 node_context_11_74827_991167
  intro a
  fin_cases a
  · exact context_12_299308_991022
  · exact context_12_299309_991073
  · exact context_12_299310_991115
  · exact context_12_299311_991166

theorem unmarked_context_10_18706_991168 : frontier 11 ⟨991168, by decide⟩
    (prefixCache 10 18706) (prefixPartial 10 18706) = false := by
  decide +kernel

theorem node_context_10_18706_991168 : EJMOriginalGlobalDAGData.nodes 11 ⟨991168, by decide⟩ =
    .split (coordinate 10) (![⟨990632, by decide⟩,⟨990812, by decide⟩,⟨990982, by decide⟩,⟨991167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18706_991168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18706 ⟨991168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18706
    ⟨991168, by decide⟩ (by decide) (![⟨990632, by decide⟩,⟨990812, by decide⟩,⟨990982, by decide⟩,⟨991167, by decide⟩]) unmarked_context_10_18706_991168 node_context_10_18706_991168
  intro a
  fin_cases a
  · exact context_11_74824_990632
  · exact context_11_74825_990812
  · exact context_11_74826_990982
  · exact context_11_74827_991167

theorem selected_cut_37103 : selected 9 ⟨991210, by decide⟩
    (prefixPartial 12 299312) = some ⟨12, 2, 0, 991210, 299312, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_299312_991210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299312 ⟨991210, by decide⟩ :=
  accepted_of_selected 12 299312 ⟨991210, by decide⟩ ⟨12, 2, 0, 991210, 299312, 2605, 65536⟩
    (by decide) selected_cut_37103

theorem selected_cut_37104 : selected 9 ⟨991253, by decide⟩
    (prefixPartial 12 299313) = some ⟨12, 2, 0, 991253, 299313, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_299313_991253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299313 ⟨991253, by decide⟩ :=
  accepted_of_selected 12 299313 ⟨991253, by decide⟩ ⟨12, 2, 0, 991253, 299313, 2557, 65536⟩
    (by decide) selected_cut_37104

theorem selected_cut_37105 : selected 9 ⟨991281, by decide⟩
    (prefixPartial 12 299314) = some ⟨12, 2, 0, 991281, 299314, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_299314_991281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299314 ⟨991281, by decide⟩ :=
  accepted_of_selected 12 299314 ⟨991281, by decide⟩ ⟨12, 2, 0, 991281, 299314, 2245, 65536⟩
    (by decide) selected_cut_37105

theorem selected_cut_37106 : selected 9 ⟨991321, by decide⟩
    (prefixPartial 12 299315) = some ⟨12, 2, 0, 991321, 299315, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_299315_991321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299315 ⟨991321, by decide⟩ :=
  accepted_of_selected 12 299315 ⟨991321, by decide⟩ ⟨12, 2, 0, 991321, 299315, 2405, 65536⟩
    (by decide) selected_cut_37106

theorem unmarked_context_11_74828_991322 : frontier 10 ⟨991322, by decide⟩
    (prefixCache 11 74828) (prefixPartial 11 74828) = false := by
  decide +kernel

theorem node_context_11_74828_991322 : EJMOriginalGlobalDAGData.nodes 10 ⟨991322, by decide⟩ =
    .split (coordinate 11) (![⟨991210, by decide⟩,⟨991253, by decide⟩,⟨991281, by decide⟩,⟨991321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74828_991322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74828 ⟨991322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74828
    ⟨991322, by decide⟩ (by decide) (![⟨991210, by decide⟩,⟨991253, by decide⟩,⟨991281, by decide⟩,⟨991321, by decide⟩]) unmarked_context_11_74828_991322 node_context_11_74828_991322
  intro a
  fin_cases a
  · exact context_12_299312_991210
  · exact context_12_299313_991253
  · exact context_12_299314_991281
  · exact context_12_299315_991321

theorem selected_cut_37107 : selected 9 ⟨991383, by decide⟩
    (prefixPartial 12 299316) = some ⟨12, 2, 0, 991383, 299316, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_299316_991383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299316 ⟨991383, by decide⟩ :=
  accepted_of_selected 12 299316 ⟨991383, by decide⟩ ⟨12, 2, 0, 991383, 299316, 3441, 65536⟩
    (by decide) selected_cut_37107

theorem selected_cut_37108 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 299317) = some ⟨12, 1, 0, 891951, 299317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299317_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299317 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 299317 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 299317, 1, 65536⟩
    (by decide) selected_cut_37108

theorem selected_cut_37109 : selected 9 ⟨991427, by decide⟩
    (prefixPartial 12 299318) = some ⟨12, 2, 0, 991427, 299318, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_299318_991427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299318 ⟨991427, by decide⟩ :=
  accepted_of_selected 12 299318 ⟨991427, by decide⟩ ⟨12, 2, 0, 991427, 299318, 2913, 65536⟩
    (by decide) selected_cut_37109

theorem selected_cut_37110 : selected 9 ⟨991466, by decide⟩
    (prefixPartial 12 299319) = some ⟨12, 2, 0, 991466, 299319, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_299319_991466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299319 ⟨991466, by decide⟩ :=
  accepted_of_selected 12 299319 ⟨991466, by decide⟩ ⟨12, 2, 0, 991466, 299319, 2929, 65536⟩
    (by decide) selected_cut_37110

theorem unmarked_context_11_74829_991467 : frontier 10 ⟨991467, by decide⟩
    (prefixCache 11 74829) (prefixPartial 11 74829) = false := by
  decide +kernel

theorem node_context_11_74829_991467 : EJMOriginalGlobalDAGData.nodes 10 ⟨991467, by decide⟩ =
    .split (coordinate 11) (![⟨991383, by decide⟩,⟨891951, by decide⟩,⟨991427, by decide⟩,⟨991466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74829_991467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74829 ⟨991467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74829
    ⟨991467, by decide⟩ (by decide) (![⟨991383, by decide⟩,⟨891951, by decide⟩,⟨991427, by decide⟩,⟨991466, by decide⟩]) unmarked_context_11_74829_991467 node_context_11_74829_991467
  intro a
  fin_cases a
  · exact context_12_299316_991383
  · exact context_12_299317_891951
  · exact context_12_299318_991427
  · exact context_12_299319_991466

theorem selected_cut_37111 : selected 9 ⟨991508, by decide⟩
    (prefixPartial 12 299320) = some ⟨12, 2, 0, 991508, 299320, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_299320_991508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299320 ⟨991508, by decide⟩ :=
  accepted_of_selected 12 299320 ⟨991508, by decide⟩ ⟨12, 2, 0, 991508, 299320, 2669, 65536⟩
    (by decide) selected_cut_37111

theorem selected_cut_37112 : selected 9 ⟨991548, by decide⟩
    (prefixPartial 12 299321) = some ⟨12, 2, 0, 991548, 299321, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_299321_991548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299321 ⟨991548, by decide⟩ :=
  accepted_of_selected 12 299321 ⟨991548, by decide⟩ ⟨12, 2, 0, 991548, 299321, 2545, 65536⟩
    (by decide) selected_cut_37112

theorem selected_cut_37113 : selected 9 ⟨991585, by decide⟩
    (prefixPartial 12 299322) = some ⟨12, 2, 0, 991585, 299322, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_299322_991585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299322 ⟨991585, by decide⟩ :=
  accepted_of_selected 12 299322 ⟨991585, by decide⟩ ⟨12, 2, 0, 991585, 299322, 2641, 65536⟩
    (by decide) selected_cut_37113

theorem selected_cut_37114 : selected 9 ⟨991624, by decide⟩
    (prefixPartial 12 299323) = some ⟨12, 2, 0, 991624, 299323, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_299323_991624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299323 ⟨991624, by decide⟩ :=
  accepted_of_selected 12 299323 ⟨991624, by decide⟩ ⟨12, 2, 0, 991624, 299323, 2493, 65536⟩
    (by decide) selected_cut_37114

theorem unmarked_context_11_74830_991625 : frontier 10 ⟨991625, by decide⟩
    (prefixCache 11 74830) (prefixPartial 11 74830) = false := by
  decide +kernel

theorem node_context_11_74830_991625 : EJMOriginalGlobalDAGData.nodes 10 ⟨991625, by decide⟩ =
    .split (coordinate 11) (![⟨991508, by decide⟩,⟨991548, by decide⟩,⟨991585, by decide⟩,⟨991624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74830_991625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74830 ⟨991625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74830
    ⟨991625, by decide⟩ (by decide) (![⟨991508, by decide⟩,⟨991548, by decide⟩,⟨991585, by decide⟩,⟨991624, by decide⟩]) unmarked_context_11_74830_991625 node_context_11_74830_991625
  intro a
  fin_cases a
  · exact context_12_299320_991508
  · exact context_12_299321_991548
  · exact context_12_299322_991585
  · exact context_12_299323_991624

theorem selected_cut_37115 : selected 9 ⟨991658, by decide⟩
    (prefixPartial 12 299324) = some ⟨12, 2, 0, 991658, 299324, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_299324_991658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299324 ⟨991658, by decide⟩ :=
  accepted_of_selected 12 299324 ⟨991658, by decide⟩ ⟨12, 2, 0, 991658, 299324, 2533, 65536⟩
    (by decide) selected_cut_37115

theorem selected_cut_37116 : selected 9 ⟨991699, by decide⟩
    (prefixPartial 12 299325) = some ⟨12, 2, 0, 991699, 299325, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_299325_991699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299325 ⟨991699, by decide⟩ :=
  accepted_of_selected 12 299325 ⟨991699, by decide⟩ ⟨12, 2, 0, 991699, 299325, 2641, 65536⟩
    (by decide) selected_cut_37116

theorem selected_cut_37117 : selected 9 ⟨991732, by decide⟩
    (prefixPartial 12 299326) = some ⟨12, 2, 0, 991732, 299326, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_299326_991732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299326 ⟨991732, by decide⟩ :=
  accepted_of_selected 12 299326 ⟨991732, by decide⟩ ⟨12, 2, 0, 991732, 299326, 2333, 65536⟩
    (by decide) selected_cut_37117

theorem selected_cut_37118 : selected 9 ⟨991767, by decide⟩
    (prefixPartial 12 299327) = some ⟨12, 2, 0, 991767, 299327, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_299327_991767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299327 ⟨991767, by decide⟩ :=
  accepted_of_selected 12 299327 ⟨991767, by decide⟩ ⟨12, 2, 0, 991767, 299327, 2485, 65536⟩
    (by decide) selected_cut_37118

theorem unmarked_context_11_74831_991768 : frontier 10 ⟨991768, by decide⟩
    (prefixCache 11 74831) (prefixPartial 11 74831) = false := by
  decide +kernel

theorem node_context_11_74831_991768 : EJMOriginalGlobalDAGData.nodes 10 ⟨991768, by decide⟩ =
    .split (coordinate 11) (![⟨991658, by decide⟩,⟨991699, by decide⟩,⟨991732, by decide⟩,⟨991767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74831_991768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74831 ⟨991768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74831
    ⟨991768, by decide⟩ (by decide) (![⟨991658, by decide⟩,⟨991699, by decide⟩,⟨991732, by decide⟩,⟨991767, by decide⟩]) unmarked_context_11_74831_991768 node_context_11_74831_991768
  intro a
  fin_cases a
  · exact context_12_299324_991658
  · exact context_12_299325_991699
  · exact context_12_299326_991732
  · exact context_12_299327_991767

theorem unmarked_context_10_18707_991769 : frontier 11 ⟨991769, by decide⟩
    (prefixCache 10 18707) (prefixPartial 10 18707) = false := by
  decide +kernel

theorem node_context_10_18707_991769 : EJMOriginalGlobalDAGData.nodes 11 ⟨991769, by decide⟩ =
    .split (coordinate 10) (![⟨991322, by decide⟩,⟨991467, by decide⟩,⟨991625, by decide⟩,⟨991768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18707_991769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18707 ⟨991769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18707
    ⟨991769, by decide⟩ (by decide) (![⟨991322, by decide⟩,⟨991467, by decide⟩,⟨991625, by decide⟩,⟨991768, by decide⟩]) unmarked_context_10_18707_991769 node_context_10_18707_991769
  intro a
  fin_cases a
  · exact context_11_74828_991322
  · exact context_11_74829_991467
  · exact context_11_74830_991625
  · exact context_11_74831_991768

theorem unmarked_context_9_4676_991770 : frontier 12 ⟨991770, by decide⟩
    (prefixCache 9 4676) (prefixPartial 9 4676) = false := by
  decide +kernel

theorem node_context_9_4676_991770 : EJMOriginalGlobalDAGData.nodes 12 ⟨991770, by decide⟩ =
    .split (coordinate 9) (![⟨989813, by decide⟩,⟨990475, by decide⟩,⟨991168, by decide⟩,⟨991769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4676_991770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4676 ⟨991770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4676
    ⟨991770, by decide⟩ (by decide) (![⟨989813, by decide⟩,⟨990475, by decide⟩,⟨991168, by decide⟩,⟨991769, by decide⟩]) unmarked_context_9_4676_991770 node_context_9_4676_991770
  intro a
  fin_cases a
  · exact context_10_18704_989813
  · exact context_10_18705_990475
  · exact context_10_18706_991168
  · exact context_10_18707_991769

theorem selected_cut_37119 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74832) = some ⟨11, 1, 0, 907917, 74832, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74832_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74832 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74832 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74832, 1, 262144⟩
    (by decide) selected_cut_37119

theorem selected_cut_37120 : selected 9 ⟨991817, by decide⟩
    (prefixPartial 12 299332) = some ⟨12, 2, 0, 991817, 299332, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_299332_991817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299332 ⟨991817, by decide⟩ :=
  accepted_of_selected 12 299332 ⟨991817, by decide⟩ ⟨12, 2, 0, 991817, 299332, 2601, 65536⟩
    (by decide) selected_cut_37120

theorem selected_cut_37121 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 299333) = some ⟨12, 1, 0, 891951, 299333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299333_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299333 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 299333 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 299333, 1, 65536⟩
    (by decide) selected_cut_37121

theorem selected_cut_37122 : selected 9 ⟨991854, by decide⟩
    (prefixPartial 12 299334) = some ⟨12, 2, 0, 991854, 299334, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_299334_991854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299334 ⟨991854, by decide⟩ :=
  accepted_of_selected 12 299334 ⟨991854, by decide⟩ ⟨12, 2, 0, 991854, 299334, 2097, 65536⟩
    (by decide) selected_cut_37122

theorem selected_cut_37123 : selected 9 ⟨991882, by decide⟩
    (prefixPartial 12 299335) = some ⟨12, 2, 0, 991882, 299335, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_299335_991882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299335 ⟨991882, by decide⟩ :=
  accepted_of_selected 12 299335 ⟨991882, by decide⟩ ⟨12, 2, 0, 991882, 299335, 2205, 65536⟩
    (by decide) selected_cut_37123

theorem unmarked_context_11_74833_991883 : frontier 10 ⟨991883, by decide⟩
    (prefixCache 11 74833) (prefixPartial 11 74833) = false := by
  decide +kernel

theorem node_context_11_74833_991883 : EJMOriginalGlobalDAGData.nodes 10 ⟨991883, by decide⟩ =
    .split (coordinate 11) (![⟨991817, by decide⟩,⟨891951, by decide⟩,⟨991854, by decide⟩,⟨991882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74833_991883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74833 ⟨991883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74833
    ⟨991883, by decide⟩ (by decide) (![⟨991817, by decide⟩,⟨891951, by decide⟩,⟨991854, by decide⟩,⟨991882, by decide⟩]) unmarked_context_11_74833_991883 node_context_11_74833_991883
  intro a
  fin_cases a
  · exact context_12_299332_991817
  · exact context_12_299333_891951
  · exact context_12_299334_991854
  · exact context_12_299335_991882

theorem selected_cut_37124 : selected 9 ⟨991916, by decide⟩
    (prefixPartial 12 299336) = some ⟨12, 2, 0, 991916, 299336, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_299336_991916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299336 ⟨991916, by decide⟩ :=
  accepted_of_selected 12 299336 ⟨991916, by decide⟩ ⟨12, 2, 0, 991916, 299336, 2225, 65536⟩
    (by decide) selected_cut_37124

theorem selected_cut_37125 : selected 9 ⟨991946, by decide⟩
    (prefixPartial 12 299337) = some ⟨12, 2, 0, 991946, 299337, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_299337_991946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299337 ⟨991946, by decide⟩ :=
  accepted_of_selected 12 299337 ⟨991946, by decide⟩ ⟨12, 2, 0, 991946, 299337, 2149, 65536⟩
    (by decide) selected_cut_37125

theorem selected_cut_37126 : selected 9 ⟨991978, by decide⟩
    (prefixPartial 12 299338) = some ⟨12, 2, 0, 991978, 299338, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_299338_991978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299338 ⟨991978, by decide⟩ :=
  accepted_of_selected 12 299338 ⟨991978, by decide⟩ ⟨12, 2, 0, 991978, 299338, 2145, 65536⟩
    (by decide) selected_cut_37126

theorem selected_cut_37127 : selected 9 ⟨992002, by decide⟩
    (prefixPartial 12 299339) = some ⟨12, 2, 0, 992002, 299339, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_299339_992002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299339 ⟨992002, by decide⟩ :=
  accepted_of_selected 12 299339 ⟨992002, by decide⟩ ⟨12, 2, 0, 992002, 299339, 1961, 65536⟩
    (by decide) selected_cut_37127

theorem unmarked_context_11_74834_992003 : frontier 10 ⟨992003, by decide⟩
    (prefixCache 11 74834) (prefixPartial 11 74834) = false := by
  decide +kernel

theorem node_context_11_74834_992003 : EJMOriginalGlobalDAGData.nodes 10 ⟨992003, by decide⟩ =
    .split (coordinate 11) (![⟨991916, by decide⟩,⟨991946, by decide⟩,⟨991978, by decide⟩,⟨992002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74834_992003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74834 ⟨992003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74834
    ⟨992003, by decide⟩ (by decide) (![⟨991916, by decide⟩,⟨991946, by decide⟩,⟨991978, by decide⟩,⟨992002, by decide⟩]) unmarked_context_11_74834_992003 node_context_11_74834_992003
  intro a
  fin_cases a
  · exact context_12_299336_991916
  · exact context_12_299337_991946
  · exact context_12_299338_991978
  · exact context_12_299339_992002

theorem selected_cut_37128 : selected 9 ⟨992038, by decide⟩
    (prefixPartial 12 299340) = some ⟨12, 2, 0, 992038, 299340, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_299340_992038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299340 ⟨992038, by decide⟩ :=
  accepted_of_selected 12 299340 ⟨992038, by decide⟩ ⟨12, 2, 0, 992038, 299340, 2181, 65536⟩
    (by decide) selected_cut_37128

theorem selected_cut_37129 : selected 9 ⟨992068, by decide⟩
    (prefixPartial 12 299341) = some ⟨12, 2, 0, 992068, 299341, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_299341_992068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299341 ⟨992068, by decide⟩ :=
  accepted_of_selected 12 299341 ⟨992068, by decide⟩ ⟨12, 2, 0, 992068, 299341, 2185, 65536⟩
    (by decide) selected_cut_37129

theorem selected_cut_37130 : selected 9 ⟨992094, by decide⟩
    (prefixPartial 12 299342) = some ⟨12, 2, 0, 992094, 299342, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_299342_992094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299342 ⟨992094, by decide⟩ :=
  accepted_of_selected 12 299342 ⟨992094, by decide⟩ ⟨12, 2, 0, 992094, 299342, 1881, 65536⟩
    (by decide) selected_cut_37130

theorem selected_cut_37131 : selected 9 ⟨992126, by decide⟩
    (prefixPartial 12 299343) = some ⟨12, 2, 0, 992126, 299343, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_299343_992126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299343 ⟨992126, by decide⟩ :=
  accepted_of_selected 12 299343 ⟨992126, by decide⟩ ⟨12, 2, 0, 992126, 299343, 2109, 65536⟩
    (by decide) selected_cut_37131

theorem unmarked_context_11_74835_992127 : frontier 10 ⟨992127, by decide⟩
    (prefixCache 11 74835) (prefixPartial 11 74835) = false := by
  decide +kernel

theorem node_context_11_74835_992127 : EJMOriginalGlobalDAGData.nodes 10 ⟨992127, by decide⟩ =
    .split (coordinate 11) (![⟨992038, by decide⟩,⟨992068, by decide⟩,⟨992094, by decide⟩,⟨992126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74835_992127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74835 ⟨992127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74835
    ⟨992127, by decide⟩ (by decide) (![⟨992038, by decide⟩,⟨992068, by decide⟩,⟨992094, by decide⟩,⟨992126, by decide⟩]) unmarked_context_11_74835_992127 node_context_11_74835_992127
  intro a
  fin_cases a
  · exact context_12_299340_992038
  · exact context_12_299341_992068
  · exact context_12_299342_992094
  · exact context_12_299343_992126

theorem unmarked_context_10_18708_992128 : frontier 11 ⟨992128, by decide⟩
    (prefixCache 10 18708) (prefixPartial 10 18708) = false := by
  decide +kernel

theorem node_context_10_18708_992128 : EJMOriginalGlobalDAGData.nodes 11 ⟨992128, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨991883, by decide⟩,⟨992003, by decide⟩,⟨992127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18708_992128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18708 ⟨992128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18708
    ⟨992128, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨991883, by decide⟩,⟨992003, by decide⟩,⟨992127, by decide⟩]) unmarked_context_10_18708_992128 node_context_10_18708_992128
  intro a
  fin_cases a
  · exact context_11_74832_907917
  · exact context_11_74833_991883
  · exact context_11_74834_992003
  · exact context_11_74835_992127

theorem selected_cut_37132 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18709) = some ⟨10, 1, 0, 893098, 18709, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18709_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18709 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18709 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18709, 1, 1048576⟩
    (by decide) selected_cut_37132

theorem selected_cut_37133 : selected 9 ⟨992161, by decide⟩
    (prefixPartial 12 299360) = some ⟨12, 2, 0, 992161, 299360, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_299360_992161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299360 ⟨992161, by decide⟩ :=
  accepted_of_selected 12 299360 ⟨992161, by decide⟩ ⟨12, 2, 0, 992161, 299360, 1869, 65536⟩
    (by decide) selected_cut_37133

theorem selected_cut_37134 : selected 9 ⟨992190, by decide⟩
    (prefixPartial 12 299361) = some ⟨12, 2, 0, 992190, 299361, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_299361_992190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299361 ⟨992190, by decide⟩ :=
  accepted_of_selected 12 299361 ⟨992190, by decide⟩ ⟨12, 2, 0, 992190, 299361, 1997, 65536⟩
    (by decide) selected_cut_37134

theorem selected_cut_37135 : selected 9 ⟨992213, by decide⟩
    (prefixPartial 12 299362) = some ⟨12, 2, 0, 992213, 299362, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_299362_992213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299362 ⟨992213, by decide⟩ :=
  accepted_of_selected 12 299362 ⟨992213, by decide⟩ ⟨12, 2, 0, 992213, 299362, 1677, 65536⟩
    (by decide) selected_cut_37135

theorem selected_cut_37136 : selected 9 ⟨992234, by decide⟩
    (prefixPartial 12 299363) = some ⟨12, 2, 0, 992234, 299363, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_299363_992234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299363 ⟨992234, by decide⟩ :=
  accepted_of_selected 12 299363 ⟨992234, by decide⟩ ⟨12, 2, 0, 992234, 299363, 1697, 65536⟩
    (by decide) selected_cut_37136

theorem unmarked_context_11_74840_992235 : frontier 10 ⟨992235, by decide⟩
    (prefixCache 11 74840) (prefixPartial 11 74840) = false := by
  decide +kernel

theorem node_context_11_74840_992235 : EJMOriginalGlobalDAGData.nodes 10 ⟨992235, by decide⟩ =
    .split (coordinate 11) (![⟨992161, by decide⟩,⟨992190, by decide⟩,⟨992213, by decide⟩,⟨992234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74840_992235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74840 ⟨992235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74840
    ⟨992235, by decide⟩ (by decide) (![⟨992161, by decide⟩,⟨992190, by decide⟩,⟨992213, by decide⟩,⟨992234, by decide⟩]) unmarked_context_11_74840_992235 node_context_11_74840_992235
  intro a
  fin_cases a
  · exact context_12_299360_992161
  · exact context_12_299361_992190
  · exact context_12_299362_992213
  · exact context_12_299363_992234

theorem selected_cut_37137 : selected 9 ⟨992264, by decide⟩
    (prefixPartial 12 299364) = some ⟨12, 2, 0, 992264, 299364, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_299364_992264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299364 ⟨992264, by decide⟩ :=
  accepted_of_selected 12 299364 ⟨992264, by decide⟩ ⟨12, 2, 0, 992264, 299364, 2021, 65536⟩
    (by decide) selected_cut_37137

theorem selected_cut_37138 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 299365) = some ⟨12, 1, 0, 891951, 299365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299365_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299365 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 299365 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 299365, 1, 65536⟩
    (by decide) selected_cut_37138

theorem selected_cut_37139 : selected 9 ⟨992287, by decide⟩
    (prefixPartial 12 299366) = some ⟨12, 2, 0, 992287, 299366, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_299366_992287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299366 ⟨992287, by decide⟩ :=
  accepted_of_selected 12 299366 ⟨992287, by decide⟩ ⟨12, 2, 0, 992287, 299366, 1721, 65536⟩
    (by decide) selected_cut_37139

theorem selected_cut_37140 : selected 9 ⟨992310, by decide⟩
    (prefixPartial 12 299367) = some ⟨12, 2, 0, 992310, 299367, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_299367_992310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299367 ⟨992310, by decide⟩ :=
  accepted_of_selected 12 299367 ⟨992310, by decide⟩ ⟨12, 2, 0, 992310, 299367, 1865, 65536⟩
    (by decide) selected_cut_37140

theorem unmarked_context_11_74841_992311 : frontier 10 ⟨992311, by decide⟩
    (prefixCache 11 74841) (prefixPartial 11 74841) = false := by
  decide +kernel

theorem node_context_11_74841_992311 : EJMOriginalGlobalDAGData.nodes 10 ⟨992311, by decide⟩ =
    .split (coordinate 11) (![⟨992264, by decide⟩,⟨891951, by decide⟩,⟨992287, by decide⟩,⟨992310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74841_992311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74841 ⟨992311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74841
    ⟨992311, by decide⟩ (by decide) (![⟨992264, by decide⟩,⟨891951, by decide⟩,⟨992287, by decide⟩,⟨992310, by decide⟩]) unmarked_context_11_74841_992311 node_context_11_74841_992311
  intro a
  fin_cases a
  · exact context_12_299364_992264
  · exact context_12_299365_891951
  · exact context_12_299366_992287
  · exact context_12_299367_992310

theorem selected_cut_37141 : selected 9 ⟨992334, by decide⟩
    (prefixPartial 12 299368) = some ⟨12, 2, 0, 992334, 299368, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_299368_992334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299368 ⟨992334, by decide⟩ :=
  accepted_of_selected 12 299368 ⟨992334, by decide⟩ ⟨12, 2, 0, 992334, 299368, 1797, 65536⟩
    (by decide) selected_cut_37141

theorem selected_cut_37142 : selected 9 ⟨992363, by decide⟩
    (prefixPartial 12 299369) = some ⟨12, 2, 0, 992363, 299369, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_299369_992363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299369 ⟨992363, by decide⟩ :=
  accepted_of_selected 12 299369 ⟨992363, by decide⟩ ⟨12, 2, 0, 992363, 299369, 2013, 65536⟩
    (by decide) selected_cut_37142

theorem selected_cut_37143 : selected 9 ⟨992417, by decide⟩
    (prefixPartial 12 299370) = some ⟨12, 2, 0, 992417, 299370, 865, 65536⟩ := by
  decide +kernel

theorem context_12_299370_992417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299370 ⟨992417, by decide⟩ :=
  accepted_of_selected 12 299370 ⟨992417, by decide⟩ ⟨12, 2, 0, 992417, 299370, 865, 65536⟩
    (by decide) selected_cut_37143

theorem selected_cut_37144 : selected 9 ⟨992447, by decide⟩
    (prefixPartial 12 299371) = some ⟨12, 2, 0, 992447, 299371, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_299371_992447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299371 ⟨992447, by decide⟩ :=
  accepted_of_selected 12 299371 ⟨992447, by decide⟩ ⟨12, 2, 0, 992447, 299371, 1749, 65536⟩
    (by decide) selected_cut_37144

theorem unmarked_context_11_74842_992448 : frontier 10 ⟨992448, by decide⟩
    (prefixCache 11 74842) (prefixPartial 11 74842) = false := by
  decide +kernel

theorem node_context_11_74842_992448 : EJMOriginalGlobalDAGData.nodes 10 ⟨992448, by decide⟩ =
    .split (coordinate 11) (![⟨992334, by decide⟩,⟨992363, by decide⟩,⟨992417, by decide⟩,⟨992447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74842_992448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74842 ⟨992448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74842
    ⟨992448, by decide⟩ (by decide) (![⟨992334, by decide⟩,⟨992363, by decide⟩,⟨992417, by decide⟩,⟨992447, by decide⟩]) unmarked_context_11_74842_992448 node_context_11_74842_992448
  intro a
  fin_cases a
  · exact context_12_299368_992334
  · exact context_12_299369_992363
  · exact context_12_299370_992417
  · exact context_12_299371_992447

theorem selected_cut_37145 : selected 9 ⟨992470, by decide⟩
    (prefixPartial 12 299372) = some ⟨12, 2, 0, 992470, 299372, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_299372_992470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299372 ⟨992470, by decide⟩ :=
  accepted_of_selected 12 299372 ⟨992470, by decide⟩ ⟨12, 2, 0, 992470, 299372, 1741, 65536⟩
    (by decide) selected_cut_37145

theorem selected_cut_37146 : selected 9 ⟨992496, by decide⟩
    (prefixPartial 12 299373) = some ⟨12, 2, 0, 992496, 299373, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_299373_992496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299373 ⟨992496, by decide⟩ :=
  accepted_of_selected 12 299373 ⟨992496, by decide⟩ ⟨12, 2, 0, 992496, 299373, 1917, 65536⟩
    (by decide) selected_cut_37146

theorem selected_cut_37147 : selected 9 ⟨992520, by decide⟩
    (prefixPartial 12 299374) = some ⟨12, 2, 0, 992520, 299374, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_299374_992520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299374 ⟨992520, by decide⟩ :=
  accepted_of_selected 12 299374 ⟨992520, by decide⟩ ⟨12, 2, 0, 992520, 299374, 1713, 65536⟩
    (by decide) selected_cut_37147

theorem selected_cut_37148 : selected 9 ⟨992546, by decide⟩
    (prefixPartial 12 299375) = some ⟨12, 2, 0, 992546, 299375, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_299375_992546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299375 ⟨992546, by decide⟩ :=
  accepted_of_selected 12 299375 ⟨992546, by decide⟩ ⟨12, 2, 0, 992546, 299375, 1841, 65536⟩
    (by decide) selected_cut_37148

theorem unmarked_context_11_74843_992547 : frontier 10 ⟨992547, by decide⟩
    (prefixCache 11 74843) (prefixPartial 11 74843) = false := by
  decide +kernel

theorem node_context_11_74843_992547 : EJMOriginalGlobalDAGData.nodes 10 ⟨992547, by decide⟩ =
    .split (coordinate 11) (![⟨992470, by decide⟩,⟨992496, by decide⟩,⟨992520, by decide⟩,⟨992546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74843_992547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74843 ⟨992547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74843
    ⟨992547, by decide⟩ (by decide) (![⟨992470, by decide⟩,⟨992496, by decide⟩,⟨992520, by decide⟩,⟨992546, by decide⟩]) unmarked_context_11_74843_992547 node_context_11_74843_992547
  intro a
  fin_cases a
  · exact context_12_299372_992470
  · exact context_12_299373_992496
  · exact context_12_299374_992520
  · exact context_12_299375_992546

theorem unmarked_context_10_18710_992548 : frontier 11 ⟨992548, by decide⟩
    (prefixCache 10 18710) (prefixPartial 10 18710) = false := by
  decide +kernel

theorem node_context_10_18710_992548 : EJMOriginalGlobalDAGData.nodes 11 ⟨992548, by decide⟩ =
    .split (coordinate 10) (![⟨992235, by decide⟩,⟨992311, by decide⟩,⟨992448, by decide⟩,⟨992547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18710_992548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18710 ⟨992548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18710
    ⟨992548, by decide⟩ (by decide) (![⟨992235, by decide⟩,⟨992311, by decide⟩,⟨992448, by decide⟩,⟨992547, by decide⟩]) unmarked_context_10_18710_992548 node_context_10_18710_992548
  intro a
  fin_cases a
  · exact context_11_74840_992235
  · exact context_11_74841_992311
  · exact context_11_74842_992448
  · exact context_11_74843_992547

theorem selected_cut_37149 : selected 9 ⟨992566, by decide⟩
    (prefixPartial 12 299376) = some ⟨12, 2, 0, 992566, 299376, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_299376_992566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299376 ⟨992566, by decide⟩ :=
  accepted_of_selected 12 299376 ⟨992566, by decide⟩ ⟨12, 2, 0, 992566, 299376, 1641, 65536⟩
    (by decide) selected_cut_37149

theorem selected_cut_37150 : selected 9 ⟨992587, by decide⟩
    (prefixPartial 12 299377) = some ⟨12, 2, 0, 992587, 299377, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_299377_992587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299377 ⟨992587, by decide⟩ :=
  accepted_of_selected 12 299377 ⟨992587, by decide⟩ ⟨12, 2, 0, 992587, 299377, 1713, 65536⟩
    (by decide) selected_cut_37150

theorem selected_cut_37151 : selected 9 ⟨992607, by decide⟩
    (prefixPartial 12 299378) = some ⟨12, 2, 0, 992607, 299378, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_299378_992607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299378 ⟨992607, by decide⟩ :=
  accepted_of_selected 12 299378 ⟨992607, by decide⟩ ⟨12, 2, 0, 992607, 299378, 1405, 65536⟩
    (by decide) selected_cut_37151

theorem selected_cut_37152 : selected 9 ⟨992625, by decide⟩
    (prefixPartial 12 299379) = some ⟨12, 2, 0, 992625, 299379, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_299379_992625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299379 ⟨992625, by decide⟩ :=
  accepted_of_selected 12 299379 ⟨992625, by decide⟩ ⟨12, 2, 0, 992625, 299379, 1493, 65536⟩
    (by decide) selected_cut_37152

theorem unmarked_context_11_74844_992626 : frontier 10 ⟨992626, by decide⟩
    (prefixCache 11 74844) (prefixPartial 11 74844) = false := by
  decide +kernel

theorem node_context_11_74844_992626 : EJMOriginalGlobalDAGData.nodes 10 ⟨992626, by decide⟩ =
    .split (coordinate 11) (![⟨992566, by decide⟩,⟨992587, by decide⟩,⟨992607, by decide⟩,⟨992625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74844_992626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74844 ⟨992626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74844
    ⟨992626, by decide⟩ (by decide) (![⟨992566, by decide⟩,⟨992587, by decide⟩,⟨992607, by decide⟩,⟨992625, by decide⟩]) unmarked_context_11_74844_992626 node_context_11_74844_992626
  intro a
  fin_cases a
  · exact context_12_299376_992566
  · exact context_12_299377_992587
  · exact context_12_299378_992607
  · exact context_12_299379_992625

theorem selected_cut_37153 : selected 9 ⟨992651, by decide⟩
    (prefixPartial 12 299380) = some ⟨12, 2, 0, 992651, 299380, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_299380_992651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299380 ⟨992651, by decide⟩ :=
  accepted_of_selected 12 299380 ⟨992651, by decide⟩ ⟨12, 2, 0, 992651, 299380, 1825, 65536⟩
    (by decide) selected_cut_37153

theorem selected_cut_37154 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 299381) = some ⟨12, 1, 0, 891951, 299381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299381_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299381 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 299381 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 299381, 1, 65536⟩
    (by decide) selected_cut_37154

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
