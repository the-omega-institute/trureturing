/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover074
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07203 : selected 8 ⟨209791, by decide⟩
    (prefixPartial 13 88470) = some ⟨13, 2, 0, 209791, 88470, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_88470_209791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88470 ⟨209791, by decide⟩ :=
  accepted_of_selected 13 88470 ⟨209791, by decide⟩ ⟨13, 2, 0, 209791, 88470, 2105, 16384⟩
    (by decide) selected_cut_07203

theorem selected_cut_07204 : selected 8 ⟨209801, by decide⟩
    (prefixPartial 13 88471) = some ⟨13, 2, 0, 209801, 88471, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_88471_209801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88471 ⟨209801, by decide⟩ :=
  accepted_of_selected 13 88471 ⟨209801, by decide⟩ ⟨13, 2, 0, 209801, 88471, 1025, 16384⟩
    (by decide) selected_cut_07204

theorem unmarked_context_12_22117_209802 : frontier 9 ⟨209802, by decide⟩
    (prefixCache 12 22117) (prefixPartial 12 22117) = false := by
  decide +kernel

theorem node_context_12_22117_209802 : EJMOriginalGlobalDAGData.nodes 9 ⟨209802, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209762, by decide⟩,⟨209791, by decide⟩,⟨209801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22117_209802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22117 ⟨209802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22117
    ⟨209802, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209762, by decide⟩,⟨209791, by decide⟩,⟨209801, by decide⟩]) unmarked_context_12_22117_209802 node_context_12_22117_209802
  intro a
  fin_cases a
  · exact context_13_88468_3444
  · exact context_13_88469_209762
  · exact context_13_88470_209791
  · exact context_13_88471_209801

theorem selected_cut_07205 : selected 9 ⟨209844, by decide⟩
    (prefixPartial 12 22118) = some ⟨12, 2, 0, 209844, 22118, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_22118_209844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22118 ⟨209844, by decide⟩ :=
  accepted_of_selected 12 22118 ⟨209844, by decide⟩ ⟨12, 2, 0, 209844, 22118, 3245, 65536⟩
    (by decide) selected_cut_07205

theorem selected_cut_07206 : selected 9 ⟨209890, by decide⟩
    (prefixPartial 12 22119) = some ⟨12, 2, 0, 209890, 22119, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_22119_209890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22119 ⟨209890, by decide⟩ :=
  accepted_of_selected 12 22119 ⟨209890, by decide⟩ ⟨12, 2, 0, 209890, 22119, 3889, 65536⟩
    (by decide) selected_cut_07206

theorem unmarked_context_11_5529_209891 : frontier 10 ⟨209891, by decide⟩
    (prefixCache 11 5529) (prefixPartial 11 5529) = false := by
  decide +kernel

theorem node_context_11_5529_209891 : EJMOriginalGlobalDAGData.nodes 10 ⟨209891, by decide⟩ =
    .split (coordinate 11) (![⟨209743, by decide⟩,⟨209802, by decide⟩,⟨209844, by decide⟩,⟨209890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5529_209891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5529 ⟨209891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5529
    ⟨209891, by decide⟩ (by decide) (![⟨209743, by decide⟩,⟨209802, by decide⟩,⟨209844, by decide⟩,⟨209890, by decide⟩]) unmarked_context_11_5529_209891 node_context_11_5529_209891
  intro a
  fin_cases a
  · exact context_12_22116_209743
  · exact context_12_22117_209802
  · exact context_12_22118_209844
  · exact context_12_22119_209890

theorem selected_cut_07207 : selected 9 ⟨209926, by decide⟩
    (prefixPartial 12 22120) = some ⟨12, 2, 0, 209926, 22120, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_22120_209926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22120 ⟨209926, by decide⟩ :=
  accepted_of_selected 12 22120 ⟨209926, by decide⟩ ⟨12, 2, 0, 209926, 22120, 3329, 65536⟩
    (by decide) selected_cut_07207

theorem selected_cut_07208 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88484) = some ⟨13, 1, 0, 3444, 88484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88484, 1, 16384⟩
    (by decide) selected_cut_07208

theorem selected_cut_07209 : selected 8 ⟨209941, by decide⟩
    (prefixPartial 13 88485) = some ⟨13, 2, 0, 209941, 88485, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_88485_209941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88485 ⟨209941, by decide⟩ :=
  accepted_of_selected 13 88485 ⟨209941, by decide⟩ ⟨13, 2, 0, 209941, 88485, 1189, 16384⟩
    (by decide) selected_cut_07209

theorem selected_cut_07210 : selected 8 ⟨209972, by decide⟩
    (prefixPartial 13 88486) = some ⟨13, 2, 0, 209972, 88486, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_88486_209972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88486 ⟨209972, by decide⟩ :=
  accepted_of_selected 13 88486 ⟨209972, by decide⟩ ⟨13, 2, 0, 209972, 88486, 2217, 16384⟩
    (by decide) selected_cut_07210

theorem selected_cut_07211 : selected 8 ⟨209986, by decide⟩
    (prefixPartial 13 88487) = some ⟨13, 2, 0, 209986, 88487, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_88487_209986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88487 ⟨209986, by decide⟩ :=
  accepted_of_selected 13 88487 ⟨209986, by decide⟩ ⟨13, 2, 0, 209986, 88487, 1165, 16384⟩
    (by decide) selected_cut_07211

theorem unmarked_context_12_22121_209987 : frontier 9 ⟨209987, by decide⟩
    (prefixCache 12 22121) (prefixPartial 12 22121) = false := by
  decide +kernel

theorem node_context_12_22121_209987 : EJMOriginalGlobalDAGData.nodes 9 ⟨209987, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209941, by decide⟩,⟨209972, by decide⟩,⟨209986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22121_209987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22121 ⟨209987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22121
    ⟨209987, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209941, by decide⟩,⟨209972, by decide⟩,⟨209986, by decide⟩]) unmarked_context_12_22121_209987 node_context_12_22121_209987
  intro a
  fin_cases a
  · exact context_13_88484_3444
  · exact context_13_88485_209941
  · exact context_13_88486_209972
  · exact context_13_88487_209986

theorem selected_cut_07212 : selected 9 ⟨210098, by decide⟩
    (prefixPartial 12 22122) = some ⟨12, 2, 0, 210098, 22122, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_22122_210098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22122 ⟨210098, by decide⟩ :=
  accepted_of_selected 12 22122 ⟨210098, by decide⟩ ⟨12, 2, 0, 210098, 22122, 1997, 65536⟩
    (by decide) selected_cut_07212

theorem selected_cut_07213 : selected 9 ⟨210143, by decide⟩
    (prefixPartial 12 22123) = some ⟨12, 2, 0, 210143, 22123, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_22123_210143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22123 ⟨210143, by decide⟩ :=
  accepted_of_selected 12 22123 ⟨210143, by decide⟩ ⟨12, 2, 0, 210143, 22123, 3629, 65536⟩
    (by decide) selected_cut_07213

theorem unmarked_context_11_5530_210144 : frontier 10 ⟨210144, by decide⟩
    (prefixCache 11 5530) (prefixPartial 11 5530) = false := by
  decide +kernel

theorem node_context_11_5530_210144 : EJMOriginalGlobalDAGData.nodes 10 ⟨210144, by decide⟩ =
    .split (coordinate 11) (![⟨209926, by decide⟩,⟨209987, by decide⟩,⟨210098, by decide⟩,⟨210143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5530_210144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5530 ⟨210144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5530
    ⟨210144, by decide⟩ (by decide) (![⟨209926, by decide⟩,⟨209987, by decide⟩,⟨210098, by decide⟩,⟨210143, by decide⟩]) unmarked_context_11_5530_210144 node_context_11_5530_210144
  intro a
  fin_cases a
  · exact context_12_22120_209926
  · exact context_12_22121_209987
  · exact context_12_22122_210098
  · exact context_12_22123_210143

theorem selected_cut_07214 : selected 9 ⟨210183, by decide⟩
    (prefixPartial 12 22124) = some ⟨12, 2, 0, 210183, 22124, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_22124_210183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22124 ⟨210183, by decide⟩ :=
  accepted_of_selected 12 22124 ⟨210183, by decide⟩ ⟨12, 2, 0, 210183, 22124, 3697, 65536⟩
    (by decide) selected_cut_07214

theorem selected_cut_07215 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88500) = some ⟨13, 1, 0, 3444, 88500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88500, 1, 16384⟩
    (by decide) selected_cut_07215

theorem selected_cut_07216 : selected 8 ⟨210199, by decide⟩
    (prefixPartial 13 88501) = some ⟨13, 2, 0, 210199, 88501, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_88501_210199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88501 ⟨210199, by decide⟩ :=
  accepted_of_selected 13 88501 ⟨210199, by decide⟩ ⟨13, 2, 0, 210199, 88501, 1169, 16384⟩
    (by decide) selected_cut_07216

theorem selected_cut_07217 : selected 8 ⟨210232, by decide⟩
    (prefixPartial 13 88502) = some ⟨13, 2, 0, 210232, 88502, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_88502_210232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88502 ⟨210232, by decide⟩ :=
  accepted_of_selected 13 88502 ⟨210232, by decide⟩ ⟨13, 2, 0, 210232, 88502, 2541, 16384⟩
    (by decide) selected_cut_07217

theorem selected_cut_07218 : selected 8 ⟨210247, by decide⟩
    (prefixPartial 13 88503) = some ⟨13, 2, 0, 210247, 88503, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_88503_210247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88503 ⟨210247, by decide⟩ :=
  accepted_of_selected 13 88503 ⟨210247, by decide⟩ ⟨13, 2, 0, 210247, 88503, 1197, 16384⟩
    (by decide) selected_cut_07218

theorem unmarked_context_12_22125_210248 : frontier 9 ⟨210248, by decide⟩
    (prefixCache 12 22125) (prefixPartial 12 22125) = false := by
  decide +kernel

theorem node_context_12_22125_210248 : EJMOriginalGlobalDAGData.nodes 9 ⟨210248, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨210199, by decide⟩,⟨210232, by decide⟩,⟨210247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22125_210248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22125 ⟨210248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22125
    ⟨210248, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨210199, by decide⟩,⟨210232, by decide⟩,⟨210247, by decide⟩]) unmarked_context_12_22125_210248 node_context_12_22125_210248
  intro a
  fin_cases a
  · exact context_13_88500_3444
  · exact context_13_88501_210199
  · exact context_13_88502_210232
  · exact context_13_88503_210247

theorem selected_cut_07219 : selected 9 ⟨210285, by decide⟩
    (prefixPartial 12 22126) = some ⟨12, 2, 0, 210285, 22126, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_22126_210285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22126 ⟨210285, by decide⟩ :=
  accepted_of_selected 12 22126 ⟨210285, by decide⟩ ⟨12, 2, 0, 210285, 22126, 3461, 65536⟩
    (by decide) selected_cut_07219

theorem selected_cut_07220 : selected 9 ⟨210326, by decide⟩
    (prefixPartial 12 22127) = some ⟨12, 2, 0, 210326, 22127, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_22127_210326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22127 ⟨210326, by decide⟩ :=
  accepted_of_selected 12 22127 ⟨210326, by decide⟩ ⟨12, 2, 0, 210326, 22127, 3717, 65536⟩
    (by decide) selected_cut_07220

theorem unmarked_context_11_5531_210327 : frontier 10 ⟨210327, by decide⟩
    (prefixCache 11 5531) (prefixPartial 11 5531) = false := by
  decide +kernel

theorem node_context_11_5531_210327 : EJMOriginalGlobalDAGData.nodes 10 ⟨210327, by decide⟩ =
    .split (coordinate 11) (![⟨210183, by decide⟩,⟨210248, by decide⟩,⟨210285, by decide⟩,⟨210326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5531_210327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5531 ⟨210327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5531
    ⟨210327, by decide⟩ (by decide) (![⟨210183, by decide⟩,⟨210248, by decide⟩,⟨210285, by decide⟩,⟨210326, by decide⟩]) unmarked_context_11_5531_210327 node_context_11_5531_210327
  intro a
  fin_cases a
  · exact context_12_22124_210183
  · exact context_12_22125_210248
  · exact context_12_22126_210285
  · exact context_12_22127_210326

theorem unmarked_context_10_1382_210328 : frontier 11 ⟨210328, by decide⟩
    (prefixCache 10 1382) (prefixPartial 10 1382) = false := by
  decide +kernel

theorem node_context_10_1382_210328 : EJMOriginalGlobalDAGData.nodes 11 ⟨210328, by decide⟩ =
    .split (coordinate 10) (![⟨209696, by decide⟩,⟨209891, by decide⟩,⟨210144, by decide⟩,⟨210327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1382_210328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1382 ⟨210328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1382
    ⟨210328, by decide⟩ (by decide) (![⟨209696, by decide⟩,⟨209891, by decide⟩,⟨210144, by decide⟩,⟨210327, by decide⟩]) unmarked_context_10_1382_210328 node_context_10_1382_210328
  intro a
  fin_cases a
  · exact context_11_5528_209696
  · exact context_11_5529_209891
  · exact context_11_5530_210144
  · exact context_11_5531_210327

theorem selected_cut_07221 : selected 9 ⟨210360, by decide⟩
    (prefixPartial 12 22128) = some ⟨12, 2, 0, 210360, 22128, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_22128_210360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22128 ⟨210360, by decide⟩ :=
  accepted_of_selected 12 22128 ⟨210360, by decide⟩ ⟨12, 2, 0, 210360, 22128, 3053, 65536⟩
    (by decide) selected_cut_07221

theorem selected_cut_07222 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88516) = some ⟨13, 1, 0, 3444, 88516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88516, 1, 16384⟩
    (by decide) selected_cut_07222

theorem selected_cut_07223 : selected 8 ⟨210374, by decide⟩
    (prefixPartial 13 88517) = some ⟨13, 2, 0, 210374, 88517, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_88517_210374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88517 ⟨210374, by decide⟩ :=
  accepted_of_selected 13 88517 ⟨210374, by decide⟩ ⟨13, 2, 0, 210374, 88517, 1021, 16384⟩
    (by decide) selected_cut_07223

theorem selected_cut_07224 : selected 8 ⟨210400, by decide⟩
    (prefixPartial 13 88518) = some ⟨13, 2, 0, 210400, 88518, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_88518_210400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88518 ⟨210400, by decide⟩ :=
  accepted_of_selected 13 88518 ⟨210400, by decide⟩ ⟨13, 2, 0, 210400, 88518, 2097, 16384⟩
    (by decide) selected_cut_07224

theorem selected_cut_07225 : selected 8 ⟨210410, by decide⟩
    (prefixPartial 13 88519) = some ⟨13, 2, 0, 210410, 88519, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_88519_210410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88519 ⟨210410, by decide⟩ :=
  accepted_of_selected 13 88519 ⟨210410, by decide⟩ ⟨13, 2, 0, 210410, 88519, 1081, 16384⟩
    (by decide) selected_cut_07225

theorem unmarked_context_12_22129_210411 : frontier 9 ⟨210411, by decide⟩
    (prefixCache 12 22129) (prefixPartial 12 22129) = false := by
  decide +kernel

theorem node_context_12_22129_210411 : EJMOriginalGlobalDAGData.nodes 9 ⟨210411, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨210374, by decide⟩,⟨210400, by decide⟩,⟨210410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22129_210411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22129 ⟨210411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22129
    ⟨210411, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨210374, by decide⟩,⟨210400, by decide⟩,⟨210410, by decide⟩]) unmarked_context_12_22129_210411 node_context_12_22129_210411
  intro a
  fin_cases a
  · exact context_13_88516_3444
  · exact context_13_88517_210374
  · exact context_13_88518_210400
  · exact context_13_88519_210410

theorem selected_cut_07226 : selected 9 ⟨210449, by decide⟩
    (prefixPartial 12 22130) = some ⟨12, 2, 0, 210449, 22130, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_22130_210449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22130 ⟨210449, by decide⟩ :=
  accepted_of_selected 12 22130 ⟨210449, by decide⟩ ⟨12, 2, 0, 210449, 22130, 2833, 65536⟩
    (by decide) selected_cut_07226

theorem selected_cut_07227 : selected 9 ⟨210494, by decide⟩
    (prefixPartial 12 22131) = some ⟨12, 2, 0, 210494, 22131, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_22131_210494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22131 ⟨210494, by decide⟩ :=
  accepted_of_selected 12 22131 ⟨210494, by decide⟩ ⟨12, 2, 0, 210494, 22131, 3229, 65536⟩
    (by decide) selected_cut_07227

theorem unmarked_context_11_5532_210495 : frontier 10 ⟨210495, by decide⟩
    (prefixCache 11 5532) (prefixPartial 11 5532) = false := by
  decide +kernel

theorem node_context_11_5532_210495 : EJMOriginalGlobalDAGData.nodes 10 ⟨210495, by decide⟩ =
    .split (coordinate 11) (![⟨210360, by decide⟩,⟨210411, by decide⟩,⟨210449, by decide⟩,⟨210494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5532_210495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5532 ⟨210495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5532
    ⟨210495, by decide⟩ (by decide) (![⟨210360, by decide⟩,⟨210411, by decide⟩,⟨210449, by decide⟩,⟨210494, by decide⟩]) unmarked_context_11_5532_210495 node_context_11_5532_210495
  intro a
  fin_cases a
  · exact context_12_22128_210360
  · exact context_12_22129_210411
  · exact context_12_22130_210449
  · exact context_12_22131_210494

theorem selected_cut_07228 : selected 9 ⟨210529, by decide⟩
    (prefixPartial 12 22132) = some ⟨12, 2, 0, 210529, 22132, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_22132_210529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22132 ⟨210529, by decide⟩ :=
  accepted_of_selected 12 22132 ⟨210529, by decide⟩ ⟨12, 2, 0, 210529, 22132, 2957, 65536⟩
    (by decide) selected_cut_07228

theorem selected_cut_07229 : selected 9 ⟨210580, by decide⟩
    (prefixPartial 12 22133) = some ⟨12, 2, 0, 210580, 22133, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_22133_210580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22133 ⟨210580, by decide⟩ :=
  accepted_of_selected 12 22133 ⟨210580, by decide⟩ ⟨12, 2, 0, 210580, 22133, 3901, 65536⟩
    (by decide) selected_cut_07229

theorem selected_cut_07230 : selected 9 ⟨210613, by decide⟩
    (prefixPartial 12 22134) = some ⟨12, 2, 0, 210613, 22134, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_22134_210613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22134 ⟨210613, by decide⟩ :=
  accepted_of_selected 12 22134 ⟨210613, by decide⟩ ⟨12, 2, 0, 210613, 22134, 2721, 65536⟩
    (by decide) selected_cut_07230

theorem selected_cut_07231 : selected 9 ⟨210652, by decide⟩
    (prefixPartial 12 22135) = some ⟨12, 2, 0, 210652, 22135, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_22135_210652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22135 ⟨210652, by decide⟩ :=
  accepted_of_selected 12 22135 ⟨210652, by decide⟩ ⟨12, 2, 0, 210652, 22135, 3141, 65536⟩
    (by decide) selected_cut_07231

theorem unmarked_context_11_5533_210653 : frontier 10 ⟨210653, by decide⟩
    (prefixCache 11 5533) (prefixPartial 11 5533) = false := by
  decide +kernel

theorem node_context_11_5533_210653 : EJMOriginalGlobalDAGData.nodes 10 ⟨210653, by decide⟩ =
    .split (coordinate 11) (![⟨210529, by decide⟩,⟨210580, by decide⟩,⟨210613, by decide⟩,⟨210652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5533_210653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5533 ⟨210653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5533
    ⟨210653, by decide⟩ (by decide) (![⟨210529, by decide⟩,⟨210580, by decide⟩,⟨210613, by decide⟩,⟨210652, by decide⟩]) unmarked_context_11_5533_210653 node_context_11_5533_210653
  intro a
  fin_cases a
  · exact context_12_22132_210529
  · exact context_12_22133_210580
  · exact context_12_22134_210613
  · exact context_12_22135_210652

theorem selected_cut_07232 : selected 9 ⟨210682, by decide⟩
    (prefixPartial 12 22136) = some ⟨12, 2, 0, 210682, 22136, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_22136_210682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22136 ⟨210682, by decide⟩ :=
  accepted_of_selected 12 22136 ⟨210682, by decide⟩ ⟨12, 2, 0, 210682, 22136, 2541, 65536⟩
    (by decide) selected_cut_07232

theorem selected_cut_07233 : selected 9 ⟨210734, by decide⟩
    (prefixPartial 12 22137) = some ⟨12, 2, 0, 210734, 22137, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_22137_210734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22137 ⟨210734, by decide⟩ :=
  accepted_of_selected 12 22137 ⟨210734, by decide⟩ ⟨12, 2, 0, 210734, 22137, 3757, 65536⟩
    (by decide) selected_cut_07233

theorem selected_cut_07234 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88552) = some ⟨13, 1, 0, 3444, 88552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88552, 1, 16384⟩
    (by decide) selected_cut_07234

theorem selected_cut_07235 : selected 8 ⟨210740, by decide⟩
    (prefixPartial 13 88553) = some ⟨13, 2, 0, 210740, 88553, 397, 16384⟩ := by
  decide +kernel

theorem context_13_88553_210740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88553 ⟨210740, by decide⟩ :=
  accepted_of_selected 13 88553 ⟨210740, by decide⟩ ⟨13, 2, 0, 210740, 88553, 397, 16384⟩
    (by decide) selected_cut_07235

theorem selected_cut_07236 : selected 8 ⟨210777, by decide⟩
    (prefixPartial 13 88554) = some ⟨13, 2, 0, 210777, 88554, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_88554_210777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88554 ⟨210777, by decide⟩ :=
  accepted_of_selected 13 88554 ⟨210777, by decide⟩ ⟨13, 2, 0, 210777, 88554, 2645, 16384⟩
    (by decide) selected_cut_07236

theorem selected_cut_07237 : selected 8 ⟨210790, by decide⟩
    (prefixPartial 13 88555) = some ⟨13, 2, 0, 210790, 88555, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_88555_210790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88555 ⟨210790, by decide⟩ :=
  accepted_of_selected 13 88555 ⟨210790, by decide⟩ ⟨13, 2, 0, 210790, 88555, 1161, 16384⟩
    (by decide) selected_cut_07237

theorem unmarked_context_12_22138_210791 : frontier 9 ⟨210791, by decide⟩
    (prefixCache 12 22138) (prefixPartial 12 22138) = false := by
  decide +kernel

theorem node_context_12_22138_210791 : EJMOriginalGlobalDAGData.nodes 9 ⟨210791, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨210740, by decide⟩,⟨210777, by decide⟩,⟨210790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22138_210791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22138 ⟨210791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22138
    ⟨210791, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨210740, by decide⟩,⟨210777, by decide⟩,⟨210790, by decide⟩]) unmarked_context_12_22138_210791 node_context_12_22138_210791
  intro a
  fin_cases a
  · exact context_13_88552_3444
  · exact context_13_88553_210740
  · exact context_13_88554_210777
  · exact context_13_88555_210790

theorem selected_cut_07238 : selected 9 ⟨210819, by decide⟩
    (prefixPartial 12 22139) = some ⟨12, 2, 0, 210819, 22139, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_22139_210819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22139 ⟨210819, by decide⟩ :=
  accepted_of_selected 12 22139 ⟨210819, by decide⟩ ⟨12, 2, 0, 210819, 22139, 2549, 65536⟩
    (by decide) selected_cut_07238

theorem unmarked_context_11_5534_210820 : frontier 10 ⟨210820, by decide⟩
    (prefixCache 11 5534) (prefixPartial 11 5534) = false := by
  decide +kernel

theorem node_context_11_5534_210820 : EJMOriginalGlobalDAGData.nodes 10 ⟨210820, by decide⟩ =
    .split (coordinate 11) (![⟨210682, by decide⟩,⟨210734, by decide⟩,⟨210791, by decide⟩,⟨210819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5534_210820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5534 ⟨210820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5534
    ⟨210820, by decide⟩ (by decide) (![⟨210682, by decide⟩,⟨210734, by decide⟩,⟨210791, by decide⟩,⟨210819, by decide⟩]) unmarked_context_11_5534_210820 node_context_11_5534_210820
  intro a
  fin_cases a
  · exact context_12_22136_210682
  · exact context_12_22137_210734
  · exact context_12_22138_210791
  · exact context_12_22139_210819

theorem selected_cut_07239 : selected 9 ⟨210855, by decide⟩
    (prefixPartial 12 22140) = some ⟨12, 2, 0, 210855, 22140, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_22140_210855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22140 ⟨210855, by decide⟩ :=
  accepted_of_selected 12 22140 ⟨210855, by decide⟩ ⟨12, 2, 0, 210855, 22140, 3077, 65536⟩
    (by decide) selected_cut_07239

theorem selected_cut_07240 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88564) = some ⟨13, 1, 0, 3444, 88564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88564, 1, 16384⟩
    (by decide) selected_cut_07240

theorem selected_cut_07241 : selected 8 ⟨210860, by decide⟩
    (prefixPartial 13 88565) = some ⟨13, 2, 0, 210860, 88565, 201, 16384⟩ := by
  decide +kernel

theorem context_13_88565_210860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88565 ⟨210860, by decide⟩ :=
  accepted_of_selected 13 88565 ⟨210860, by decide⟩ ⟨13, 2, 0, 210860, 88565, 201, 16384⟩
    (by decide) selected_cut_07241

theorem selected_cut_07242 : selected 8 ⟨210909, by decide⟩
    (prefixPartial 13 88566) = some ⟨13, 2, 0, 210909, 88566, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_88566_210909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88566 ⟨210909, by decide⟩ :=
  accepted_of_selected 13 88566 ⟨210909, by decide⟩ ⟨13, 2, 0, 210909, 88566, 2817, 16384⟩
    (by decide) selected_cut_07242

theorem selected_cut_07243 : selected 8 ⟨210920, by decide⟩
    (prefixPartial 13 88567) = some ⟨13, 2, 0, 210920, 88567, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_88567_210920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88567 ⟨210920, by decide⟩ :=
  accepted_of_selected 13 88567 ⟨210920, by decide⟩ ⟨13, 2, 0, 210920, 88567, 1229, 16384⟩
    (by decide) selected_cut_07243

theorem unmarked_context_12_22141_210921 : frontier 9 ⟨210921, by decide⟩
    (prefixCache 12 22141) (prefixPartial 12 22141) = false := by
  decide +kernel

theorem node_context_12_22141_210921 : EJMOriginalGlobalDAGData.nodes 9 ⟨210921, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨210860, by decide⟩,⟨210909, by decide⟩,⟨210920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22141_210921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22141 ⟨210921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22141
    ⟨210921, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨210860, by decide⟩,⟨210909, by decide⟩,⟨210920, by decide⟩]) unmarked_context_12_22141_210921 node_context_12_22141_210921
  intro a
  fin_cases a
  · exact context_13_88564_3444
  · exact context_13_88565_210860
  · exact context_13_88566_210909
  · exact context_13_88567_210920

theorem selected_cut_07244 : selected 9 ⟨210958, by decide⟩
    (prefixPartial 12 22142) = some ⟨12, 2, 0, 210958, 22142, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_22142_210958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22142 ⟨210958, by decide⟩ :=
  accepted_of_selected 12 22142 ⟨210958, by decide⟩ ⟨12, 2, 0, 210958, 22142, 2789, 65536⟩
    (by decide) selected_cut_07244

theorem selected_cut_07245 : selected 9 ⟨210991, by decide⟩
    (prefixPartial 12 22143) = some ⟨12, 2, 0, 210991, 22143, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_22143_210991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22143 ⟨210991, by decide⟩ :=
  accepted_of_selected 12 22143 ⟨210991, by decide⟩ ⟨12, 2, 0, 210991, 22143, 2981, 65536⟩
    (by decide) selected_cut_07245

theorem unmarked_context_11_5535_210992 : frontier 10 ⟨210992, by decide⟩
    (prefixCache 11 5535) (prefixPartial 11 5535) = false := by
  decide +kernel

theorem node_context_11_5535_210992 : EJMOriginalGlobalDAGData.nodes 10 ⟨210992, by decide⟩ =
    .split (coordinate 11) (![⟨210855, by decide⟩,⟨210921, by decide⟩,⟨210958, by decide⟩,⟨210991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5535_210992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5535 ⟨210992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5535
    ⟨210992, by decide⟩ (by decide) (![⟨210855, by decide⟩,⟨210921, by decide⟩,⟨210958, by decide⟩,⟨210991, by decide⟩]) unmarked_context_11_5535_210992 node_context_11_5535_210992
  intro a
  fin_cases a
  · exact context_12_22140_210855
  · exact context_12_22141_210921
  · exact context_12_22142_210958
  · exact context_12_22143_210991

theorem unmarked_context_10_1383_210993 : frontier 11 ⟨210993, by decide⟩
    (prefixCache 10 1383) (prefixPartial 10 1383) = false := by
  decide +kernel

theorem node_context_10_1383_210993 : EJMOriginalGlobalDAGData.nodes 11 ⟨210993, by decide⟩ =
    .split (coordinate 10) (![⟨210495, by decide⟩,⟨210653, by decide⟩,⟨210820, by decide⟩,⟨210992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1383_210993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1383 ⟨210993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1383
    ⟨210993, by decide⟩ (by decide) (![⟨210495, by decide⟩,⟨210653, by decide⟩,⟨210820, by decide⟩,⟨210992, by decide⟩]) unmarked_context_10_1383_210993 node_context_10_1383_210993
  intro a
  fin_cases a
  · exact context_11_5532_210495
  · exact context_11_5533_210653
  · exact context_11_5534_210820
  · exact context_11_5535_210992

theorem unmarked_context_9_345_210994 : frontier 12 ⟨210994, by decide⟩
    (prefixCache 9 345) (prefixPartial 9 345) = false := by
  decide +kernel

theorem node_context_9_345_210994 : EJMOriginalGlobalDAGData.nodes 12 ⟨210994, by decide⟩ =
    .split (coordinate 9) (![⟨208592, by decide⟩,⟨209488, by decide⟩,⟨210328, by decide⟩,⟨210993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_345_210994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 345 ⟨210994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 345
    ⟨210994, by decide⟩ (by decide) (![⟨208592, by decide⟩,⟨209488, by decide⟩,⟨210328, by decide⟩,⟨210993, by decide⟩]) unmarked_context_9_345_210994 node_context_9_345_210994
  intro a
  fin_cases a
  · exact context_10_1380_208592
  · exact context_10_1381_209488
  · exact context_10_1382_210328
  · exact context_10_1383_210993

theorem selected_cut_07246 : selected 9 ⟨211023, by decide⟩
    (prefixPartial 12 22144) = some ⟨12, 2, 0, 211023, 22144, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_22144_211023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22144 ⟨211023, by decide⟩ :=
  accepted_of_selected 12 22144 ⟨211023, by decide⟩ ⟨12, 2, 0, 211023, 22144, 2313, 65536⟩
    (by decide) selected_cut_07246

theorem selected_cut_07247 : selected 9 ⟨211054, by decide⟩
    (prefixPartial 12 22145) = some ⟨12, 2, 0, 211054, 22145, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_22145_211054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22145 ⟨211054, by decide⟩ :=
  accepted_of_selected 12 22145 ⟨211054, by decide⟩ ⟨12, 2, 0, 211054, 22145, 2057, 65536⟩
    (by decide) selected_cut_07247

theorem selected_cut_07248 : selected 9 ⟨211084, by decide⟩
    (prefixPartial 12 22146) = some ⟨12, 2, 0, 211084, 22146, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_22146_211084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22146 ⟨211084, by decide⟩ :=
  accepted_of_selected 12 22146 ⟨211084, by decide⟩ ⟨12, 2, 0, 211084, 22146, 1981, 65536⟩
    (by decide) selected_cut_07248

theorem selected_cut_07249 : selected 9 ⟨211116, by decide⟩
    (prefixPartial 12 22147) = some ⟨12, 2, 0, 211116, 22147, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_22147_211116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22147 ⟨211116, by decide⟩ :=
  accepted_of_selected 12 22147 ⟨211116, by decide⟩ ⟨12, 2, 0, 211116, 22147, 2341, 65536⟩
    (by decide) selected_cut_07249

theorem unmarked_context_11_5536_211117 : frontier 10 ⟨211117, by decide⟩
    (prefixCache 11 5536) (prefixPartial 11 5536) = false := by
  decide +kernel

theorem node_context_11_5536_211117 : EJMOriginalGlobalDAGData.nodes 10 ⟨211117, by decide⟩ =
    .split (coordinate 11) (![⟨211023, by decide⟩,⟨211054, by decide⟩,⟨211084, by decide⟩,⟨211116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5536_211117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5536 ⟨211117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5536
    ⟨211117, by decide⟩ (by decide) (![⟨211023, by decide⟩,⟨211054, by decide⟩,⟨211084, by decide⟩,⟨211116, by decide⟩]) unmarked_context_11_5536_211117 node_context_11_5536_211117
  intro a
  fin_cases a
  · exact context_12_22144_211023
  · exact context_12_22145_211054
  · exact context_12_22146_211084
  · exact context_12_22147_211116

theorem selected_cut_07250 : selected 9 ⟨211150, by decide⟩
    (prefixPartial 12 22148) = some ⟨12, 2, 0, 211150, 22148, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_22148_211150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22148 ⟨211150, by decide⟩ :=
  accepted_of_selected 12 22148 ⟨211150, by decide⟩ ⟨12, 2, 0, 211150, 22148, 2429, 65536⟩
    (by decide) selected_cut_07250

theorem selected_cut_07251 : selected 9 ⟨211179, by decide⟩
    (prefixPartial 12 22149) = some ⟨12, 2, 0, 211179, 22149, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_22149_211179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22149 ⟨211179, by decide⟩ :=
  accepted_of_selected 12 22149 ⟨211179, by decide⟩ ⟨12, 2, 0, 211179, 22149, 2229, 65536⟩
    (by decide) selected_cut_07251

theorem selected_cut_07252 : selected 9 ⟨211208, by decide⟩
    (prefixPartial 12 22150) = some ⟨12, 2, 0, 211208, 22150, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_22150_211208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22150 ⟨211208, by decide⟩ :=
  accepted_of_selected 12 22150 ⟨211208, by decide⟩ ⟨12, 2, 0, 211208, 22150, 2081, 65536⟩
    (by decide) selected_cut_07252

theorem selected_cut_07253 : selected 9 ⟨211236, by decide⟩
    (prefixPartial 12 22151) = some ⟨12, 2, 0, 211236, 22151, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_22151_211236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22151 ⟨211236, by decide⟩ :=
  accepted_of_selected 12 22151 ⟨211236, by decide⟩ ⟨12, 2, 0, 211236, 22151, 2453, 65536⟩
    (by decide) selected_cut_07253

theorem unmarked_context_11_5537_211237 : frontier 10 ⟨211237, by decide⟩
    (prefixCache 11 5537) (prefixPartial 11 5537) = false := by
  decide +kernel

theorem node_context_11_5537_211237 : EJMOriginalGlobalDAGData.nodes 10 ⟨211237, by decide⟩ =
    .split (coordinate 11) (![⟨211150, by decide⟩,⟨211179, by decide⟩,⟨211208, by decide⟩,⟨211236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5537_211237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5537 ⟨211237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5537
    ⟨211237, by decide⟩ (by decide) (![⟨211150, by decide⟩,⟨211179, by decide⟩,⟨211208, by decide⟩,⟨211236, by decide⟩]) unmarked_context_11_5537_211237 node_context_11_5537_211237
  intro a
  fin_cases a
  · exact context_12_22148_211150
  · exact context_12_22149_211179
  · exact context_12_22150_211208
  · exact context_12_22151_211236

theorem selected_cut_07254 : selected 9 ⟨211262, by decide⟩
    (prefixPartial 12 22152) = some ⟨12, 2, 0, 211262, 22152, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_22152_211262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22152 ⟨211262, by decide⟩ :=
  accepted_of_selected 12 22152 ⟨211262, by decide⟩ ⟨12, 2, 0, 211262, 22152, 1973, 65536⟩
    (by decide) selected_cut_07254

theorem selected_cut_07255 : selected 9 ⟨211285, by decide⟩
    (prefixPartial 12 22153) = some ⟨12, 2, 0, 211285, 22153, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_22153_211285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22153 ⟨211285, by decide⟩ :=
  accepted_of_selected 12 22153 ⟨211285, by decide⟩ ⟨12, 2, 0, 211285, 22153, 1809, 65536⟩
    (by decide) selected_cut_07255

theorem selected_cut_07256 : selected 9 ⟨211323, by decide⟩
    (prefixPartial 12 22154) = some ⟨12, 2, 0, 211323, 22154, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_22154_211323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22154 ⟨211323, by decide⟩ :=
  accepted_of_selected 12 22154 ⟨211323, by decide⟩ ⟨12, 2, 0, 211323, 22154, 3001, 65536⟩
    (by decide) selected_cut_07256

theorem selected_cut_07257 : selected 9 ⟨211347, by decide⟩
    (prefixPartial 12 22155) = some ⟨12, 2, 0, 211347, 22155, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_22155_211347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22155 ⟨211347, by decide⟩ :=
  accepted_of_selected 12 22155 ⟨211347, by decide⟩ ⟨12, 2, 0, 211347, 22155, 1937, 65536⟩
    (by decide) selected_cut_07257

theorem unmarked_context_11_5538_211348 : frontier 10 ⟨211348, by decide⟩
    (prefixCache 11 5538) (prefixPartial 11 5538) = false := by
  decide +kernel

theorem node_context_11_5538_211348 : EJMOriginalGlobalDAGData.nodes 10 ⟨211348, by decide⟩ =
    .split (coordinate 11) (![⟨211262, by decide⟩,⟨211285, by decide⟩,⟨211323, by decide⟩,⟨211347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5538_211348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5538 ⟨211348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5538
    ⟨211348, by decide⟩ (by decide) (![⟨211262, by decide⟩,⟨211285, by decide⟩,⟨211323, by decide⟩,⟨211347, by decide⟩]) unmarked_context_11_5538_211348 node_context_11_5538_211348
  intro a
  fin_cases a
  · exact context_12_22152_211262
  · exact context_12_22153_211285
  · exact context_12_22154_211323
  · exact context_12_22155_211347

theorem selected_cut_07258 : selected 9 ⟨211377, by decide⟩
    (prefixPartial 12 22156) = some ⟨12, 2, 0, 211377, 22156, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_22156_211377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22156 ⟨211377, by decide⟩ :=
  accepted_of_selected 12 22156 ⟨211377, by decide⟩ ⟨12, 2, 0, 211377, 22156, 2269, 65536⟩
    (by decide) selected_cut_07258

theorem selected_cut_07259 : selected 9 ⟨211406, by decide⟩
    (prefixPartial 12 22157) = some ⟨12, 2, 0, 211406, 22157, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_22157_211406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22157 ⟨211406, by decide⟩ :=
  accepted_of_selected 12 22157 ⟨211406, by decide⟩ ⟨12, 2, 0, 211406, 22157, 2065, 65536⟩
    (by decide) selected_cut_07259

theorem selected_cut_07260 : selected 9 ⟨211430, by decide⟩
    (prefixPartial 12 22158) = some ⟨12, 2, 0, 211430, 22158, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_22158_211430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22158 ⟨211430, by decide⟩ :=
  accepted_of_selected 12 22158 ⟨211430, by decide⟩ ⟨12, 2, 0, 211430, 22158, 1841, 65536⟩
    (by decide) selected_cut_07260

theorem selected_cut_07261 : selected 9 ⟨211454, by decide⟩
    (prefixPartial 12 22159) = some ⟨12, 2, 0, 211454, 22159, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_22159_211454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22159 ⟨211454, by decide⟩ :=
  accepted_of_selected 12 22159 ⟨211454, by decide⟩ ⟨12, 2, 0, 211454, 22159, 2105, 65536⟩
    (by decide) selected_cut_07261

theorem unmarked_context_11_5539_211455 : frontier 10 ⟨211455, by decide⟩
    (prefixCache 11 5539) (prefixPartial 11 5539) = false := by
  decide +kernel

theorem node_context_11_5539_211455 : EJMOriginalGlobalDAGData.nodes 10 ⟨211455, by decide⟩ =
    .split (coordinate 11) (![⟨211377, by decide⟩,⟨211406, by decide⟩,⟨211430, by decide⟩,⟨211454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5539_211455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5539 ⟨211455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5539
    ⟨211455, by decide⟩ (by decide) (![⟨211377, by decide⟩,⟨211406, by decide⟩,⟨211430, by decide⟩,⟨211454, by decide⟩]) unmarked_context_11_5539_211455 node_context_11_5539_211455
  intro a
  fin_cases a
  · exact context_12_22156_211377
  · exact context_12_22157_211406
  · exact context_12_22158_211430
  · exact context_12_22159_211454

theorem unmarked_context_10_1384_211456 : frontier 11 ⟨211456, by decide⟩
    (prefixCache 10 1384) (prefixPartial 10 1384) = false := by
  decide +kernel

theorem node_context_10_1384_211456 : EJMOriginalGlobalDAGData.nodes 11 ⟨211456, by decide⟩ =
    .split (coordinate 10) (![⟨211117, by decide⟩,⟨211237, by decide⟩,⟨211348, by decide⟩,⟨211455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1384_211456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1384 ⟨211456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1384
    ⟨211456, by decide⟩ (by decide) (![⟨211117, by decide⟩,⟨211237, by decide⟩,⟨211348, by decide⟩,⟨211455, by decide⟩]) unmarked_context_10_1384_211456 node_context_10_1384_211456
  intro a
  fin_cases a
  · exact context_11_5536_211117
  · exact context_11_5537_211237
  · exact context_11_5538_211348
  · exact context_11_5539_211455

theorem selected_cut_07262 : selected 9 ⟨211480, by decide⟩
    (prefixPartial 12 22160) = some ⟨12, 2, 0, 211480, 22160, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_22160_211480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22160 ⟨211480, by decide⟩ :=
  accepted_of_selected 12 22160 ⟨211480, by decide⟩ ⟨12, 2, 0, 211480, 22160, 2337, 65536⟩
    (by decide) selected_cut_07262

theorem selected_cut_07263 : selected 9 ⟨211504, by decide⟩
    (prefixPartial 12 22161) = some ⟨12, 2, 0, 211504, 22161, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_22161_211504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22161 ⟨211504, by decide⟩ :=
  accepted_of_selected 12 22161 ⟨211504, by decide⟩ ⟨12, 2, 0, 211504, 22161, 2161, 65536⟩
    (by decide) selected_cut_07263

theorem selected_cut_07264 : selected 9 ⟨211528, by decide⟩
    (prefixPartial 12 22162) = some ⟨12, 2, 0, 211528, 22162, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_22162_211528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22162 ⟨211528, by decide⟩ :=
  accepted_of_selected 12 22162 ⟨211528, by decide⟩ ⟨12, 2, 0, 211528, 22162, 2101, 65536⟩
    (by decide) selected_cut_07264

theorem selected_cut_07265 : selected 9 ⟨211554, by decide⟩
    (prefixPartial 12 22163) = some ⟨12, 2, 0, 211554, 22163, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_22163_211554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22163 ⟨211554, by decide⟩ :=
  accepted_of_selected 12 22163 ⟨211554, by decide⟩ ⟨12, 2, 0, 211554, 22163, 2417, 65536⟩
    (by decide) selected_cut_07265

theorem unmarked_context_11_5540_211555 : frontier 10 ⟨211555, by decide⟩
    (prefixCache 11 5540) (prefixPartial 11 5540) = false := by
  decide +kernel

theorem node_context_11_5540_211555 : EJMOriginalGlobalDAGData.nodes 10 ⟨211555, by decide⟩ =
    .split (coordinate 11) (![⟨211480, by decide⟩,⟨211504, by decide⟩,⟨211528, by decide⟩,⟨211554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5540_211555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5540 ⟨211555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5540
    ⟨211555, by decide⟩ (by decide) (![⟨211480, by decide⟩,⟨211504, by decide⟩,⟨211528, by decide⟩,⟨211554, by decide⟩]) unmarked_context_11_5540_211555 node_context_11_5540_211555
  intro a
  fin_cases a
  · exact context_12_22160_211480
  · exact context_12_22161_211504
  · exact context_12_22162_211528
  · exact context_12_22163_211554

theorem selected_cut_07266 : selected 9 ⟨211609, by decide⟩
    (prefixPartial 12 22164) = some ⟨12, 2, 0, 211609, 22164, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_22164_211609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22164 ⟨211609, by decide⟩ :=
  accepted_of_selected 12 22164 ⟨211609, by decide⟩ ⟨12, 2, 0, 211609, 22164, 2861, 65536⟩
    (by decide) selected_cut_07266

theorem selected_cut_07267 : selected 9 ⟨211639, by decide⟩
    (prefixPartial 12 22165) = some ⟨12, 2, 0, 211639, 22165, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_22165_211639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22165 ⟨211639, by decide⟩ :=
  accepted_of_selected 12 22165 ⟨211639, by decide⟩ ⟨12, 2, 0, 211639, 22165, 2529, 65536⟩
    (by decide) selected_cut_07267

theorem selected_cut_07268 : selected 9 ⟨211670, by decide⟩
    (prefixPartial 12 22166) = some ⟨12, 2, 0, 211670, 22166, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_22166_211670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22166 ⟨211670, by decide⟩ :=
  accepted_of_selected 12 22166 ⟨211670, by decide⟩ ⟨12, 2, 0, 211670, 22166, 2517, 65536⟩
    (by decide) selected_cut_07268

theorem selected_cut_07269 : selected 9 ⟨211716, by decide⟩
    (prefixPartial 12 22167) = some ⟨12, 2, 0, 211716, 22167, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_22167_211716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22167 ⟨211716, by decide⟩ :=
  accepted_of_selected 12 22167 ⟨211716, by decide⟩ ⟨12, 2, 0, 211716, 22167, 2917, 65536⟩
    (by decide) selected_cut_07269

theorem unmarked_context_11_5541_211717 : frontier 10 ⟨211717, by decide⟩
    (prefixCache 11 5541) (prefixPartial 11 5541) = false := by
  decide +kernel

theorem node_context_11_5541_211717 : EJMOriginalGlobalDAGData.nodes 10 ⟨211717, by decide⟩ =
    .split (coordinate 11) (![⟨211609, by decide⟩,⟨211639, by decide⟩,⟨211670, by decide⟩,⟨211716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5541_211717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5541 ⟨211717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5541
    ⟨211717, by decide⟩ (by decide) (![⟨211609, by decide⟩,⟨211639, by decide⟩,⟨211670, by decide⟩,⟨211716, by decide⟩]) unmarked_context_11_5541_211717 node_context_11_5541_211717
  intro a
  fin_cases a
  · exact context_12_22164_211609
  · exact context_12_22165_211639
  · exact context_12_22166_211670
  · exact context_12_22167_211716

theorem selected_cut_07270 : selected 9 ⟨211741, by decide⟩
    (prefixPartial 12 22168) = some ⟨12, 2, 0, 211741, 22168, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_22168_211741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22168 ⟨211741, by decide⟩ :=
  accepted_of_selected 12 22168 ⟨211741, by decide⟩ ⟨12, 2, 0, 211741, 22168, 1881, 65536⟩
    (by decide) selected_cut_07270

theorem selected_cut_07271 : selected 9 ⟨211765, by decide⟩
    (prefixPartial 12 22169) = some ⟨12, 2, 0, 211765, 22169, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_22169_211765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22169 ⟨211765, by decide⟩ :=
  accepted_of_selected 12 22169 ⟨211765, by decide⟩ ⟨12, 2, 0, 211765, 22169, 1937, 65536⟩
    (by decide) selected_cut_07271

theorem selected_cut_07272 : selected 9 ⟨211832, by decide⟩
    (prefixPartial 12 22170) = some ⟨12, 2, 0, 211832, 22170, 917, 65536⟩ := by
  decide +kernel

theorem context_12_22170_211832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22170 ⟨211832, by decide⟩ :=
  accepted_of_selected 12 22170 ⟨211832, by decide⟩ ⟨12, 2, 0, 211832, 22170, 917, 65536⟩
    (by decide) selected_cut_07272

theorem selected_cut_07273 : selected 9 ⟨211858, by decide⟩
    (prefixPartial 12 22171) = some ⟨12, 2, 0, 211858, 22171, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_22171_211858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22171 ⟨211858, by decide⟩ :=
  accepted_of_selected 12 22171 ⟨211858, by decide⟩ ⟨12, 2, 0, 211858, 22171, 2045, 65536⟩
    (by decide) selected_cut_07273

theorem unmarked_context_11_5542_211859 : frontier 10 ⟨211859, by decide⟩
    (prefixCache 11 5542) (prefixPartial 11 5542) = false := by
  decide +kernel

theorem node_context_11_5542_211859 : EJMOriginalGlobalDAGData.nodes 10 ⟨211859, by decide⟩ =
    .split (coordinate 11) (![⟨211741, by decide⟩,⟨211765, by decide⟩,⟨211832, by decide⟩,⟨211858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5542_211859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5542 ⟨211859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5542
    ⟨211859, by decide⟩ (by decide) (![⟨211741, by decide⟩,⟨211765, by decide⟩,⟨211832, by decide⟩,⟨211858, by decide⟩]) unmarked_context_11_5542_211859 node_context_11_5542_211859
  intro a
  fin_cases a
  · exact context_12_22168_211741
  · exact context_12_22169_211765
  · exact context_12_22170_211832
  · exact context_12_22171_211858

theorem selected_cut_07274 : selected 9 ⟨211885, by decide⟩
    (prefixPartial 12 22172) = some ⟨12, 2, 0, 211885, 22172, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_22172_211885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22172 ⟨211885, by decide⟩ :=
  accepted_of_selected 12 22172 ⟨211885, by decide⟩ ⟨12, 2, 0, 211885, 22172, 2057, 65536⟩
    (by decide) selected_cut_07274

theorem selected_cut_07275 : selected 9 ⟨211908, by decide⟩
    (prefixPartial 12 22173) = some ⟨12, 2, 0, 211908, 22173, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_22173_211908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22173 ⟨211908, by decide⟩ :=
  accepted_of_selected 12 22173 ⟨211908, by decide⟩ ⟨12, 2, 0, 211908, 22173, 1957, 65536⟩
    (by decide) selected_cut_07275

theorem selected_cut_07276 : selected 9 ⟨211930, by decide⟩
    (prefixPartial 12 22174) = some ⟨12, 2, 0, 211930, 22174, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_22174_211930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22174 ⟨211930, by decide⟩ :=
  accepted_of_selected 12 22174 ⟨211930, by decide⟩ ⟨12, 2, 0, 211930, 22174, 1773, 65536⟩
    (by decide) selected_cut_07276

theorem selected_cut_07277 : selected 9 ⟨211946, by decide⟩
    (prefixPartial 12 22175) = some ⟨12, 2, 0, 211946, 22175, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_22175_211946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22175 ⟨211946, by decide⟩ :=
  accepted_of_selected 12 22175 ⟨211946, by decide⟩ ⟨12, 2, 0, 211946, 22175, 1993, 65536⟩
    (by decide) selected_cut_07277

theorem unmarked_context_11_5543_211947 : frontier 10 ⟨211947, by decide⟩
    (prefixCache 11 5543) (prefixPartial 11 5543) = false := by
  decide +kernel

theorem node_context_11_5543_211947 : EJMOriginalGlobalDAGData.nodes 10 ⟨211947, by decide⟩ =
    .split (coordinate 11) (![⟨211885, by decide⟩,⟨211908, by decide⟩,⟨211930, by decide⟩,⟨211946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5543_211947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5543 ⟨211947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5543
    ⟨211947, by decide⟩ (by decide) (![⟨211885, by decide⟩,⟨211908, by decide⟩,⟨211930, by decide⟩,⟨211946, by decide⟩]) unmarked_context_11_5543_211947 node_context_11_5543_211947
  intro a
  fin_cases a
  · exact context_12_22172_211885
  · exact context_12_22173_211908
  · exact context_12_22174_211930
  · exact context_12_22175_211946

theorem unmarked_context_10_1385_211948 : frontier 11 ⟨211948, by decide⟩
    (prefixCache 10 1385) (prefixPartial 10 1385) = false := by
  decide +kernel

theorem node_context_10_1385_211948 : EJMOriginalGlobalDAGData.nodes 11 ⟨211948, by decide⟩ =
    .split (coordinate 10) (![⟨211555, by decide⟩,⟨211717, by decide⟩,⟨211859, by decide⟩,⟨211947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1385_211948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1385 ⟨211948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1385
    ⟨211948, by decide⟩ (by decide) (![⟨211555, by decide⟩,⟨211717, by decide⟩,⟨211859, by decide⟩,⟨211947, by decide⟩]) unmarked_context_10_1385_211948 node_context_10_1385_211948
  intro a
  fin_cases a
  · exact context_11_5540_211555
  · exact context_11_5541_211717
  · exact context_11_5542_211859
  · exact context_11_5543_211947

theorem selected_cut_07278 : selected 9 ⟨211964, by decide⟩
    (prefixPartial 12 22176) = some ⟨12, 2, 0, 211964, 22176, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_22176_211964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22176 ⟨211964, by decide⟩ :=
  accepted_of_selected 12 22176 ⟨211964, by decide⟩ ⟨12, 2, 0, 211964, 22176, 1341, 65536⟩
    (by decide) selected_cut_07278

theorem selected_cut_07279 : selected 9 ⟨211981, by decide⟩
    (prefixPartial 12 22177) = some ⟨12, 2, 0, 211981, 22177, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_22177_211981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22177 ⟨211981, by decide⟩ :=
  accepted_of_selected 12 22177 ⟨211981, by decide⟩ ⟨12, 2, 0, 211981, 22177, 1533, 65536⟩
    (by decide) selected_cut_07279

theorem selected_cut_07280 : selected 9 ⟨211999, by decide⟩
    (prefixPartial 12 22178) = some ⟨12, 2, 0, 211999, 22178, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_22178_211999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22178 ⟨211999, by decide⟩ :=
  accepted_of_selected 12 22178 ⟨211999, by decide⟩ ⟨12, 2, 0, 211999, 22178, 1349, 65536⟩
    (by decide) selected_cut_07280

theorem selected_cut_07281 : selected 9 ⟨212015, by decide⟩
    (prefixPartial 12 22179) = some ⟨12, 2, 0, 212015, 22179, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_22179_212015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22179 ⟨212015, by decide⟩ :=
  accepted_of_selected 12 22179 ⟨212015, by decide⟩ ⟨12, 2, 0, 212015, 22179, 1473, 65536⟩
    (by decide) selected_cut_07281

theorem unmarked_context_11_5544_212016 : frontier 10 ⟨212016, by decide⟩
    (prefixCache 11 5544) (prefixPartial 11 5544) = false := by
  decide +kernel

theorem node_context_11_5544_212016 : EJMOriginalGlobalDAGData.nodes 10 ⟨212016, by decide⟩ =
    .split (coordinate 11) (![⟨211964, by decide⟩,⟨211981, by decide⟩,⟨211999, by decide⟩,⟨212015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5544_212016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5544 ⟨212016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5544
    ⟨212016, by decide⟩ (by decide) (![⟨211964, by decide⟩,⟨211981, by decide⟩,⟨211999, by decide⟩,⟨212015, by decide⟩]) unmarked_context_11_5544_212016 node_context_11_5544_212016
  intro a
  fin_cases a
  · exact context_12_22176_211964
  · exact context_12_22177_211981
  · exact context_12_22178_211999
  · exact context_12_22179_212015

theorem selected_cut_07282 : selected 9 ⟨212032, by decide⟩
    (prefixPartial 12 22180) = some ⟨12, 2, 0, 212032, 22180, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_22180_212032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22180 ⟨212032, by decide⟩ :=
  accepted_of_selected 12 22180 ⟨212032, by decide⟩ ⟨12, 2, 0, 212032, 22180, 1357, 65536⟩
    (by decide) selected_cut_07282

theorem selected_cut_07283 : selected 9 ⟨212050, by decide⟩
    (prefixPartial 12 22181) = some ⟨12, 2, 0, 212050, 22181, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_22181_212050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22181 ⟨212050, by decide⟩ :=
  accepted_of_selected 12 22181 ⟨212050, by decide⟩ ⟨12, 2, 0, 212050, 22181, 1417, 65536⟩
    (by decide) selected_cut_07283

theorem selected_cut_07284 : selected 9 ⟨212065, by decide⟩
    (prefixPartial 12 22182) = some ⟨12, 2, 0, 212065, 22182, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_22182_212065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22182 ⟨212065, by decide⟩ :=
  accepted_of_selected 12 22182 ⟨212065, by decide⟩ ⟨12, 2, 0, 212065, 22182, 1225, 65536⟩
    (by decide) selected_cut_07284

theorem selected_cut_07285 : selected 9 ⟨212082, by decide⟩
    (prefixPartial 12 22183) = some ⟨12, 2, 0, 212082, 22183, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_22183_212082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22183 ⟨212082, by decide⟩ :=
  accepted_of_selected 12 22183 ⟨212082, by decide⟩ ⟨12, 2, 0, 212082, 22183, 1425, 65536⟩
    (by decide) selected_cut_07285

theorem unmarked_context_11_5545_212083 : frontier 10 ⟨212083, by decide⟩
    (prefixCache 11 5545) (prefixPartial 11 5545) = false := by
  decide +kernel

theorem node_context_11_5545_212083 : EJMOriginalGlobalDAGData.nodes 10 ⟨212083, by decide⟩ =
    .split (coordinate 11) (![⟨212032, by decide⟩,⟨212050, by decide⟩,⟨212065, by decide⟩,⟨212082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5545_212083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5545 ⟨212083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5545
    ⟨212083, by decide⟩ (by decide) (![⟨212032, by decide⟩,⟨212050, by decide⟩,⟨212065, by decide⟩,⟨212082, by decide⟩]) unmarked_context_11_5545_212083 node_context_11_5545_212083
  intro a
  fin_cases a
  · exact context_12_22180_212032
  · exact context_12_22181_212050
  · exact context_12_22182_212065
  · exact context_12_22183_212082

theorem selected_cut_07286 : selected 10 ⟨212133, by decide⟩
    (prefixPartial 11 5546) = some ⟨11, 2, 0, 212133, 5546, 4009, 262144⟩ := by
  decide +kernel

theorem context_11_5546_212133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5546 ⟨212133, by decide⟩ :=
  accepted_of_selected 11 5546 ⟨212133, by decide⟩ ⟨11, 2, 0, 212133, 5546, 4009, 262144⟩
    (by decide) selected_cut_07286

theorem selected_cut_07287 : selected 9 ⟨212147, by decide⟩
    (prefixPartial 12 22188) = some ⟨12, 2, 0, 212147, 22188, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_22188_212147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22188 ⟨212147, by decide⟩ :=
  accepted_of_selected 12 22188 ⟨212147, by decide⟩ ⟨12, 2, 0, 212147, 22188, 1341, 65536⟩
    (by decide) selected_cut_07287

theorem selected_cut_07288 : selected 9 ⟨212163, by decide⟩
    (prefixPartial 12 22189) = some ⟨12, 2, 0, 212163, 22189, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_22189_212163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22189 ⟨212163, by decide⟩ :=
  accepted_of_selected 12 22189 ⟨212163, by decide⟩ ⟨12, 2, 0, 212163, 22189, 1373, 65536⟩
    (by decide) selected_cut_07288

theorem selected_cut_07289 : selected 9 ⟨212177, by decide⟩
    (prefixPartial 12 22190) = some ⟨12, 2, 0, 212177, 22190, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_22190_212177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22190 ⟨212177, by decide⟩ :=
  accepted_of_selected 12 22190 ⟨212177, by decide⟩ ⟨12, 2, 0, 212177, 22190, 1181, 65536⟩
    (by decide) selected_cut_07289

theorem selected_cut_07290 : selected 9 ⟨212190, by decide⟩
    (prefixPartial 12 22191) = some ⟨12, 2, 0, 212190, 22191, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_22191_212190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22191 ⟨212190, by decide⟩ :=
  accepted_of_selected 12 22191 ⟨212190, by decide⟩ ⟨12, 2, 0, 212190, 22191, 1277, 65536⟩
    (by decide) selected_cut_07290

theorem unmarked_context_11_5547_212191 : frontier 10 ⟨212191, by decide⟩
    (prefixCache 11 5547) (prefixPartial 11 5547) = false := by
  decide +kernel

theorem node_context_11_5547_212191 : EJMOriginalGlobalDAGData.nodes 10 ⟨212191, by decide⟩ =
    .split (coordinate 11) (![⟨212147, by decide⟩,⟨212163, by decide⟩,⟨212177, by decide⟩,⟨212190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5547_212191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5547 ⟨212191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5547
    ⟨212191, by decide⟩ (by decide) (![⟨212147, by decide⟩,⟨212163, by decide⟩,⟨212177, by decide⟩,⟨212190, by decide⟩]) unmarked_context_11_5547_212191 node_context_11_5547_212191
  intro a
  fin_cases a
  · exact context_12_22188_212147
  · exact context_12_22189_212163
  · exact context_12_22190_212177
  · exact context_12_22191_212190

theorem unmarked_context_10_1386_212192 : frontier 11 ⟨212192, by decide⟩
    (prefixCache 10 1386) (prefixPartial 10 1386) = false := by
  decide +kernel

theorem node_context_10_1386_212192 : EJMOriginalGlobalDAGData.nodes 11 ⟨212192, by decide⟩ =
    .split (coordinate 10) (![⟨212016, by decide⟩,⟨212083, by decide⟩,⟨212133, by decide⟩,⟨212191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1386_212192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1386 ⟨212192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1386
    ⟨212192, by decide⟩ (by decide) (![⟨212016, by decide⟩,⟨212083, by decide⟩,⟨212133, by decide⟩,⟨212191, by decide⟩]) unmarked_context_10_1386_212192 node_context_10_1386_212192
  intro a
  fin_cases a
  · exact context_11_5544_212016
  · exact context_11_5545_212083
  · exact context_11_5546_212133
  · exact context_11_5547_212191

theorem selected_cut_07291 : selected 9 ⟨212204, by decide⟩
    (prefixPartial 12 22192) = some ⟨12, 2, 0, 212204, 22192, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_22192_212204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22192 ⟨212204, by decide⟩ :=
  accepted_of_selected 12 22192 ⟨212204, by decide⟩ ⟨12, 2, 0, 212204, 22192, 1145, 65536⟩
    (by decide) selected_cut_07291

theorem selected_cut_07292 : selected 9 ⟨212218, by decide⟩
    (prefixPartial 12 22193) = some ⟨12, 2, 0, 212218, 22193, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_22193_212218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22193 ⟨212218, by decide⟩ :=
  accepted_of_selected 12 22193 ⟨212218, by decide⟩ ⟨12, 2, 0, 212218, 22193, 1229, 65536⟩
    (by decide) selected_cut_07292

theorem selected_cut_07293 : selected 9 ⟨212232, by decide⟩
    (prefixPartial 12 22194) = some ⟨12, 2, 0, 212232, 22194, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_22194_212232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22194 ⟨212232, by decide⟩ :=
  accepted_of_selected 12 22194 ⟨212232, by decide⟩ ⟨12, 2, 0, 212232, 22194, 1133, 65536⟩
    (by decide) selected_cut_07293

theorem selected_cut_07294 : selected 9 ⟨212241, by decide⟩
    (prefixPartial 12 22195) = some ⟨12, 2, 0, 212241, 22195, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_22195_212241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22195 ⟨212241, by decide⟩ :=
  accepted_of_selected 12 22195 ⟨212241, by decide⟩ ⟨12, 2, 0, 212241, 22195, 1161, 65536⟩
    (by decide) selected_cut_07294

theorem unmarked_context_11_5548_212242 : frontier 10 ⟨212242, by decide⟩
    (prefixCache 11 5548) (prefixPartial 11 5548) = false := by
  decide +kernel

theorem node_context_11_5548_212242 : EJMOriginalGlobalDAGData.nodes 10 ⟨212242, by decide⟩ =
    .split (coordinate 11) (![⟨212204, by decide⟩,⟨212218, by decide⟩,⟨212232, by decide⟩,⟨212241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5548_212242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5548 ⟨212242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5548
    ⟨212242, by decide⟩ (by decide) (![⟨212204, by decide⟩,⟨212218, by decide⟩,⟨212232, by decide⟩,⟨212241, by decide⟩]) unmarked_context_11_5548_212242 node_context_11_5548_212242
  intro a
  fin_cases a
  · exact context_12_22192_212204
  · exact context_12_22193_212218
  · exact context_12_22194_212232
  · exact context_12_22195_212241

theorem selected_cut_07295 : selected 9 ⟨212256, by decide⟩
    (prefixPartial 12 22196) = some ⟨12, 2, 0, 212256, 22196, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_22196_212256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22196 ⟨212256, by decide⟩ :=
  accepted_of_selected 12 22196 ⟨212256, by decide⟩ ⟨12, 2, 0, 212256, 22196, 1169, 65536⟩
    (by decide) selected_cut_07295

theorem selected_cut_07296 : selected 9 ⟨212269, by decide⟩
    (prefixPartial 12 22197) = some ⟨12, 2, 0, 212269, 22197, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_22197_212269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22197 ⟨212269, by decide⟩ :=
  accepted_of_selected 12 22197 ⟨212269, by decide⟩ ⟨12, 2, 0, 212269, 22197, 1153, 65536⟩
    (by decide) selected_cut_07296

theorem selected_cut_07297 : selected 9 ⟨212283, by decide⟩
    (prefixPartial 12 22198) = some ⟨12, 2, 0, 212283, 22198, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_22198_212283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22198 ⟨212283, by decide⟩ :=
  accepted_of_selected 12 22198 ⟨212283, by decide⟩ ⟨12, 2, 0, 212283, 22198, 1089, 65536⟩
    (by decide) selected_cut_07297

theorem selected_cut_07298 : selected 9 ⟨212294, by decide⟩
    (prefixPartial 12 22199) = some ⟨12, 2, 0, 212294, 22199, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_22199_212294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22199 ⟨212294, by decide⟩ :=
  accepted_of_selected 12 22199 ⟨212294, by decide⟩ ⟨12, 2, 0, 212294, 22199, 1101, 65536⟩
    (by decide) selected_cut_07298

theorem unmarked_context_11_5549_212295 : frontier 10 ⟨212295, by decide⟩
    (prefixCache 11 5549) (prefixPartial 11 5549) = false := by
  decide +kernel

theorem node_context_11_5549_212295 : EJMOriginalGlobalDAGData.nodes 10 ⟨212295, by decide⟩ =
    .split (coordinate 11) (![⟨212256, by decide⟩,⟨212269, by decide⟩,⟨212283, by decide⟩,⟨212294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5549_212295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5549 ⟨212295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5549
    ⟨212295, by decide⟩ (by decide) (![⟨212256, by decide⟩,⟨212269, by decide⟩,⟨212283, by decide⟩,⟨212294, by decide⟩]) unmarked_context_11_5549_212295 node_context_11_5549_212295
  intro a
  fin_cases a
  · exact context_12_22196_212256
  · exact context_12_22197_212269
  · exact context_12_22198_212283
  · exact context_12_22199_212294

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
