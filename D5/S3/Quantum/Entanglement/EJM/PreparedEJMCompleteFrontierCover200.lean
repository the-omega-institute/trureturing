/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover199
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19203 : selected 8 ⟨490968, by decide⟩
    (prefixPartial 13 288162) = some ⟨13, 2, 0, 490968, 288162, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_288162_490968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288162 ⟨490968, by decide⟩ :=
  accepted_of_selected 13 288162 ⟨490968, by decide⟩ ⟨13, 2, 0, 490968, 288162, 2741, 16384⟩
    (by decide) selected_cut_19203

theorem selected_cut_19204 : selected 8 ⟨491005, by decide⟩
    (prefixPartial 13 288163) = some ⟨13, 2, 0, 491005, 288163, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_288163_491005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288163 ⟨491005, by decide⟩ :=
  accepted_of_selected 13 288163 ⟨491005, by decide⟩ ⟨13, 2, 0, 491005, 288163, 1821, 16384⟩
    (by decide) selected_cut_19204

theorem unmarked_context_12_72040_491006 : frontier 9 ⟨491006, by decide⟩
    (prefixCache 12 72040) (prefixPartial 12 72040) = false := by
  decide +kernel

theorem node_context_12_72040_491006 : EJMOriginalGlobalDAGData.nodes 9 ⟨491006, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490920, by decide⟩,⟨490968, by decide⟩,⟨491005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72040_491006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72040 ⟨491006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72040
    ⟨491006, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490920, by decide⟩,⟨490968, by decide⟩,⟨491005, by decide⟩]) unmarked_context_12_72040_491006 node_context_12_72040_491006
  intro a
  fin_cases a
  · exact context_13_288160_3444
  · exact context_13_288161_490920
  · exact context_13_288162_490968
  · exact context_13_288163_491005

theorem selected_cut_19205 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288164) = some ⟨13, 1, 0, 3444, 288164, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288164_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288164 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288164 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288164, 1, 16384⟩
    (by decide) selected_cut_19205

theorem selected_cut_19206 : selected 8 ⟨491025, by decide⟩
    (prefixPartial 13 288165) = some ⟨13, 2, 0, 491025, 288165, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_288165_491025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288165 ⟨491025, by decide⟩ :=
  accepted_of_selected 13 288165 ⟨491025, by decide⟩ ⟨13, 2, 0, 491025, 288165, 1285, 16384⟩
    (by decide) selected_cut_19206

theorem selected_cut_19207 : selected 8 ⟨491053, by decide⟩
    (prefixPartial 13 288166) = some ⟨13, 2, 0, 491053, 288166, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_288166_491053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288166 ⟨491053, by decide⟩ :=
  accepted_of_selected 13 288166 ⟨491053, by decide⟩ ⟨13, 2, 0, 491053, 288166, 2537, 16384⟩
    (by decide) selected_cut_19207

theorem selected_cut_19208 : selected 8 ⟨491097, by decide⟩
    (prefixPartial 13 288167) = some ⟨13, 2, 0, 491097, 288167, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_288167_491097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288167 ⟨491097, by decide⟩ :=
  accepted_of_selected 13 288167 ⟨491097, by decide⟩ ⟨13, 2, 0, 491097, 288167, 1897, 16384⟩
    (by decide) selected_cut_19208

theorem unmarked_context_12_72041_491098 : frontier 9 ⟨491098, by decide⟩
    (prefixCache 12 72041) (prefixPartial 12 72041) = false := by
  decide +kernel

theorem node_context_12_72041_491098 : EJMOriginalGlobalDAGData.nodes 9 ⟨491098, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491025, by decide⟩,⟨491053, by decide⟩,⟨491097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72041_491098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72041 ⟨491098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72041
    ⟨491098, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491025, by decide⟩,⟨491053, by decide⟩,⟨491097, by decide⟩]) unmarked_context_12_72041_491098 node_context_12_72041_491098
  intro a
  fin_cases a
  · exact context_13_288164_3444
  · exact context_13_288165_491025
  · exact context_13_288166_491053
  · exact context_13_288167_491097

theorem selected_cut_19209 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 72042) = some ⟨12, 1, 0, 474208, 72042, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72042_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72042 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 72042 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 72042, 1, 65536⟩
    (by decide) selected_cut_19209

theorem selected_cut_19210 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288172) = some ⟨13, 1, 0, 3444, 288172, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288172_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288172 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288172 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288172, 1, 16384⟩
    (by decide) selected_cut_19210

theorem selected_cut_19211 : selected 8 ⟨491129, by decide⟩
    (prefixPartial 13 288173) = some ⟨13, 2, 0, 491129, 288173, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_288173_491129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288173 ⟨491129, by decide⟩ :=
  accepted_of_selected 13 288173 ⟨491129, by decide⟩ ⟨13, 2, 0, 491129, 288173, 1649, 16384⟩
    (by decide) selected_cut_19211

theorem selected_cut_19212 : selected 8 ⟨491207, by decide⟩
    (prefixPartial 13 288174) = some ⟨13, 2, 0, 491207, 288174, 3253, 16384⟩ := by
  decide +kernel

theorem context_13_288174_491207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288174 ⟨491207, by decide⟩ :=
  accepted_of_selected 13 288174 ⟨491207, by decide⟩ ⟨13, 2, 0, 491207, 288174, 3253, 16384⟩
    (by decide) selected_cut_19212

theorem selected_cut_19213 : selected 8 ⟨491239, by decide⟩
    (prefixPartial 13 288175) = some ⟨13, 2, 0, 491239, 288175, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_288175_491239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288175 ⟨491239, by decide⟩ :=
  accepted_of_selected 13 288175 ⟨491239, by decide⟩ ⟨13, 2, 0, 491239, 288175, 1633, 16384⟩
    (by decide) selected_cut_19213

theorem unmarked_context_12_72043_491240 : frontier 9 ⟨491240, by decide⟩
    (prefixCache 12 72043) (prefixPartial 12 72043) = false := by
  decide +kernel

theorem node_context_12_72043_491240 : EJMOriginalGlobalDAGData.nodes 9 ⟨491240, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491129, by decide⟩,⟨491207, by decide⟩,⟨491239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72043_491240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72043 ⟨491240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72043
    ⟨491240, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491129, by decide⟩,⟨491207, by decide⟩,⟨491239, by decide⟩]) unmarked_context_12_72043_491240 node_context_12_72043_491240
  intro a
  fin_cases a
  · exact context_13_288172_3444
  · exact context_13_288173_491129
  · exact context_13_288174_491207
  · exact context_13_288175_491239

theorem unmarked_context_11_18010_491241 : frontier 10 ⟨491241, by decide⟩
    (prefixCache 11 18010) (prefixPartial 11 18010) = false := by
  decide +kernel

theorem node_context_11_18010_491241 : EJMOriginalGlobalDAGData.nodes 10 ⟨491241, by decide⟩ =
    .split (coordinate 11) (![⟨491006, by decide⟩,⟨491098, by decide⟩,⟨474208, by decide⟩,⟨491240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18010_491241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18010 ⟨491241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18010
    ⟨491241, by decide⟩ (by decide) (![⟨491006, by decide⟩,⟨491098, by decide⟩,⟨474208, by decide⟩,⟨491240, by decide⟩]) unmarked_context_11_18010_491241 node_context_11_18010_491241
  intro a
  fin_cases a
  · exact context_12_72040_491006
  · exact context_12_72041_491098
  · exact context_12_72042_474208
  · exact context_12_72043_491240

theorem selected_cut_19214 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288176) = some ⟨13, 1, 0, 3444, 288176, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288176_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288176 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288176 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288176, 1, 16384⟩
    (by decide) selected_cut_19214

theorem selected_cut_19215 : selected 8 ⟨491257, by decide⟩
    (prefixPartial 13 288177) = some ⟨13, 2, 0, 491257, 288177, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_288177_491257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288177 ⟨491257, by decide⟩ :=
  accepted_of_selected 13 288177 ⟨491257, by decide⟩ ⟨13, 2, 0, 491257, 288177, 1181, 16384⟩
    (by decide) selected_cut_19215

theorem selected_cut_19216 : selected 8 ⟨491289, by decide⟩
    (prefixPartial 13 288178) = some ⟨13, 2, 0, 491289, 288178, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_288178_491289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288178 ⟨491289, by decide⟩ :=
  accepted_of_selected 13 288178 ⟨491289, by decide⟩ ⟨13, 2, 0, 491289, 288178, 2281, 16384⟩
    (by decide) selected_cut_19216

theorem selected_cut_19217 : selected 8 ⟨491308, by decide⟩
    (prefixPartial 13 288179) = some ⟨13, 2, 0, 491308, 288179, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_288179_491308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288179 ⟨491308, by decide⟩ :=
  accepted_of_selected 13 288179 ⟨491308, by decide⟩ ⟨13, 2, 0, 491308, 288179, 1481, 16384⟩
    (by decide) selected_cut_19217

theorem unmarked_context_12_72044_491309 : frontier 9 ⟨491309, by decide⟩
    (prefixCache 12 72044) (prefixPartial 12 72044) = false := by
  decide +kernel

theorem node_context_12_72044_491309 : EJMOriginalGlobalDAGData.nodes 9 ⟨491309, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491257, by decide⟩,⟨491289, by decide⟩,⟨491308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72044_491309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72044 ⟨491309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72044
    ⟨491309, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491257, by decide⟩,⟨491289, by decide⟩,⟨491308, by decide⟩]) unmarked_context_12_72044_491309 node_context_12_72044_491309
  intro a
  fin_cases a
  · exact context_13_288176_3444
  · exact context_13_288177_491257
  · exact context_13_288178_491289
  · exact context_13_288179_491308

theorem selected_cut_19218 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288180) = some ⟨13, 1, 0, 3444, 288180, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288180_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288180 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288180 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288180, 1, 16384⟩
    (by decide) selected_cut_19218

theorem selected_cut_19219 : selected 8 ⟨491317, by decide⟩
    (prefixPartial 13 288181) = some ⟨13, 2, 0, 491317, 288181, 841, 16384⟩ := by
  decide +kernel

theorem context_13_288181_491317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288181 ⟨491317, by decide⟩ :=
  accepted_of_selected 13 288181 ⟨491317, by decide⟩ ⟨13, 2, 0, 491317, 288181, 841, 16384⟩
    (by decide) selected_cut_19219

theorem selected_cut_19220 : selected 8 ⟨491340, by decide⟩
    (prefixPartial 13 288182) = some ⟨13, 2, 0, 491340, 288182, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_288182_491340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288182 ⟨491340, by decide⟩ :=
  accepted_of_selected 13 288182 ⟨491340, by decide⟩ ⟨13, 2, 0, 491340, 288182, 2201, 16384⟩
    (by decide) selected_cut_19220

theorem selected_cut_19221 : selected 8 ⟨491360, by decide⟩
    (prefixPartial 13 288183) = some ⟨13, 2, 0, 491360, 288183, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_288183_491360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288183 ⟨491360, by decide⟩ :=
  accepted_of_selected 13 288183 ⟨491360, by decide⟩ ⟨13, 2, 0, 491360, 288183, 1389, 16384⟩
    (by decide) selected_cut_19221

theorem unmarked_context_12_72045_491361 : frontier 9 ⟨491361, by decide⟩
    (prefixCache 12 72045) (prefixPartial 12 72045) = false := by
  decide +kernel

theorem node_context_12_72045_491361 : EJMOriginalGlobalDAGData.nodes 9 ⟨491361, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491317, by decide⟩,⟨491340, by decide⟩,⟨491360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72045_491361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72045 ⟨491361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72045
    ⟨491361, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491317, by decide⟩,⟨491340, by decide⟩,⟨491360, by decide⟩]) unmarked_context_12_72045_491361 node_context_12_72045_491361
  intro a
  fin_cases a
  · exact context_13_288180_3444
  · exact context_13_288181_491317
  · exact context_13_288182_491340
  · exact context_13_288183_491360

theorem selected_cut_19222 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288184) = some ⟨13, 1, 0, 3444, 288184, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288184_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288184 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288184 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288184, 1, 16384⟩
    (by decide) selected_cut_19222

theorem selected_cut_19223 : selected 8 ⟨491375, by decide⟩
    (prefixPartial 13 288185) = some ⟨13, 2, 0, 491375, 288185, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_288185_491375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288185 ⟨491375, by decide⟩ :=
  accepted_of_selected 13 288185 ⟨491375, by decide⟩ ⟨13, 2, 0, 491375, 288185, 1045, 16384⟩
    (by decide) selected_cut_19223

theorem selected_cut_19224 : selected 8 ⟨491422, by decide⟩
    (prefixPartial 13 288186) = some ⟨13, 2, 0, 491422, 288186, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_288186_491422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288186 ⟨491422, by decide⟩ :=
  accepted_of_selected 13 288186 ⟨491422, by decide⟩ ⟨13, 2, 0, 491422, 288186, 2649, 16384⟩
    (by decide) selected_cut_19224

theorem selected_cut_19225 : selected 8 ⟨491443, by decide⟩
    (prefixPartial 13 288187) = some ⟨13, 2, 0, 491443, 288187, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_288187_491443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288187 ⟨491443, by decide⟩ :=
  accepted_of_selected 13 288187 ⟨491443, by decide⟩ ⟨13, 2, 0, 491443, 288187, 1453, 16384⟩
    (by decide) selected_cut_19225

theorem unmarked_context_12_72046_491444 : frontier 9 ⟨491444, by decide⟩
    (prefixCache 12 72046) (prefixPartial 12 72046) = false := by
  decide +kernel

theorem node_context_12_72046_491444 : EJMOriginalGlobalDAGData.nodes 9 ⟨491444, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491375, by decide⟩,⟨491422, by decide⟩,⟨491443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72046_491444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72046 ⟨491444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72046
    ⟨491444, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491375, by decide⟩,⟨491422, by decide⟩,⟨491443, by decide⟩]) unmarked_context_12_72046_491444 node_context_12_72046_491444
  intro a
  fin_cases a
  · exact context_13_288184_3444
  · exact context_13_288185_491375
  · exact context_13_288186_491422
  · exact context_13_288187_491443

theorem selected_cut_19226 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288188) = some ⟨13, 1, 0, 3444, 288188, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288188_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288188 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288188 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288188, 1, 16384⟩
    (by decide) selected_cut_19226

theorem selected_cut_19227 : selected 8 ⟨491455, by decide⟩
    (prefixPartial 13 288189) = some ⟨13, 2, 0, 491455, 288189, 953, 16384⟩ := by
  decide +kernel

theorem context_13_288189_491455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288189 ⟨491455, by decide⟩ :=
  accepted_of_selected 13 288189 ⟨491455, by decide⟩ ⟨13, 2, 0, 491455, 288189, 953, 16384⟩
    (by decide) selected_cut_19227

theorem selected_cut_19228 : selected 8 ⟨491494, by decide⟩
    (prefixPartial 13 288190) = some ⟨13, 2, 0, 491494, 288190, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_288190_491494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288190 ⟨491494, by decide⟩ :=
  accepted_of_selected 13 288190 ⟨491494, by decide⟩ ⟨13, 2, 0, 491494, 288190, 2709, 16384⟩
    (by decide) selected_cut_19228

theorem selected_cut_19229 : selected 8 ⟨491503, by decide⟩
    (prefixPartial 13 288191) = some ⟨13, 2, 0, 491503, 288191, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_288191_491503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288191 ⟨491503, by decide⟩ :=
  accepted_of_selected 13 288191 ⟨491503, by decide⟩ ⟨13, 2, 0, 491503, 288191, 1269, 16384⟩
    (by decide) selected_cut_19229

theorem unmarked_context_12_72047_491504 : frontier 9 ⟨491504, by decide⟩
    (prefixCache 12 72047) (prefixPartial 12 72047) = false := by
  decide +kernel

theorem node_context_12_72047_491504 : EJMOriginalGlobalDAGData.nodes 9 ⟨491504, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491455, by decide⟩,⟨491494, by decide⟩,⟨491503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72047_491504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72047 ⟨491504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72047
    ⟨491504, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491455, by decide⟩,⟨491494, by decide⟩,⟨491503, by decide⟩]) unmarked_context_12_72047_491504 node_context_12_72047_491504
  intro a
  fin_cases a
  · exact context_13_288188_3444
  · exact context_13_288189_491455
  · exact context_13_288190_491494
  · exact context_13_288191_491503

theorem unmarked_context_11_18011_491505 : frontier 10 ⟨491505, by decide⟩
    (prefixCache 11 18011) (prefixPartial 11 18011) = false := by
  decide +kernel

theorem node_context_11_18011_491505 : EJMOriginalGlobalDAGData.nodes 10 ⟨491505, by decide⟩ =
    .split (coordinate 11) (![⟨491309, by decide⟩,⟨491361, by decide⟩,⟨491444, by decide⟩,⟨491504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18011_491505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18011 ⟨491505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18011
    ⟨491505, by decide⟩ (by decide) (![⟨491309, by decide⟩,⟨491361, by decide⟩,⟨491444, by decide⟩,⟨491504, by decide⟩]) unmarked_context_11_18011_491505 node_context_11_18011_491505
  intro a
  fin_cases a
  · exact context_12_72044_491309
  · exact context_12_72045_491361
  · exact context_12_72046_491444
  · exact context_12_72047_491504

theorem unmarked_context_10_4502_491506 : frontier 11 ⟨491506, by decide⟩
    (prefixCache 10 4502) (prefixPartial 10 4502) = false := by
  decide +kernel

theorem node_context_10_4502_491506 : EJMOriginalGlobalDAGData.nodes 11 ⟨491506, by decide⟩ =
    .split (coordinate 10) (![⟨490691, by decide⟩,⟨490888, by decide⟩,⟨491241, by decide⟩,⟨491505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4502_491506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4502 ⟨491506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4502
    ⟨491506, by decide⟩ (by decide) (![⟨490691, by decide⟩,⟨490888, by decide⟩,⟨491241, by decide⟩,⟨491505, by decide⟩]) unmarked_context_10_4502_491506 node_context_10_4502_491506
  intro a
  fin_cases a
  · exact context_11_18008_490691
  · exact context_11_18009_490888
  · exact context_11_18010_491241
  · exact context_11_18011_491505

theorem selected_cut_19230 : selected 9 ⟨491553, by decide⟩
    (prefixPartial 12 72048) = some ⟨12, 2, 0, 491553, 72048, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_72048_491553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72048 ⟨491553, by decide⟩ :=
  accepted_of_selected 12 72048 ⟨491553, by decide⟩ ⟨12, 2, 0, 491553, 72048, 3881, 65536⟩
    (by decide) selected_cut_19230

theorem selected_cut_19231 : selected 9 ⟨491599, by decide⟩
    (prefixPartial 12 72049) = some ⟨12, 2, 0, 491599, 72049, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_72049_491599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72049 ⟨491599, by decide⟩ :=
  accepted_of_selected 12 72049 ⟨491599, by decide⟩ ⟨12, 2, 0, 491599, 72049, 4089, 65536⟩
    (by decide) selected_cut_19231

theorem selected_cut_19232 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288200) = some ⟨13, 1, 0, 3444, 288200, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288200_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288200 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288200 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288200, 1, 16384⟩
    (by decide) selected_cut_19232

theorem selected_cut_19233 : selected 8 ⟨491615, by decide⟩
    (prefixPartial 13 288201) = some ⟨13, 2, 0, 491615, 288201, 877, 16384⟩ := by
  decide +kernel

theorem context_13_288201_491615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288201 ⟨491615, by decide⟩ :=
  accepted_of_selected 13 288201 ⟨491615, by decide⟩ ⟨13, 2, 0, 491615, 288201, 877, 16384⟩
    (by decide) selected_cut_19233

theorem selected_cut_19234 : selected 8 ⟨491667, by decide⟩
    (prefixPartial 13 288202) = some ⟨13, 2, 0, 491667, 288202, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_288202_491667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288202 ⟨491667, by decide⟩ :=
  accepted_of_selected 13 288202 ⟨491667, by decide⟩ ⟨13, 2, 0, 491667, 288202, 2813, 16384⟩
    (by decide) selected_cut_19234

theorem selected_cut_19235 : selected 8 ⟨491681, by decide⟩
    (prefixPartial 13 288203) = some ⟨13, 2, 0, 491681, 288203, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_288203_491681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288203 ⟨491681, by decide⟩ :=
  accepted_of_selected 13 288203 ⟨491681, by decide⟩ ⟨13, 2, 0, 491681, 288203, 1245, 16384⟩
    (by decide) selected_cut_19235

theorem unmarked_context_12_72050_491682 : frontier 9 ⟨491682, by decide⟩
    (prefixCache 12 72050) (prefixPartial 12 72050) = false := by
  decide +kernel

theorem node_context_12_72050_491682 : EJMOriginalGlobalDAGData.nodes 9 ⟨491682, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491615, by decide⟩,⟨491667, by decide⟩,⟨491681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72050_491682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72050 ⟨491682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72050
    ⟨491682, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491615, by decide⟩,⟨491667, by decide⟩,⟨491681, by decide⟩]) unmarked_context_12_72050_491682 node_context_12_72050_491682
  intro a
  fin_cases a
  · exact context_13_288200_3444
  · exact context_13_288201_491615
  · exact context_13_288202_491667
  · exact context_13_288203_491681

theorem selected_cut_19236 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288204) = some ⟨13, 1, 0, 3444, 288204, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288204_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288204 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288204 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288204, 1, 16384⟩
    (by decide) selected_cut_19236

theorem selected_cut_19237 : selected 8 ⟨491702, by decide⟩
    (prefixPartial 13 288205) = some ⟨13, 2, 0, 491702, 288205, 877, 16384⟩ := by
  decide +kernel

theorem context_13_288205_491702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288205 ⟨491702, by decide⟩ :=
  accepted_of_selected 13 288205 ⟨491702, by decide⟩ ⟨13, 2, 0, 491702, 288205, 877, 16384⟩
    (by decide) selected_cut_19237

theorem selected_cut_19238 : selected 8 ⟨491743, by decide⟩
    (prefixPartial 13 288206) = some ⟨13, 2, 0, 491743, 288206, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_288206_491743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288206 ⟨491743, by decide⟩ :=
  accepted_of_selected 13 288206 ⟨491743, by decide⟩ ⟨13, 2, 0, 491743, 288206, 2877, 16384⟩
    (by decide) selected_cut_19238

theorem selected_cut_19239 : selected 8 ⟨491752, by decide⟩
    (prefixPartial 13 288207) = some ⟨13, 2, 0, 491752, 288207, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_288207_491752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288207 ⟨491752, by decide⟩ :=
  accepted_of_selected 13 288207 ⟨491752, by decide⟩ ⟨13, 2, 0, 491752, 288207, 1173, 16384⟩
    (by decide) selected_cut_19239

theorem unmarked_context_12_72051_491753 : frontier 9 ⟨491753, by decide⟩
    (prefixCache 12 72051) (prefixPartial 12 72051) = false := by
  decide +kernel

theorem node_context_12_72051_491753 : EJMOriginalGlobalDAGData.nodes 9 ⟨491753, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491702, by decide⟩,⟨491743, by decide⟩,⟨491752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72051_491753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72051 ⟨491753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72051
    ⟨491753, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491702, by decide⟩,⟨491743, by decide⟩,⟨491752, by decide⟩]) unmarked_context_12_72051_491753 node_context_12_72051_491753
  intro a
  fin_cases a
  · exact context_13_288204_3444
  · exact context_13_288205_491702
  · exact context_13_288206_491743
  · exact context_13_288207_491752

theorem unmarked_context_11_18012_491754 : frontier 10 ⟨491754, by decide⟩
    (prefixCache 11 18012) (prefixPartial 11 18012) = false := by
  decide +kernel

theorem node_context_11_18012_491754 : EJMOriginalGlobalDAGData.nodes 10 ⟨491754, by decide⟩ =
    .split (coordinate 11) (![⟨491553, by decide⟩,⟨491599, by decide⟩,⟨491682, by decide⟩,⟨491753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18012_491754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18012 ⟨491754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18012
    ⟨491754, by decide⟩ (by decide) (![⟨491553, by decide⟩,⟨491599, by decide⟩,⟨491682, by decide⟩,⟨491753, by decide⟩]) unmarked_context_11_18012_491754 node_context_11_18012_491754
  intro a
  fin_cases a
  · exact context_12_72048_491553
  · exact context_12_72049_491599
  · exact context_12_72050_491682
  · exact context_12_72051_491753

theorem selected_cut_19240 : selected 9 ⟨491798, by decide⟩
    (prefixPartial 12 72052) = some ⟨12, 2, 0, 491798, 72052, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_72052_491798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72052 ⟨491798, by decide⟩ :=
  accepted_of_selected 12 72052 ⟨491798, by decide⟩ ⟨12, 2, 0, 491798, 72052, 3945, 65536⟩
    (by decide) selected_cut_19240

theorem selected_cut_19241 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 72053) = some ⟨12, 1, 0, 441672, 72053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72053_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72053 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 72053 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 72053, 1, 65536⟩
    (by decide) selected_cut_19241

theorem selected_cut_19242 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288216) = some ⟨13, 1, 0, 3444, 288216, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288216_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288216 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288216 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288216, 1, 16384⟩
    (by decide) selected_cut_19242

theorem selected_cut_19243 : selected 8 ⟨491812, by decide⟩
    (prefixPartial 13 288217) = some ⟨13, 2, 0, 491812, 288217, 589, 16384⟩ := by
  decide +kernel

theorem context_13_288217_491812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288217 ⟨491812, by decide⟩ :=
  accepted_of_selected 13 288217 ⟨491812, by decide⟩ ⟨13, 2, 0, 491812, 288217, 589, 16384⟩
    (by decide) selected_cut_19243

theorem selected_cut_19244 : selected 8 ⟨491856, by decide⟩
    (prefixPartial 13 288218) = some ⟨13, 2, 0, 491856, 288218, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_288218_491856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288218 ⟨491856, by decide⟩ :=
  accepted_of_selected 13 288218 ⟨491856, by decide⟩ ⟨13, 2, 0, 491856, 288218, 2793, 16384⟩
    (by decide) selected_cut_19244

theorem selected_cut_19245 : selected 8 ⟨491872, by decide⟩
    (prefixPartial 13 288219) = some ⟨13, 2, 0, 491872, 288219, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_288219_491872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288219 ⟨491872, by decide⟩ :=
  accepted_of_selected 13 288219 ⟨491872, by decide⟩ ⟨13, 2, 0, 491872, 288219, 1285, 16384⟩
    (by decide) selected_cut_19245

theorem unmarked_context_12_72054_491873 : frontier 9 ⟨491873, by decide⟩
    (prefixCache 12 72054) (prefixPartial 12 72054) = false := by
  decide +kernel

theorem node_context_12_72054_491873 : EJMOriginalGlobalDAGData.nodes 9 ⟨491873, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491812, by decide⟩,⟨491856, by decide⟩,⟨491872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72054_491873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72054 ⟨491873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72054
    ⟨491873, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491812, by decide⟩,⟨491856, by decide⟩,⟨491872, by decide⟩]) unmarked_context_12_72054_491873 node_context_12_72054_491873
  intro a
  fin_cases a
  · exact context_13_288216_3444
  · exact context_13_288217_491812
  · exact context_13_288218_491856
  · exact context_13_288219_491872

theorem selected_cut_19246 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288220) = some ⟨13, 1, 0, 3444, 288220, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288220_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288220 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288220 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288220, 1, 16384⟩
    (by decide) selected_cut_19246

theorem selected_cut_19247 : selected 8 ⟨491887, by decide⟩
    (prefixPartial 13 288221) = some ⟨13, 2, 0, 491887, 288221, 573, 16384⟩ := by
  decide +kernel

theorem context_13_288221_491887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288221 ⟨491887, by decide⟩ :=
  accepted_of_selected 13 288221 ⟨491887, by decide⟩ ⟨13, 2, 0, 491887, 288221, 573, 16384⟩
    (by decide) selected_cut_19247

theorem selected_cut_19248 : selected 8 ⟨491928, by decide⟩
    (prefixPartial 13 288222) = some ⟨13, 2, 0, 491928, 288222, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_288222_491928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288222 ⟨491928, by decide⟩ :=
  accepted_of_selected 13 288222 ⟨491928, by decide⟩ ⟨13, 2, 0, 491928, 288222, 2849, 16384⟩
    (by decide) selected_cut_19248

theorem selected_cut_19249 : selected 8 ⟨491935, by decide⟩
    (prefixPartial 13 288223) = some ⟨13, 2, 0, 491935, 288223, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_288223_491935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288223 ⟨491935, by decide⟩ :=
  accepted_of_selected 13 288223 ⟨491935, by decide⟩ ⟨13, 2, 0, 491935, 288223, 1093, 16384⟩
    (by decide) selected_cut_19249

theorem unmarked_context_12_72055_491936 : frontier 9 ⟨491936, by decide⟩
    (prefixCache 12 72055) (prefixPartial 12 72055) = false := by
  decide +kernel

theorem node_context_12_72055_491936 : EJMOriginalGlobalDAGData.nodes 9 ⟨491936, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491887, by decide⟩,⟨491928, by decide⟩,⟨491935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72055_491936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72055 ⟨491936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72055
    ⟨491936, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491887, by decide⟩,⟨491928, by decide⟩,⟨491935, by decide⟩]) unmarked_context_12_72055_491936 node_context_12_72055_491936
  intro a
  fin_cases a
  · exact context_13_288220_3444
  · exact context_13_288221_491887
  · exact context_13_288222_491928
  · exact context_13_288223_491935

theorem unmarked_context_11_18013_491937 : frontier 10 ⟨491937, by decide⟩
    (prefixCache 11 18013) (prefixPartial 11 18013) = false := by
  decide +kernel

theorem node_context_11_18013_491937 : EJMOriginalGlobalDAGData.nodes 10 ⟨491937, by decide⟩ =
    .split (coordinate 11) (![⟨491798, by decide⟩,⟨441672, by decide⟩,⟨491873, by decide⟩,⟨491936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18013_491937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18013 ⟨491937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18013
    ⟨491937, by decide⟩ (by decide) (![⟨491798, by decide⟩,⟨441672, by decide⟩,⟨491873, by decide⟩,⟨491936, by decide⟩]) unmarked_context_11_18013_491937 node_context_11_18013_491937
  intro a
  fin_cases a
  · exact context_12_72052_491798
  · exact context_12_72053_441672
  · exact context_12_72054_491873
  · exact context_12_72055_491936

theorem selected_cut_19250 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288224) = some ⟨13, 1, 0, 3444, 288224, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288224_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288224 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288224 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288224, 1, 16384⟩
    (by decide) selected_cut_19250

theorem selected_cut_19251 : selected 8 ⟨491945, by decide⟩
    (prefixPartial 13 288225) = some ⟨13, 2, 0, 491945, 288225, 505, 16384⟩ := by
  decide +kernel

theorem context_13_288225_491945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288225 ⟨491945, by decide⟩ :=
  accepted_of_selected 13 288225 ⟨491945, by decide⟩ ⟨13, 2, 0, 491945, 288225, 505, 16384⟩
    (by decide) selected_cut_19251

theorem selected_cut_19252 : selected 8 ⟨491979, by decide⟩
    (prefixPartial 13 288226) = some ⟨13, 2, 0, 491979, 288226, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_288226_491979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288226 ⟨491979, by decide⟩ :=
  accepted_of_selected 13 288226 ⟨491979, by decide⟩ ⟨13, 2, 0, 491979, 288226, 2581, 16384⟩
    (by decide) selected_cut_19252

theorem selected_cut_19253 : selected 8 ⟨491992, by decide⟩
    (prefixPartial 13 288227) = some ⟨13, 2, 0, 491992, 288227, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_288227_491992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288227 ⟨491992, by decide⟩ :=
  accepted_of_selected 13 288227 ⟨491992, by decide⟩ ⟨13, 2, 0, 491992, 288227, 1301, 16384⟩
    (by decide) selected_cut_19253

theorem unmarked_context_12_72056_491993 : frontier 9 ⟨491993, by decide⟩
    (prefixCache 12 72056) (prefixPartial 12 72056) = false := by
  decide +kernel

theorem node_context_12_72056_491993 : EJMOriginalGlobalDAGData.nodes 9 ⟨491993, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491945, by decide⟩,⟨491979, by decide⟩,⟨491992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72056_491993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72056 ⟨491993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72056
    ⟨491993, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491945, by decide⟩,⟨491979, by decide⟩,⟨491992, by decide⟩]) unmarked_context_12_72056_491993 node_context_12_72056_491993
  intro a
  fin_cases a
  · exact context_13_288224_3444
  · exact context_13_288225_491945
  · exact context_13_288226_491979
  · exact context_13_288227_491992

theorem selected_cut_19254 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288228) = some ⟨13, 1, 0, 3444, 288228, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288228_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288228 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288228 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288228, 1, 16384⟩
    (by decide) selected_cut_19254

theorem selected_cut_19255 : selected 8 ⟨491998, by decide⟩
    (prefixPartial 13 288229) = some ⟨13, 2, 0, 491998, 288229, 405, 16384⟩ := by
  decide +kernel

theorem context_13_288229_491998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288229 ⟨491998, by decide⟩ :=
  accepted_of_selected 13 288229 ⟨491998, by decide⟩ ⟨13, 2, 0, 491998, 288229, 405, 16384⟩
    (by decide) selected_cut_19255

theorem selected_cut_19256 : selected 8 ⟨492017, by decide⟩
    (prefixPartial 13 288230) = some ⟨13, 2, 0, 492017, 288230, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_288230_492017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288230 ⟨492017, by decide⟩ :=
  accepted_of_selected 13 288230 ⟨492017, by decide⟩ ⟨13, 2, 0, 492017, 288230, 2349, 16384⟩
    (by decide) selected_cut_19256

theorem selected_cut_19257 : selected 8 ⟨492034, by decide⟩
    (prefixPartial 13 288231) = some ⟨13, 2, 0, 492034, 288231, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_288231_492034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288231 ⟨492034, by decide⟩ :=
  accepted_of_selected 13 288231 ⟨492034, by decide⟩ ⟨13, 2, 0, 492034, 288231, 1373, 16384⟩
    (by decide) selected_cut_19257

theorem unmarked_context_12_72057_492035 : frontier 9 ⟨492035, by decide⟩
    (prefixCache 12 72057) (prefixPartial 12 72057) = false := by
  decide +kernel

theorem node_context_12_72057_492035 : EJMOriginalGlobalDAGData.nodes 9 ⟨492035, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨491998, by decide⟩,⟨492017, by decide⟩,⟨492034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72057_492035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72057 ⟨492035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72057
    ⟨492035, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨491998, by decide⟩,⟨492017, by decide⟩,⟨492034, by decide⟩]) unmarked_context_12_72057_492035 node_context_12_72057_492035
  intro a
  fin_cases a
  · exact context_13_288228_3444
  · exact context_13_288229_491998
  · exact context_13_288230_492017
  · exact context_13_288231_492034

theorem selected_cut_19258 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288232) = some ⟨13, 1, 0, 3444, 288232, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288232_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288232 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288232 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288232, 1, 16384⟩
    (by decide) selected_cut_19258

theorem selected_cut_19259 : selected 8 ⟨492041, by decide⟩
    (prefixPartial 13 288233) = some ⟨13, 2, 0, 492041, 288233, 365, 16384⟩ := by
  decide +kernel

theorem context_13_288233_492041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288233 ⟨492041, by decide⟩ :=
  accepted_of_selected 13 288233 ⟨492041, by decide⟩ ⟨13, 2, 0, 492041, 288233, 365, 16384⟩
    (by decide) selected_cut_19259

theorem selected_cut_19260 : selected 8 ⟨492084, by decide⟩
    (prefixPartial 13 288234) = some ⟨13, 2, 0, 492084, 288234, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_288234_492084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288234 ⟨492084, by decide⟩ :=
  accepted_of_selected 13 288234 ⟨492084, by decide⟩ ⟨13, 2, 0, 492084, 288234, 2857, 16384⟩
    (by decide) selected_cut_19260

theorem selected_cut_19261 : selected 8 ⟨492097, by decide⟩
    (prefixPartial 13 288235) = some ⟨13, 2, 0, 492097, 288235, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_288235_492097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288235 ⟨492097, by decide⟩ :=
  accepted_of_selected 13 288235 ⟨492097, by decide⟩ ⟨13, 2, 0, 492097, 288235, 1301, 16384⟩
    (by decide) selected_cut_19261

theorem unmarked_context_12_72058_492098 : frontier 9 ⟨492098, by decide⟩
    (prefixCache 12 72058) (prefixPartial 12 72058) = false := by
  decide +kernel

theorem node_context_12_72058_492098 : EJMOriginalGlobalDAGData.nodes 9 ⟨492098, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨492041, by decide⟩,⟨492084, by decide⟩,⟨492097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72058_492098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72058 ⟨492098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72058
    ⟨492098, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨492041, by decide⟩,⟨492084, by decide⟩,⟨492097, by decide⟩]) unmarked_context_12_72058_492098 node_context_12_72058_492098
  intro a
  fin_cases a
  · exact context_13_288232_3444
  · exact context_13_288233_492041
  · exact context_13_288234_492084
  · exact context_13_288235_492097

theorem selected_cut_19262 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288236) = some ⟨13, 1, 0, 3444, 288236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288236, 1, 16384⟩
    (by decide) selected_cut_19262

theorem selected_cut_19263 : selected 8 ⟨492104, by decide⟩
    (prefixPartial 13 288237) = some ⟨13, 2, 0, 492104, 288237, 349, 16384⟩ := by
  decide +kernel

theorem context_13_288237_492104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288237 ⟨492104, by decide⟩ :=
  accepted_of_selected 13 288237 ⟨492104, by decide⟩ ⟨13, 2, 0, 492104, 288237, 349, 16384⟩
    (by decide) selected_cut_19263

theorem selected_cut_19264 : selected 8 ⟨492151, by decide⟩
    (prefixPartial 13 288238) = some ⟨13, 2, 0, 492151, 288238, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_288238_492151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288238 ⟨492151, by decide⟩ :=
  accepted_of_selected 13 288238 ⟨492151, by decide⟩ ⟨13, 2, 0, 492151, 288238, 2905, 16384⟩
    (by decide) selected_cut_19264

theorem selected_cut_19265 : selected 8 ⟨492165, by decide⟩
    (prefixPartial 13 288239) = some ⟨13, 2, 0, 492165, 288239, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_288239_492165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288239 ⟨492165, by decide⟩ :=
  accepted_of_selected 13 288239 ⟨492165, by decide⟩ ⟨13, 2, 0, 492165, 288239, 1261, 16384⟩
    (by decide) selected_cut_19265

theorem unmarked_context_12_72059_492166 : frontier 9 ⟨492166, by decide⟩
    (prefixCache 12 72059) (prefixPartial 12 72059) = false := by
  decide +kernel

theorem node_context_12_72059_492166 : EJMOriginalGlobalDAGData.nodes 9 ⟨492166, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨492104, by decide⟩,⟨492151, by decide⟩,⟨492165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72059_492166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72059 ⟨492166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72059
    ⟨492166, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨492104, by decide⟩,⟨492151, by decide⟩,⟨492165, by decide⟩]) unmarked_context_12_72059_492166 node_context_12_72059_492166
  intro a
  fin_cases a
  · exact context_13_288236_3444
  · exact context_13_288237_492104
  · exact context_13_288238_492151
  · exact context_13_288239_492165

theorem unmarked_context_11_18014_492167 : frontier 10 ⟨492167, by decide⟩
    (prefixCache 11 18014) (prefixPartial 11 18014) = false := by
  decide +kernel

theorem node_context_11_18014_492167 : EJMOriginalGlobalDAGData.nodes 10 ⟨492167, by decide⟩ =
    .split (coordinate 11) (![⟨491993, by decide⟩,⟨492035, by decide⟩,⟨492098, by decide⟩,⟨492166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18014_492167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18014 ⟨492167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18014
    ⟨492167, by decide⟩ (by decide) (![⟨491993, by decide⟩,⟨492035, by decide⟩,⟨492098, by decide⟩,⟨492166, by decide⟩]) unmarked_context_11_18014_492167 node_context_11_18014_492167
  intro a
  fin_cases a
  · exact context_12_72056_491993
  · exact context_12_72057_492035
  · exact context_12_72058_492098
  · exact context_12_72059_492166

theorem selected_cut_19266 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288240) = some ⟨13, 1, 0, 3444, 288240, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288240_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288240 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288240 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288240, 1, 16384⟩
    (by decide) selected_cut_19266

theorem selected_cut_19267 : selected 8 ⟨492172, by decide⟩
    (prefixPartial 13 288241) = some ⟨13, 2, 0, 492172, 288241, 265, 16384⟩ := by
  decide +kernel

theorem context_13_288241_492172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288241 ⟨492172, by decide⟩ :=
  accepted_of_selected 13 288241 ⟨492172, by decide⟩ ⟨13, 2, 0, 492172, 288241, 265, 16384⟩
    (by decide) selected_cut_19267

theorem selected_cut_19268 : selected 8 ⟨492214, by decide⟩
    (prefixPartial 13 288242) = some ⟨13, 2, 0, 492214, 288242, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_288242_492214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288242 ⟨492214, by decide⟩ :=
  accepted_of_selected 13 288242 ⟨492214, by decide⟩ ⟨13, 2, 0, 492214, 288242, 2613, 16384⟩
    (by decide) selected_cut_19268

theorem selected_cut_19269 : selected 8 ⟨492231, by decide⟩
    (prefixPartial 13 288243) = some ⟨13, 2, 0, 492231, 288243, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_288243_492231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288243 ⟨492231, by decide⟩ :=
  accepted_of_selected 13 288243 ⟨492231, by decide⟩ ⟨13, 2, 0, 492231, 288243, 1349, 16384⟩
    (by decide) selected_cut_19269

theorem unmarked_context_12_72060_492232 : frontier 9 ⟨492232, by decide⟩
    (prefixCache 12 72060) (prefixPartial 12 72060) = false := by
  decide +kernel

theorem node_context_12_72060_492232 : EJMOriginalGlobalDAGData.nodes 9 ⟨492232, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨492172, by decide⟩,⟨492214, by decide⟩,⟨492231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72060_492232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72060 ⟨492232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72060
    ⟨492232, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨492172, by decide⟩,⟨492214, by decide⟩,⟨492231, by decide⟩]) unmarked_context_12_72060_492232 node_context_12_72060_492232
  intro a
  fin_cases a
  · exact context_13_288240_3444
  · exact context_13_288241_492172
  · exact context_13_288242_492214
  · exact context_13_288243_492231

theorem selected_cut_19270 : selected 9 ⟨492274, by decide⟩
    (prefixPartial 12 72061) = some ⟨12, 2, 0, 492274, 72061, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_72061_492274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72061 ⟨492274, by decide⟩ :=
  accepted_of_selected 12 72061 ⟨492274, by decide⟩ ⟨12, 2, 0, 492274, 72061, 3933, 65536⟩
    (by decide) selected_cut_19270

theorem selected_cut_19271 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288248) = some ⟨13, 1, 0, 3444, 288248, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288248_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288248 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288248 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288248, 1, 16384⟩
    (by decide) selected_cut_19271

theorem selected_cut_19272 : selected 8 ⟨492278, by decide⟩
    (prefixPartial 13 288249) = some ⟨13, 2, 0, 492278, 288249, 157, 16384⟩ := by
  decide +kernel

theorem context_13_288249_492278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288249 ⟨492278, by decide⟩ :=
  accepted_of_selected 13 288249 ⟨492278, by decide⟩ ⟨13, 2, 0, 492278, 288249, 157, 16384⟩
    (by decide) selected_cut_19272

theorem selected_cut_19273 : selected 8 ⟨492320, by decide⟩
    (prefixPartial 13 288250) = some ⟨13, 2, 0, 492320, 288250, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_288250_492320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288250 ⟨492320, by decide⟩ :=
  accepted_of_selected 13 288250 ⟨492320, by decide⟩ ⟨13, 2, 0, 492320, 288250, 2965, 16384⟩
    (by decide) selected_cut_19273

theorem selected_cut_19274 : selected 8 ⟨492334, by decide⟩
    (prefixPartial 13 288251) = some ⟨13, 2, 0, 492334, 288251, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_288251_492334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288251 ⟨492334, by decide⟩ :=
  accepted_of_selected 13 288251 ⟨492334, by decide⟩ ⟨13, 2, 0, 492334, 288251, 1325, 16384⟩
    (by decide) selected_cut_19274

theorem unmarked_context_12_72062_492335 : frontier 9 ⟨492335, by decide⟩
    (prefixCache 12 72062) (prefixPartial 12 72062) = false := by
  decide +kernel

theorem node_context_12_72062_492335 : EJMOriginalGlobalDAGData.nodes 9 ⟨492335, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨492278, by decide⟩,⟨492320, by decide⟩,⟨492334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72062_492335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72062 ⟨492335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72062
    ⟨492335, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨492278, by decide⟩,⟨492320, by decide⟩,⟨492334, by decide⟩]) unmarked_context_12_72062_492335 node_context_12_72062_492335
  intro a
  fin_cases a
  · exact context_13_288248_3444
  · exact context_13_288249_492278
  · exact context_13_288250_492320
  · exact context_13_288251_492334

theorem selected_cut_19275 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288252) = some ⟨13, 1, 0, 3444, 288252, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288252_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288252 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288252 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288252, 1, 16384⟩
    (by decide) selected_cut_19275

theorem selected_cut_19276 : selected 8 ⟨492340, by decide⟩
    (prefixPartial 13 288253) = some ⟨13, 2, 0, 492340, 288253, 89, 16384⟩ := by
  decide +kernel

theorem context_13_288253_492340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288253 ⟨492340, by decide⟩ :=
  accepted_of_selected 13 288253 ⟨492340, by decide⟩ ⟨13, 2, 0, 492340, 288253, 89, 16384⟩
    (by decide) selected_cut_19276

theorem selected_cut_19277 : selected 8 ⟨492381, by decide⟩
    (prefixPartial 13 288254) = some ⟨13, 2, 0, 492381, 288254, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_288254_492381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288254 ⟨492381, by decide⟩ :=
  accepted_of_selected 13 288254 ⟨492381, by decide⟩ ⟨13, 2, 0, 492381, 288254, 2917, 16384⟩
    (by decide) selected_cut_19277

theorem selected_cut_19278 : selected 8 ⟨492392, by decide⟩
    (prefixPartial 13 288255) = some ⟨13, 2, 0, 492392, 288255, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_288255_492392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288255 ⟨492392, by decide⟩ :=
  accepted_of_selected 13 288255 ⟨492392, by decide⟩ ⟨13, 2, 0, 492392, 288255, 1253, 16384⟩
    (by decide) selected_cut_19278

theorem unmarked_context_12_72063_492393 : frontier 9 ⟨492393, by decide⟩
    (prefixCache 12 72063) (prefixPartial 12 72063) = false := by
  decide +kernel

theorem node_context_12_72063_492393 : EJMOriginalGlobalDAGData.nodes 9 ⟨492393, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨492340, by decide⟩,⟨492381, by decide⟩,⟨492392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72063_492393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72063 ⟨492393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72063
    ⟨492393, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨492340, by decide⟩,⟨492381, by decide⟩,⟨492392, by decide⟩]) unmarked_context_12_72063_492393 node_context_12_72063_492393
  intro a
  fin_cases a
  · exact context_13_288252_3444
  · exact context_13_288253_492340
  · exact context_13_288254_492381
  · exact context_13_288255_492392

theorem unmarked_context_11_18015_492394 : frontier 10 ⟨492394, by decide⟩
    (prefixCache 11 18015) (prefixPartial 11 18015) = false := by
  decide +kernel

theorem node_context_11_18015_492394 : EJMOriginalGlobalDAGData.nodes 10 ⟨492394, by decide⟩ =
    .split (coordinate 11) (![⟨492232, by decide⟩,⟨492274, by decide⟩,⟨492335, by decide⟩,⟨492393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18015_492394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18015 ⟨492394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18015
    ⟨492394, by decide⟩ (by decide) (![⟨492232, by decide⟩,⟨492274, by decide⟩,⟨492335, by decide⟩,⟨492393, by decide⟩]) unmarked_context_11_18015_492394 node_context_11_18015_492394
  intro a
  fin_cases a
  · exact context_12_72060_492232
  · exact context_12_72061_492274
  · exact context_12_72062_492335
  · exact context_12_72063_492393

theorem unmarked_context_10_4503_492395 : frontier 11 ⟨492395, by decide⟩
    (prefixCache 10 4503) (prefixPartial 10 4503) = false := by
  decide +kernel

theorem node_context_10_4503_492395 : EJMOriginalGlobalDAGData.nodes 11 ⟨492395, by decide⟩ =
    .split (coordinate 10) (![⟨491754, by decide⟩,⟨491937, by decide⟩,⟨492167, by decide⟩,⟨492394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4503_492395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4503 ⟨492395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4503
    ⟨492395, by decide⟩ (by decide) (![⟨491754, by decide⟩,⟨491937, by decide⟩,⟨492167, by decide⟩,⟨492394, by decide⟩]) unmarked_context_10_4503_492395 node_context_10_4503_492395
  intro a
  fin_cases a
  · exact context_11_18012_491754
  · exact context_11_18013_491937
  · exact context_11_18014_492167
  · exact context_11_18015_492394

theorem unmarked_context_9_1125_492396 : frontier 12 ⟨492396, by decide⟩
    (prefixCache 9 1125) (prefixPartial 9 1125) = false := by
  decide +kernel

theorem node_context_9_1125_492396 : EJMOriginalGlobalDAGData.nodes 12 ⟨492396, by decide⟩ =
    .split (coordinate 9) (![⟨489405, by decide⟩,⟨490429, by decide⟩,⟨491506, by decide⟩,⟨492395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1125_492396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1125 ⟨492396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1125
    ⟨492396, by decide⟩ (by decide) (![⟨489405, by decide⟩,⟨490429, by decide⟩,⟨491506, by decide⟩,⟨492395, by decide⟩]) unmarked_context_9_1125_492396 node_context_9_1125_492396
  intro a
  fin_cases a
  · exact context_10_4500_489405
  · exact context_10_4501_490429
  · exact context_10_4502_491506
  · exact context_10_4503_492395

theorem selected_cut_19279 : selected 9 ⟨492422, by decide⟩
    (prefixPartial 12 72064) = some ⟨12, 2, 0, 492422, 72064, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_72064_492422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72064 ⟨492422, by decide⟩ :=
  accepted_of_selected 12 72064 ⟨492422, by decide⟩ ⟨12, 2, 0, 492422, 72064, 2889, 65536⟩
    (by decide) selected_cut_19279

theorem selected_cut_19280 : selected 9 ⟨492456, by decide⟩
    (prefixPartial 12 72065) = some ⟨12, 2, 0, 492456, 72065, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_72065_492456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72065 ⟨492456, by decide⟩ :=
  accepted_of_selected 12 72065 ⟨492456, by decide⟩ ⟨12, 2, 0, 492456, 72065, 3385, 65536⟩
    (by decide) selected_cut_19280

theorem selected_cut_19281 : selected 9 ⟨492508, by decide⟩
    (prefixPartial 12 72066) = some ⟨12, 2, 0, 492508, 72066, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_72066_492508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72066 ⟨492508, by decide⟩ :=
  accepted_of_selected 12 72066 ⟨492508, by decide⟩ ⟨12, 2, 0, 492508, 72066, 3773, 65536⟩
    (by decide) selected_cut_19281

theorem selected_cut_19282 : selected 9 ⟨492545, by decide⟩
    (prefixPartial 12 72067) = some ⟨12, 2, 0, 492545, 72067, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_72067_492545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72067 ⟨492545, by decide⟩ :=
  accepted_of_selected 12 72067 ⟨492545, by decide⟩ ⟨12, 2, 0, 492545, 72067, 3453, 65536⟩
    (by decide) selected_cut_19282

theorem unmarked_context_11_18016_492546 : frontier 10 ⟨492546, by decide⟩
    (prefixCache 11 18016) (prefixPartial 11 18016) = false := by
  decide +kernel

theorem node_context_11_18016_492546 : EJMOriginalGlobalDAGData.nodes 10 ⟨492546, by decide⟩ =
    .split (coordinate 11) (![⟨492422, by decide⟩,⟨492456, by decide⟩,⟨492508, by decide⟩,⟨492545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18016_492546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18016 ⟨492546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18016
    ⟨492546, by decide⟩ (by decide) (![⟨492422, by decide⟩,⟨492456, by decide⟩,⟨492508, by decide⟩,⟨492545, by decide⟩]) unmarked_context_11_18016_492546 node_context_11_18016_492546
  intro a
  fin_cases a
  · exact context_12_72064_492422
  · exact context_12_72065_492456
  · exact context_12_72066_492508
  · exact context_12_72067_492545

theorem selected_cut_19283 : selected 9 ⟨492571, by decide⟩
    (prefixPartial 12 72068) = some ⟨12, 2, 0, 492571, 72068, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_72068_492571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72068 ⟨492571, by decide⟩ :=
  accepted_of_selected 12 72068 ⟨492571, by decide⟩ ⟨12, 2, 0, 492571, 72068, 2817, 65536⟩
    (by decide) selected_cut_19283

theorem selected_cut_19284 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288276) = some ⟨13, 1, 0, 3444, 288276, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288276_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288276 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288276 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288276, 1, 16384⟩
    (by decide) selected_cut_19284

theorem selected_cut_19285 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288277) = some ⟨13, 1, 0, 3444, 288277, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288277_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288277 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288277 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288277, 1, 16384⟩
    (by decide) selected_cut_19285

theorem selected_cut_19286 : selected 8 ⟨492619, by decide⟩
    (prefixPartial 13 288278) = some ⟨13, 2, 0, 492619, 288278, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_288278_492619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288278 ⟨492619, by decide⟩ :=
  accepted_of_selected 13 288278 ⟨492619, by decide⟩ ⟨13, 2, 0, 492619, 288278, 2729, 16384⟩
    (by decide) selected_cut_19286

theorem selected_cut_19287 : selected 8 ⟨492646, by decide⟩
    (prefixPartial 13 288279) = some ⟨13, 2, 0, 492646, 288279, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_288279_492646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288279 ⟨492646, by decide⟩ :=
  accepted_of_selected 13 288279 ⟨492646, by decide⟩ ⟨13, 2, 0, 492646, 288279, 1501, 16384⟩
    (by decide) selected_cut_19287

theorem unmarked_context_12_72069_492647 : frontier 9 ⟨492647, by decide⟩
    (prefixCache 12 72069) (prefixPartial 12 72069) = false := by
  decide +kernel

theorem node_context_12_72069_492647 : EJMOriginalGlobalDAGData.nodes 9 ⟨492647, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨492619, by decide⟩,⟨492646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72069_492647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72069 ⟨492647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72069
    ⟨492647, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨492619, by decide⟩,⟨492646, by decide⟩]) unmarked_context_12_72069_492647 node_context_12_72069_492647
  intro a
  fin_cases a
  · exact context_13_288276_3444
  · exact context_13_288277_3444
  · exact context_13_288278_492619
  · exact context_13_288279_492646

theorem selected_cut_19288 : selected 9 ⟨492682, by decide⟩
    (prefixPartial 12 72070) = some ⟨12, 2, 0, 492682, 72070, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_72070_492682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72070 ⟨492682, by decide⟩ :=
  accepted_of_selected 12 72070 ⟨492682, by decide⟩ ⟨12, 2, 0, 492682, 72070, 3317, 65536⟩
    (by decide) selected_cut_19288

theorem selected_cut_19289 : selected 9 ⟨492713, by decide⟩
    (prefixPartial 12 72071) = some ⟨12, 2, 0, 492713, 72071, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_72071_492713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72071 ⟨492713, by decide⟩ :=
  accepted_of_selected 12 72071 ⟨492713, by decide⟩ ⟨12, 2, 0, 492713, 72071, 3017, 65536⟩
    (by decide) selected_cut_19289

theorem unmarked_context_11_18017_492714 : frontier 10 ⟨492714, by decide⟩
    (prefixCache 11 18017) (prefixPartial 11 18017) = false := by
  decide +kernel

theorem node_context_11_18017_492714 : EJMOriginalGlobalDAGData.nodes 10 ⟨492714, by decide⟩ =
    .split (coordinate 11) (![⟨492571, by decide⟩,⟨492647, by decide⟩,⟨492682, by decide⟩,⟨492713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18017_492714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18017 ⟨492714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18017
    ⟨492714, by decide⟩ (by decide) (![⟨492571, by decide⟩,⟨492647, by decide⟩,⟨492682, by decide⟩,⟨492713, by decide⟩]) unmarked_context_11_18017_492714 node_context_11_18017_492714
  intro a
  fin_cases a
  · exact context_12_72068_492571
  · exact context_12_72069_492647
  · exact context_12_72070_492682
  · exact context_12_72071_492713

theorem selected_cut_19290 : selected 9 ⟨492736, by decide⟩
    (prefixPartial 12 72072) = some ⟨12, 2, 0, 492736, 72072, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_72072_492736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72072 ⟨492736, by decide⟩ :=
  accepted_of_selected 12 72072 ⟨492736, by decide⟩ ⟨12, 2, 0, 492736, 72072, 2661, 65536⟩
    (by decide) selected_cut_19290

theorem selected_cut_19291 : selected 9 ⟨492760, by decide⟩
    (prefixPartial 12 72073) = some ⟨12, 2, 0, 492760, 72073, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_72073_492760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72073 ⟨492760, by decide⟩ :=
  accepted_of_selected 12 72073 ⟨492760, by decide⟩ ⟨12, 2, 0, 492760, 72073, 2969, 65536⟩
    (by decide) selected_cut_19291

theorem selected_cut_19292 : selected 9 ⟨492793, by decide⟩
    (prefixPartial 12 72074) = some ⟨12, 2, 0, 492793, 72074, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_72074_492793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72074 ⟨492793, by decide⟩ :=
  accepted_of_selected 12 72074 ⟨492793, by decide⟩ ⟨12, 2, 0, 492793, 72074, 3085, 65536⟩
    (by decide) selected_cut_19292

theorem selected_cut_19293 : selected 9 ⟨492819, by decide⟩
    (prefixPartial 12 72075) = some ⟨12, 2, 0, 492819, 72075, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_72075_492819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72075 ⟨492819, by decide⟩ :=
  accepted_of_selected 12 72075 ⟨492819, by decide⟩ ⟨12, 2, 0, 492819, 72075, 2881, 65536⟩
    (by decide) selected_cut_19293

theorem unmarked_context_11_18018_492820 : frontier 10 ⟨492820, by decide⟩
    (prefixCache 11 18018) (prefixPartial 11 18018) = false := by
  decide +kernel

theorem node_context_11_18018_492820 : EJMOriginalGlobalDAGData.nodes 10 ⟨492820, by decide⟩ =
    .split (coordinate 11) (![⟨492736, by decide⟩,⟨492760, by decide⟩,⟨492793, by decide⟩,⟨492819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18018_492820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18018 ⟨492820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18018
    ⟨492820, by decide⟩ (by decide) (![⟨492736, by decide⟩,⟨492760, by decide⟩,⟨492793, by decide⟩,⟨492819, by decide⟩]) unmarked_context_11_18018_492820 node_context_11_18018_492820
  intro a
  fin_cases a
  · exact context_12_72072_492736
  · exact context_12_72073_492760
  · exact context_12_72074_492793
  · exact context_12_72075_492819

theorem selected_cut_19294 : selected 9 ⟨492840, by decide⟩
    (prefixPartial 12 72076) = some ⟨12, 2, 0, 492840, 72076, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_72076_492840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72076 ⟨492840, by decide⟩ :=
  accepted_of_selected 12 72076 ⟨492840, by decide⟩ ⟨12, 2, 0, 492840, 72076, 2745, 65536⟩
    (by decide) selected_cut_19294

theorem selected_cut_19295 : selected 9 ⟨492866, by decide⟩
    (prefixPartial 12 72077) = some ⟨12, 2, 0, 492866, 72077, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_72077_492866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72077 ⟨492866, by decide⟩ :=
  accepted_of_selected 12 72077 ⟨492866, by decide⟩ ⟨12, 2, 0, 492866, 72077, 2849, 65536⟩
    (by decide) selected_cut_19295

theorem selected_cut_19296 : selected 9 ⟨492897, by decide⟩
    (prefixPartial 12 72078) = some ⟨12, 2, 0, 492897, 72078, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_72078_492897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72078 ⟨492897, by decide⟩ :=
  accepted_of_selected 12 72078 ⟨492897, by decide⟩ ⟨12, 2, 0, 492897, 72078, 3021, 65536⟩
    (by decide) selected_cut_19296

theorem selected_cut_19297 : selected 9 ⟨492919, by decide⟩
    (prefixPartial 12 72079) = some ⟨12, 2, 0, 492919, 72079, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_72079_492919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72079 ⟨492919, by decide⟩ :=
  accepted_of_selected 12 72079 ⟨492919, by decide⟩ ⟨12, 2, 0, 492919, 72079, 2849, 65536⟩
    (by decide) selected_cut_19297

theorem unmarked_context_11_18019_492920 : frontier 10 ⟨492920, by decide⟩
    (prefixCache 11 18019) (prefixPartial 11 18019) = false := by
  decide +kernel

theorem node_context_11_18019_492920 : EJMOriginalGlobalDAGData.nodes 10 ⟨492920, by decide⟩ =
    .split (coordinate 11) (![⟨492840, by decide⟩,⟨492866, by decide⟩,⟨492897, by decide⟩,⟨492919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18019_492920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18019 ⟨492920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18019
    ⟨492920, by decide⟩ (by decide) (![⟨492840, by decide⟩,⟨492866, by decide⟩,⟨492897, by decide⟩,⟨492919, by decide⟩]) unmarked_context_11_18019_492920 node_context_11_18019_492920
  intro a
  fin_cases a
  · exact context_12_72076_492840
  · exact context_12_72077_492866
  · exact context_12_72078_492897
  · exact context_12_72079_492919

theorem unmarked_context_10_4504_492921 : frontier 11 ⟨492921, by decide⟩
    (prefixCache 10 4504) (prefixPartial 10 4504) = false := by
  decide +kernel

theorem node_context_10_4504_492921 : EJMOriginalGlobalDAGData.nodes 11 ⟨492921, by decide⟩ =
    .split (coordinate 10) (![⟨492546, by decide⟩,⟨492714, by decide⟩,⟨492820, by decide⟩,⟨492920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4504_492921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4504 ⟨492921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4504
    ⟨492921, by decide⟩ (by decide) (![⟨492546, by decide⟩,⟨492714, by decide⟩,⟨492820, by decide⟩,⟨492920, by decide⟩]) unmarked_context_10_4504_492921 node_context_10_4504_492921
  intro a
  fin_cases a
  · exact context_11_18016_492546
  · exact context_11_18017_492714
  · exact context_11_18018_492820
  · exact context_11_18019_492920

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
