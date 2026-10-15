/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover064
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06243 : selected 9 ⟨187900, by decide⟩
    (prefixPartial 12 21147) = some ⟨12, 2, 0, 187900, 21147, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_21147_187900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21147 ⟨187900, by decide⟩ :=
  accepted_of_selected 12 21147 ⟨187900, by decide⟩ ⟨12, 2, 0, 187900, 21147, 2373, 65536⟩
    (by decide) selected_cut_06243

theorem unmarked_context_11_5286_187901 : frontier 10 ⟨187901, by decide⟩
    (prefixCache 11 5286) (prefixPartial 11 5286) = false := by
  decide +kernel

theorem node_context_11_5286_187901 : EJMOriginalGlobalDAGData.nodes 10 ⟨187901, by decide⟩ =
    .split (coordinate 11) (![⟨187807, by decide⟩,⟨187829, by decide⟩,⟨187877, by decide⟩,⟨187900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5286_187901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5286 ⟨187901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5286
    ⟨187901, by decide⟩ (by decide) (![⟨187807, by decide⟩,⟨187829, by decide⟩,⟨187877, by decide⟩,⟨187900, by decide⟩]) unmarked_context_11_5286_187901 node_context_11_5286_187901
  intro a
  fin_cases a
  · exact context_12_21144_187807
  · exact context_12_21145_187829
  · exact context_12_21146_187877
  · exact context_12_21147_187900

theorem selected_cut_06244 : selected 9 ⟨187925, by decide⟩
    (prefixPartial 12 21148) = some ⟨12, 2, 0, 187925, 21148, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_21148_187925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21148 ⟨187925, by decide⟩ :=
  accepted_of_selected 12 21148 ⟨187925, by decide⟩ ⟨12, 2, 0, 187925, 21148, 1957, 65536⟩
    (by decide) selected_cut_06244

theorem selected_cut_06245 : selected 9 ⟨187951, by decide⟩
    (prefixPartial 12 21149) = some ⟨12, 2, 0, 187951, 21149, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_21149_187951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21149 ⟨187951, by decide⟩ :=
  accepted_of_selected 12 21149 ⟨187951, by decide⟩ ⟨12, 2, 0, 187951, 21149, 2393, 65536⟩
    (by decide) selected_cut_06245

theorem selected_cut_06246 : selected 9 ⟨187980, by decide⟩
    (prefixPartial 12 21150) = some ⟨12, 2, 0, 187980, 21150, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_21150_187980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21150 ⟨187980, by decide⟩ :=
  accepted_of_selected 12 21150 ⟨187980, by decide⟩ ⟨12, 2, 0, 187980, 21150, 2097, 65536⟩
    (by decide) selected_cut_06246

theorem selected_cut_06247 : selected 9 ⟨188002, by decide⟩
    (prefixPartial 12 21151) = some ⟨12, 2, 0, 188002, 21151, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_21151_188002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21151 ⟨188002, by decide⟩ :=
  accepted_of_selected 12 21151 ⟨188002, by decide⟩ ⟨12, 2, 0, 188002, 21151, 2317, 65536⟩
    (by decide) selected_cut_06247

theorem unmarked_context_11_5287_188003 : frontier 10 ⟨188003, by decide⟩
    (prefixCache 11 5287) (prefixPartial 11 5287) = false := by
  decide +kernel

theorem node_context_11_5287_188003 : EJMOriginalGlobalDAGData.nodes 10 ⟨188003, by decide⟩ =
    .split (coordinate 11) (![⟨187925, by decide⟩,⟨187951, by decide⟩,⟨187980, by decide⟩,⟨188002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5287_188003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5287 ⟨188003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5287
    ⟨188003, by decide⟩ (by decide) (![⟨187925, by decide⟩,⟨187951, by decide⟩,⟨187980, by decide⟩,⟨188002, by decide⟩]) unmarked_context_11_5287_188003 node_context_11_5287_188003
  intro a
  fin_cases a
  · exact context_12_21148_187925
  · exact context_12_21149_187951
  · exact context_12_21150_187980
  · exact context_12_21151_188002

theorem unmarked_context_10_1321_188004 : frontier 11 ⟨188004, by decide⟩
    (prefixCache 10 1321) (prefixPartial 10 1321) = false := by
  decide +kernel

theorem node_context_10_1321_188004 : EJMOriginalGlobalDAGData.nodes 11 ⟨188004, by decide⟩ =
    .split (coordinate 10) (![⟨187690, by decide⟩,⟨187786, by decide⟩,⟨187901, by decide⟩,⟨188003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1321_188004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1321 ⟨188004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1321
    ⟨188004, by decide⟩ (by decide) (![⟨187690, by decide⟩,⟨187786, by decide⟩,⟨187901, by decide⟩,⟨188003, by decide⟩]) unmarked_context_10_1321_188004 node_context_10_1321_188004
  intro a
  fin_cases a
  · exact context_11_5284_187690
  · exact context_11_5285_187786
  · exact context_11_5286_187901
  · exact context_11_5287_188003

theorem selected_cut_06248 : selected 9 ⟨188018, by decide⟩
    (prefixPartial 12 21152) = some ⟨12, 2, 0, 188018, 21152, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_21152_188018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21152 ⟨188018, by decide⟩ :=
  accepted_of_selected 12 21152 ⟨188018, by decide⟩ ⟨12, 2, 0, 188018, 21152, 1237, 65536⟩
    (by decide) selected_cut_06248

theorem selected_cut_06249 : selected 9 ⟨188037, by decide⟩
    (prefixPartial 12 21153) = some ⟨12, 2, 0, 188037, 21153, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_21153_188037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21153 ⟨188037, by decide⟩ :=
  accepted_of_selected 12 21153 ⟨188037, by decide⟩ ⟨12, 2, 0, 188037, 21153, 1641, 65536⟩
    (by decide) selected_cut_06249

theorem selected_cut_06250 : selected 9 ⟨188058, by decide⟩
    (prefixPartial 12 21154) = some ⟨12, 2, 0, 188058, 21154, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_21154_188058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21154 ⟨188058, by decide⟩ :=
  accepted_of_selected 12 21154 ⟨188058, by decide⟩ ⟨12, 2, 0, 188058, 21154, 1385, 65536⟩
    (by decide) selected_cut_06250

theorem selected_cut_06251 : selected 9 ⟨188074, by decide⟩
    (prefixPartial 12 21155) = some ⟨12, 2, 0, 188074, 21155, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_21155_188074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21155 ⟨188074, by decide⟩ :=
  accepted_of_selected 12 21155 ⟨188074, by decide⟩ ⟨12, 2, 0, 188074, 21155, 1509, 65536⟩
    (by decide) selected_cut_06251

theorem unmarked_context_11_5288_188075 : frontier 10 ⟨188075, by decide⟩
    (prefixCache 11 5288) (prefixPartial 11 5288) = false := by
  decide +kernel

theorem node_context_11_5288_188075 : EJMOriginalGlobalDAGData.nodes 10 ⟨188075, by decide⟩ =
    .split (coordinate 11) (![⟨188018, by decide⟩,⟨188037, by decide⟩,⟨188058, by decide⟩,⟨188074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5288_188075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5288 ⟨188075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5288
    ⟨188075, by decide⟩ (by decide) (![⟨188018, by decide⟩,⟨188037, by decide⟩,⟨188058, by decide⟩,⟨188074, by decide⟩]) unmarked_context_11_5288_188075 node_context_11_5288_188075
  intro a
  fin_cases a
  · exact context_12_21152_188018
  · exact context_12_21153_188037
  · exact context_12_21154_188058
  · exact context_12_21155_188074

theorem selected_cut_06252 : selected 9 ⟨188091, by decide⟩
    (prefixPartial 12 21156) = some ⟨12, 2, 0, 188091, 21156, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_21156_188091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21156 ⟨188091, by decide⟩ :=
  accepted_of_selected 12 21156 ⟨188091, by decide⟩ ⟨12, 2, 0, 188091, 21156, 1213, 65536⟩
    (by decide) selected_cut_06252

theorem selected_cut_06253 : selected 9 ⟨188112, by decide⟩
    (prefixPartial 12 21157) = some ⟨12, 2, 0, 188112, 21157, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_21157_188112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21157 ⟨188112, by decide⟩ :=
  accepted_of_selected 12 21157 ⟨188112, by decide⟩ ⟨12, 2, 0, 188112, 21157, 1537, 65536⟩
    (by decide) selected_cut_06253

theorem selected_cut_06254 : selected 9 ⟨188132, by decide⟩
    (prefixPartial 12 21158) = some ⟨12, 2, 0, 188132, 21158, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_21158_188132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21158 ⟨188132, by decide⟩ :=
  accepted_of_selected 12 21158 ⟨188132, by decide⟩ ⟨12, 2, 0, 188132, 21158, 1277, 65536⟩
    (by decide) selected_cut_06254

theorem selected_cut_06255 : selected 9 ⟨188151, by decide⟩
    (prefixPartial 12 21159) = some ⟨12, 2, 0, 188151, 21159, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_21159_188151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21159 ⟨188151, by decide⟩ :=
  accepted_of_selected 12 21159 ⟨188151, by decide⟩ ⟨12, 2, 0, 188151, 21159, 1393, 65536⟩
    (by decide) selected_cut_06255

theorem unmarked_context_11_5289_188152 : frontier 10 ⟨188152, by decide⟩
    (prefixCache 11 5289) (prefixPartial 11 5289) = false := by
  decide +kernel

theorem node_context_11_5289_188152 : EJMOriginalGlobalDAGData.nodes 10 ⟨188152, by decide⟩ =
    .split (coordinate 11) (![⟨188091, by decide⟩,⟨188112, by decide⟩,⟨188132, by decide⟩,⟨188151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5289_188152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5289 ⟨188152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5289
    ⟨188152, by decide⟩ (by decide) (![⟨188091, by decide⟩,⟨188112, by decide⟩,⟨188132, by decide⟩,⟨188151, by decide⟩]) unmarked_context_11_5289_188152 node_context_11_5289_188152
  intro a
  fin_cases a
  · exact context_12_21156_188091
  · exact context_12_21157_188112
  · exact context_12_21158_188132
  · exact context_12_21159_188151

theorem selected_cut_06256 : selected 9 ⟨188169, by decide⟩
    (prefixPartial 12 21160) = some ⟨12, 2, 0, 188169, 21160, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_21160_188169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21160 ⟨188169, by decide⟩ :=
  accepted_of_selected 12 21160 ⟨188169, by decide⟩ ⟨12, 2, 0, 188169, 21160, 1181, 65536⟩
    (by decide) selected_cut_06256

theorem selected_cut_06257 : selected 9 ⟨188188, by decide⟩
    (prefixPartial 12 21161) = some ⟨12, 2, 0, 188188, 21161, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_21161_188188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21161 ⟨188188, by decide⟩ :=
  accepted_of_selected 12 21161 ⟨188188, by decide⟩ ⟨12, 2, 0, 188188, 21161, 1581, 65536⟩
    (by decide) selected_cut_06257

theorem selected_cut_06258 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 21162) = some ⟨12, 1, 0, 188189, 21162, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21162_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21162 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 21162 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 21162, 1, 65536⟩
    (by decide) selected_cut_06258

theorem selected_cut_06259 : selected 9 ⟨188207, by decide⟩
    (prefixPartial 12 21163) = some ⟨12, 2, 0, 188207, 21163, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_21163_188207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21163 ⟨188207, by decide⟩ :=
  accepted_of_selected 12 21163 ⟨188207, by decide⟩ ⟨12, 2, 0, 188207, 21163, 1433, 65536⟩
    (by decide) selected_cut_06259

theorem unmarked_context_11_5290_188208 : frontier 10 ⟨188208, by decide⟩
    (prefixCache 11 5290) (prefixPartial 11 5290) = false := by
  decide +kernel

theorem node_context_11_5290_188208 : EJMOriginalGlobalDAGData.nodes 10 ⟨188208, by decide⟩ =
    .split (coordinate 11) (![⟨188169, by decide⟩,⟨188188, by decide⟩,⟨188189, by decide⟩,⟨188207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5290_188208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5290 ⟨188208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5290
    ⟨188208, by decide⟩ (by decide) (![⟨188169, by decide⟩,⟨188188, by decide⟩,⟨188189, by decide⟩,⟨188207, by decide⟩]) unmarked_context_11_5290_188208 node_context_11_5290_188208
  intro a
  fin_cases a
  · exact context_12_21160_188169
  · exact context_12_21161_188188
  · exact context_12_21162_188189
  · exact context_12_21163_188207

theorem selected_cut_06260 : selected 9 ⟨188226, by decide⟩
    (prefixPartial 12 21164) = some ⟨12, 2, 0, 188226, 21164, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_21164_188226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21164 ⟨188226, by decide⟩ :=
  accepted_of_selected 12 21164 ⟨188226, by decide⟩ ⟨12, 2, 0, 188226, 21164, 1369, 65536⟩
    (by decide) selected_cut_06260

theorem selected_cut_06261 : selected 9 ⟨188241, by decide⟩
    (prefixPartial 12 21165) = some ⟨12, 2, 0, 188241, 21165, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_21165_188241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21165 ⟨188241, by decide⟩ :=
  accepted_of_selected 12 21165 ⟨188241, by decide⟩ ⟨12, 2, 0, 188241, 21165, 1717, 65536⟩
    (by decide) selected_cut_06261

theorem selected_cut_06262 : selected 9 ⟨188261, by decide⟩
    (prefixPartial 12 21166) = some ⟨12, 2, 0, 188261, 21166, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_21166_188261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21166 ⟨188261, by decide⟩ :=
  accepted_of_selected 12 21166 ⟨188261, by decide⟩ ⟨12, 2, 0, 188261, 21166, 1425, 65536⟩
    (by decide) selected_cut_06262

theorem selected_cut_06263 : selected 9 ⟨188277, by decide⟩
    (prefixPartial 12 21167) = some ⟨12, 2, 0, 188277, 21167, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_21167_188277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21167 ⟨188277, by decide⟩ :=
  accepted_of_selected 12 21167 ⟨188277, by decide⟩ ⟨12, 2, 0, 188277, 21167, 1553, 65536⟩
    (by decide) selected_cut_06263

theorem unmarked_context_11_5291_188278 : frontier 10 ⟨188278, by decide⟩
    (prefixCache 11 5291) (prefixPartial 11 5291) = false := by
  decide +kernel

theorem node_context_11_5291_188278 : EJMOriginalGlobalDAGData.nodes 10 ⟨188278, by decide⟩ =
    .split (coordinate 11) (![⟨188226, by decide⟩,⟨188241, by decide⟩,⟨188261, by decide⟩,⟨188277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5291_188278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5291 ⟨188278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5291
    ⟨188278, by decide⟩ (by decide) (![⟨188226, by decide⟩,⟨188241, by decide⟩,⟨188261, by decide⟩,⟨188277, by decide⟩]) unmarked_context_11_5291_188278 node_context_11_5291_188278
  intro a
  fin_cases a
  · exact context_12_21164_188226
  · exact context_12_21165_188241
  · exact context_12_21166_188261
  · exact context_12_21167_188277

theorem unmarked_context_10_1322_188279 : frontier 11 ⟨188279, by decide⟩
    (prefixCache 10 1322) (prefixPartial 10 1322) = false := by
  decide +kernel

theorem node_context_10_1322_188279 : EJMOriginalGlobalDAGData.nodes 11 ⟨188279, by decide⟩ =
    .split (coordinate 10) (![⟨188075, by decide⟩,⟨188152, by decide⟩,⟨188208, by decide⟩,⟨188278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1322_188279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1322 ⟨188279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1322
    ⟨188279, by decide⟩ (by decide) (![⟨188075, by decide⟩,⟨188152, by decide⟩,⟨188208, by decide⟩,⟨188278, by decide⟩]) unmarked_context_10_1322_188279 node_context_10_1322_188279
  intro a
  fin_cases a
  · exact context_11_5288_188075
  · exact context_11_5289_188152
  · exact context_11_5290_188208
  · exact context_11_5291_188278

theorem selected_cut_06264 : selected 9 ⟨188289, by decide⟩
    (prefixPartial 12 21168) = some ⟨12, 2, 0, 188289, 21168, 973, 65536⟩ := by
  decide +kernel

theorem context_12_21168_188289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21168 ⟨188289, by decide⟩ :=
  accepted_of_selected 12 21168 ⟨188289, by decide⟩ ⟨12, 2, 0, 188289, 21168, 973, 65536⟩
    (by decide) selected_cut_06264

theorem selected_cut_06265 : selected 9 ⟨188305, by decide⟩
    (prefixPartial 12 21169) = some ⟨12, 2, 0, 188305, 21169, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_21169_188305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21169 ⟨188305, by decide⟩ :=
  accepted_of_selected 12 21169 ⟨188305, by decide⟩ ⟨12, 2, 0, 188305, 21169, 1245, 65536⟩
    (by decide) selected_cut_06265

theorem selected_cut_06266 : selected 9 ⟨188317, by decide⟩
    (prefixPartial 12 21170) = some ⟨12, 2, 0, 188317, 21170, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_21170_188317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21170 ⟨188317, by decide⟩ :=
  accepted_of_selected 12 21170 ⟨188317, by decide⟩ ⟨12, 2, 0, 188317, 21170, 1073, 65536⟩
    (by decide) selected_cut_06266

theorem selected_cut_06267 : selected 9 ⟨188330, by decide⟩
    (prefixPartial 12 21171) = some ⟨12, 2, 0, 188330, 21171, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_21171_188330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21171 ⟨188330, by decide⟩ :=
  accepted_of_selected 12 21171 ⟨188330, by decide⟩ ⟨12, 2, 0, 188330, 21171, 1245, 65536⟩
    (by decide) selected_cut_06267

theorem unmarked_context_11_5292_188331 : frontier 10 ⟨188331, by decide⟩
    (prefixCache 11 5292) (prefixPartial 11 5292) = false := by
  decide +kernel

theorem node_context_11_5292_188331 : EJMOriginalGlobalDAGData.nodes 10 ⟨188331, by decide⟩ =
    .split (coordinate 11) (![⟨188289, by decide⟩,⟨188305, by decide⟩,⟨188317, by decide⟩,⟨188330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5292_188331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5292 ⟨188331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5292
    ⟨188331, by decide⟩ (by decide) (![⟨188289, by decide⟩,⟨188305, by decide⟩,⟨188317, by decide⟩,⟨188330, by decide⟩]) unmarked_context_11_5292_188331 node_context_11_5292_188331
  intro a
  fin_cases a
  · exact context_12_21168_188289
  · exact context_12_21169_188305
  · exact context_12_21170_188317
  · exact context_12_21171_188330

theorem selected_cut_06268 : selected 9 ⟨188343, by decide⟩
    (prefixPartial 12 21172) = some ⟨12, 2, 0, 188343, 21172, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_21172_188343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21172 ⟨188343, by decide⟩ :=
  accepted_of_selected 12 21172 ⟨188343, by decide⟩ ⟨12, 2, 0, 188343, 21172, 1013, 65536⟩
    (by decide) selected_cut_06268

theorem selected_cut_06269 : selected 9 ⟨188359, by decide⟩
    (prefixPartial 12 21173) = some ⟨12, 2, 0, 188359, 21173, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_21173_188359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21173 ⟨188359, by decide⟩ :=
  accepted_of_selected 12 21173 ⟨188359, by decide⟩ ⟨12, 2, 0, 188359, 21173, 1209, 65536⟩
    (by decide) selected_cut_06269

theorem selected_cut_06270 : selected 9 ⟨188374, by decide⟩
    (prefixPartial 12 21174) = some ⟨12, 2, 0, 188374, 21174, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_21174_188374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21174 ⟨188374, by decide⟩ :=
  accepted_of_selected 12 21174 ⟨188374, by decide⟩ ⟨12, 2, 0, 188374, 21174, 1085, 65536⟩
    (by decide) selected_cut_06270

theorem selected_cut_06271 : selected 9 ⟨188389, by decide⟩
    (prefixPartial 12 21175) = some ⟨12, 2, 0, 188389, 21175, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_21175_188389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21175 ⟨188389, by decide⟩ :=
  accepted_of_selected 12 21175 ⟨188389, by decide⟩ ⟨12, 2, 0, 188389, 21175, 1249, 65536⟩
    (by decide) selected_cut_06271

theorem unmarked_context_11_5293_188390 : frontier 10 ⟨188390, by decide⟩
    (prefixCache 11 5293) (prefixPartial 11 5293) = false := by
  decide +kernel

theorem node_context_11_5293_188390 : EJMOriginalGlobalDAGData.nodes 10 ⟨188390, by decide⟩ =
    .split (coordinate 11) (![⟨188343, by decide⟩,⟨188359, by decide⟩,⟨188374, by decide⟩,⟨188389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5293_188390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5293 ⟨188390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5293
    ⟨188390, by decide⟩ (by decide) (![⟨188343, by decide⟩,⟨188359, by decide⟩,⟨188374, by decide⟩,⟨188389, by decide⟩]) unmarked_context_11_5293_188390 node_context_11_5293_188390
  intro a
  fin_cases a
  · exact context_12_21172_188343
  · exact context_12_21173_188359
  · exact context_12_21174_188374
  · exact context_12_21175_188389

theorem selected_cut_06272 : selected 9 ⟨188403, by decide⟩
    (prefixPartial 12 21176) = some ⟨12, 2, 0, 188403, 21176, 993, 65536⟩ := by
  decide +kernel

theorem context_12_21176_188403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21176 ⟨188403, by decide⟩ :=
  accepted_of_selected 12 21176 ⟨188403, by decide⟩ ⟨12, 2, 0, 188403, 21176, 993, 65536⟩
    (by decide) selected_cut_06272

theorem selected_cut_06273 : selected 9 ⟨188417, by decide⟩
    (prefixPartial 12 21177) = some ⟨12, 2, 0, 188417, 21177, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_21177_188417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21177 ⟨188417, by decide⟩ :=
  accepted_of_selected 12 21177 ⟨188417, by decide⟩ ⟨12, 2, 0, 188417, 21177, 1281, 65536⟩
    (by decide) selected_cut_06273

theorem selected_cut_06274 : selected 9 ⟨188434, by decide⟩
    (prefixPartial 12 21178) = some ⟨12, 2, 0, 188434, 21178, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_21178_188434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21178 ⟨188434, by decide⟩ :=
  accepted_of_selected 12 21178 ⟨188434, by decide⟩ ⟨12, 2, 0, 188434, 21178, 1489, 65536⟩
    (by decide) selected_cut_06274

theorem selected_cut_06275 : selected 9 ⟨188446, by decide⟩
    (prefixPartial 12 21179) = some ⟨12, 2, 0, 188446, 21179, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_21179_188446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21179 ⟨188446, by decide⟩ :=
  accepted_of_selected 12 21179 ⟨188446, by decide⟩ ⟨12, 2, 0, 188446, 21179, 1201, 65536⟩
    (by decide) selected_cut_06275

theorem unmarked_context_11_5294_188447 : frontier 10 ⟨188447, by decide⟩
    (prefixCache 11 5294) (prefixPartial 11 5294) = false := by
  decide +kernel

theorem node_context_11_5294_188447 : EJMOriginalGlobalDAGData.nodes 10 ⟨188447, by decide⟩ =
    .split (coordinate 11) (![⟨188403, by decide⟩,⟨188417, by decide⟩,⟨188434, by decide⟩,⟨188446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5294_188447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5294 ⟨188447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5294
    ⟨188447, by decide⟩ (by decide) (![⟨188403, by decide⟩,⟨188417, by decide⟩,⟨188434, by decide⟩,⟨188446, by decide⟩]) unmarked_context_11_5294_188447 node_context_11_5294_188447
  intro a
  fin_cases a
  · exact context_12_21176_188403
  · exact context_12_21177_188417
  · exact context_12_21178_188434
  · exact context_12_21179_188446

theorem selected_cut_06276 : selected 9 ⟨188458, by decide⟩
    (prefixPartial 12 21180) = some ⟨12, 2, 0, 188458, 21180, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_21180_188458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21180 ⟨188458, by decide⟩ :=
  accepted_of_selected 12 21180 ⟨188458, by decide⟩ ⟨12, 2, 0, 188458, 21180, 1017, 65536⟩
    (by decide) selected_cut_06276

theorem selected_cut_06277 : selected 9 ⟨188470, by decide⟩
    (prefixPartial 12 21181) = some ⟨12, 2, 0, 188470, 21181, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_21181_188470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21181 ⟨188470, by decide⟩ :=
  accepted_of_selected 12 21181 ⟨188470, by decide⟩ ⟨12, 2, 0, 188470, 21181, 1165, 65536⟩
    (by decide) selected_cut_06277

theorem selected_cut_06278 : selected 9 ⟨188482, by decide⟩
    (prefixPartial 12 21182) = some ⟨12, 2, 0, 188482, 21182, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_21182_188482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21182 ⟨188482, by decide⟩ :=
  accepted_of_selected 12 21182 ⟨188482, by decide⟩ ⟨12, 2, 0, 188482, 21182, 1009, 65536⟩
    (by decide) selected_cut_06278

theorem selected_cut_06279 : selected 9 ⟨188494, by decide⟩
    (prefixPartial 12 21183) = some ⟨12, 2, 0, 188494, 21183, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_21183_188494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21183 ⟨188494, by decide⟩ :=
  accepted_of_selected 12 21183 ⟨188494, by decide⟩ ⟨12, 2, 0, 188494, 21183, 1169, 65536⟩
    (by decide) selected_cut_06279

theorem unmarked_context_11_5295_188495 : frontier 10 ⟨188495, by decide⟩
    (prefixCache 11 5295) (prefixPartial 11 5295) = false := by
  decide +kernel

theorem node_context_11_5295_188495 : EJMOriginalGlobalDAGData.nodes 10 ⟨188495, by decide⟩ =
    .split (coordinate 11) (![⟨188458, by decide⟩,⟨188470, by decide⟩,⟨188482, by decide⟩,⟨188494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5295_188495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5295 ⟨188495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5295
    ⟨188495, by decide⟩ (by decide) (![⟨188458, by decide⟩,⟨188470, by decide⟩,⟨188482, by decide⟩,⟨188494, by decide⟩]) unmarked_context_11_5295_188495 node_context_11_5295_188495
  intro a
  fin_cases a
  · exact context_12_21180_188458
  · exact context_12_21181_188470
  · exact context_12_21182_188482
  · exact context_12_21183_188494

theorem unmarked_context_10_1323_188496 : frontier 11 ⟨188496, by decide⟩
    (prefixCache 10 1323) (prefixPartial 10 1323) = false := by
  decide +kernel

theorem node_context_10_1323_188496 : EJMOriginalGlobalDAGData.nodes 11 ⟨188496, by decide⟩ =
    .split (coordinate 10) (![⟨188331, by decide⟩,⟨188390, by decide⟩,⟨188447, by decide⟩,⟨188495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1323_188496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1323 ⟨188496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1323
    ⟨188496, by decide⟩ (by decide) (![⟨188331, by decide⟩,⟨188390, by decide⟩,⟨188447, by decide⟩,⟨188495, by decide⟩]) unmarked_context_10_1323_188496 node_context_10_1323_188496
  intro a
  fin_cases a
  · exact context_11_5292_188331
  · exact context_11_5293_188390
  · exact context_11_5294_188447
  · exact context_11_5295_188495

theorem unmarked_context_9_330_188497 : frontier 12 ⟨188497, by decide⟩
    (prefixCache 9 330) (prefixPartial 9 330) = false := by
  decide +kernel

theorem node_context_9_330_188497 : EJMOriginalGlobalDAGData.nodes 12 ⟨188497, by decide⟩ =
    .split (coordinate 9) (![⟨187589, by decide⟩,⟨188004, by decide⟩,⟨188279, by decide⟩,⟨188496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_330_188497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 330 ⟨188497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 330
    ⟨188497, by decide⟩ (by decide) (![⟨187589, by decide⟩,⟨188004, by decide⟩,⟨188279, by decide⟩,⟨188496, by decide⟩]) unmarked_context_9_330_188497 node_context_9_330_188497
  intro a
  fin_cases a
  · exact context_10_1320_187589
  · exact context_10_1321_188004
  · exact context_10_1322_188279
  · exact context_10_1323_188496

theorem selected_cut_06280 : selected 9 ⟨188509, by decide⟩
    (prefixPartial 12 21184) = some ⟨12, 2, 0, 188509, 21184, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_21184_188509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21184 ⟨188509, by decide⟩ :=
  accepted_of_selected 12 21184 ⟨188509, by decide⟩ ⟨12, 2, 0, 188509, 21184, 1017, 65536⟩
    (by decide) selected_cut_06280

theorem selected_cut_06281 : selected 9 ⟨188525, by decide⟩
    (prefixPartial 12 21185) = some ⟨12, 2, 0, 188525, 21185, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_21185_188525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21185 ⟨188525, by decide⟩ :=
  accepted_of_selected 12 21185 ⟨188525, by decide⟩ ⟨12, 2, 0, 188525, 21185, 1189, 65536⟩
    (by decide) selected_cut_06281

theorem selected_cut_06282 : selected 9 ⟨188540, by decide⟩
    (prefixPartial 12 21186) = some ⟨12, 2, 0, 188540, 21186, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_21186_188540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21186 ⟨188540, by decide⟩ :=
  accepted_of_selected 12 21186 ⟨188540, by decide⟩ ⟨12, 2, 0, 188540, 21186, 1201, 65536⟩
    (by decide) selected_cut_06282

theorem selected_cut_06283 : selected 9 ⟨188550, by decide⟩
    (prefixPartial 12 21187) = some ⟨12, 2, 0, 188550, 21187, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_21187_188550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21187 ⟨188550, by decide⟩ :=
  accepted_of_selected 12 21187 ⟨188550, by decide⟩ ⟨12, 2, 0, 188550, 21187, 1117, 65536⟩
    (by decide) selected_cut_06283

theorem unmarked_context_11_5296_188551 : frontier 10 ⟨188551, by decide⟩
    (prefixCache 11 5296) (prefixPartial 11 5296) = false := by
  decide +kernel

theorem node_context_11_5296_188551 : EJMOriginalGlobalDAGData.nodes 10 ⟨188551, by decide⟩ =
    .split (coordinate 11) (![⟨188509, by decide⟩,⟨188525, by decide⟩,⟨188540, by decide⟩,⟨188550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5296_188551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5296 ⟨188551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5296
    ⟨188551, by decide⟩ (by decide) (![⟨188509, by decide⟩,⟨188525, by decide⟩,⟨188540, by decide⟩,⟨188550, by decide⟩]) unmarked_context_11_5296_188551 node_context_11_5296_188551
  intro a
  fin_cases a
  · exact context_12_21184_188509
  · exact context_12_21185_188525
  · exact context_12_21186_188540
  · exact context_12_21187_188550

theorem selected_cut_06284 : selected 10 ⟨188586, by decide⟩
    (prefixPartial 11 5297) = some ⟨11, 2, 0, 188586, 5297, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_5297_188586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5297 ⟨188586, by decide⟩ :=
  accepted_of_selected 11 5297 ⟨188586, by decide⟩ ⟨11, 2, 0, 188586, 5297, 2989, 262144⟩
    (by decide) selected_cut_06284

theorem selected_cut_06285 : selected 10 ⟨188614, by decide⟩
    (prefixPartial 11 5298) = some ⟨11, 2, 0, 188614, 5298, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_5298_188614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5298 ⟨188614, by decide⟩ :=
  accepted_of_selected 11 5298 ⟨188614, by decide⟩ ⟨11, 2, 0, 188614, 5298, 3161, 262144⟩
    (by decide) selected_cut_06285

theorem selected_cut_06286 : selected 10 ⟨188646, by decide⟩
    (prefixPartial 11 5299) = some ⟨11, 2, 0, 188646, 5299, 3001, 262144⟩ := by
  decide +kernel

theorem context_11_5299_188646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5299 ⟨188646, by decide⟩ :=
  accepted_of_selected 11 5299 ⟨188646, by decide⟩ ⟨11, 2, 0, 188646, 5299, 3001, 262144⟩
    (by decide) selected_cut_06286

theorem unmarked_context_10_1324_188647 : frontier 11 ⟨188647, by decide⟩
    (prefixCache 10 1324) (prefixPartial 10 1324) = false := by
  decide +kernel

theorem node_context_10_1324_188647 : EJMOriginalGlobalDAGData.nodes 11 ⟨188647, by decide⟩ =
    .split (coordinate 10) (![⟨188551, by decide⟩,⟨188586, by decide⟩,⟨188614, by decide⟩,⟨188646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1324_188647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1324 ⟨188647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1324
    ⟨188647, by decide⟩ (by decide) (![⟨188551, by decide⟩,⟨188586, by decide⟩,⟨188614, by decide⟩,⟨188646, by decide⟩]) unmarked_context_10_1324_188647 node_context_10_1324_188647
  intro a
  fin_cases a
  · exact context_11_5296_188551
  · exact context_11_5297_188586
  · exact context_11_5298_188614
  · exact context_11_5299_188646

theorem selected_cut_06287 : selected 10 ⟨188670, by decide⟩
    (prefixPartial 11 5300) = some ⟨11, 2, 0, 188670, 5300, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_5300_188670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5300 ⟨188670, by decide⟩ :=
  accepted_of_selected 11 5300 ⟨188670, by decide⟩ ⟨11, 2, 0, 188670, 5300, 2313, 262144⟩
    (by decide) selected_cut_06287

theorem selected_cut_06288 : selected 10 ⟨188693, by decide⟩
    (prefixPartial 11 5301) = some ⟨11, 2, 0, 188693, 5301, 1977, 262144⟩ := by
  decide +kernel

theorem context_11_5301_188693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5301 ⟨188693, by decide⟩ :=
  accepted_of_selected 11 5301 ⟨188693, by decide⟩ ⟨11, 2, 0, 188693, 5301, 1977, 262144⟩
    (by decide) selected_cut_06288

theorem selected_cut_06289 : selected 10 ⟨188714, by decide⟩
    (prefixPartial 11 5302) = some ⟨11, 2, 0, 188714, 5302, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_5302_188714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5302 ⟨188714, by decide⟩ :=
  accepted_of_selected 11 5302 ⟨188714, by decide⟩ ⟨11, 2, 0, 188714, 5302, 1985, 262144⟩
    (by decide) selected_cut_06289

theorem selected_cut_06290 : selected 10 ⟨188736, by decide⟩
    (prefixPartial 11 5303) = some ⟨11, 2, 0, 188736, 5303, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_5303_188736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5303 ⟨188736, by decide⟩ :=
  accepted_of_selected 11 5303 ⟨188736, by decide⟩ ⟨11, 2, 0, 188736, 5303, 1709, 262144⟩
    (by decide) selected_cut_06290

theorem unmarked_context_10_1325_188737 : frontier 11 ⟨188737, by decide⟩
    (prefixCache 10 1325) (prefixPartial 10 1325) = false := by
  decide +kernel

theorem node_context_10_1325_188737 : EJMOriginalGlobalDAGData.nodes 11 ⟨188737, by decide⟩ =
    .split (coordinate 10) (![⟨188670, by decide⟩,⟨188693, by decide⟩,⟨188714, by decide⟩,⟨188736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1325_188737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1325 ⟨188737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1325
    ⟨188737, by decide⟩ (by decide) (![⟨188670, by decide⟩,⟨188693, by decide⟩,⟨188714, by decide⟩,⟨188736, by decide⟩]) unmarked_context_10_1325_188737 node_context_10_1325_188737
  intro a
  fin_cases a
  · exact context_11_5300_188670
  · exact context_11_5301_188693
  · exact context_11_5302_188714
  · exact context_11_5303_188736

theorem selected_cut_06291 : selected 11 ⟨188793, by decide⟩
    (prefixPartial 10 1326) = some ⟨10, 2, 0, 188793, 1326, 4089, 1048576⟩ := by
  decide +kernel

theorem context_10_1326_188793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1326 ⟨188793, by decide⟩ :=
  accepted_of_selected 10 1326 ⟨188793, by decide⟩ ⟨10, 2, 0, 188793, 1326, 4089, 1048576⟩
    (by decide) selected_cut_06291

theorem selected_cut_06292 : selected 11 ⟨188832, by decide⟩
    (prefixPartial 10 1327) = some ⟨10, 2, 0, 188832, 1327, 1505, 1048576⟩ := by
  decide +kernel

theorem context_10_1327_188832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1327 ⟨188832, by decide⟩ :=
  accepted_of_selected 10 1327 ⟨188832, by decide⟩ ⟨10, 2, 0, 188832, 1327, 1505, 1048576⟩
    (by decide) selected_cut_06292

theorem unmarked_context_9_331_188833 : frontier 12 ⟨188833, by decide⟩
    (prefixCache 9 331) (prefixPartial 9 331) = false := by
  decide +kernel

theorem node_context_9_331_188833 : EJMOriginalGlobalDAGData.nodes 12 ⟨188833, by decide⟩ =
    .split (coordinate 9) (![⟨188647, by decide⟩,⟨188737, by decide⟩,⟨188793, by decide⟩,⟨188832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_331_188833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 331 ⟨188833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 331
    ⟨188833, by decide⟩ (by decide) (![⟨188647, by decide⟩,⟨188737, by decide⟩,⟨188793, by decide⟩,⟨188832, by decide⟩]) unmarked_context_9_331_188833 node_context_9_331_188833
  intro a
  fin_cases a
  · exact context_10_1324_188647
  · exact context_10_1325_188737
  · exact context_10_1326_188793
  · exact context_10_1327_188832

theorem unmarked_context_8_82_188834 : frontier 13 ⟨188834, by decide⟩
    (prefixCache 8 82) (prefixPartial 8 82) = false := by
  decide +kernel

theorem node_context_8_82_188834 : EJMOriginalGlobalDAGData.nodes 13 ⟨188834, by decide⟩ =
    .split (coordinate 8) (![⟨183892, by decide⟩,⟨187105, by decide⟩,⟨188497, by decide⟩,⟨188833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_82_188834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 82 ⟨188834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 82
    ⟨188834, by decide⟩ (by decide) (![⟨183892, by decide⟩,⟨187105, by decide⟩,⟨188497, by decide⟩,⟨188833, by decide⟩]) unmarked_context_8_82_188834 node_context_8_82_188834
  intro a
  fin_cases a
  · exact context_9_328_183892
  · exact context_9_329_187105
  · exact context_9_330_188497
  · exact context_9_331_188833

theorem selected_cut_06293 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 83) = some ⟨8, 1, 0, 14298, 83, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_83_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 83 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 83 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 83, 1, 16777216⟩
    (by decide) selected_cut_06293

theorem unmarked_context_7_20_188835 : frontier 14 ⟨188835, by decide⟩
    (prefixCache 7 20) (prefixPartial 7 20) = false := by
  decide +kernel

theorem node_context_7_20_188835 : EJMOriginalGlobalDAGData.nodes 14 ⟨188835, by decide⟩ =
    .split (coordinate 7) (![⟨172865, by decide⟩,⟨178213, by decide⟩,⟨188834, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_20_188835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 20 ⟨188835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 20
    ⟨188835, by decide⟩ (by decide) (![⟨172865, by decide⟩,⟨178213, by decide⟩,⟨188834, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_20_188835 node_context_7_20_188835
  intro a
  fin_cases a
  · exact context_8_80_172865
  · exact context_8_81_178213
  · exact context_8_82_188834
  · exact context_8_83_14298

theorem selected_cut_06294 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 21504) = some ⟨12, 1, 0, 34034, 21504, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21504_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21504 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 21504 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 21504, 1, 65536⟩
    (by decide) selected_cut_06294

theorem selected_cut_06295 : selected 9 ⟨188926, by decide⟩
    (prefixPartial 12 21505) = some ⟨12, 2, 0, 188926, 21505, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_21505_188926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21505 ⟨188926, by decide⟩ :=
  accepted_of_selected 12 21505 ⟨188926, by decide⟩ ⟨12, 2, 0, 188926, 21505, 2533, 65536⟩
    (by decide) selected_cut_06295

theorem selected_cut_06296 : selected 8 ⟨188989, by decide⟩
    (prefixPartial 13 86024) = some ⟨13, 2, 0, 188989, 86024, 3373, 16384⟩ := by
  decide +kernel

theorem context_13_86024_188989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86024 ⟨188989, by decide⟩ :=
  accepted_of_selected 13 86024 ⟨188989, by decide⟩ ⟨13, 2, 0, 188989, 86024, 3373, 16384⟩
    (by decide) selected_cut_06296

theorem selected_cut_06297 : selected 8 ⟨189029, by decide⟩
    (prefixPartial 13 86025) = some ⟨13, 2, 0, 189029, 86025, 3301, 16384⟩ := by
  decide +kernel

theorem context_13_86025_189029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86025 ⟨189029, by decide⟩ :=
  accepted_of_selected 13 86025 ⟨189029, by decide⟩ ⟨13, 2, 0, 189029, 86025, 3301, 16384⟩
    (by decide) selected_cut_06297

theorem selected_cut_06298 : selected 8 ⟨189055, by decide⟩
    (prefixPartial 13 86026) = some ⟨13, 2, 0, 189055, 86026, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_86026_189055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86026 ⟨189055, by decide⟩ :=
  accepted_of_selected 13 86026 ⟨189055, by decide⟩ ⟨13, 2, 0, 189055, 86026, 1909, 16384⟩
    (by decide) selected_cut_06298

theorem selected_cut_06299 : selected 8 ⟨189073, by decide⟩
    (prefixPartial 13 86027) = some ⟨13, 2, 0, 189073, 86027, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_86027_189073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86027 ⟨189073, by decide⟩ :=
  accepted_of_selected 13 86027 ⟨189073, by decide⟩ ⟨13, 2, 0, 189073, 86027, 1149, 16384⟩
    (by decide) selected_cut_06299

theorem unmarked_context_12_21506_189074 : frontier 9 ⟨189074, by decide⟩
    (prefixCache 12 21506) (prefixPartial 12 21506) = false := by
  decide +kernel

theorem node_context_12_21506_189074 : EJMOriginalGlobalDAGData.nodes 9 ⟨189074, by decide⟩ =
    .split (coordinate 12) (![⟨188989, by decide⟩,⟨189029, by decide⟩,⟨189055, by decide⟩,⟨189073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21506_189074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21506 ⟨189074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21506
    ⟨189074, by decide⟩ (by decide) (![⟨188989, by decide⟩,⟨189029, by decide⟩,⟨189055, by decide⟩,⟨189073, by decide⟩]) unmarked_context_12_21506_189074 node_context_12_21506_189074
  intro a
  fin_cases a
  · exact context_13_86024_188989
  · exact context_13_86025_189029
  · exact context_13_86026_189055
  · exact context_13_86027_189073

theorem selected_cut_06300 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21507) = some ⟨12, 1, 0, 893, 21507, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21507_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21507 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21507 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21507, 1, 65536⟩
    (by decide) selected_cut_06300

theorem unmarked_context_11_5376_189075 : frontier 10 ⟨189075, by decide⟩
    (prefixCache 11 5376) (prefixPartial 11 5376) = false := by
  decide +kernel

theorem node_context_11_5376_189075 : EJMOriginalGlobalDAGData.nodes 10 ⟨189075, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨188926, by decide⟩,⟨189074, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5376_189075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5376 ⟨189075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5376
    ⟨189075, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨188926, by decide⟩,⟨189074, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5376_189075 node_context_11_5376_189075
  intro a
  fin_cases a
  · exact context_12_21504_34034
  · exact context_12_21505_188926
  · exact context_12_21506_189074
  · exact context_12_21507_893

theorem selected_cut_06301 : selected 8 ⟨189100, by decide⟩
    (prefixPartial 13 86032) = some ⟨13, 2, 0, 189100, 86032, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_86032_189100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86032 ⟨189100, by decide⟩ :=
  accepted_of_selected 13 86032 ⟨189100, by decide⟩ ⟨13, 2, 0, 189100, 86032, 1161, 16384⟩
    (by decide) selected_cut_06301

theorem selected_cut_06302 : selected 8 ⟨189152, by decide⟩
    (prefixPartial 13 86033) = some ⟨13, 2, 0, 189152, 86033, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_86033_189152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86033 ⟨189152, by decide⟩ :=
  accepted_of_selected 13 86033 ⟨189152, by decide⟩ ⟨13, 2, 0, 189152, 86033, 1993, 16384⟩
    (by decide) selected_cut_06302

theorem selected_cut_06303 : selected 8 ⟨189185, by decide⟩
    (prefixPartial 13 86034) = some ⟨13, 2, 0, 189185, 86034, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_86034_189185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86034 ⟨189185, by decide⟩ :=
  accepted_of_selected 13 86034 ⟨189185, by decide⟩ ⟨13, 2, 0, 189185, 86034, 1861, 16384⟩
    (by decide) selected_cut_06303

theorem selected_cut_06304 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 86035) = some ⟨13, 1, 0, 414, 86035, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86035_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86035 ⟨414, by decide⟩ :=
  accepted_of_selected 13 86035 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 86035, 1, 16384⟩
    (by decide) selected_cut_06304

theorem unmarked_context_12_21508_189186 : frontier 9 ⟨189186, by decide⟩
    (prefixCache 12 21508) (prefixPartial 12 21508) = false := by
  decide +kernel

theorem node_context_12_21508_189186 : EJMOriginalGlobalDAGData.nodes 9 ⟨189186, by decide⟩ =
    .split (coordinate 12) (![⟨189100, by decide⟩,⟨189152, by decide⟩,⟨189185, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21508_189186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21508 ⟨189186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21508
    ⟨189186, by decide⟩ (by decide) (![⟨189100, by decide⟩,⟨189152, by decide⟩,⟨189185, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_21508_189186 node_context_12_21508_189186
  intro a
  fin_cases a
  · exact context_13_86032_189100
  · exact context_13_86033_189152
  · exact context_13_86034_189185
  · exact context_13_86035_414

theorem selected_cut_06305 : selected 8 ⟨189208, by decide⟩
    (prefixPartial 13 86036) = some ⟨13, 2, 0, 189208, 86036, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_86036_189208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86036 ⟨189208, by decide⟩ :=
  accepted_of_selected 13 86036 ⟨189208, by decide⟩ ⟨13, 2, 0, 189208, 86036, 1141, 16384⟩
    (by decide) selected_cut_06305

theorem selected_cut_06306 : selected 8 ⟨189242, by decide⟩
    (prefixPartial 13 86037) = some ⟨13, 2, 0, 189242, 86037, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_86037_189242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86037 ⟨189242, by decide⟩ :=
  accepted_of_selected 13 86037 ⟨189242, by decide⟩ ⟨13, 2, 0, 189242, 86037, 1637, 16384⟩
    (by decide) selected_cut_06306

theorem selected_cut_06307 : selected 8 ⟨189268, by decide⟩
    (prefixPartial 13 86038) = some ⟨13, 2, 0, 189268, 86038, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_86038_189268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86038 ⟨189268, by decide⟩ :=
  accepted_of_selected 13 86038 ⟨189268, by decide⟩ ⟨13, 2, 0, 189268, 86038, 1825, 16384⟩
    (by decide) selected_cut_06307

theorem selected_cut_06308 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 86039) = some ⟨13, 1, 0, 414, 86039, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86039_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86039 ⟨414, by decide⟩ :=
  accepted_of_selected 13 86039 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 86039, 1, 16384⟩
    (by decide) selected_cut_06308

theorem unmarked_context_12_21509_189269 : frontier 9 ⟨189269, by decide⟩
    (prefixCache 12 21509) (prefixPartial 12 21509) = false := by
  decide +kernel

theorem node_context_12_21509_189269 : EJMOriginalGlobalDAGData.nodes 9 ⟨189269, by decide⟩ =
    .split (coordinate 12) (![⟨189208, by decide⟩,⟨189242, by decide⟩,⟨189268, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21509_189269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21509 ⟨189269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21509
    ⟨189269, by decide⟩ (by decide) (![⟨189208, by decide⟩,⟨189242, by decide⟩,⟨189268, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_21509_189269 node_context_12_21509_189269
  intro a
  fin_cases a
  · exact context_13_86036_189208
  · exact context_13_86037_189242
  · exact context_13_86038_189268
  · exact context_13_86039_414

theorem selected_cut_06309 : selected 8 ⟨189325, by decide⟩
    (prefixPartial 13 86040) = some ⟨13, 2, 0, 189325, 86040, 3321, 16384⟩ := by
  decide +kernel

theorem context_13_86040_189325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86040 ⟨189325, by decide⟩ :=
  accepted_of_selected 13 86040 ⟨189325, by decide⟩ ⟨13, 2, 0, 189325, 86040, 3321, 16384⟩
    (by decide) selected_cut_06309

theorem selected_cut_06310 : selected 8 ⟨189396, by decide⟩
    (prefixPartial 13 86041) = some ⟨13, 2, 0, 189396, 86041, 4029, 16384⟩ := by
  decide +kernel

theorem context_13_86041_189396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86041 ⟨189396, by decide⟩ :=
  accepted_of_selected 13 86041 ⟨189396, by decide⟩ ⟨13, 2, 0, 189396, 86041, 4029, 16384⟩
    (by decide) selected_cut_06310

theorem selected_cut_06311 : selected 8 ⟨189428, by decide⟩
    (prefixPartial 13 86042) = some ⟨13, 2, 0, 189428, 86042, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_86042_189428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86042 ⟨189428, by decide⟩ :=
  accepted_of_selected 13 86042 ⟨189428, by decide⟩ ⟨13, 2, 0, 189428, 86042, 2177, 16384⟩
    (by decide) selected_cut_06311

theorem selected_cut_06312 : selected 8 ⟨189444, by decide⟩
    (prefixPartial 13 86043) = some ⟨13, 2, 0, 189444, 86043, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_86043_189444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86043 ⟨189444, by decide⟩ :=
  accepted_of_selected 13 86043 ⟨189444, by decide⟩ ⟨13, 2, 0, 189444, 86043, 1141, 16384⟩
    (by decide) selected_cut_06312

theorem unmarked_context_12_21510_189445 : frontier 9 ⟨189445, by decide⟩
    (prefixCache 12 21510) (prefixPartial 12 21510) = false := by
  decide +kernel

theorem node_context_12_21510_189445 : EJMOriginalGlobalDAGData.nodes 9 ⟨189445, by decide⟩ =
    .split (coordinate 12) (![⟨189325, by decide⟩,⟨189396, by decide⟩,⟨189428, by decide⟩,⟨189444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21510_189445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21510 ⟨189445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21510
    ⟨189445, by decide⟩ (by decide) (![⟨189325, by decide⟩,⟨189396, by decide⟩,⟨189428, by decide⟩,⟨189444, by decide⟩]) unmarked_context_12_21510_189445 node_context_12_21510_189445
  intro a
  fin_cases a
  · exact context_13_86040_189325
  · exact context_13_86041_189396
  · exact context_13_86042_189428
  · exact context_13_86043_189444

theorem selected_cut_06313 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21511) = some ⟨12, 1, 0, 893, 21511, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21511_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21511 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21511 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21511, 1, 65536⟩
    (by decide) selected_cut_06313

theorem unmarked_context_11_5377_189446 : frontier 10 ⟨189446, by decide⟩
    (prefixCache 11 5377) (prefixPartial 11 5377) = false := by
  decide +kernel

theorem node_context_11_5377_189446 : EJMOriginalGlobalDAGData.nodes 10 ⟨189446, by decide⟩ =
    .split (coordinate 11) (![⟨189186, by decide⟩,⟨189269, by decide⟩,⟨189445, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5377_189446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5377 ⟨189446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5377
    ⟨189446, by decide⟩ (by decide) (![⟨189186, by decide⟩,⟨189269, by decide⟩,⟨189445, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5377_189446 node_context_11_5377_189446
  intro a
  fin_cases a
  · exact context_12_21508_189186
  · exact context_12_21509_189269
  · exact context_12_21510_189445
  · exact context_12_21511_893

theorem selected_cut_06314 : selected 8 ⟨189484, by decide⟩
    (prefixPartial 13 86048) = some ⟨13, 2, 0, 189484, 86048, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_86048_189484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86048 ⟨189484, by decide⟩ :=
  accepted_of_selected 13 86048 ⟨189484, by decide⟩ ⟨13, 2, 0, 189484, 86048, 1921, 16384⟩
    (by decide) selected_cut_06314

theorem selected_cut_06315 : selected 8 ⟨189525, by decide⟩
    (prefixPartial 13 86049) = some ⟨13, 2, 0, 189525, 86049, 3557, 16384⟩ := by
  decide +kernel

theorem context_13_86049_189525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86049 ⟨189525, by decide⟩ :=
  accepted_of_selected 13 86049 ⟨189525, by decide⟩ ⟨13, 2, 0, 189525, 86049, 3557, 16384⟩
    (by decide) selected_cut_06315

theorem selected_cut_06316 : selected 8 ⟨189548, by decide⟩
    (prefixPartial 13 86050) = some ⟨13, 2, 0, 189548, 86050, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_86050_189548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86050 ⟨189548, by decide⟩ :=
  accepted_of_selected 13 86050 ⟨189548, by decide⟩ ⟨13, 2, 0, 189548, 86050, 2101, 16384⟩
    (by decide) selected_cut_06316

theorem selected_cut_06317 : selected 8 ⟨189559, by decide⟩
    (prefixPartial 13 86051) = some ⟨13, 2, 0, 189559, 86051, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_86051_189559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86051 ⟨189559, by decide⟩ :=
  accepted_of_selected 13 86051 ⟨189559, by decide⟩ ⟨13, 2, 0, 189559, 86051, 1069, 16384⟩
    (by decide) selected_cut_06317

theorem unmarked_context_12_21512_189560 : frontier 9 ⟨189560, by decide⟩
    (prefixCache 12 21512) (prefixPartial 12 21512) = false := by
  decide +kernel

theorem node_context_12_21512_189560 : EJMOriginalGlobalDAGData.nodes 9 ⟨189560, by decide⟩ =
    .split (coordinate 12) (![⟨189484, by decide⟩,⟨189525, by decide⟩,⟨189548, by decide⟩,⟨189559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21512_189560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21512 ⟨189560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21512
    ⟨189560, by decide⟩ (by decide) (![⟨189484, by decide⟩,⟨189525, by decide⟩,⟨189548, by decide⟩,⟨189559, by decide⟩]) unmarked_context_12_21512_189560 node_context_12_21512_189560
  intro a
  fin_cases a
  · exact context_13_86048_189484
  · exact context_13_86049_189525
  · exact context_13_86050_189548
  · exact context_13_86051_189559

theorem selected_cut_06318 : selected 8 ⟨189598, by decide⟩
    (prefixPartial 13 86052) = some ⟨13, 2, 0, 189598, 86052, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_86052_189598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86052 ⟨189598, by decide⟩ :=
  accepted_of_selected 13 86052 ⟨189598, by decide⟩ ⟨13, 2, 0, 189598, 86052, 2237, 16384⟩
    (by decide) selected_cut_06318

theorem selected_cut_06319 : selected 8 ⟨189649, by decide⟩
    (prefixPartial 13 86053) = some ⟨13, 2, 0, 189649, 86053, 3105, 16384⟩ := by
  decide +kernel

theorem context_13_86053_189649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86053 ⟨189649, by decide⟩ :=
  accepted_of_selected 13 86053 ⟨189649, by decide⟩ ⟨13, 2, 0, 189649, 86053, 3105, 16384⟩
    (by decide) selected_cut_06319

theorem selected_cut_06320 : selected 8 ⟨189672, by decide⟩
    (prefixPartial 13 86054) = some ⟨13, 2, 0, 189672, 86054, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_86054_189672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86054 ⟨189672, by decide⟩ :=
  accepted_of_selected 13 86054 ⟨189672, by decide⟩ ⟨13, 2, 0, 189672, 86054, 1953, 16384⟩
    (by decide) selected_cut_06320

theorem selected_cut_06321 : selected 8 ⟨189681, by decide⟩
    (prefixPartial 13 86055) = some ⟨13, 2, 0, 189681, 86055, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_86055_189681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86055 ⟨189681, by decide⟩ :=
  accepted_of_selected 13 86055 ⟨189681, by decide⟩ ⟨13, 2, 0, 189681, 86055, 1025, 16384⟩
    (by decide) selected_cut_06321

theorem unmarked_context_12_21513_189682 : frontier 9 ⟨189682, by decide⟩
    (prefixCache 12 21513) (prefixPartial 12 21513) = false := by
  decide +kernel

theorem node_context_12_21513_189682 : EJMOriginalGlobalDAGData.nodes 9 ⟨189682, by decide⟩ =
    .split (coordinate 12) (![⟨189598, by decide⟩,⟨189649, by decide⟩,⟨189672, by decide⟩,⟨189681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21513_189682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21513 ⟨189682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21513
    ⟨189682, by decide⟩ (by decide) (![⟨189598, by decide⟩,⟨189649, by decide⟩,⟨189672, by decide⟩,⟨189681, by decide⟩]) unmarked_context_12_21513_189682 node_context_12_21513_189682
  intro a
  fin_cases a
  · exact context_13_86052_189598
  · exact context_13_86053_189649
  · exact context_13_86054_189672
  · exact context_13_86055_189681

theorem selected_cut_06322 : selected 8 ⟨189758, by decide⟩
    (prefixPartial 13 86056) = some ⟨13, 2, 0, 189758, 86056, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_86056_189758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86056 ⟨189758, by decide⟩ :=
  accepted_of_selected 13 86056 ⟨189758, by decide⟩ ⟨13, 2, 0, 189758, 86056, 2905, 16384⟩
    (by decide) selected_cut_06322

theorem selected_cut_06323 : selected 8 ⟨189835, by decide⟩
    (prefixPartial 13 86057) = some ⟨13, 2, 0, 189835, 86057, 3881, 16384⟩ := by
  decide +kernel

theorem context_13_86057_189835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86057 ⟨189835, by decide⟩ :=
  accepted_of_selected 13 86057 ⟨189835, by decide⟩ ⟨13, 2, 0, 189835, 86057, 3881, 16384⟩
    (by decide) selected_cut_06323

theorem selected_cut_06324 : selected 8 ⟨189861, by decide⟩
    (prefixPartial 13 86058) = some ⟨13, 2, 0, 189861, 86058, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_86058_189861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86058 ⟨189861, by decide⟩ :=
  accepted_of_selected 13 86058 ⟨189861, by decide⟩ ⟨13, 2, 0, 189861, 86058, 1729, 16384⟩
    (by decide) selected_cut_06324

theorem selected_cut_06325 : selected 8 ⟨189875, by decide⟩
    (prefixPartial 13 86059) = some ⟨13, 2, 0, 189875, 86059, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_86059_189875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86059 ⟨189875, by decide⟩ :=
  accepted_of_selected 13 86059 ⟨189875, by decide⟩ ⟨13, 2, 0, 189875, 86059, 1201, 16384⟩
    (by decide) selected_cut_06325

theorem unmarked_context_12_21514_189876 : frontier 9 ⟨189876, by decide⟩
    (prefixCache 12 21514) (prefixPartial 12 21514) = false := by
  decide +kernel

theorem node_context_12_21514_189876 : EJMOriginalGlobalDAGData.nodes 9 ⟨189876, by decide⟩ =
    .split (coordinate 12) (![⟨189758, by decide⟩,⟨189835, by decide⟩,⟨189861, by decide⟩,⟨189875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21514_189876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21514 ⟨189876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21514
    ⟨189876, by decide⟩ (by decide) (![⟨189758, by decide⟩,⟨189835, by decide⟩,⟨189861, by decide⟩,⟨189875, by decide⟩]) unmarked_context_12_21514_189876 node_context_12_21514_189876
  intro a
  fin_cases a
  · exact context_13_86056_189758
  · exact context_13_86057_189835
  · exact context_13_86058_189861
  · exact context_13_86059_189875

theorem selected_cut_06326 : selected 8 ⟨189931, by decide⟩
    (prefixPartial 13 86060) = some ⟨13, 2, 0, 189931, 86060, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_86060_189931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86060 ⟨189931, by decide⟩ :=
  accepted_of_selected 13 86060 ⟨189931, by decide⟩ ⟨13, 2, 0, 189931, 86060, 2925, 16384⟩
    (by decide) selected_cut_06326

theorem selected_cut_06327 : selected 8 ⟨189997, by decide⟩
    (prefixPartial 13 86061) = some ⟨13, 2, 0, 189997, 86061, 4033, 16384⟩ := by
  decide +kernel

theorem context_13_86061_189997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86061 ⟨189997, by decide⟩ :=
  accepted_of_selected 13 86061 ⟨189997, by decide⟩ ⟨13, 2, 0, 189997, 86061, 4033, 16384⟩
    (by decide) selected_cut_06327

theorem selected_cut_06328 : selected 8 ⟨190025, by decide⟩
    (prefixPartial 13 86062) = some ⟨13, 2, 0, 190025, 86062, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_86062_190025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86062 ⟨190025, by decide⟩ :=
  accepted_of_selected 13 86062 ⟨190025, by decide⟩ ⟨13, 2, 0, 190025, 86062, 2033, 16384⟩
    (by decide) selected_cut_06328

theorem selected_cut_06329 : selected 8 ⟨190041, by decide⟩
    (prefixPartial 13 86063) = some ⟨13, 2, 0, 190041, 86063, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_86063_190041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86063 ⟨190041, by decide⟩ :=
  accepted_of_selected 13 86063 ⟨190041, by decide⟩ ⟨13, 2, 0, 190041, 86063, 1037, 16384⟩
    (by decide) selected_cut_06329

theorem unmarked_context_12_21515_190042 : frontier 9 ⟨190042, by decide⟩
    (prefixCache 12 21515) (prefixPartial 12 21515) = false := by
  decide +kernel

theorem node_context_12_21515_190042 : EJMOriginalGlobalDAGData.nodes 9 ⟨190042, by decide⟩ =
    .split (coordinate 12) (![⟨189931, by decide⟩,⟨189997, by decide⟩,⟨190025, by decide⟩,⟨190041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21515_190042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21515 ⟨190042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21515
    ⟨190042, by decide⟩ (by decide) (![⟨189931, by decide⟩,⟨189997, by decide⟩,⟨190025, by decide⟩,⟨190041, by decide⟩]) unmarked_context_12_21515_190042 node_context_12_21515_190042
  intro a
  fin_cases a
  · exact context_13_86060_189931
  · exact context_13_86061_189997
  · exact context_13_86062_190025
  · exact context_13_86063_190041

theorem unmarked_context_11_5378_190043 : frontier 10 ⟨190043, by decide⟩
    (prefixCache 11 5378) (prefixPartial 11 5378) = false := by
  decide +kernel

theorem node_context_11_5378_190043 : EJMOriginalGlobalDAGData.nodes 10 ⟨190043, by decide⟩ =
    .split (coordinate 11) (![⟨189560, by decide⟩,⟨189682, by decide⟩,⟨189876, by decide⟩,⟨190042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5378_190043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5378 ⟨190043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5378
    ⟨190043, by decide⟩ (by decide) (![⟨189560, by decide⟩,⟨189682, by decide⟩,⟨189876, by decide⟩,⟨190042, by decide⟩]) unmarked_context_11_5378_190043 node_context_11_5378_190043
  intro a
  fin_cases a
  · exact context_12_21512_189560
  · exact context_12_21513_189682
  · exact context_12_21514_189876
  · exact context_12_21515_190042

theorem selected_cut_06330 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5379) = some ⟨11, 1, 0, 1736, 5379, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5379_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5379 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5379 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5379, 1, 262144⟩
    (by decide) selected_cut_06330

theorem unmarked_context_10_1344_190044 : frontier 11 ⟨190044, by decide⟩
    (prefixCache 10 1344) (prefixPartial 10 1344) = false := by
  decide +kernel

theorem node_context_10_1344_190044 : EJMOriginalGlobalDAGData.nodes 11 ⟨190044, by decide⟩ =
    .split (coordinate 10) (![⟨189075, by decide⟩,⟨189446, by decide⟩,⟨190043, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1344_190044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1344 ⟨190044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1344
    ⟨190044, by decide⟩ (by decide) (![⟨189075, by decide⟩,⟨189446, by decide⟩,⟨190043, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1344_190044 node_context_10_1344_190044
  intro a
  fin_cases a
  · exact context_11_5376_189075
  · exact context_11_5377_189446
  · exact context_11_5378_190043
  · exact context_11_5379_1736

theorem selected_cut_06331 : selected 9 ⟨190141, by decide⟩
    (prefixPartial 12 21520) = some ⟨12, 2, 0, 190141, 21520, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_21520_190141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21520 ⟨190141, by decide⟩ :=
  accepted_of_selected 12 21520 ⟨190141, by decide⟩ ⟨12, 2, 0, 190141, 21520, 2709, 65536⟩
    (by decide) selected_cut_06331

theorem selected_cut_06332 : selected 9 ⟨190185, by decide⟩
    (prefixPartial 12 21521) = some ⟨12, 2, 0, 190185, 21521, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_21521_190185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21521 ⟨190185, by decide⟩ :=
  accepted_of_selected 12 21521 ⟨190185, by decide⟩ ⟨12, 2, 0, 190185, 21521, 2073, 65536⟩
    (by decide) selected_cut_06332

theorem selected_cut_06333 : selected 8 ⟨190207, by decide⟩
    (prefixPartial 13 86088) = some ⟨13, 2, 0, 190207, 86088, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_86088_190207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86088 ⟨190207, by decide⟩ :=
  accepted_of_selected 13 86088 ⟨190207, by decide⟩ ⟨13, 2, 0, 190207, 86088, 1249, 16384⟩
    (by decide) selected_cut_06333

theorem selected_cut_06334 : selected 8 ⟨190230, by decide⟩
    (prefixPartial 13 86089) = some ⟨13, 2, 0, 190230, 86089, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_86089_190230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86089 ⟨190230, by decide⟩ :=
  accepted_of_selected 13 86089 ⟨190230, by decide⟩ ⟨13, 2, 0, 190230, 86089, 1493, 16384⟩
    (by decide) selected_cut_06334

theorem selected_cut_06335 : selected 8 ⟨190249, by decide⟩
    (prefixPartial 13 86090) = some ⟨13, 2, 0, 190249, 86090, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_86090_190249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86090 ⟨190249, by decide⟩ :=
  accepted_of_selected 13 86090 ⟨190249, by decide⟩ ⟨13, 2, 0, 190249, 86090, 1209, 16384⟩
    (by decide) selected_cut_06335

theorem selected_cut_06336 : selected 8 ⟨190258, by decide⟩
    (prefixPartial 13 86091) = some ⟨13, 2, 0, 190258, 86091, 881, 16384⟩ := by
  decide +kernel

theorem context_13_86091_190258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86091 ⟨190258, by decide⟩ :=
  accepted_of_selected 13 86091 ⟨190258, by decide⟩ ⟨13, 2, 0, 190258, 86091, 881, 16384⟩
    (by decide) selected_cut_06336

theorem unmarked_context_12_21522_190259 : frontier 9 ⟨190259, by decide⟩
    (prefixCache 12 21522) (prefixPartial 12 21522) = false := by
  decide +kernel

theorem node_context_12_21522_190259 : EJMOriginalGlobalDAGData.nodes 9 ⟨190259, by decide⟩ =
    .split (coordinate 12) (![⟨190207, by decide⟩,⟨190230, by decide⟩,⟨190249, by decide⟩,⟨190258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21522_190259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21522 ⟨190259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21522
    ⟨190259, by decide⟩ (by decide) (![⟨190207, by decide⟩,⟨190230, by decide⟩,⟨190249, by decide⟩,⟨190258, by decide⟩]) unmarked_context_12_21522_190259 node_context_12_21522_190259
  intro a
  fin_cases a
  · exact context_13_86088_190207
  · exact context_13_86089_190230
  · exact context_13_86090_190249
  · exact context_13_86091_190258

theorem selected_cut_06337 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21523) = some ⟨12, 1, 0, 893, 21523, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21523_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21523 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21523 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21523, 1, 65536⟩
    (by decide) selected_cut_06337

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
