/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover387
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_74885_995076 : frontier 10 ⟨995076, by decide⟩
    (prefixCache 11 74885) (prefixPartial 11 74885) = false := by
  decide +kernel

theorem node_context_11_74885_995076 : EJMOriginalGlobalDAGData.nodes 10 ⟨995076, by decide⟩ =
    .split (coordinate 11) (![⟨994808, by decide⟩,⟨994956, by decide⟩,⟨995010, by decide⟩,⟨995075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74885_995076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74885 ⟨995076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74885
    ⟨995076, by decide⟩ (by decide) (![⟨994808, by decide⟩,⟨994956, by decide⟩,⟨995010, by decide⟩,⟨995075, by decide⟩]) unmarked_context_11_74885_995076 node_context_11_74885_995076
  intro a
  fin_cases a
  · exact context_12_299540_994808
  · exact context_12_299541_994956
  · exact context_12_299542_995010
  · exact context_12_299543_995075

theorem selected_cut_37251 : selected 8 ⟨995098, by decide⟩
    (prefixPartial 13 1198176) = some ⟨13, 2, 0, 995098, 1198176, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_1198176_995098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198176 ⟨995098, by decide⟩ :=
  accepted_of_selected 13 1198176 ⟨995098, by decide⟩ ⟨13, 2, 0, 995098, 1198176, 1497, 16384⟩
    (by decide) selected_cut_37251

theorem selected_cut_37252 : selected 8 ⟨995116, by decide⟩
    (prefixPartial 13 1198177) = some ⟨13, 2, 0, 995116, 1198177, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_1198177_995116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198177 ⟨995116, by decide⟩ :=
  accepted_of_selected 13 1198177 ⟨995116, by decide⟩ ⟨13, 2, 0, 995116, 1198177, 1149, 16384⟩
    (by decide) selected_cut_37252

theorem selected_cut_37253 : selected 8 ⟨995134, by decide⟩
    (prefixPartial 13 1198178) = some ⟨13, 2, 0, 995134, 1198178, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_1198178_995134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198178 ⟨995134, by decide⟩ :=
  accepted_of_selected 13 1198178 ⟨995134, by decide⟩ ⟨13, 2, 0, 995134, 1198178, 1097, 16384⟩
    (by decide) selected_cut_37253

theorem selected_cut_37254 : selected 8 ⟨995139, by decide⟩
    (prefixPartial 13 1198179) = some ⟨13, 2, 0, 995139, 1198179, 573, 16384⟩ := by
  decide +kernel

theorem context_13_1198179_995139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198179 ⟨995139, by decide⟩ :=
  accepted_of_selected 13 1198179 ⟨995139, by decide⟩ ⟨13, 2, 0, 995139, 1198179, 573, 16384⟩
    (by decide) selected_cut_37254

theorem unmarked_context_12_299544_995140 : frontier 9 ⟨995140, by decide⟩
    (prefixCache 12 299544) (prefixPartial 12 299544) = false := by
  decide +kernel

theorem node_context_12_299544_995140 : EJMOriginalGlobalDAGData.nodes 9 ⟨995140, by decide⟩ =
    .split (coordinate 12) (![⟨995098, by decide⟩,⟨995116, by decide⟩,⟨995134, by decide⟩,⟨995139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299544_995140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299544 ⟨995140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299544
    ⟨995140, by decide⟩ (by decide) (![⟨995098, by decide⟩,⟨995116, by decide⟩,⟨995134, by decide⟩,⟨995139, by decide⟩]) unmarked_context_12_299544_995140 node_context_12_299544_995140
  intro a
  fin_cases a
  · exact context_13_1198176_995098
  · exact context_13_1198177_995116
  · exact context_13_1198178_995134
  · exact context_13_1198179_995139

theorem selected_cut_37255 : selected 8 ⟨995158, by decide⟩
    (prefixPartial 13 1198180) = some ⟨13, 2, 0, 995158, 1198180, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_1198180_995158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198180 ⟨995158, by decide⟩ :=
  accepted_of_selected 13 1198180 ⟨995158, by decide⟩ ⟨13, 2, 0, 995158, 1198180, 1249, 16384⟩
    (by decide) selected_cut_37255

theorem selected_cut_37256 : selected 8 ⟨995177, by decide⟩
    (prefixPartial 13 1198181) = some ⟨13, 2, 0, 995177, 1198181, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_1198181_995177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198181 ⟨995177, by decide⟩ :=
  accepted_of_selected 13 1198181 ⟨995177, by decide⟩ ⟨13, 2, 0, 995177, 1198181, 1281, 16384⟩
    (by decide) selected_cut_37256

theorem selected_cut_37257 : selected 8 ⟨995199, by decide⟩
    (prefixPartial 13 1198182) = some ⟨13, 2, 0, 995199, 1198182, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_1198182_995199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198182 ⟨995199, by decide⟩ :=
  accepted_of_selected 13 1198182 ⟨995199, by decide⟩ ⟨13, 2, 0, 995199, 1198182, 1097, 16384⟩
    (by decide) selected_cut_37257

theorem selected_cut_37258 : selected 8 ⟨995206, by decide⟩
    (prefixPartial 13 1198183) = some ⟨13, 2, 0, 995206, 1198183, 613, 16384⟩ := by
  decide +kernel

theorem context_13_1198183_995206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198183 ⟨995206, by decide⟩ :=
  accepted_of_selected 13 1198183 ⟨995206, by decide⟩ ⟨13, 2, 0, 995206, 1198183, 613, 16384⟩
    (by decide) selected_cut_37258

theorem unmarked_context_12_299545_995207 : frontier 9 ⟨995207, by decide⟩
    (prefixCache 12 299545) (prefixPartial 12 299545) = false := by
  decide +kernel

theorem node_context_12_299545_995207 : EJMOriginalGlobalDAGData.nodes 9 ⟨995207, by decide⟩ =
    .split (coordinate 12) (![⟨995158, by decide⟩,⟨995177, by decide⟩,⟨995199, by decide⟩,⟨995206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299545_995207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299545 ⟨995207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299545
    ⟨995207, by decide⟩ (by decide) (![⟨995158, by decide⟩,⟨995177, by decide⟩,⟨995199, by decide⟩,⟨995206, by decide⟩]) unmarked_context_12_299545_995207 node_context_12_299545_995207
  intro a
  fin_cases a
  · exact context_13_1198180_995158
  · exact context_13_1198181_995177
  · exact context_13_1198182_995199
  · exact context_13_1198183_995206

theorem selected_cut_37259 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 299546) = some ⟨12, 1, 0, 893903, 299546, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299546_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299546 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 299546 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 299546, 1, 65536⟩
    (by decide) selected_cut_37259

theorem selected_cut_37260 : selected 9 ⟨995267, by decide⟩
    (prefixPartial 12 299547) = some ⟨12, 2, 0, 995267, 299547, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_299547_995267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299547 ⟨995267, by decide⟩ :=
  accepted_of_selected 12 299547 ⟨995267, by decide⟩ ⟨12, 2, 0, 995267, 299547, 4061, 65536⟩
    (by decide) selected_cut_37260

theorem unmarked_context_11_74886_995268 : frontier 10 ⟨995268, by decide⟩
    (prefixCache 11 74886) (prefixPartial 11 74886) = false := by
  decide +kernel

theorem node_context_11_74886_995268 : EJMOriginalGlobalDAGData.nodes 10 ⟨995268, by decide⟩ =
    .split (coordinate 11) (![⟨995140, by decide⟩,⟨995207, by decide⟩,⟨893903, by decide⟩,⟨995267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74886_995268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74886 ⟨995268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74886
    ⟨995268, by decide⟩ (by decide) (![⟨995140, by decide⟩,⟨995207, by decide⟩,⟨893903, by decide⟩,⟨995267, by decide⟩]) unmarked_context_11_74886_995268 node_context_11_74886_995268
  intro a
  fin_cases a
  · exact context_12_299544_995140
  · exact context_12_299545_995207
  · exact context_12_299546_893903
  · exact context_12_299547_995267

theorem selected_cut_37261 : selected 8 ⟨995303, by decide⟩
    (prefixPartial 13 1198192) = some ⟨13, 2, 0, 995303, 1198192, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_1198192_995303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198192 ⟨995303, by decide⟩ :=
  accepted_of_selected 13 1198192 ⟨995303, by decide⟩ ⟨13, 2, 0, 995303, 1198192, 1969, 16384⟩
    (by decide) selected_cut_37261

theorem selected_cut_37262 : selected 8 ⟨995323, by decide⟩
    (prefixPartial 13 1198193) = some ⟨13, 2, 0, 995323, 1198193, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_1198193_995323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198193 ⟨995323, by decide⟩ :=
  accepted_of_selected 13 1198193 ⟨995323, by decide⟩ ⟨13, 2, 0, 995323, 1198193, 1313, 16384⟩
    (by decide) selected_cut_37262

theorem selected_cut_37263 : selected 8 ⟨995346, by decide⟩
    (prefixPartial 13 1198194) = some ⟨13, 2, 0, 995346, 1198194, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_1198194_995346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198194 ⟨995346, by decide⟩ :=
  accepted_of_selected 13 1198194 ⟨995346, by decide⟩ ⟨13, 2, 0, 995346, 1198194, 1205, 16384⟩
    (by decide) selected_cut_37263

theorem selected_cut_37264 : selected 8 ⟨995353, by decide⟩
    (prefixPartial 13 1198195) = some ⟨13, 2, 0, 995353, 1198195, 737, 16384⟩ := by
  decide +kernel

theorem context_13_1198195_995353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198195 ⟨995353, by decide⟩ :=
  accepted_of_selected 13 1198195 ⟨995353, by decide⟩ ⟨13, 2, 0, 995353, 1198195, 737, 16384⟩
    (by decide) selected_cut_37264

theorem unmarked_context_12_299548_995354 : frontier 9 ⟨995354, by decide⟩
    (prefixCache 12 299548) (prefixPartial 12 299548) = false := by
  decide +kernel

theorem node_context_12_299548_995354 : EJMOriginalGlobalDAGData.nodes 9 ⟨995354, by decide⟩ =
    .split (coordinate 12) (![⟨995303, by decide⟩,⟨995323, by decide⟩,⟨995346, by decide⟩,⟨995353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299548_995354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299548 ⟨995354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299548
    ⟨995354, by decide⟩ (by decide) (![⟨995303, by decide⟩,⟨995323, by decide⟩,⟨995346, by decide⟩,⟨995353, by decide⟩]) unmarked_context_12_299548_995354 node_context_12_299548_995354
  intro a
  fin_cases a
  · exact context_13_1198192_995303
  · exact context_13_1198193_995323
  · exact context_13_1198194_995346
  · exact context_13_1198195_995353

theorem selected_cut_37265 : selected 8 ⟨995379, by decide⟩
    (prefixPartial 13 1198196) = some ⟨13, 2, 0, 995379, 1198196, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_1198196_995379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198196 ⟨995379, by decide⟩ :=
  accepted_of_selected 13 1198196 ⟨995379, by decide⟩ ⟨13, 2, 0, 995379, 1198196, 1461, 16384⟩
    (by decide) selected_cut_37265

theorem selected_cut_37266 : selected 8 ⟨995396, by decide⟩
    (prefixPartial 13 1198197) = some ⟨13, 2, 0, 995396, 1198197, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_1198197_995396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198197 ⟨995396, by decide⟩ :=
  accepted_of_selected 13 1198197 ⟨995396, by decide⟩ ⟨13, 2, 0, 995396, 1198197, 1309, 16384⟩
    (by decide) selected_cut_37266

theorem selected_cut_37267 : selected 8 ⟨995415, by decide⟩
    (prefixPartial 13 1198198) = some ⟨13, 2, 0, 995415, 1198198, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_1198198_995415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198198 ⟨995415, by decide⟩ :=
  accepted_of_selected 13 1198198 ⟨995415, by decide⟩ ⟨13, 2, 0, 995415, 1198198, 1229, 16384⟩
    (by decide) selected_cut_37267

theorem selected_cut_37268 : selected 8 ⟨995422, by decide⟩
    (prefixPartial 13 1198199) = some ⟨13, 2, 0, 995422, 1198199, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1198199_995422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198199 ⟨995422, by decide⟩ :=
  accepted_of_selected 13 1198199 ⟨995422, by decide⟩ ⟨13, 2, 0, 995422, 1198199, 725, 16384⟩
    (by decide) selected_cut_37268

theorem unmarked_context_12_299549_995423 : frontier 9 ⟨995423, by decide⟩
    (prefixCache 12 299549) (prefixPartial 12 299549) = false := by
  decide +kernel

theorem node_context_12_299549_995423 : EJMOriginalGlobalDAGData.nodes 9 ⟨995423, by decide⟩ =
    .split (coordinate 12) (![⟨995379, by decide⟩,⟨995396, by decide⟩,⟨995415, by decide⟩,⟨995422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299549_995423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299549 ⟨995423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299549
    ⟨995423, by decide⟩ (by decide) (![⟨995379, by decide⟩,⟨995396, by decide⟩,⟨995415, by decide⟩,⟨995422, by decide⟩]) unmarked_context_12_299549_995423 node_context_12_299549_995423
  intro a
  fin_cases a
  · exact context_13_1198196_995379
  · exact context_13_1198197_995396
  · exact context_13_1198198_995415
  · exact context_13_1198199_995422

theorem selected_cut_37269 : selected 8 ⟨995448, by decide⟩
    (prefixPartial 13 1198200) = some ⟨13, 2, 0, 995448, 1198200, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_1198200_995448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198200 ⟨995448, by decide⟩ :=
  accepted_of_selected 13 1198200 ⟨995448, by decide⟩ ⟨13, 2, 0, 995448, 1198200, 1405, 16384⟩
    (by decide) selected_cut_37269

theorem selected_cut_37270 : selected 8 ⟨995466, by decide⟩
    (prefixPartial 13 1198201) = some ⟨13, 2, 0, 995466, 1198201, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_1198201_995466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198201 ⟨995466, by decide⟩ :=
  accepted_of_selected 13 1198201 ⟨995466, by decide⟩ ⟨13, 2, 0, 995466, 1198201, 1309, 16384⟩
    (by decide) selected_cut_37270

theorem selected_cut_37271 : selected 8 ⟨995487, by decide⟩
    (prefixPartial 13 1198202) = some ⟨13, 2, 0, 995487, 1198202, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_1198202_995487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198202 ⟨995487, by decide⟩ :=
  accepted_of_selected 13 1198202 ⟨995487, by decide⟩ ⟨13, 2, 0, 995487, 1198202, 1197, 16384⟩
    (by decide) selected_cut_37271

theorem selected_cut_37272 : selected 8 ⟨995494, by decide⟩
    (prefixPartial 13 1198203) = some ⟨13, 2, 0, 995494, 1198203, 733, 16384⟩ := by
  decide +kernel

theorem context_13_1198203_995494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198203 ⟨995494, by decide⟩ :=
  accepted_of_selected 13 1198203 ⟨995494, by decide⟩ ⟨13, 2, 0, 995494, 1198203, 733, 16384⟩
    (by decide) selected_cut_37272

theorem unmarked_context_12_299550_995495 : frontier 9 ⟨995495, by decide⟩
    (prefixCache 12 299550) (prefixPartial 12 299550) = false := by
  decide +kernel

theorem node_context_12_299550_995495 : EJMOriginalGlobalDAGData.nodes 9 ⟨995495, by decide⟩ =
    .split (coordinate 12) (![⟨995448, by decide⟩,⟨995466, by decide⟩,⟨995487, by decide⟩,⟨995494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299550_995495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299550 ⟨995495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299550
    ⟨995495, by decide⟩ (by decide) (![⟨995448, by decide⟩,⟨995466, by decide⟩,⟨995487, by decide⟩,⟨995494, by decide⟩]) unmarked_context_12_299550_995495 node_context_12_299550_995495
  intro a
  fin_cases a
  · exact context_13_1198200_995448
  · exact context_13_1198201_995466
  · exact context_13_1198202_995487
  · exact context_13_1198203_995494

theorem selected_cut_37273 : selected 8 ⟨995517, by decide⟩
    (prefixPartial 13 1198204) = some ⟨13, 2, 0, 995517, 1198204, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_1198204_995517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198204 ⟨995517, by decide⟩ :=
  accepted_of_selected 13 1198204 ⟨995517, by decide⟩ ⟨13, 2, 0, 995517, 1198204, 1413, 16384⟩
    (by decide) selected_cut_37273

theorem selected_cut_37274 : selected 8 ⟨995534, by decide⟩
    (prefixPartial 13 1198205) = some ⟨13, 2, 0, 995534, 1198205, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_1198205_995534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198205 ⟨995534, by decide⟩ :=
  accepted_of_selected 13 1198205 ⟨995534, by decide⟩ ⟨13, 2, 0, 995534, 1198205, 1217, 16384⟩
    (by decide) selected_cut_37274

theorem selected_cut_37275 : selected 8 ⟨995554, by decide⟩
    (prefixPartial 13 1198206) = some ⟨13, 2, 0, 995554, 1198206, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_1198206_995554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198206 ⟨995554, by decide⟩ :=
  accepted_of_selected 13 1198206 ⟨995554, by decide⟩ ⟨13, 2, 0, 995554, 1198206, 1069, 16384⟩
    (by decide) selected_cut_37275

theorem selected_cut_37276 : selected 8 ⟨995561, by decide⟩
    (prefixPartial 13 1198207) = some ⟨13, 2, 0, 995561, 1198207, 653, 16384⟩ := by
  decide +kernel

theorem context_13_1198207_995561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198207 ⟨995561, by decide⟩ :=
  accepted_of_selected 13 1198207 ⟨995561, by decide⟩ ⟨13, 2, 0, 995561, 1198207, 653, 16384⟩
    (by decide) selected_cut_37276

theorem unmarked_context_12_299551_995562 : frontier 9 ⟨995562, by decide⟩
    (prefixCache 12 299551) (prefixPartial 12 299551) = false := by
  decide +kernel

theorem node_context_12_299551_995562 : EJMOriginalGlobalDAGData.nodes 9 ⟨995562, by decide⟩ =
    .split (coordinate 12) (![⟨995517, by decide⟩,⟨995534, by decide⟩,⟨995554, by decide⟩,⟨995561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299551_995562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299551 ⟨995562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299551
    ⟨995562, by decide⟩ (by decide) (![⟨995517, by decide⟩,⟨995534, by decide⟩,⟨995554, by decide⟩,⟨995561, by decide⟩]) unmarked_context_12_299551_995562 node_context_12_299551_995562
  intro a
  fin_cases a
  · exact context_13_1198204_995517
  · exact context_13_1198205_995534
  · exact context_13_1198206_995554
  · exact context_13_1198207_995561

theorem unmarked_context_11_74887_995563 : frontier 10 ⟨995563, by decide⟩
    (prefixCache 11 74887) (prefixPartial 11 74887) = false := by
  decide +kernel

theorem node_context_11_74887_995563 : EJMOriginalGlobalDAGData.nodes 10 ⟨995563, by decide⟩ =
    .split (coordinate 11) (![⟨995354, by decide⟩,⟨995423, by decide⟩,⟨995495, by decide⟩,⟨995562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74887_995563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74887 ⟨995563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74887
    ⟨995563, by decide⟩ (by decide) (![⟨995354, by decide⟩,⟨995423, by decide⟩,⟨995495, by decide⟩,⟨995562, by decide⟩]) unmarked_context_11_74887_995563 node_context_11_74887_995563
  intro a
  fin_cases a
  · exact context_12_299548_995354
  · exact context_12_299549_995423
  · exact context_12_299550_995495
  · exact context_12_299551_995562

theorem unmarked_context_10_18721_995564 : frontier 11 ⟨995564, by decide⟩
    (prefixCache 10 18721) (prefixPartial 10 18721) = false := by
  decide +kernel

theorem node_context_10_18721_995564 : EJMOriginalGlobalDAGData.nodes 11 ⟨995564, by decide⟩ =
    .split (coordinate 10) (![⟨994728, by decide⟩,⟨995076, by decide⟩,⟨995268, by decide⟩,⟨995563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18721_995564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18721 ⟨995564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18721
    ⟨995564, by decide⟩ (by decide) (![⟨994728, by decide⟩,⟨995076, by decide⟩,⟨995268, by decide⟩,⟨995563, by decide⟩]) unmarked_context_10_18721_995564 node_context_10_18721_995564
  intro a
  fin_cases a
  · exact context_11_74884_994728
  · exact context_11_74885_995076
  · exact context_11_74886_995268
  · exact context_11_74887_995563

theorem selected_cut_37277 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 299552) = some ⟨12, 1, 0, 994572, 299552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299552_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299552 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 299552 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 299552, 1, 65536⟩
    (by decide) selected_cut_37277

theorem selected_cut_37278 : selected 9 ⟨995619, by decide⟩
    (prefixPartial 12 299553) = some ⟨12, 2, 0, 995619, 299553, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_299553_995619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299553 ⟨995619, by decide⟩ :=
  accepted_of_selected 12 299553 ⟨995619, by decide⟩ ⟨12, 2, 0, 995619, 299553, 3317, 65536⟩
    (by decide) selected_cut_37278

theorem selected_cut_37279 : selected 9 ⟨995667, by decide⟩
    (prefixPartial 12 299554) = some ⟨12, 2, 0, 995667, 299554, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_299554_995667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299554 ⟨995667, by decide⟩ :=
  accepted_of_selected 12 299554 ⟨995667, by decide⟩ ⟨12, 2, 0, 995667, 299554, 2929, 65536⟩
    (by decide) selected_cut_37279

theorem selected_cut_37280 : selected 9 ⟨995714, by decide⟩
    (prefixPartial 12 299555) = some ⟨12, 2, 0, 995714, 299555, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_299555_995714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299555 ⟨995714, by decide⟩ :=
  accepted_of_selected 12 299555 ⟨995714, by decide⟩ ⟨12, 2, 0, 995714, 299555, 3233, 65536⟩
    (by decide) selected_cut_37280

theorem unmarked_context_11_74888_995715 : frontier 10 ⟨995715, by decide⟩
    (prefixCache 11 74888) (prefixPartial 11 74888) = false := by
  decide +kernel

theorem node_context_11_74888_995715 : EJMOriginalGlobalDAGData.nodes 10 ⟨995715, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨995619, by decide⟩,⟨995667, by decide⟩,⟨995714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74888_995715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74888 ⟨995715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74888
    ⟨995715, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨995619, by decide⟩,⟨995667, by decide⟩,⟨995714, by decide⟩]) unmarked_context_11_74888_995715 node_context_11_74888_995715
  intro a
  fin_cases a
  · exact context_12_299552_994572
  · exact context_12_299553_995619
  · exact context_12_299554_995667
  · exact context_12_299555_995714

theorem selected_cut_37281 : selected 9 ⟨995777, by decide⟩
    (prefixPartial 12 299556) = some ⟨12, 2, 0, 995777, 299556, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_299556_995777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299556 ⟨995777, by decide⟩ :=
  accepted_of_selected 12 299556 ⟨995777, by decide⟩ ⟨12, 2, 0, 995777, 299556, 3977, 65536⟩
    (by decide) selected_cut_37281

theorem selected_cut_37282 : selected 9 ⟨995837, by decide⟩
    (prefixPartial 12 299557) = some ⟨12, 2, 0, 995837, 299557, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_299557_995837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299557 ⟨995837, by decide⟩ :=
  accepted_of_selected 12 299557 ⟨995837, by decide⟩ ⟨12, 2, 0, 995837, 299557, 3869, 65536⟩
    (by decide) selected_cut_37282

theorem selected_cut_37283 : selected 9 ⟨995881, by decide⟩
    (prefixPartial 12 299558) = some ⟨12, 2, 0, 995881, 299558, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_299558_995881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299558 ⟨995881, by decide⟩ :=
  accepted_of_selected 12 299558 ⟨995881, by decide⟩ ⟨12, 2, 0, 995881, 299558, 3313, 65536⟩
    (by decide) selected_cut_37283

theorem selected_cut_37284 : selected 9 ⟨995930, by decide⟩
    (prefixPartial 12 299559) = some ⟨12, 2, 0, 995930, 299559, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_299559_995930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299559 ⟨995930, by decide⟩ :=
  accepted_of_selected 12 299559 ⟨995930, by decide⟩ ⟨12, 2, 0, 995930, 299559, 3633, 65536⟩
    (by decide) selected_cut_37284

theorem unmarked_context_11_74889_995931 : frontier 10 ⟨995931, by decide⟩
    (prefixCache 11 74889) (prefixPartial 11 74889) = false := by
  decide +kernel

theorem node_context_11_74889_995931 : EJMOriginalGlobalDAGData.nodes 10 ⟨995931, by decide⟩ =
    .split (coordinate 11) (![⟨995777, by decide⟩,⟨995837, by decide⟩,⟨995881, by decide⟩,⟨995930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74889_995931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74889 ⟨995931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74889
    ⟨995931, by decide⟩ (by decide) (![⟨995777, by decide⟩,⟨995837, by decide⟩,⟨995881, by decide⟩,⟨995930, by decide⟩]) unmarked_context_11_74889_995931 node_context_11_74889_995931
  intro a
  fin_cases a
  · exact context_12_299556_995777
  · exact context_12_299557_995837
  · exact context_12_299558_995881
  · exact context_12_299559_995930

theorem selected_cut_37285 : selected 9 ⟨995982, by decide⟩
    (prefixPartial 12 299560) = some ⟨12, 2, 0, 995982, 299560, 3709, 65536⟩ := by
  decide +kernel

theorem context_12_299560_995982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299560 ⟨995982, by decide⟩ :=
  accepted_of_selected 12 299560 ⟨995982, by decide⟩ ⟨12, 2, 0, 995982, 299560, 3709, 65536⟩
    (by decide) selected_cut_37285

theorem selected_cut_37286 : selected 9 ⟨996042, by decide⟩
    (prefixPartial 12 299561) = some ⟨12, 2, 0, 996042, 299561, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_299561_996042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299561 ⟨996042, by decide⟩ :=
  accepted_of_selected 12 299561 ⟨996042, by decide⟩ ⟨12, 2, 0, 996042, 299561, 3841, 65536⟩
    (by decide) selected_cut_37286

theorem selected_cut_37287 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 299562) = some ⟨12, 1, 0, 242157, 299562, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299562_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299562 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 299562 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 299562, 1, 65536⟩
    (by decide) selected_cut_37287

theorem selected_cut_37288 : selected 9 ⟨996095, by decide⟩
    (prefixPartial 12 299563) = some ⟨12, 2, 0, 996095, 299563, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_299563_996095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299563 ⟨996095, by decide⟩ :=
  accepted_of_selected 12 299563 ⟨996095, by decide⟩ ⟨12, 2, 0, 996095, 299563, 3521, 65536⟩
    (by decide) selected_cut_37288

theorem unmarked_context_11_74890_996096 : frontier 10 ⟨996096, by decide⟩
    (prefixCache 11 74890) (prefixPartial 11 74890) = false := by
  decide +kernel

theorem node_context_11_74890_996096 : EJMOriginalGlobalDAGData.nodes 10 ⟨996096, by decide⟩ =
    .split (coordinate 11) (![⟨995982, by decide⟩,⟨996042, by decide⟩,⟨242157, by decide⟩,⟨996095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74890_996096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74890 ⟨996096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74890
    ⟨996096, by decide⟩ (by decide) (![⟨995982, by decide⟩,⟨996042, by decide⟩,⟨242157, by decide⟩,⟨996095, by decide⟩]) unmarked_context_11_74890_996096 node_context_11_74890_996096
  intro a
  fin_cases a
  · exact context_12_299560_995982
  · exact context_12_299561_996042
  · exact context_12_299562_242157
  · exact context_12_299563_996095

theorem selected_cut_37289 : selected 9 ⟨996155, by decide⟩
    (prefixPartial 12 299564) = some ⟨12, 2, 0, 996155, 299564, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_299564_996155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299564 ⟨996155, by decide⟩ :=
  accepted_of_selected 12 299564 ⟨996155, by decide⟩ ⟨12, 2, 0, 996155, 299564, 3937, 65536⟩
    (by decide) selected_cut_37289

theorem selected_cut_37290 : selected 9 ⟨996213, by decide⟩
    (prefixPartial 12 299565) = some ⟨12, 2, 0, 996213, 299565, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_299565_996213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299565 ⟨996213, by decide⟩ :=
  accepted_of_selected 12 299565 ⟨996213, by decide⟩ ⟨12, 2, 0, 996213, 299565, 3893, 65536⟩
    (by decide) selected_cut_37290

theorem selected_cut_37291 : selected 9 ⟨996257, by decide⟩
    (prefixPartial 12 299566) = some ⟨12, 2, 0, 996257, 299566, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_299566_996257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299566 ⟨996257, by decide⟩ :=
  accepted_of_selected 12 299566 ⟨996257, by decide⟩ ⟨12, 2, 0, 996257, 299566, 3593, 65536⟩
    (by decide) selected_cut_37291

theorem selected_cut_37292 : selected 9 ⟨996305, by decide⟩
    (prefixPartial 12 299567) = some ⟨12, 2, 0, 996305, 299567, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_299567_996305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299567 ⟨996305, by decide⟩ :=
  accepted_of_selected 12 299567 ⟨996305, by decide⟩ ⟨12, 2, 0, 996305, 299567, 3521, 65536⟩
    (by decide) selected_cut_37292

theorem unmarked_context_11_74891_996306 : frontier 10 ⟨996306, by decide⟩
    (prefixCache 11 74891) (prefixPartial 11 74891) = false := by
  decide +kernel

theorem node_context_11_74891_996306 : EJMOriginalGlobalDAGData.nodes 10 ⟨996306, by decide⟩ =
    .split (coordinate 11) (![⟨996155, by decide⟩,⟨996213, by decide⟩,⟨996257, by decide⟩,⟨996305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74891_996306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74891 ⟨996306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74891
    ⟨996306, by decide⟩ (by decide) (![⟨996155, by decide⟩,⟨996213, by decide⟩,⟨996257, by decide⟩,⟨996305, by decide⟩]) unmarked_context_11_74891_996306 node_context_11_74891_996306
  intro a
  fin_cases a
  · exact context_12_299564_996155
  · exact context_12_299565_996213
  · exact context_12_299566_996257
  · exact context_12_299567_996305

theorem unmarked_context_10_18722_996307 : frontier 11 ⟨996307, by decide⟩
    (prefixCache 10 18722) (prefixPartial 10 18722) = false := by
  decide +kernel

theorem node_context_10_18722_996307 : EJMOriginalGlobalDAGData.nodes 11 ⟨996307, by decide⟩ =
    .split (coordinate 10) (![⟨995715, by decide⟩,⟨995931, by decide⟩,⟨996096, by decide⟩,⟨996306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18722_996307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18722 ⟨996307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18722
    ⟨996307, by decide⟩ (by decide) (![⟨995715, by decide⟩,⟨995931, by decide⟩,⟨996096, by decide⟩,⟨996306, by decide⟩]) unmarked_context_10_18722_996307 node_context_10_18722_996307
  intro a
  fin_cases a
  · exact context_11_74888_995715
  · exact context_11_74889_995931
  · exact context_11_74890_996096
  · exact context_11_74891_996306

theorem selected_cut_37293 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 299568) = some ⟨12, 1, 0, 994572, 299568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299568_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299568 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 299568 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 299568, 1, 65536⟩
    (by decide) selected_cut_37293

theorem selected_cut_37294 : selected 9 ⟨996353, by decide⟩
    (prefixPartial 12 299569) = some ⟨12, 2, 0, 996353, 299569, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_299569_996353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299569 ⟨996353, by decide⟩ :=
  accepted_of_selected 12 299569 ⟨996353, by decide⟩ ⟨12, 2, 0, 996353, 299569, 3169, 65536⟩
    (by decide) selected_cut_37294

theorem selected_cut_37295 : selected 9 ⟨996392, by decide⟩
    (prefixPartial 12 299570) = some ⟨12, 2, 0, 996392, 299570, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_299570_996392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299570 ⟨996392, by decide⟩ :=
  accepted_of_selected 12 299570 ⟨996392, by decide⟩ ⟨12, 2, 0, 996392, 299570, 2845, 65536⟩
    (by decide) selected_cut_37295

theorem selected_cut_37296 : selected 9 ⟨996433, by decide⟩
    (prefixPartial 12 299571) = some ⟨12, 2, 0, 996433, 299571, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_299571_996433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299571 ⟨996433, by decide⟩ :=
  accepted_of_selected 12 299571 ⟨996433, by decide⟩ ⟨12, 2, 0, 996433, 299571, 3137, 65536⟩
    (by decide) selected_cut_37296

theorem unmarked_context_11_74892_996434 : frontier 10 ⟨996434, by decide⟩
    (prefixCache 11 74892) (prefixPartial 11 74892) = false := by
  decide +kernel

theorem node_context_11_74892_996434 : EJMOriginalGlobalDAGData.nodes 10 ⟨996434, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨996353, by decide⟩,⟨996392, by decide⟩,⟨996433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74892_996434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74892 ⟨996434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74892
    ⟨996434, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨996353, by decide⟩,⟨996392, by decide⟩,⟨996433, by decide⟩]) unmarked_context_11_74892_996434 node_context_11_74892_996434
  intro a
  fin_cases a
  · exact context_12_299568_994572
  · exact context_12_299569_996353
  · exact context_12_299570_996392
  · exact context_12_299571_996433

theorem selected_cut_37297 : selected 9 ⟨996510, by decide⟩
    (prefixPartial 12 299572) = some ⟨12, 2, 0, 996510, 299572, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_299572_996510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299572 ⟨996510, by decide⟩ :=
  accepted_of_selected 12 299572 ⟨996510, by decide⟩ ⟨12, 2, 0, 996510, 299572, 4005, 65536⟩
    (by decide) selected_cut_37297

theorem selected_cut_37298 : selected 9 ⟨996576, by decide⟩
    (prefixPartial 12 299573) = some ⟨12, 2, 0, 996576, 299573, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_299573_996576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299573 ⟨996576, by decide⟩ :=
  accepted_of_selected 12 299573 ⟨996576, by decide⟩ ⟨12, 2, 0, 996576, 299573, 3805, 65536⟩
    (by decide) selected_cut_37298

theorem selected_cut_37299 : selected 9 ⟨996624, by decide⟩
    (prefixPartial 12 299574) = some ⟨12, 2, 0, 996624, 299574, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_299574_996624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299574 ⟨996624, by decide⟩ :=
  accepted_of_selected 12 299574 ⟨996624, by decide⟩ ⟨12, 2, 0, 996624, 299574, 3385, 65536⟩
    (by decide) selected_cut_37299

theorem selected_cut_37300 : selected 9 ⟨996678, by decide⟩
    (prefixPartial 12 299575) = some ⟨12, 2, 0, 996678, 299575, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_299575_996678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299575 ⟨996678, by decide⟩ :=
  accepted_of_selected 12 299575 ⟨996678, by decide⟩ ⟨12, 2, 0, 996678, 299575, 3445, 65536⟩
    (by decide) selected_cut_37300

theorem unmarked_context_11_74893_996679 : frontier 10 ⟨996679, by decide⟩
    (prefixCache 11 74893) (prefixPartial 11 74893) = false := by
  decide +kernel

theorem node_context_11_74893_996679 : EJMOriginalGlobalDAGData.nodes 10 ⟨996679, by decide⟩ =
    .split (coordinate 11) (![⟨996510, by decide⟩,⟨996576, by decide⟩,⟨996624, by decide⟩,⟨996678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74893_996679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74893 ⟨996679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74893
    ⟨996679, by decide⟩ (by decide) (![⟨996510, by decide⟩,⟨996576, by decide⟩,⟨996624, by decide⟩,⟨996678, by decide⟩]) unmarked_context_11_74893_996679 node_context_11_74893_996679
  intro a
  fin_cases a
  · exact context_12_299572_996510
  · exact context_12_299573_996576
  · exact context_12_299574_996624
  · exact context_12_299575_996678

theorem selected_cut_37301 : selected 9 ⟨996737, by decide⟩
    (prefixPartial 12 299576) = some ⟨12, 2, 0, 996737, 299576, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_299576_996737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299576 ⟨996737, by decide⟩ :=
  accepted_of_selected 12 299576 ⟨996737, by decide⟩ ⟨12, 2, 0, 996737, 299576, 3569, 65536⟩
    (by decide) selected_cut_37301

theorem selected_cut_37302 : selected 9 ⟨996792, by decide⟩
    (prefixPartial 12 299577) = some ⟨12, 2, 0, 996792, 299577, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_299577_996792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299577 ⟨996792, by decide⟩ :=
  accepted_of_selected 12 299577 ⟨996792, by decide⟩ ⟨12, 2, 0, 996792, 299577, 3597, 65536⟩
    (by decide) selected_cut_37302

theorem selected_cut_37303 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 299578) = some ⟨12, 1, 0, 893903, 299578, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299578_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299578 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 299578 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 299578, 1, 65536⟩
    (by decide) selected_cut_37303

theorem selected_cut_37304 : selected 9 ⟨996846, by decide⟩
    (prefixPartial 12 299579) = some ⟨12, 2, 0, 996846, 299579, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_299579_996846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299579 ⟨996846, by decide⟩ :=
  accepted_of_selected 12 299579 ⟨996846, by decide⟩ ⟨12, 2, 0, 996846, 299579, 3365, 65536⟩
    (by decide) selected_cut_37304

theorem unmarked_context_11_74894_996847 : frontier 10 ⟨996847, by decide⟩
    (prefixCache 11 74894) (prefixPartial 11 74894) = false := by
  decide +kernel

theorem node_context_11_74894_996847 : EJMOriginalGlobalDAGData.nodes 10 ⟨996847, by decide⟩ =
    .split (coordinate 11) (![⟨996737, by decide⟩,⟨996792, by decide⟩,⟨893903, by decide⟩,⟨996846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74894_996847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74894 ⟨996847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74894
    ⟨996847, by decide⟩ (by decide) (![⟨996737, by decide⟩,⟨996792, by decide⟩,⟨893903, by decide⟩,⟨996846, by decide⟩]) unmarked_context_11_74894_996847 node_context_11_74894_996847
  intro a
  fin_cases a
  · exact context_12_299576_996737
  · exact context_12_299577_996792
  · exact context_12_299578_893903
  · exact context_12_299579_996846

theorem selected_cut_37305 : selected 9 ⟨996905, by decide⟩
    (prefixPartial 12 299580) = some ⟨12, 2, 0, 996905, 299580, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_299580_996905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299580 ⟨996905, by decide⟩ :=
  accepted_of_selected 12 299580 ⟨996905, by decide⟩ ⟨12, 2, 0, 996905, 299580, 3585, 65536⟩
    (by decide) selected_cut_37305

theorem selected_cut_37306 : selected 9 ⟨996958, by decide⟩
    (prefixPartial 12 299581) = some ⟨12, 2, 0, 996958, 299581, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_299581_996958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299581 ⟨996958, by decide⟩ :=
  accepted_of_selected 12 299581 ⟨996958, by decide⟩ ⟨12, 2, 0, 996958, 299581, 3525, 65536⟩
    (by decide) selected_cut_37306

theorem selected_cut_37307 : selected 9 ⟨997008, by decide⟩
    (prefixPartial 12 299582) = some ⟨12, 2, 0, 997008, 299582, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_299582_997008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299582 ⟨997008, by decide⟩ :=
  accepted_of_selected 12 299582 ⟨997008, by decide⟩ ⟨12, 2, 0, 997008, 299582, 3249, 65536⟩
    (by decide) selected_cut_37307

theorem selected_cut_37308 : selected 9 ⟨997050, by decide⟩
    (prefixPartial 12 299583) = some ⟨12, 2, 0, 997050, 299583, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_299583_997050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299583 ⟨997050, by decide⟩ :=
  accepted_of_selected 12 299583 ⟨997050, by decide⟩ ⟨12, 2, 0, 997050, 299583, 3037, 65536⟩
    (by decide) selected_cut_37308

theorem unmarked_context_11_74895_997051 : frontier 10 ⟨997051, by decide⟩
    (prefixCache 11 74895) (prefixPartial 11 74895) = false := by
  decide +kernel

theorem node_context_11_74895_997051 : EJMOriginalGlobalDAGData.nodes 10 ⟨997051, by decide⟩ =
    .split (coordinate 11) (![⟨996905, by decide⟩,⟨996958, by decide⟩,⟨997008, by decide⟩,⟨997050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74895_997051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74895 ⟨997051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74895
    ⟨997051, by decide⟩ (by decide) (![⟨996905, by decide⟩,⟨996958, by decide⟩,⟨997008, by decide⟩,⟨997050, by decide⟩]) unmarked_context_11_74895_997051 node_context_11_74895_997051
  intro a
  fin_cases a
  · exact context_12_299580_996905
  · exact context_12_299581_996958
  · exact context_12_299582_997008
  · exact context_12_299583_997050

theorem unmarked_context_10_18723_997052 : frontier 11 ⟨997052, by decide⟩
    (prefixCache 10 18723) (prefixPartial 10 18723) = false := by
  decide +kernel

theorem node_context_10_18723_997052 : EJMOriginalGlobalDAGData.nodes 11 ⟨997052, by decide⟩ =
    .split (coordinate 10) (![⟨996434, by decide⟩,⟨996679, by decide⟩,⟨996847, by decide⟩,⟨997051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18723_997052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18723 ⟨997052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18723
    ⟨997052, by decide⟩ (by decide) (![⟨996434, by decide⟩,⟨996679, by decide⟩,⟨996847, by decide⟩,⟨997051, by decide⟩]) unmarked_context_10_18723_997052 node_context_10_18723_997052
  intro a
  fin_cases a
  · exact context_11_74892_996434
  · exact context_11_74893_996679
  · exact context_11_74894_996847
  · exact context_11_74895_997051

theorem unmarked_context_9_4680_997053 : frontier 12 ⟨997053, by decide⟩
    (prefixCache 9 4680) (prefixPartial 9 4680) = false := by
  decide +kernel

theorem node_context_9_4680_997053 : EJMOriginalGlobalDAGData.nodes 12 ⟨997053, by decide⟩ =
    .split (coordinate 9) (![⟨994571, by decide⟩,⟨995564, by decide⟩,⟨996307, by decide⟩,⟨997052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4680_997053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4680 ⟨997053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4680
    ⟨997053, by decide⟩ (by decide) (![⟨994571, by decide⟩,⟨995564, by decide⟩,⟨996307, by decide⟩,⟨997052, by decide⟩]) unmarked_context_9_4680_997053 node_context_9_4680_997053
  intro a
  fin_cases a
  · exact context_10_18720_994571
  · exact context_10_18721_995564
  · exact context_10_18722_996307
  · exact context_10_18723_997052

theorem selected_cut_37309 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74896) = some ⟨11, 1, 0, 907917, 74896, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74896_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74896 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74896 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74896, 1, 262144⟩
    (by decide) selected_cut_37309

theorem selected_cut_37310 : selected 9 ⟨997095, by decide⟩
    (prefixPartial 12 299588) = some ⟨12, 2, 0, 997095, 299588, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_299588_997095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299588 ⟨997095, by decide⟩ :=
  accepted_of_selected 12 299588 ⟨997095, by decide⟩ ⟨12, 2, 0, 997095, 299588, 2861, 65536⟩
    (by decide) selected_cut_37310

theorem selected_cut_37311 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 299589) = some ⟨12, 1, 0, 691709, 299589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299589_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299589 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 299589 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 299589, 1, 65536⟩
    (by decide) selected_cut_37311

theorem selected_cut_37312 : selected 9 ⟨997136, by decide⟩
    (prefixPartial 12 299590) = some ⟨12, 2, 0, 997136, 299590, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_299590_997136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299590 ⟨997136, by decide⟩ :=
  accepted_of_selected 12 299590 ⟨997136, by decide⟩ ⟨12, 2, 0, 997136, 299590, 2509, 65536⟩
    (by decide) selected_cut_37312

theorem selected_cut_37313 : selected 9 ⟨997178, by decide⟩
    (prefixPartial 12 299591) = some ⟨12, 2, 0, 997178, 299591, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_299591_997178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299591 ⟨997178, by decide⟩ :=
  accepted_of_selected 12 299591 ⟨997178, by decide⟩ ⟨12, 2, 0, 997178, 299591, 2613, 65536⟩
    (by decide) selected_cut_37313

theorem unmarked_context_11_74897_997179 : frontier 10 ⟨997179, by decide⟩
    (prefixCache 11 74897) (prefixPartial 11 74897) = false := by
  decide +kernel

theorem node_context_11_74897_997179 : EJMOriginalGlobalDAGData.nodes 10 ⟨997179, by decide⟩ =
    .split (coordinate 11) (![⟨997095, by decide⟩,⟨691709, by decide⟩,⟨997136, by decide⟩,⟨997178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74897_997179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74897 ⟨997179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74897
    ⟨997179, by decide⟩ (by decide) (![⟨997095, by decide⟩,⟨691709, by decide⟩,⟨997136, by decide⟩,⟨997178, by decide⟩]) unmarked_context_11_74897_997179 node_context_11_74897_997179
  intro a
  fin_cases a
  · exact context_12_299588_997095
  · exact context_12_299589_691709
  · exact context_12_299590_997136
  · exact context_12_299591_997178

theorem selected_cut_37314 : selected 9 ⟨997217, by decide⟩
    (prefixPartial 12 299592) = some ⟨12, 2, 0, 997217, 299592, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_299592_997217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299592 ⟨997217, by decide⟩ :=
  accepted_of_selected 12 299592 ⟨997217, by decide⟩ ⟨12, 2, 0, 997217, 299592, 2833, 65536⟩
    (by decide) selected_cut_37314

theorem selected_cut_37315 : selected 9 ⟨997263, by decide⟩
    (prefixPartial 12 299593) = some ⟨12, 2, 0, 997263, 299593, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_299593_997263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299593 ⟨997263, by decide⟩ :=
  accepted_of_selected 12 299593 ⟨997263, by decide⟩ ⟨12, 2, 0, 997263, 299593, 2957, 65536⟩
    (by decide) selected_cut_37315

theorem selected_cut_37316 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 299594) = some ⟨12, 1, 0, 893903, 299594, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299594_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299594 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 299594 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 299594, 1, 65536⟩
    (by decide) selected_cut_37316

theorem selected_cut_37317 : selected 9 ⟨997306, by decide⟩
    (prefixPartial 12 299595) = some ⟨12, 2, 0, 997306, 299595, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_299595_997306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299595 ⟨997306, by decide⟩ :=
  accepted_of_selected 12 299595 ⟨997306, by decide⟩ ⟨12, 2, 0, 997306, 299595, 2793, 65536⟩
    (by decide) selected_cut_37317

theorem unmarked_context_11_74898_997307 : frontier 10 ⟨997307, by decide⟩
    (prefixCache 11 74898) (prefixPartial 11 74898) = false := by
  decide +kernel

theorem node_context_11_74898_997307 : EJMOriginalGlobalDAGData.nodes 10 ⟨997307, by decide⟩ =
    .split (coordinate 11) (![⟨997217, by decide⟩,⟨997263, by decide⟩,⟨893903, by decide⟩,⟨997306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74898_997307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74898 ⟨997307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74898
    ⟨997307, by decide⟩ (by decide) (![⟨997217, by decide⟩,⟨997263, by decide⟩,⟨893903, by decide⟩,⟨997306, by decide⟩]) unmarked_context_11_74898_997307 node_context_11_74898_997307
  intro a
  fin_cases a
  · exact context_12_299592_997217
  · exact context_12_299593_997263
  · exact context_12_299594_893903
  · exact context_12_299595_997306

theorem selected_cut_37318 : selected 9 ⟨997351, by decide⟩
    (prefixPartial 12 299596) = some ⟨12, 2, 0, 997351, 299596, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_299596_997351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299596 ⟨997351, by decide⟩ :=
  accepted_of_selected 12 299596 ⟨997351, by decide⟩ ⟨12, 2, 0, 997351, 299596, 2901, 65536⟩
    (by decide) selected_cut_37318

theorem selected_cut_37319 : selected 9 ⟨997394, by decide⟩
    (prefixPartial 12 299597) = some ⟨12, 2, 0, 997394, 299597, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_299597_997394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299597 ⟨997394, by decide⟩ :=
  accepted_of_selected 12 299597 ⟨997394, by decide⟩ ⟨12, 2, 0, 997394, 299597, 2817, 65536⟩
    (by decide) selected_cut_37319

theorem selected_cut_37320 : selected 9 ⟨997435, by decide⟩
    (prefixPartial 12 299598) = some ⟨12, 2, 0, 997435, 299598, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_299598_997435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299598 ⟨997435, by decide⟩ :=
  accepted_of_selected 12 299598 ⟨997435, by decide⟩ ⟨12, 2, 0, 997435, 299598, 2641, 65536⟩
    (by decide) selected_cut_37320

theorem selected_cut_37321 : selected 9 ⟨997475, by decide⟩
    (prefixPartial 12 299599) = some ⟨12, 2, 0, 997475, 299599, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_299599_997475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299599 ⟨997475, by decide⟩ :=
  accepted_of_selected 12 299599 ⟨997475, by decide⟩ ⟨12, 2, 0, 997475, 299599, 2525, 65536⟩
    (by decide) selected_cut_37321

theorem unmarked_context_11_74899_997476 : frontier 10 ⟨997476, by decide⟩
    (prefixCache 11 74899) (prefixPartial 11 74899) = false := by
  decide +kernel

theorem node_context_11_74899_997476 : EJMOriginalGlobalDAGData.nodes 10 ⟨997476, by decide⟩ =
    .split (coordinate 11) (![⟨997351, by decide⟩,⟨997394, by decide⟩,⟨997435, by decide⟩,⟨997475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74899_997476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74899 ⟨997476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74899
    ⟨997476, by decide⟩ (by decide) (![⟨997351, by decide⟩,⟨997394, by decide⟩,⟨997435, by decide⟩,⟨997475, by decide⟩]) unmarked_context_11_74899_997476 node_context_11_74899_997476
  intro a
  fin_cases a
  · exact context_12_299596_997351
  · exact context_12_299597_997394
  · exact context_12_299598_997435
  · exact context_12_299599_997475

theorem unmarked_context_10_18724_997477 : frontier 11 ⟨997477, by decide⟩
    (prefixCache 10 18724) (prefixPartial 10 18724) = false := by
  decide +kernel

theorem node_context_10_18724_997477 : EJMOriginalGlobalDAGData.nodes 11 ⟨997477, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨997179, by decide⟩,⟨997307, by decide⟩,⟨997476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18724_997477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18724 ⟨997477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18724
    ⟨997477, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨997179, by decide⟩,⟨997307, by decide⟩,⟨997476, by decide⟩]) unmarked_context_10_18724_997477 node_context_10_18724_997477
  intro a
  fin_cases a
  · exact context_11_74896_907917
  · exact context_11_74897_997179
  · exact context_11_74898_997307
  · exact context_11_74899_997476

theorem selected_cut_37322 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18725) = some ⟨10, 1, 0, 893098, 18725, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18725_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18725 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18725 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18725, 1, 1048576⟩
    (by decide) selected_cut_37322

theorem selected_cut_37323 : selected 9 ⟨997504, by decide⟩
    (prefixPartial 12 299616) = some ⟨12, 2, 0, 997504, 299616, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_299616_997504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299616 ⟨997504, by decide⟩ :=
  accepted_of_selected 12 299616 ⟨997504, by decide⟩ ⟨12, 2, 0, 997504, 299616, 1981, 65536⟩
    (by decide) selected_cut_37323

theorem selected_cut_37324 : selected 9 ⟨997538, by decide⟩
    (prefixPartial 12 299617) = some ⟨12, 2, 0, 997538, 299617, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_299617_997538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299617 ⟨997538, by decide⟩ :=
  accepted_of_selected 12 299617 ⟨997538, by decide⟩ ⟨12, 2, 0, 997538, 299617, 2317, 65536⟩
    (by decide) selected_cut_37324

theorem selected_cut_37325 : selected 9 ⟨997564, by decide⟩
    (prefixPartial 12 299618) = some ⟨12, 2, 0, 997564, 299618, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_299618_997564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299618 ⟨997564, by decide⟩ :=
  accepted_of_selected 12 299618 ⟨997564, by decide⟩ ⟨12, 2, 0, 997564, 299618, 1833, 65536⟩
    (by decide) selected_cut_37325

theorem selected_cut_37326 : selected 9 ⟨997594, by decide⟩
    (prefixPartial 12 299619) = some ⟨12, 2, 0, 997594, 299619, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_299619_997594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299619 ⟨997594, by decide⟩ :=
  accepted_of_selected 12 299619 ⟨997594, by decide⟩ ⟨12, 2, 0, 997594, 299619, 2025, 65536⟩
    (by decide) selected_cut_37326

theorem unmarked_context_11_74904_997595 : frontier 10 ⟨997595, by decide⟩
    (prefixCache 11 74904) (prefixPartial 11 74904) = false := by
  decide +kernel

theorem node_context_11_74904_997595 : EJMOriginalGlobalDAGData.nodes 10 ⟨997595, by decide⟩ =
    .split (coordinate 11) (![⟨997504, by decide⟩,⟨997538, by decide⟩,⟨997564, by decide⟩,⟨997594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74904_997595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74904 ⟨997595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74904
    ⟨997595, by decide⟩ (by decide) (![⟨997504, by decide⟩,⟨997538, by decide⟩,⟨997564, by decide⟩,⟨997594, by decide⟩]) unmarked_context_11_74904_997595 node_context_11_74904_997595
  intro a
  fin_cases a
  · exact context_12_299616_997504
  · exact context_12_299617_997538
  · exact context_12_299618_997564
  · exact context_12_299619_997594

theorem selected_cut_37327 : selected 9 ⟨997622, by decide⟩
    (prefixPartial 12 299620) = some ⟨12, 2, 0, 997622, 299620, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_299620_997622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299620 ⟨997622, by decide⟩ :=
  accepted_of_selected 12 299620 ⟨997622, by decide⟩ ⟨12, 2, 0, 997622, 299620, 1937, 65536⟩
    (by decide) selected_cut_37327

theorem selected_cut_37328 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 299621) = some ⟨12, 1, 0, 691709, 299621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299621_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299621 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 299621 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 299621, 1, 65536⟩
    (by decide) selected_cut_37328

theorem selected_cut_37329 : selected 9 ⟨997647, by decide⟩
    (prefixPartial 12 299622) = some ⟨12, 2, 0, 997647, 299622, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_299622_997647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299622 ⟨997647, by decide⟩ :=
  accepted_of_selected 12 299622 ⟨997647, by decide⟩ ⟨12, 2, 0, 997647, 299622, 1713, 65536⟩
    (by decide) selected_cut_37329

theorem selected_cut_37330 : selected 9 ⟨997674, by decide⟩
    (prefixPartial 12 299623) = some ⟨12, 2, 0, 997674, 299623, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_299623_997674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299623 ⟨997674, by decide⟩ :=
  accepted_of_selected 12 299623 ⟨997674, by decide⟩ ⟨12, 2, 0, 997674, 299623, 1941, 65536⟩
    (by decide) selected_cut_37330

theorem unmarked_context_11_74905_997675 : frontier 10 ⟨997675, by decide⟩
    (prefixCache 11 74905) (prefixPartial 11 74905) = false := by
  decide +kernel

theorem node_context_11_74905_997675 : EJMOriginalGlobalDAGData.nodes 10 ⟨997675, by decide⟩ =
    .split (coordinate 11) (![⟨997622, by decide⟩,⟨691709, by decide⟩,⟨997647, by decide⟩,⟨997674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74905_997675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74905 ⟨997675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74905
    ⟨997675, by decide⟩ (by decide) (![⟨997622, by decide⟩,⟨691709, by decide⟩,⟨997647, by decide⟩,⟨997674, by decide⟩]) unmarked_context_11_74905_997675 node_context_11_74905_997675
  intro a
  fin_cases a
  · exact context_12_299620_997622
  · exact context_12_299621_691709
  · exact context_12_299622_997647
  · exact context_12_299623_997674

theorem selected_cut_37331 : selected 9 ⟨997704, by decide⟩
    (prefixPartial 12 299624) = some ⟨12, 2, 0, 997704, 299624, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_299624_997704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299624 ⟨997704, by decide⟩ :=
  accepted_of_selected 12 299624 ⟨997704, by decide⟩ ⟨12, 2, 0, 997704, 299624, 2181, 65536⟩
    (by decide) selected_cut_37331

theorem selected_cut_37332 : selected 9 ⟨997747, by decide⟩
    (prefixPartial 12 299625) = some ⟨12, 2, 0, 997747, 299625, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_299625_997747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299625 ⟨997747, by decide⟩ :=
  accepted_of_selected 12 299625 ⟨997747, by decide⟩ ⟨12, 2, 0, 997747, 299625, 2409, 65536⟩
    (by decide) selected_cut_37332

theorem selected_cut_37333 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 299626) = some ⟨12, 1, 0, 242157, 299626, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299626_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299626 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 299626 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 299626, 1, 65536⟩
    (by decide) selected_cut_37333

theorem selected_cut_37334 : selected 9 ⟨997777, by decide⟩
    (prefixPartial 12 299627) = some ⟨12, 2, 0, 997777, 299627, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_299627_997777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299627 ⟨997777, by decide⟩ :=
  accepted_of_selected 12 299627 ⟨997777, by decide⟩ ⟨12, 2, 0, 997777, 299627, 2221, 65536⟩
    (by decide) selected_cut_37334

theorem unmarked_context_11_74906_997778 : frontier 10 ⟨997778, by decide⟩
    (prefixCache 11 74906) (prefixPartial 11 74906) = false := by
  decide +kernel

theorem node_context_11_74906_997778 : EJMOriginalGlobalDAGData.nodes 10 ⟨997778, by decide⟩ =
    .split (coordinate 11) (![⟨997704, by decide⟩,⟨997747, by decide⟩,⟨242157, by decide⟩,⟨997777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74906_997778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74906 ⟨997778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74906
    ⟨997778, by decide⟩ (by decide) (![⟨997704, by decide⟩,⟨997747, by decide⟩,⟨242157, by decide⟩,⟨997777, by decide⟩]) unmarked_context_11_74906_997778 node_context_11_74906_997778
  intro a
  fin_cases a
  · exact context_12_299624_997704
  · exact context_12_299625_997747
  · exact context_12_299626_242157
  · exact context_12_299627_997777

theorem selected_cut_37335 : selected 9 ⟨997813, by decide⟩
    (prefixPartial 12 299628) = some ⟨12, 2, 0, 997813, 299628, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_299628_997813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299628 ⟨997813, by decide⟩ :=
  accepted_of_selected 12 299628 ⟨997813, by decide⟩ ⟨12, 2, 0, 997813, 299628, 2085, 65536⟩
    (by decide) selected_cut_37335

theorem selected_cut_37336 : selected 9 ⟨997850, by decide⟩
    (prefixPartial 12 299629) = some ⟨12, 2, 0, 997850, 299629, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_299629_997850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299629 ⟨997850, by decide⟩ :=
  accepted_of_selected 12 299629 ⟨997850, by decide⟩ ⟨12, 2, 0, 997850, 299629, 2265, 65536⟩
    (by decide) selected_cut_37336

theorem selected_cut_37337 : selected 9 ⟨997878, by decide⟩
    (prefixPartial 12 299630) = some ⟨12, 2, 0, 997878, 299630, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_299630_997878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299630 ⟨997878, by decide⟩ :=
  accepted_of_selected 12 299630 ⟨997878, by decide⟩ ⟨12, 2, 0, 997878, 299630, 1837, 65536⟩
    (by decide) selected_cut_37337

theorem selected_cut_37338 : selected 9 ⟨997907, by decide⟩
    (prefixPartial 12 299631) = some ⟨12, 2, 0, 997907, 299631, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_299631_997907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299631 ⟨997907, by decide⟩ :=
  accepted_of_selected 12 299631 ⟨997907, by decide⟩ ⟨12, 2, 0, 997907, 299631, 1933, 65536⟩
    (by decide) selected_cut_37338

theorem unmarked_context_11_74907_997908 : frontier 10 ⟨997908, by decide⟩
    (prefixCache 11 74907) (prefixPartial 11 74907) = false := by
  decide +kernel

theorem node_context_11_74907_997908 : EJMOriginalGlobalDAGData.nodes 10 ⟨997908, by decide⟩ =
    .split (coordinate 11) (![⟨997813, by decide⟩,⟨997850, by decide⟩,⟨997878, by decide⟩,⟨997907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74907_997908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74907 ⟨997908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74907
    ⟨997908, by decide⟩ (by decide) (![⟨997813, by decide⟩,⟨997850, by decide⟩,⟨997878, by decide⟩,⟨997907, by decide⟩]) unmarked_context_11_74907_997908 node_context_11_74907_997908
  intro a
  fin_cases a
  · exact context_12_299628_997813
  · exact context_12_299629_997850
  · exact context_12_299630_997878
  · exact context_12_299631_997907

theorem unmarked_context_10_18726_997909 : frontier 11 ⟨997909, by decide⟩
    (prefixCache 10 18726) (prefixPartial 10 18726) = false := by
  decide +kernel

theorem node_context_10_18726_997909 : EJMOriginalGlobalDAGData.nodes 11 ⟨997909, by decide⟩ =
    .split (coordinate 10) (![⟨997595, by decide⟩,⟨997675, by decide⟩,⟨997778, by decide⟩,⟨997908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18726_997909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18726 ⟨997909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18726
    ⟨997909, by decide⟩ (by decide) (![⟨997595, by decide⟩,⟨997675, by decide⟩,⟨997778, by decide⟩,⟨997908, by decide⟩]) unmarked_context_10_18726_997909 node_context_10_18726_997909
  intro a
  fin_cases a
  · exact context_11_74904_997595
  · exact context_11_74905_997675
  · exact context_11_74906_997778
  · exact context_11_74907_997908

theorem selected_cut_37339 : selected 9 ⟨997936, by decide⟩
    (prefixPartial 12 299632) = some ⟨12, 2, 0, 997936, 299632, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_299632_997936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299632 ⟨997936, by decide⟩ :=
  accepted_of_selected 12 299632 ⟨997936, by decide⟩ ⟨12, 2, 0, 997936, 299632, 1821, 65536⟩
    (by decide) selected_cut_37339

theorem selected_cut_37340 : selected 9 ⟨997967, by decide⟩
    (prefixPartial 12 299633) = some ⟨12, 2, 0, 997967, 299633, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_299633_997967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299633 ⟨997967, by decide⟩ :=
  accepted_of_selected 12 299633 ⟨997967, by decide⟩ ⟨12, 2, 0, 997967, 299633, 1981, 65536⟩
    (by decide) selected_cut_37340

theorem selected_cut_37341 : selected 9 ⟨997982, by decide⟩
    (prefixPartial 12 299634) = some ⟨12, 2, 0, 997982, 299634, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_299634_997982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299634 ⟨997982, by decide⟩ :=
  accepted_of_selected 12 299634 ⟨997982, by decide⟩ ⟨12, 2, 0, 997982, 299634, 1557, 65536⟩
    (by decide) selected_cut_37341

theorem selected_cut_37342 : selected 9 ⟨998010, by decide⟩
    (prefixPartial 12 299635) = some ⟨12, 2, 0, 998010, 299635, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_299635_998010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299635 ⟨998010, by decide⟩ :=
  accepted_of_selected 12 299635 ⟨998010, by decide⟩ ⟨12, 2, 0, 998010, 299635, 1861, 65536⟩
    (by decide) selected_cut_37342

theorem unmarked_context_11_74908_998011 : frontier 10 ⟨998011, by decide⟩
    (prefixCache 11 74908) (prefixPartial 11 74908) = false := by
  decide +kernel

theorem node_context_11_74908_998011 : EJMOriginalGlobalDAGData.nodes 10 ⟨998011, by decide⟩ =
    .split (coordinate 11) (![⟨997936, by decide⟩,⟨997967, by decide⟩,⟨997982, by decide⟩,⟨998010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74908_998011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74908 ⟨998011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74908
    ⟨998011, by decide⟩ (by decide) (![⟨997936, by decide⟩,⟨997967, by decide⟩,⟨997982, by decide⟩,⟨998010, by decide⟩]) unmarked_context_11_74908_998011 node_context_11_74908_998011
  intro a
  fin_cases a
  · exact context_12_299632_997936
  · exact context_12_299633_997967
  · exact context_12_299634_997982
  · exact context_12_299635_998010

theorem selected_cut_37343 : selected 9 ⟨998038, by decide⟩
    (prefixPartial 12 299636) = some ⟨12, 2, 0, 998038, 299636, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_299636_998038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299636 ⟨998038, by decide⟩ :=
  accepted_of_selected 12 299636 ⟨998038, by decide⟩ ⟨12, 2, 0, 998038, 299636, 1829, 65536⟩
    (by decide) selected_cut_37343

theorem selected_cut_37344 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 299637) = some ⟨12, 1, 0, 691709, 299637, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299637_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299637 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 299637 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 299637, 1, 65536⟩
    (by decide) selected_cut_37344

theorem selected_cut_37345 : selected 9 ⟨998055, by decide⟩
    (prefixPartial 12 299638) = some ⟨12, 2, 0, 998055, 299638, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_299638_998055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299638 ⟨998055, by decide⟩ :=
  accepted_of_selected 12 299638 ⟨998055, by decide⟩ ⟨12, 2, 0, 998055, 299638, 1537, 65536⟩
    (by decide) selected_cut_37345

theorem selected_cut_37346 : selected 9 ⟨998081, by decide⟩
    (prefixPartial 12 299639) = some ⟨12, 2, 0, 998081, 299639, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_299639_998081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299639 ⟨998081, by decide⟩ :=
  accepted_of_selected 12 299639 ⟨998081, by decide⟩ ⟨12, 2, 0, 998081, 299639, 1813, 65536⟩
    (by decide) selected_cut_37346

theorem unmarked_context_11_74909_998082 : frontier 10 ⟨998082, by decide⟩
    (prefixCache 11 74909) (prefixPartial 11 74909) = false := by
  decide +kernel

theorem node_context_11_74909_998082 : EJMOriginalGlobalDAGData.nodes 10 ⟨998082, by decide⟩ =
    .split (coordinate 11) (![⟨998038, by decide⟩,⟨691709, by decide⟩,⟨998055, by decide⟩,⟨998081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74909_998082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74909 ⟨998082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74909
    ⟨998082, by decide⟩ (by decide) (![⟨998038, by decide⟩,⟨691709, by decide⟩,⟨998055, by decide⟩,⟨998081, by decide⟩]) unmarked_context_11_74909_998082 node_context_11_74909_998082
  intro a
  fin_cases a
  · exact context_12_299636_998038
  · exact context_12_299637_691709
  · exact context_12_299638_998055
  · exact context_12_299639_998081

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
