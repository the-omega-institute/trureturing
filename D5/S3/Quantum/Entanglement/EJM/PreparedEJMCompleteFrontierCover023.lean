/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover022
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_5642_72950 : frontier 9 ⟨72950, by decide⟩
    (prefixCache 12 5642) (prefixPartial 12 5642) = false := by
  decide +kernel

theorem node_context_12_5642_72950 : EJMOriginalGlobalDAGData.nodes 9 ⟨72950, by decide⟩ =
    .split (coordinate 12) (![⟨72701, by decide⟩,⟨72816, by decide⟩,⟨72890, by decide⟩,⟨72949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5642_72950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5642 ⟨72950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5642
    ⟨72950, by decide⟩ (by decide) (![⟨72701, by decide⟩,⟨72816, by decide⟩,⟨72890, by decide⟩,⟨72949, by decide⟩]) unmarked_context_12_5642_72950 node_context_12_5642_72950
  intro a
  fin_cases a
  · exact context_13_22568_72701
  · exact context_13_22569_72816
  · exact context_13_22570_72890
  · exact context_13_22571_72949

theorem selected_cut_02211 : selected 7 ⟨72960, by decide⟩
    (prefixPartial 14 90288) = some ⟨14, 2, 0, 72960, 90288, 653, 4096⟩ := by
  decide +kernel

theorem context_14_90288_72960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90288 ⟨72960, by decide⟩ :=
  accepted_of_selected 14 90288 ⟨72960, by decide⟩ ⟨14, 2, 0, 72960, 90288, 653, 4096⟩
    (by decide) selected_cut_02211

theorem selected_cut_02212 : selected 7 ⟨72982, by decide⟩
    (prefixPartial 14 90289) = some ⟨14, 2, 0, 72982, 90289, 1629, 4096⟩ := by
  decide +kernel

theorem context_14_90289_72982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90289 ⟨72982, by decide⟩ :=
  accepted_of_selected 14 90289 ⟨72982, by decide⟩ ⟨14, 2, 0, 72982, 90289, 1629, 4096⟩
    (by decide) selected_cut_02212

theorem selected_cut_02213 : selected 7 ⟨73001, by decide⟩
    (prefixPartial 14 90290) = some ⟨14, 2, 0, 73001, 90290, 1497, 4096⟩ := by
  decide +kernel

theorem context_14_90290_73001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90290 ⟨73001, by decide⟩ :=
  accepted_of_selected 14 90290 ⟨73001, by decide⟩ ⟨14, 2, 0, 73001, 90290, 1497, 4096⟩
    (by decide) selected_cut_02213

theorem selected_cut_02214 : selected 7 ⟨73020, by decide⟩
    (prefixPartial 14 90291) = some ⟨14, 2, 0, 73020, 90291, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_90291_73020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90291 ⟨73020, by decide⟩ :=
  accepted_of_selected 14 90291 ⟨73020, by decide⟩ ⟨14, 2, 0, 73020, 90291, 1405, 4096⟩
    (by decide) selected_cut_02214

theorem unmarked_context_13_22572_73021 : frontier 8 ⟨73021, by decide⟩
    (prefixCache 13 22572) (prefixPartial 13 22572) = false := by
  decide +kernel

theorem node_context_13_22572_73021 : EJMOriginalGlobalDAGData.nodes 8 ⟨73021, by decide⟩ =
    .split (coordinate 13) (![⟨72960, by decide⟩,⟨72982, by decide⟩,⟨73001, by decide⟩,⟨73020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22572_73021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22572 ⟨73021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22572
    ⟨73021, by decide⟩ (by decide) (![⟨72960, by decide⟩,⟨72982, by decide⟩,⟨73001, by decide⟩,⟨73020, by decide⟩]) unmarked_context_13_22572_73021 node_context_13_22572_73021
  intro a
  fin_cases a
  · exact context_14_90288_72960
  · exact context_14_90289_72982
  · exact context_14_90290_73001
  · exact context_14_90291_73020

theorem selected_cut_02215 : selected 7 ⟨73036, by decide⟩
    (prefixPartial 14 90292) = some ⟨14, 2, 0, 73036, 90292, 969, 4096⟩ := by
  decide +kernel

theorem context_14_90292_73036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90292 ⟨73036, by decide⟩ :=
  accepted_of_selected 14 90292 ⟨73036, by decide⟩ ⟨14, 2, 0, 73036, 90292, 969, 4096⟩
    (by decide) selected_cut_02215

theorem selected_cut_02216 : selected 7 ⟨73057, by decide⟩
    (prefixPartial 14 90293) = some ⟨14, 2, 0, 73057, 90293, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_90293_73057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90293 ⟨73057, by decide⟩ :=
  accepted_of_selected 14 90293 ⟨73057, by decide⟩ ⟨14, 2, 0, 73057, 90293, 1341, 4096⟩
    (by decide) selected_cut_02216

theorem selected_cut_02217 : selected 7 ⟨73078, by decide⟩
    (prefixPartial 14 90294) = some ⟨14, 2, 0, 73078, 90294, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_90294_73078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90294 ⟨73078, by decide⟩ :=
  accepted_of_selected 14 90294 ⟨73078, by decide⟩ ⟨14, 2, 0, 73078, 90294, 1153, 4096⟩
    (by decide) selected_cut_02217

theorem selected_cut_02218 : selected 7 ⟨73097, by decide⟩
    (prefixPartial 14 90295) = some ⟨14, 2, 0, 73097, 90295, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_90295_73097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90295 ⟨73097, by decide⟩ :=
  accepted_of_selected 14 90295 ⟨73097, by decide⟩ ⟨14, 2, 0, 73097, 90295, 1105, 4096⟩
    (by decide) selected_cut_02218

theorem unmarked_context_13_22573_73098 : frontier 8 ⟨73098, by decide⟩
    (prefixCache 13 22573) (prefixPartial 13 22573) = false := by
  decide +kernel

theorem node_context_13_22573_73098 : EJMOriginalGlobalDAGData.nodes 8 ⟨73098, by decide⟩ =
    .split (coordinate 13) (![⟨73036, by decide⟩,⟨73057, by decide⟩,⟨73078, by decide⟩,⟨73097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22573_73098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22573 ⟨73098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22573
    ⟨73098, by decide⟩ (by decide) (![⟨73036, by decide⟩,⟨73057, by decide⟩,⟨73078, by decide⟩,⟨73097, by decide⟩]) unmarked_context_13_22573_73098 node_context_13_22573_73098
  intro a
  fin_cases a
  · exact context_14_90292_73036
  · exact context_14_90293_73057
  · exact context_14_90294_73078
  · exact context_14_90295_73097

theorem selected_cut_02219 : selected 8 ⟨73136, by decide⟩
    (prefixPartial 13 22574) = some ⟨13, 2, 0, 73136, 22574, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_22574_73136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22574 ⟨73136, by decide⟩ :=
  accepted_of_selected 13 22574 ⟨73136, by decide⟩ ⟨13, 2, 0, 73136, 22574, 2617, 16384⟩
    (by decide) selected_cut_02219

theorem selected_cut_02220 : selected 8 ⟨73151, by decide⟩
    (prefixPartial 13 22575) = some ⟨13, 2, 0, 73151, 22575, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_22575_73151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22575 ⟨73151, by decide⟩ :=
  accepted_of_selected 13 22575 ⟨73151, by decide⟩ ⟨13, 2, 0, 73151, 22575, 1293, 16384⟩
    (by decide) selected_cut_02220

theorem unmarked_context_12_5643_73152 : frontier 9 ⟨73152, by decide⟩
    (prefixCache 12 5643) (prefixPartial 12 5643) = false := by
  decide +kernel

theorem node_context_12_5643_73152 : EJMOriginalGlobalDAGData.nodes 9 ⟨73152, by decide⟩ =
    .split (coordinate 12) (![⟨73021, by decide⟩,⟨73098, by decide⟩,⟨73136, by decide⟩,⟨73151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5643_73152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5643 ⟨73152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5643
    ⟨73152, by decide⟩ (by decide) (![⟨73021, by decide⟩,⟨73098, by decide⟩,⟨73136, by decide⟩,⟨73151, by decide⟩]) unmarked_context_12_5643_73152 node_context_12_5643_73152
  intro a
  fin_cases a
  · exact context_13_22572_73021
  · exact context_13_22573_73098
  · exact context_13_22574_73136
  · exact context_13_22575_73151

theorem unmarked_context_11_1410_73153 : frontier 10 ⟨73153, by decide⟩
    (prefixCache 11 1410) (prefixPartial 11 1410) = false := by
  decide +kernel

theorem node_context_11_1410_73153 : EJMOriginalGlobalDAGData.nodes 10 ⟨73153, by decide⟩ =
    .split (coordinate 11) (![⟨72372, by decide⟩,⟨72579, by decide⟩,⟨72950, by decide⟩,⟨73152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1410_73153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1410 ⟨73153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1410
    ⟨73153, by decide⟩ (by decide) (![⟨72372, by decide⟩,⟨72579, by decide⟩,⟨72950, by decide⟩,⟨73152, by decide⟩]) unmarked_context_11_1410_73153 node_context_11_1410_73153
  intro a
  fin_cases a
  · exact context_12_5640_72372
  · exact context_12_5641_72579
  · exact context_12_5642_72950
  · exact context_12_5643_73152

theorem selected_cut_02221 : selected 7 ⟨73162, by decide⟩
    (prefixPartial 14 90304) = some ⟨14, 2, 0, 73162, 90304, 849, 4096⟩ := by
  decide +kernel

theorem context_14_90304_73162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90304 ⟨73162, by decide⟩ :=
  accepted_of_selected 14 90304 ⟨73162, by decide⟩ ⟨14, 2, 0, 73162, 90304, 849, 4096⟩
    (by decide) selected_cut_02221

theorem selected_cut_02222 : selected 7 ⟨73184, by decide⟩
    (prefixPartial 14 90305) = some ⟨14, 2, 0, 73184, 90305, 1545, 4096⟩ := by
  decide +kernel

theorem context_14_90305_73184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90305 ⟨73184, by decide⟩ :=
  accepted_of_selected 14 90305 ⟨73184, by decide⟩ ⟨14, 2, 0, 73184, 90305, 1545, 4096⟩
    (by decide) selected_cut_02222

theorem selected_cut_02223 : selected 7 ⟨73212, by decide⟩
    (prefixPartial 14 90306) = some ⟨14, 2, 0, 73212, 90306, 1725, 4096⟩ := by
  decide +kernel

theorem context_14_90306_73212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90306 ⟨73212, by decide⟩ :=
  accepted_of_selected 14 90306 ⟨73212, by decide⟩ ⟨14, 2, 0, 73212, 90306, 1725, 4096⟩
    (by decide) selected_cut_02223

theorem selected_cut_02224 : selected 7 ⟨73227, by decide⟩
    (prefixPartial 14 90307) = some ⟨14, 2, 0, 73227, 90307, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_90307_73227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90307 ⟨73227, by decide⟩ :=
  accepted_of_selected 14 90307 ⟨73227, by decide⟩ ⟨14, 2, 0, 73227, 90307, 1193, 4096⟩
    (by decide) selected_cut_02224

theorem unmarked_context_13_22576_73228 : frontier 8 ⟨73228, by decide⟩
    (prefixCache 13 22576) (prefixPartial 13 22576) = false := by
  decide +kernel

theorem node_context_13_22576_73228 : EJMOriginalGlobalDAGData.nodes 8 ⟨73228, by decide⟩ =
    .split (coordinate 13) (![⟨73162, by decide⟩,⟨73184, by decide⟩,⟨73212, by decide⟩,⟨73227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22576_73228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22576 ⟨73228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22576
    ⟨73228, by decide⟩ (by decide) (![⟨73162, by decide⟩,⟨73184, by decide⟩,⟨73212, by decide⟩,⟨73227, by decide⟩]) unmarked_context_13_22576_73228 node_context_13_22576_73228
  intro a
  fin_cases a
  · exact context_14_90304_73162
  · exact context_14_90305_73184
  · exact context_14_90306_73212
  · exact context_14_90307_73227

theorem selected_cut_02225 : selected 7 ⟨73251, by decide⟩
    (prefixPartial 14 90308) = some ⟨14, 2, 0, 73251, 90308, 1673, 4096⟩ := by
  decide +kernel

theorem context_14_90308_73251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90308 ⟨73251, by decide⟩ :=
  accepted_of_selected 14 90308 ⟨73251, by decide⟩ ⟨14, 2, 0, 73251, 90308, 1673, 4096⟩
    (by decide) selected_cut_02225

theorem selected_cut_02226 : selected 7 ⟨73277, by decide⟩
    (prefixPartial 14 90309) = some ⟨14, 2, 0, 73277, 90309, 1713, 4096⟩ := by
  decide +kernel

theorem context_14_90309_73277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90309 ⟨73277, by decide⟩ :=
  accepted_of_selected 14 90309 ⟨73277, by decide⟩ ⟨14, 2, 0, 73277, 90309, 1713, 4096⟩
    (by decide) selected_cut_02226

theorem selected_cut_02227 : selected 7 ⟨73302, by decide⟩
    (prefixPartial 14 90310) = some ⟨14, 2, 0, 73302, 90310, 1329, 4096⟩ := by
  decide +kernel

theorem context_14_90310_73302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90310 ⟨73302, by decide⟩ :=
  accepted_of_selected 14 90310 ⟨73302, by decide⟩ ⟨14, 2, 0, 73302, 90310, 1329, 4096⟩
    (by decide) selected_cut_02227

theorem selected_cut_02228 : selected 7 ⟨73325, by decide⟩
    (prefixPartial 14 90311) = some ⟨14, 2, 0, 73325, 90311, 1481, 4096⟩ := by
  decide +kernel

theorem context_14_90311_73325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90311 ⟨73325, by decide⟩ :=
  accepted_of_selected 14 90311 ⟨73325, by decide⟩ ⟨14, 2, 0, 73325, 90311, 1481, 4096⟩
    (by decide) selected_cut_02228

theorem unmarked_context_13_22577_73326 : frontier 8 ⟨73326, by decide⟩
    (prefixCache 13 22577) (prefixPartial 13 22577) = false := by
  decide +kernel

theorem node_context_13_22577_73326 : EJMOriginalGlobalDAGData.nodes 8 ⟨73326, by decide⟩ =
    .split (coordinate 13) (![⟨73251, by decide⟩,⟨73277, by decide⟩,⟨73302, by decide⟩,⟨73325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22577_73326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22577 ⟨73326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22577
    ⟨73326, by decide⟩ (by decide) (![⟨73251, by decide⟩,⟨73277, by decide⟩,⟨73302, by decide⟩,⟨73325, by decide⟩]) unmarked_context_13_22577_73326 node_context_13_22577_73326
  intro a
  fin_cases a
  · exact context_14_90308_73251
  · exact context_14_90309_73277
  · exact context_14_90310_73302
  · exact context_14_90311_73325

theorem selected_cut_02229 : selected 8 ⟨73398, by decide⟩
    (prefixPartial 13 22578) = some ⟨13, 2, 0, 73398, 22578, 3633, 16384⟩ := by
  decide +kernel

theorem context_13_22578_73398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22578 ⟨73398, by decide⟩ :=
  accepted_of_selected 13 22578 ⟨73398, by decide⟩ ⟨13, 2, 0, 73398, 22578, 3633, 16384⟩
    (by decide) selected_cut_02229

theorem selected_cut_02230 : selected 8 ⟨73441, by decide⟩
    (prefixPartial 13 22579) = some ⟨13, 2, 0, 73441, 22579, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_22579_73441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22579 ⟨73441, by decide⟩ :=
  accepted_of_selected 13 22579 ⟨73441, by decide⟩ ⟨13, 2, 0, 73441, 22579, 1817, 16384⟩
    (by decide) selected_cut_02230

theorem unmarked_context_12_5644_73442 : frontier 9 ⟨73442, by decide⟩
    (prefixCache 12 5644) (prefixPartial 12 5644) = false := by
  decide +kernel

theorem node_context_12_5644_73442 : EJMOriginalGlobalDAGData.nodes 9 ⟨73442, by decide⟩ =
    .split (coordinate 12) (![⟨73228, by decide⟩,⟨73326, by decide⟩,⟨73398, by decide⟩,⟨73441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5644_73442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5644 ⟨73442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5644
    ⟨73442, by decide⟩ (by decide) (![⟨73228, by decide⟩,⟨73326, by decide⟩,⟨73398, by decide⟩,⟨73441, by decide⟩]) unmarked_context_12_5644_73442 node_context_12_5644_73442
  intro a
  fin_cases a
  · exact context_13_22576_73228
  · exact context_13_22577_73326
  · exact context_13_22578_73398
  · exact context_13_22579_73441

theorem selected_cut_02231 : selected 7 ⟨73449, by decide⟩
    (prefixPartial 14 90320) = some ⟨14, 2, 0, 73449, 90320, 373, 4096⟩ := by
  decide +kernel

theorem context_14_90320_73449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90320 ⟨73449, by decide⟩ :=
  accepted_of_selected 14 90320 ⟨73449, by decide⟩ ⟨14, 2, 0, 73449, 90320, 373, 4096⟩
    (by decide) selected_cut_02231

theorem selected_cut_02232 : selected 7 ⟨73472, by decide⟩
    (prefixPartial 14 90321) = some ⟨14, 2, 0, 73472, 90321, 1573, 4096⟩ := by
  decide +kernel

theorem context_14_90321_73472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90321 ⟨73472, by decide⟩ :=
  accepted_of_selected 14 90321 ⟨73472, by decide⟩ ⟨14, 2, 0, 73472, 90321, 1573, 4096⟩
    (by decide) selected_cut_02232

theorem selected_cut_02233 : selected 7 ⟨73493, by decide⟩
    (prefixPartial 14 90322) = some ⟨14, 2, 0, 73493, 90322, 1493, 4096⟩ := by
  decide +kernel

theorem context_14_90322_73493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90322 ⟨73493, by decide⟩ :=
  accepted_of_selected 14 90322 ⟨73493, by decide⟩ ⟨14, 2, 0, 73493, 90322, 1493, 4096⟩
    (by decide) selected_cut_02233

theorem selected_cut_02234 : selected 7 ⟨73510, by decide⟩
    (prefixPartial 14 90323) = some ⟨14, 2, 0, 73510, 90323, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_90323_73510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90323 ⟨73510, by decide⟩ :=
  accepted_of_selected 14 90323 ⟨73510, by decide⟩ ⟨14, 2, 0, 73510, 90323, 1249, 4096⟩
    (by decide) selected_cut_02234

theorem unmarked_context_13_22580_73511 : frontier 8 ⟨73511, by decide⟩
    (prefixCache 13 22580) (prefixPartial 13 22580) = false := by
  decide +kernel

theorem node_context_13_22580_73511 : EJMOriginalGlobalDAGData.nodes 8 ⟨73511, by decide⟩ =
    .split (coordinate 13) (![⟨73449, by decide⟩,⟨73472, by decide⟩,⟨73493, by decide⟩,⟨73510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22580_73511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22580 ⟨73511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22580
    ⟨73511, by decide⟩ (by decide) (![⟨73449, by decide⟩,⟨73472, by decide⟩,⟨73493, by decide⟩,⟨73510, by decide⟩]) unmarked_context_13_22580_73511 node_context_13_22580_73511
  intro a
  fin_cases a
  · exact context_14_90320_73449
  · exact context_14_90321_73472
  · exact context_14_90322_73493
  · exact context_14_90323_73510

theorem selected_cut_02235 : selected 7 ⟨73527, by decide⟩
    (prefixPartial 14 90324) = some ⟨14, 2, 0, 73527, 90324, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_90324_73527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90324 ⟨73527, by decide⟩ :=
  accepted_of_selected 14 90324 ⟨73527, by decide⟩ ⟨14, 2, 0, 73527, 90324, 1021, 4096⟩
    (by decide) selected_cut_02235

theorem selected_cut_02236 : selected 7 ⟨73549, by decide⟩
    (prefixPartial 14 90325) = some ⟨14, 2, 0, 73549, 90325, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_90325_73549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90325 ⟨73549, by decide⟩ :=
  accepted_of_selected 14 90325 ⟨73549, by decide⟩ ⟨14, 2, 0, 73549, 90325, 1213, 4096⟩
    (by decide) selected_cut_02236

theorem selected_cut_02237 : selected 7 ⟨73564, by decide⟩
    (prefixPartial 14 90326) = some ⟨14, 2, 0, 73564, 90326, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_90326_73564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90326 ⟨73564, by decide⟩ :=
  accepted_of_selected 14 90326 ⟨73564, by decide⟩ ⟨14, 2, 0, 73564, 90326, 1097, 4096⟩
    (by decide) selected_cut_02237

theorem selected_cut_02238 : selected 7 ⟨73577, by decide⟩
    (prefixPartial 14 90327) = some ⟨14, 2, 0, 73577, 90327, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_90327_73577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90327 ⟨73577, by decide⟩ :=
  accepted_of_selected 14 90327 ⟨73577, by decide⟩ ⟨14, 2, 0, 73577, 90327, 1021, 4096⟩
    (by decide) selected_cut_02238

theorem unmarked_context_13_22581_73578 : frontier 8 ⟨73578, by decide⟩
    (prefixCache 13 22581) (prefixPartial 13 22581) = false := by
  decide +kernel

theorem node_context_13_22581_73578 : EJMOriginalGlobalDAGData.nodes 8 ⟨73578, by decide⟩ =
    .split (coordinate 13) (![⟨73527, by decide⟩,⟨73549, by decide⟩,⟨73564, by decide⟩,⟨73577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22581_73578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22581 ⟨73578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22581
    ⟨73578, by decide⟩ (by decide) (![⟨73527, by decide⟩,⟨73549, by decide⟩,⟨73564, by decide⟩,⟨73577, by decide⟩]) unmarked_context_13_22581_73578 node_context_13_22581_73578
  intro a
  fin_cases a
  · exact context_14_90324_73527
  · exact context_14_90325_73549
  · exact context_14_90326_73564
  · exact context_14_90327_73577

theorem selected_cut_02239 : selected 8 ⟨73609, by decide⟩
    (prefixPartial 13 22582) = some ⟨13, 2, 0, 73609, 22582, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_22582_73609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22582 ⟨73609, by decide⟩ :=
  accepted_of_selected 13 22582 ⟨73609, by decide⟩ ⟨13, 2, 0, 73609, 22582, 2601, 16384⟩
    (by decide) selected_cut_02239

theorem selected_cut_02240 : selected 8 ⟨73621, by decide⟩
    (prefixPartial 13 22583) = some ⟨13, 2, 0, 73621, 22583, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_22583_73621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22583 ⟨73621, by decide⟩ :=
  accepted_of_selected 13 22583 ⟨73621, by decide⟩ ⟨13, 2, 0, 73621, 22583, 1377, 16384⟩
    (by decide) selected_cut_02240

theorem unmarked_context_12_5645_73622 : frontier 9 ⟨73622, by decide⟩
    (prefixCache 12 5645) (prefixPartial 12 5645) = false := by
  decide +kernel

theorem node_context_12_5645_73622 : EJMOriginalGlobalDAGData.nodes 9 ⟨73622, by decide⟩ =
    .split (coordinate 12) (![⟨73511, by decide⟩,⟨73578, by decide⟩,⟨73609, by decide⟩,⟨73621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5645_73622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5645 ⟨73622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5645
    ⟨73622, by decide⟩ (by decide) (![⟨73511, by decide⟩,⟨73578, by decide⟩,⟨73609, by decide⟩,⟨73621, by decide⟩]) unmarked_context_12_5645_73622 node_context_12_5645_73622
  intro a
  fin_cases a
  · exact context_13_22580_73511
  · exact context_13_22581_73578
  · exact context_13_22582_73609
  · exact context_13_22583_73621

theorem selected_cut_02241 : selected 8 ⟨73688, by decide⟩
    (prefixPartial 13 22584) = some ⟨13, 2, 0, 73688, 22584, 3981, 16384⟩ := by
  decide +kernel

theorem context_13_22584_73688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22584 ⟨73688, by decide⟩ :=
  accepted_of_selected 13 22584 ⟨73688, by decide⟩ ⟨13, 2, 0, 73688, 22584, 3981, 16384⟩
    (by decide) selected_cut_02241

theorem selected_cut_02242 : selected 8 ⟨73730, by decide⟩
    (prefixPartial 13 22585) = some ⟨13, 2, 0, 73730, 22585, 3945, 16384⟩ := by
  decide +kernel

theorem context_13_22585_73730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22585 ⟨73730, by decide⟩ :=
  accepted_of_selected 13 22585 ⟨73730, by decide⟩ ⟨13, 2, 0, 73730, 22585, 3945, 16384⟩
    (by decide) selected_cut_02242

theorem selected_cut_02243 : selected 8 ⟨73756, by decide⟩
    (prefixPartial 13 22586) = some ⟨13, 2, 0, 73756, 22586, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_22586_73756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22586 ⟨73756, by decide⟩ :=
  accepted_of_selected 13 22586 ⟨73756, by decide⟩ ⟨13, 2, 0, 73756, 22586, 2257, 16384⟩
    (by decide) selected_cut_02243

theorem selected_cut_02244 : selected 8 ⟨73768, by decide⟩
    (prefixPartial 13 22587) = some ⟨13, 2, 0, 73768, 22587, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_22587_73768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22587 ⟨73768, by decide⟩ :=
  accepted_of_selected 13 22587 ⟨73768, by decide⟩ ⟨13, 2, 0, 73768, 22587, 1281, 16384⟩
    (by decide) selected_cut_02244

theorem unmarked_context_12_5646_73769 : frontier 9 ⟨73769, by decide⟩
    (prefixCache 12 5646) (prefixPartial 12 5646) = false := by
  decide +kernel

theorem node_context_12_5646_73769 : EJMOriginalGlobalDAGData.nodes 9 ⟨73769, by decide⟩ =
    .split (coordinate 12) (![⟨73688, by decide⟩,⟨73730, by decide⟩,⟨73756, by decide⟩,⟨73768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5646_73769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5646 ⟨73769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5646
    ⟨73769, by decide⟩ (by decide) (![⟨73688, by decide⟩,⟨73730, by decide⟩,⟨73756, by decide⟩,⟨73768, by decide⟩]) unmarked_context_12_5646_73769 node_context_12_5646_73769
  intro a
  fin_cases a
  · exact context_13_22584_73688
  · exact context_13_22585_73730
  · exact context_13_22586_73756
  · exact context_13_22587_73768

theorem selected_cut_02245 : selected 7 ⟨73773, by decide⟩
    (prefixPartial 14 90352) = some ⟨14, 2, 0, 73773, 90352, 161, 4096⟩ := by
  decide +kernel

theorem context_14_90352_73773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90352 ⟨73773, by decide⟩ :=
  accepted_of_selected 14 90352 ⟨73773, by decide⟩ ⟨14, 2, 0, 73773, 90352, 161, 4096⟩
    (by decide) selected_cut_02245

theorem selected_cut_02246 : selected 7 ⟨73795, by decide⟩
    (prefixPartial 14 90353) = some ⟨14, 2, 0, 73795, 90353, 1641, 4096⟩ := by
  decide +kernel

theorem context_14_90353_73795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90353 ⟨73795, by decide⟩ :=
  accepted_of_selected 14 90353 ⟨73795, by decide⟩ ⟨14, 2, 0, 73795, 90353, 1641, 4096⟩
    (by decide) selected_cut_02246

theorem selected_cut_02247 : selected 7 ⟨73814, by decide⟩
    (prefixPartial 14 90354) = some ⟨14, 2, 0, 73814, 90354, 1493, 4096⟩ := by
  decide +kernel

theorem context_14_90354_73814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90354 ⟨73814, by decide⟩ :=
  accepted_of_selected 14 90354 ⟨73814, by decide⟩ ⟨14, 2, 0, 73814, 90354, 1493, 4096⟩
    (by decide) selected_cut_02247

theorem selected_cut_02248 : selected 7 ⟨73834, by decide⟩
    (prefixPartial 14 90355) = some ⟨14, 2, 0, 73834, 90355, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_90355_73834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90355 ⟨73834, by decide⟩ :=
  accepted_of_selected 14 90355 ⟨73834, by decide⟩ ⟨14, 2, 0, 73834, 90355, 1297, 4096⟩
    (by decide) selected_cut_02248

theorem unmarked_context_13_22588_73835 : frontier 8 ⟨73835, by decide⟩
    (prefixCache 13 22588) (prefixPartial 13 22588) = false := by
  decide +kernel

theorem node_context_13_22588_73835 : EJMOriginalGlobalDAGData.nodes 8 ⟨73835, by decide⟩ =
    .split (coordinate 13) (![⟨73773, by decide⟩,⟨73795, by decide⟩,⟨73814, by decide⟩,⟨73834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22588_73835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22588 ⟨73835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22588
    ⟨73835, by decide⟩ (by decide) (![⟨73773, by decide⟩,⟨73795, by decide⟩,⟨73814, by decide⟩,⟨73834, by decide⟩]) unmarked_context_13_22588_73835 node_context_13_22588_73835
  intro a
  fin_cases a
  · exact context_14_90352_73773
  · exact context_14_90353_73795
  · exact context_14_90354_73814
  · exact context_14_90355_73834

theorem selected_cut_02249 : selected 7 ⟨73846, by decide⟩
    (prefixPartial 14 90356) = some ⟨14, 2, 0, 73846, 90356, 957, 4096⟩ := by
  decide +kernel

theorem context_14_90356_73846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90356 ⟨73846, by decide⟩ :=
  accepted_of_selected 14 90356 ⟨73846, by decide⟩ ⟨14, 2, 0, 73846, 90356, 957, 4096⟩
    (by decide) selected_cut_02249

theorem selected_cut_02250 : selected 7 ⟨73863, by decide⟩
    (prefixPartial 14 90357) = some ⟨14, 2, 0, 73863, 90357, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_90357_73863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90357 ⟨73863, by decide⟩ :=
  accepted_of_selected 14 90357 ⟨73863, by decide⟩ ⟨14, 2, 0, 73863, 90357, 1217, 4096⟩
    (by decide) selected_cut_02250

theorem selected_cut_02251 : selected 7 ⟨73879, by decide⟩
    (prefixPartial 14 90358) = some ⟨14, 2, 0, 73879, 90358, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_90358_73879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90358 ⟨73879, by decide⟩ :=
  accepted_of_selected 14 90358 ⟨73879, by decide⟩ ⟨14, 2, 0, 73879, 90358, 1073, 4096⟩
    (by decide) selected_cut_02251

theorem selected_cut_02252 : selected 7 ⟨73894, by decide⟩
    (prefixPartial 14 90359) = some ⟨14, 2, 0, 73894, 90359, 957, 4096⟩ := by
  decide +kernel

theorem context_14_90359_73894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90359 ⟨73894, by decide⟩ :=
  accepted_of_selected 14 90359 ⟨73894, by decide⟩ ⟨14, 2, 0, 73894, 90359, 957, 4096⟩
    (by decide) selected_cut_02252

theorem unmarked_context_13_22589_73895 : frontier 8 ⟨73895, by decide⟩
    (prefixCache 13 22589) (prefixPartial 13 22589) = false := by
  decide +kernel

theorem node_context_13_22589_73895 : EJMOriginalGlobalDAGData.nodes 8 ⟨73895, by decide⟩ =
    .split (coordinate 13) (![⟨73846, by decide⟩,⟨73863, by decide⟩,⟨73879, by decide⟩,⟨73894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22589_73895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22589 ⟨73895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22589
    ⟨73895, by decide⟩ (by decide) (![⟨73846, by decide⟩,⟨73863, by decide⟩,⟨73879, by decide⟩,⟨73894, by decide⟩]) unmarked_context_13_22589_73895 node_context_13_22589_73895
  intro a
  fin_cases a
  · exact context_14_90356_73846
  · exact context_14_90357_73863
  · exact context_14_90358_73879
  · exact context_14_90359_73894

theorem selected_cut_02253 : selected 8 ⟨73926, by decide⟩
    (prefixPartial 13 22590) = some ⟨13, 2, 0, 73926, 22590, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_22590_73926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22590 ⟨73926, by decide⟩ :=
  accepted_of_selected 13 22590 ⟨73926, by decide⟩ ⟨13, 2, 0, 73926, 22590, 2513, 16384⟩
    (by decide) selected_cut_02253

theorem selected_cut_02254 : selected 8 ⟨73940, by decide⟩
    (prefixPartial 13 22591) = some ⟨13, 2, 0, 73940, 22591, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_22591_73940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22591 ⟨73940, by decide⟩ :=
  accepted_of_selected 13 22591 ⟨73940, by decide⟩ ⟨13, 2, 0, 73940, 22591, 1297, 16384⟩
    (by decide) selected_cut_02254

theorem unmarked_context_12_5647_73941 : frontier 9 ⟨73941, by decide⟩
    (prefixCache 12 5647) (prefixPartial 12 5647) = false := by
  decide +kernel

theorem node_context_12_5647_73941 : EJMOriginalGlobalDAGData.nodes 9 ⟨73941, by decide⟩ =
    .split (coordinate 12) (![⟨73835, by decide⟩,⟨73895, by decide⟩,⟨73926, by decide⟩,⟨73940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5647_73941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5647 ⟨73941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5647
    ⟨73941, by decide⟩ (by decide) (![⟨73835, by decide⟩,⟨73895, by decide⟩,⟨73926, by decide⟩,⟨73940, by decide⟩]) unmarked_context_12_5647_73941 node_context_12_5647_73941
  intro a
  fin_cases a
  · exact context_13_22588_73835
  · exact context_13_22589_73895
  · exact context_13_22590_73926
  · exact context_13_22591_73940

theorem unmarked_context_11_1411_73942 : frontier 10 ⟨73942, by decide⟩
    (prefixCache 11 1411) (prefixPartial 11 1411) = false := by
  decide +kernel

theorem node_context_11_1411_73942 : EJMOriginalGlobalDAGData.nodes 10 ⟨73942, by decide⟩ =
    .split (coordinate 11) (![⟨73442, by decide⟩,⟨73622, by decide⟩,⟨73769, by decide⟩,⟨73941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1411_73942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1411 ⟨73942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1411
    ⟨73942, by decide⟩ (by decide) (![⟨73442, by decide⟩,⟨73622, by decide⟩,⟨73769, by decide⟩,⟨73941, by decide⟩]) unmarked_context_11_1411_73942 node_context_11_1411_73942
  intro a
  fin_cases a
  · exact context_12_5644_73442
  · exact context_12_5645_73622
  · exact context_12_5646_73769
  · exact context_12_5647_73941

theorem unmarked_context_10_352_73943 : frontier 11 ⟨73943, by decide⟩
    (prefixCache 10 352) (prefixPartial 10 352) = false := by
  decide +kernel

theorem node_context_10_352_73943 : EJMOriginalGlobalDAGData.nodes 11 ⟨73943, by decide⟩ =
    .split (coordinate 10) (![⟨71118, by decide⟩,⟨72000, by decide⟩,⟨73153, by decide⟩,⟨73942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_352_73943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 352 ⟨73943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 352
    ⟨73943, by decide⟩ (by decide) (![⟨71118, by decide⟩,⟨72000, by decide⟩,⟨73153, by decide⟩,⟨73942, by decide⟩]) unmarked_context_10_352_73943 node_context_10_352_73943
  intro a
  fin_cases a
  · exact context_11_1408_71118
  · exact context_11_1409_72000
  · exact context_11_1410_73153
  · exact context_11_1411_73942

theorem selected_cut_02255 : selected 8 ⟨73986, by decide⟩
    (prefixPartial 13 22592) = some ⟨13, 2, 0, 73986, 22592, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_22592_73986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22592 ⟨73986, by decide⟩ :=
  accepted_of_selected 13 22592 ⟨73986, by decide⟩ ⟨13, 2, 0, 73986, 22592, 2745, 16384⟩
    (by decide) selected_cut_02255

theorem selected_cut_02256 : selected 8 ⟨74013, by decide⟩
    (prefixPartial 13 22593) = some ⟨13, 2, 0, 74013, 22593, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_22593_74013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22593 ⟨74013, by decide⟩ :=
  accepted_of_selected 13 22593 ⟨74013, by decide⟩ ⟨13, 2, 0, 74013, 22593, 2685, 16384⟩
    (by decide) selected_cut_02256

theorem selected_cut_02257 : selected 8 ⟨74040, by decide⟩
    (prefixPartial 13 22594) = some ⟨13, 2, 0, 74040, 22594, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_22594_74040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22594 ⟨74040, by decide⟩ :=
  accepted_of_selected 13 22594 ⟨74040, by decide⟩ ⟨13, 2, 0, 74040, 22594, 2373, 16384⟩
    (by decide) selected_cut_02257

theorem selected_cut_02258 : selected 8 ⟨74050, by decide⟩
    (prefixPartial 13 22595) = some ⟨13, 2, 0, 74050, 22595, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_22595_74050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22595 ⟨74050, by decide⟩ :=
  accepted_of_selected 13 22595 ⟨74050, by decide⟩ ⟨13, 2, 0, 74050, 22595, 1185, 16384⟩
    (by decide) selected_cut_02258

theorem unmarked_context_12_5648_74051 : frontier 9 ⟨74051, by decide⟩
    (prefixCache 12 5648) (prefixPartial 12 5648) = false := by
  decide +kernel

theorem node_context_12_5648_74051 : EJMOriginalGlobalDAGData.nodes 9 ⟨74051, by decide⟩ =
    .split (coordinate 12) (![⟨73986, by decide⟩,⟨74013, by decide⟩,⟨74040, by decide⟩,⟨74050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5648_74051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5648 ⟨74051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5648
    ⟨74051, by decide⟩ (by decide) (![⟨73986, by decide⟩,⟨74013, by decide⟩,⟨74040, by decide⟩,⟨74050, by decide⟩]) unmarked_context_12_5648_74051 node_context_12_5648_74051
  intro a
  fin_cases a
  · exact context_13_22592_73986
  · exact context_13_22593_74013
  · exact context_13_22594_74040
  · exact context_13_22595_74050

theorem selected_cut_02259 : selected 8 ⟨74087, by decide⟩
    (prefixPartial 13 22596) = some ⟨13, 2, 0, 74087, 22596, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_22596_74087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22596 ⟨74087, by decide⟩ :=
  accepted_of_selected 13 22596 ⟨74087, by decide⟩ ⟨13, 2, 0, 74087, 22596, 2349, 16384⟩
    (by decide) selected_cut_02259

theorem selected_cut_02260 : selected 8 ⟨74112, by decide⟩
    (prefixPartial 13 22597) = some ⟨13, 2, 0, 74112, 22597, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_22597_74112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22597 ⟨74112, by decide⟩ :=
  accepted_of_selected 13 22597 ⟨74112, by decide⟩ ⟨13, 2, 0, 74112, 22597, 2033, 16384⟩
    (by decide) selected_cut_02260

theorem selected_cut_02261 : selected 8 ⟨74136, by decide⟩
    (prefixPartial 13 22598) = some ⟨13, 2, 0, 74136, 22598, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_22598_74136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22598 ⟨74136, by decide⟩ :=
  accepted_of_selected 13 22598 ⟨74136, by decide⟩ ⟨13, 2, 0, 74136, 22598, 1625, 16384⟩
    (by decide) selected_cut_02261

theorem selected_cut_02262 : selected 8 ⟨74147, by decide⟩
    (prefixPartial 13 22599) = some ⟨13, 2, 0, 74147, 22599, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_22599_74147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22599 ⟨74147, by decide⟩ :=
  accepted_of_selected 13 22599 ⟨74147, by decide⟩ ⟨13, 2, 0, 74147, 22599, 1053, 16384⟩
    (by decide) selected_cut_02262

theorem unmarked_context_12_5649_74148 : frontier 9 ⟨74148, by decide⟩
    (prefixCache 12 5649) (prefixPartial 12 5649) = false := by
  decide +kernel

theorem node_context_12_5649_74148 : EJMOriginalGlobalDAGData.nodes 9 ⟨74148, by decide⟩ =
    .split (coordinate 12) (![⟨74087, by decide⟩,⟨74112, by decide⟩,⟨74136, by decide⟩,⟨74147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5649_74148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5649 ⟨74148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5649
    ⟨74148, by decide⟩ (by decide) (![⟨74087, by decide⟩,⟨74112, by decide⟩,⟨74136, by decide⟩,⟨74147, by decide⟩]) unmarked_context_12_5649_74148 node_context_12_5649_74148
  intro a
  fin_cases a
  · exact context_13_22596_74087
  · exact context_13_22597_74112
  · exact context_13_22598_74136
  · exact context_13_22599_74147

theorem selected_cut_02263 : selected 8 ⟨74184, by decide⟩
    (prefixPartial 13 22600) = some ⟨13, 2, 0, 74184, 22600, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_22600_74184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22600 ⟨74184, by decide⟩ :=
  accepted_of_selected 13 22600 ⟨74184, by decide⟩ ⟨13, 2, 0, 74184, 22600, 2093, 16384⟩
    (by decide) selected_cut_02263

theorem selected_cut_02264 : selected 8 ⟨74210, by decide⟩
    (prefixPartial 13 22601) = some ⟨13, 2, 0, 74210, 22601, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_22601_74210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22601 ⟨74210, by decide⟩ :=
  accepted_of_selected 13 22601 ⟨74210, by decide⟩ ⟨13, 2, 0, 74210, 22601, 2045, 16384⟩
    (by decide) selected_cut_02264

theorem selected_cut_02265 : selected 8 ⟨74233, by decide⟩
    (prefixPartial 13 22602) = some ⟨13, 2, 0, 74233, 22602, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_22602_74233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22602 ⟨74233, by decide⟩ :=
  accepted_of_selected 13 22602 ⟨74233, by decide⟩ ⟨13, 2, 0, 74233, 22602, 1541, 16384⟩
    (by decide) selected_cut_02265

theorem selected_cut_02266 : selected 8 ⟨74241, by decide⟩
    (prefixPartial 13 22603) = some ⟨13, 2, 0, 74241, 22603, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_22603_74241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22603 ⟨74241, by decide⟩ :=
  accepted_of_selected 13 22603 ⟨74241, by decide⟩ ⟨13, 2, 0, 74241, 22603, 1065, 16384⟩
    (by decide) selected_cut_02266

theorem unmarked_context_12_5650_74242 : frontier 9 ⟨74242, by decide⟩
    (prefixCache 12 5650) (prefixPartial 12 5650) = false := by
  decide +kernel

theorem node_context_12_5650_74242 : EJMOriginalGlobalDAGData.nodes 9 ⟨74242, by decide⟩ =
    .split (coordinate 12) (![⟨74184, by decide⟩,⟨74210, by decide⟩,⟨74233, by decide⟩,⟨74241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5650_74242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5650 ⟨74242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5650
    ⟨74242, by decide⟩ (by decide) (![⟨74184, by decide⟩,⟨74210, by decide⟩,⟨74233, by decide⟩,⟨74241, by decide⟩]) unmarked_context_12_5650_74242 node_context_12_5650_74242
  intro a
  fin_cases a
  · exact context_13_22600_74184
  · exact context_13_22601_74210
  · exact context_13_22602_74233
  · exact context_13_22603_74241

theorem selected_cut_02267 : selected 8 ⟨74281, by decide⟩
    (prefixPartial 13 22604) = some ⟨13, 2, 0, 74281, 22604, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_22604_74281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22604 ⟨74281, by decide⟩ :=
  accepted_of_selected 13 22604 ⟨74281, by decide⟩ ⟨13, 2, 0, 74281, 22604, 2521, 16384⟩
    (by decide) selected_cut_02267

theorem selected_cut_02268 : selected 8 ⟨74317, by decide⟩
    (prefixPartial 13 22605) = some ⟨13, 2, 0, 74317, 22605, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_22605_74317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22605 ⟨74317, by decide⟩ :=
  accepted_of_selected 13 22605 ⟨74317, by decide⟩ ⟨13, 2, 0, 74317, 22605, 2185, 16384⟩
    (by decide) selected_cut_02268

theorem selected_cut_02269 : selected 8 ⟨74343, by decide⟩
    (prefixPartial 13 22606) = some ⟨13, 2, 0, 74343, 22606, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_22606_74343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22606 ⟨74343, by decide⟩ :=
  accepted_of_selected 13 22606 ⟨74343, by decide⟩ ⟨13, 2, 0, 74343, 22606, 1793, 16384⟩
    (by decide) selected_cut_02269

theorem selected_cut_02270 : selected 8 ⟨74353, by decide⟩
    (prefixPartial 13 22607) = some ⟨13, 2, 0, 74353, 22607, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_22607_74353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22607 ⟨74353, by decide⟩ :=
  accepted_of_selected 13 22607 ⟨74353, by decide⟩ ⟨13, 2, 0, 74353, 22607, 1081, 16384⟩
    (by decide) selected_cut_02270

theorem unmarked_context_12_5651_74354 : frontier 9 ⟨74354, by decide⟩
    (prefixCache 12 5651) (prefixPartial 12 5651) = false := by
  decide +kernel

theorem node_context_12_5651_74354 : EJMOriginalGlobalDAGData.nodes 9 ⟨74354, by decide⟩ =
    .split (coordinate 12) (![⟨74281, by decide⟩,⟨74317, by decide⟩,⟨74343, by decide⟩,⟨74353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5651_74354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5651 ⟨74354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5651
    ⟨74354, by decide⟩ (by decide) (![⟨74281, by decide⟩,⟨74317, by decide⟩,⟨74343, by decide⟩,⟨74353, by decide⟩]) unmarked_context_12_5651_74354 node_context_12_5651_74354
  intro a
  fin_cases a
  · exact context_13_22604_74281
  · exact context_13_22605_74317
  · exact context_13_22606_74343
  · exact context_13_22607_74353

theorem unmarked_context_11_1412_74355 : frontier 10 ⟨74355, by decide⟩
    (prefixCache 11 1412) (prefixPartial 11 1412) = false := by
  decide +kernel

theorem node_context_11_1412_74355 : EJMOriginalGlobalDAGData.nodes 10 ⟨74355, by decide⟩ =
    .split (coordinate 11) (![⟨74051, by decide⟩,⟨74148, by decide⟩,⟨74242, by decide⟩,⟨74354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1412_74355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1412 ⟨74355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1412
    ⟨74355, by decide⟩ (by decide) (![⟨74051, by decide⟩,⟨74148, by decide⟩,⟨74242, by decide⟩,⟨74354, by decide⟩]) unmarked_context_11_1412_74355 node_context_11_1412_74355
  intro a
  fin_cases a
  · exact context_12_5648_74051
  · exact context_12_5649_74148
  · exact context_12_5650_74242
  · exact context_12_5651_74354

theorem selected_cut_02271 : selected 7 ⟨1739, by decide⟩
    (prefixPartial 14 90432) = some ⟨14, 1, 0, 1739, 90432, 1, 4096⟩ := by
  decide +kernel

theorem context_14_90432_1739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90432 ⟨1739, by decide⟩ :=
  accepted_of_selected 14 90432 ⟨1739, by decide⟩ ⟨14, 1, 0, 1739, 90432, 1, 4096⟩
    (by decide) selected_cut_02271

theorem selected_cut_02272 : selected 7 ⟨74376, by decide⟩
    (prefixPartial 14 90433) = some ⟨14, 2, 0, 74376, 90433, 1477, 4096⟩ := by
  decide +kernel

theorem context_14_90433_74376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90433 ⟨74376, by decide⟩ :=
  accepted_of_selected 14 90433 ⟨74376, by decide⟩ ⟨14, 2, 0, 74376, 90433, 1477, 4096⟩
    (by decide) selected_cut_02272

theorem selected_cut_02273 : selected 7 ⟨74411, by decide⟩
    (prefixPartial 14 90434) = some ⟨14, 2, 0, 74411, 90434, 1993, 4096⟩ := by
  decide +kernel

theorem context_14_90434_74411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90434 ⟨74411, by decide⟩ :=
  accepted_of_selected 14 90434 ⟨74411, by decide⟩ ⟨14, 2, 0, 74411, 90434, 1993, 4096⟩
    (by decide) selected_cut_02273

theorem selected_cut_02274 : selected 7 ⟨74431, by decide⟩
    (prefixPartial 14 90435) = some ⟨14, 2, 0, 74431, 90435, 1881, 4096⟩ := by
  decide +kernel

theorem context_14_90435_74431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90435 ⟨74431, by decide⟩ :=
  accepted_of_selected 14 90435 ⟨74431, by decide⟩ ⟨14, 2, 0, 74431, 90435, 1881, 4096⟩
    (by decide) selected_cut_02274

theorem unmarked_context_13_22608_74432 : frontier 8 ⟨74432, by decide⟩
    (prefixCache 13 22608) (prefixPartial 13 22608) = false := by
  decide +kernel

theorem node_context_13_22608_74432 : EJMOriginalGlobalDAGData.nodes 8 ⟨74432, by decide⟩ =
    .split (coordinate 13) (![⟨1739, by decide⟩,⟨74376, by decide⟩,⟨74411, by decide⟩,⟨74431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22608_74432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22608 ⟨74432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22608
    ⟨74432, by decide⟩ (by decide) (![⟨1739, by decide⟩,⟨74376, by decide⟩,⟨74411, by decide⟩,⟨74431, by decide⟩]) unmarked_context_13_22608_74432 node_context_13_22608_74432
  intro a
  fin_cases a
  · exact context_14_90432_1739
  · exact context_14_90433_74376
  · exact context_14_90434_74411
  · exact context_14_90435_74431

theorem selected_cut_02275 : selected 7 ⟨74455, by decide⟩
    (prefixPartial 14 90436) = some ⟨14, 2, 0, 74455, 90436, 1601, 4096⟩ := by
  decide +kernel

theorem context_14_90436_74455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90436 ⟨74455, by decide⟩ :=
  accepted_of_selected 14 90436 ⟨74455, by decide⟩ ⟨14, 2, 0, 74455, 90436, 1601, 4096⟩
    (by decide) selected_cut_02275

theorem selected_cut_02276 : selected 7 ⟨74481, by decide⟩
    (prefixPartial 14 90437) = some ⟨14, 2, 0, 74481, 90437, 1929, 4096⟩ := by
  decide +kernel

theorem context_14_90437_74481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90437 ⟨74481, by decide⟩ :=
  accepted_of_selected 14 90437 ⟨74481, by decide⟩ ⟨14, 2, 0, 74481, 90437, 1929, 4096⟩
    (by decide) selected_cut_02276

theorem selected_cut_02277 : selected 7 ⟨74512, by decide⟩
    (prefixPartial 14 90438) = some ⟨14, 2, 0, 74512, 90438, 1409, 4096⟩ := by
  decide +kernel

theorem context_14_90438_74512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90438 ⟨74512, by decide⟩ :=
  accepted_of_selected 14 90438 ⟨74512, by decide⟩ ⟨14, 2, 0, 74512, 90438, 1409, 4096⟩
    (by decide) selected_cut_02277

theorem selected_cut_02278 : selected 7 ⟨74534, by decide⟩
    (prefixPartial 14 90439) = some ⟨14, 2, 0, 74534, 90439, 1389, 4096⟩ := by
  decide +kernel

theorem context_14_90439_74534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90439 ⟨74534, by decide⟩ :=
  accepted_of_selected 14 90439 ⟨74534, by decide⟩ ⟨14, 2, 0, 74534, 90439, 1389, 4096⟩
    (by decide) selected_cut_02278

theorem unmarked_context_13_22609_74535 : frontier 8 ⟨74535, by decide⟩
    (prefixCache 13 22609) (prefixPartial 13 22609) = false := by
  decide +kernel

theorem node_context_13_22609_74535 : EJMOriginalGlobalDAGData.nodes 8 ⟨74535, by decide⟩ =
    .split (coordinate 13) (![⟨74455, by decide⟩,⟨74481, by decide⟩,⟨74512, by decide⟩,⟨74534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22609_74535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22609 ⟨74535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22609
    ⟨74535, by decide⟩ (by decide) (![⟨74455, by decide⟩,⟨74481, by decide⟩,⟨74512, by decide⟩,⟨74534, by decide⟩]) unmarked_context_13_22609_74535 node_context_13_22609_74535
  intro a
  fin_cases a
  · exact context_14_90436_74455
  · exact context_14_90437_74481
  · exact context_14_90438_74512
  · exact context_14_90439_74534

theorem selected_cut_02279 : selected 8 ⟨74608, by decide⟩
    (prefixPartial 13 22610) = some ⟨13, 2, 0, 74608, 22610, 3921, 16384⟩ := by
  decide +kernel

theorem context_13_22610_74608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22610 ⟨74608, by decide⟩ :=
  accepted_of_selected 13 22610 ⟨74608, by decide⟩ ⟨13, 2, 0, 74608, 22610, 3921, 16384⟩
    (by decide) selected_cut_02279

theorem selected_cut_02280 : selected 8 ⟨74653, by decide⟩
    (prefixPartial 13 22611) = some ⟨13, 2, 0, 74653, 22611, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_22611_74653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22611 ⟨74653, by decide⟩ :=
  accepted_of_selected 13 22611 ⟨74653, by decide⟩ ⟨13, 2, 0, 74653, 22611, 2025, 16384⟩
    (by decide) selected_cut_02280

theorem unmarked_context_12_5652_74654 : frontier 9 ⟨74654, by decide⟩
    (prefixCache 12 5652) (prefixPartial 12 5652) = false := by
  decide +kernel

theorem node_context_12_5652_74654 : EJMOriginalGlobalDAGData.nodes 9 ⟨74654, by decide⟩ =
    .split (coordinate 12) (![⟨74432, by decide⟩,⟨74535, by decide⟩,⟨74608, by decide⟩,⟨74653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5652_74654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5652 ⟨74654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5652
    ⟨74654, by decide⟩ (by decide) (![⟨74432, by decide⟩,⟨74535, by decide⟩,⟨74608, by decide⟩,⟨74653, by decide⟩]) unmarked_context_12_5652_74654 node_context_12_5652_74654
  intro a
  fin_cases a
  · exact context_13_22608_74432
  · exact context_13_22609_74535
  · exact context_13_22610_74608
  · exact context_13_22611_74653

theorem selected_cut_02281 : selected 8 ⟨74704, by decide⟩
    (prefixPartial 13 22612) = some ⟨13, 2, 0, 74704, 22612, 3721, 16384⟩ := by
  decide +kernel

theorem context_13_22612_74704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22612 ⟨74704, by decide⟩ :=
  accepted_of_selected 13 22612 ⟨74704, by decide⟩ ⟨13, 2, 0, 74704, 22612, 3721, 16384⟩
    (by decide) selected_cut_02281

theorem selected_cut_02282 : selected 8 ⟨74765, by decide⟩
    (prefixPartial 13 22613) = some ⟨13, 2, 0, 74765, 22613, 4077, 16384⟩ := by
  decide +kernel

theorem context_13_22613_74765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22613 ⟨74765, by decide⟩ :=
  accepted_of_selected 13 22613 ⟨74765, by decide⟩ ⟨13, 2, 0, 74765, 22613, 4077, 16384⟩
    (by decide) selected_cut_02282

theorem selected_cut_02283 : selected 8 ⟨74801, by decide⟩
    (prefixPartial 13 22614) = some ⟨13, 2, 0, 74801, 22614, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_22614_74801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22614 ⟨74801, by decide⟩ :=
  accepted_of_selected 13 22614 ⟨74801, by decide⟩ ⟨13, 2, 0, 74801, 22614, 2657, 16384⟩
    (by decide) selected_cut_02283

theorem selected_cut_02284 : selected 8 ⟨74827, by decide⟩
    (prefixPartial 13 22615) = some ⟨13, 2, 0, 74827, 22615, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_22615_74827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22615 ⟨74827, by decide⟩ :=
  accepted_of_selected 13 22615 ⟨74827, by decide⟩ ⟨13, 2, 0, 74827, 22615, 1517, 16384⟩
    (by decide) selected_cut_02284

theorem unmarked_context_12_5653_74828 : frontier 9 ⟨74828, by decide⟩
    (prefixCache 12 5653) (prefixPartial 12 5653) = false := by
  decide +kernel

theorem node_context_12_5653_74828 : EJMOriginalGlobalDAGData.nodes 9 ⟨74828, by decide⟩ =
    .split (coordinate 12) (![⟨74704, by decide⟩,⟨74765, by decide⟩,⟨74801, by decide⟩,⟨74827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5653_74828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5653 ⟨74828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5653
    ⟨74828, by decide⟩ (by decide) (![⟨74704, by decide⟩,⟨74765, by decide⟩,⟨74801, by decide⟩,⟨74827, by decide⟩]) unmarked_context_12_5653_74828 node_context_12_5653_74828
  intro a
  fin_cases a
  · exact context_13_22612_74704
  · exact context_13_22613_74765
  · exact context_13_22614_74801
  · exact context_13_22615_74827

theorem selected_cut_02285 : selected 8 ⟨74873, by decide⟩
    (prefixPartial 13 22616) = some ⟨13, 2, 0, 74873, 22616, 3353, 16384⟩ := by
  decide +kernel

theorem context_13_22616_74873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22616 ⟨74873, by decide⟩ :=
  accepted_of_selected 13 22616 ⟨74873, by decide⟩ ⟨13, 2, 0, 74873, 22616, 3353, 16384⟩
    (by decide) selected_cut_02285

theorem selected_cut_02286 : selected 8 ⟨74923, by decide⟩
    (prefixPartial 13 22617) = some ⟨13, 2, 0, 74923, 22617, 3765, 16384⟩ := by
  decide +kernel

theorem context_13_22617_74923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22617 ⟨74923, by decide⟩ :=
  accepted_of_selected 13 22617 ⟨74923, by decide⟩ ⟨13, 2, 0, 74923, 22617, 3765, 16384⟩
    (by decide) selected_cut_02286

theorem selected_cut_02287 : selected 8 ⟨74952, by decide⟩
    (prefixPartial 13 22618) = some ⟨13, 2, 0, 74952, 22618, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_22618_74952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22618 ⟨74952, by decide⟩ :=
  accepted_of_selected 13 22618 ⟨74952, by decide⟩ ⟨13, 2, 0, 74952, 22618, 2381, 16384⟩
    (by decide) selected_cut_02287

theorem selected_cut_02288 : selected 8 ⟨74983, by decide⟩
    (prefixPartial 13 22619) = some ⟨13, 2, 0, 74983, 22619, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_22619_74983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22619 ⟨74983, by decide⟩ :=
  accepted_of_selected 13 22619 ⟨74983, by decide⟩ ⟨13, 2, 0, 74983, 22619, 1625, 16384⟩
    (by decide) selected_cut_02288

theorem unmarked_context_12_5654_74984 : frontier 9 ⟨74984, by decide⟩
    (prefixCache 12 5654) (prefixPartial 12 5654) = false := by
  decide +kernel

theorem node_context_12_5654_74984 : EJMOriginalGlobalDAGData.nodes 9 ⟨74984, by decide⟩ =
    .split (coordinate 12) (![⟨74873, by decide⟩,⟨74923, by decide⟩,⟨74952, by decide⟩,⟨74983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5654_74984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5654 ⟨74984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5654
    ⟨74984, by decide⟩ (by decide) (![⟨74873, by decide⟩,⟨74923, by decide⟩,⟨74952, by decide⟩,⟨74983, by decide⟩]) unmarked_context_12_5654_74984 node_context_12_5654_74984
  intro a
  fin_cases a
  · exact context_13_22616_74873
  · exact context_13_22617_74923
  · exact context_13_22618_74952
  · exact context_13_22619_74983

theorem selected_cut_02289 : selected 7 ⟨1739, by decide⟩
    (prefixPartial 14 90480) = some ⟨14, 1, 0, 1739, 90480, 1, 4096⟩ := by
  decide +kernel

theorem context_14_90480_1739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90480 ⟨1739, by decide⟩ :=
  accepted_of_selected 14 90480 ⟨1739, by decide⟩ ⟨14, 1, 0, 1739, 90480, 1, 4096⟩
    (by decide) selected_cut_02289

theorem selected_cut_02290 : selected 7 ⟨74995, by decide⟩
    (prefixPartial 14 90481) = some ⟨14, 2, 0, 74995, 90481, 809, 4096⟩ := by
  decide +kernel

theorem context_14_90481_74995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90481 ⟨74995, by decide⟩ :=
  accepted_of_selected 14 90481 ⟨74995, by decide⟩ ⟨14, 2, 0, 74995, 90481, 809, 4096⟩
    (by decide) selected_cut_02290

theorem selected_cut_02291 : selected 7 ⟨75018, by decide⟩
    (prefixPartial 14 90482) = some ⟨14, 2, 0, 75018, 90482, 1689, 4096⟩ := by
  decide +kernel

theorem context_14_90482_75018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90482 ⟨75018, by decide⟩ :=
  accepted_of_selected 14 90482 ⟨75018, by decide⟩ ⟨14, 2, 0, 75018, 90482, 1689, 4096⟩
    (by decide) selected_cut_02291

theorem selected_cut_02292 : selected 7 ⟨75041, by decide⟩
    (prefixPartial 14 90483) = some ⟨14, 2, 0, 75041, 90483, 1813, 4096⟩ := by
  decide +kernel

theorem context_14_90483_75041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90483 ⟨75041, by decide⟩ :=
  accepted_of_selected 14 90483 ⟨75041, by decide⟩ ⟨14, 2, 0, 75041, 90483, 1813, 4096⟩
    (by decide) selected_cut_02292

theorem unmarked_context_13_22620_75042 : frontier 8 ⟨75042, by decide⟩
    (prefixCache 13 22620) (prefixPartial 13 22620) = false := by
  decide +kernel

theorem node_context_13_22620_75042 : EJMOriginalGlobalDAGData.nodes 8 ⟨75042, by decide⟩ =
    .split (coordinate 13) (![⟨1739, by decide⟩,⟨74995, by decide⟩,⟨75018, by decide⟩,⟨75041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22620_75042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22620 ⟨75042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22620
    ⟨75042, by decide⟩ (by decide) (![⟨1739, by decide⟩,⟨74995, by decide⟩,⟨75018, by decide⟩,⟨75041, by decide⟩]) unmarked_context_13_22620_75042 node_context_13_22620_75042
  intro a
  fin_cases a
  · exact context_14_90480_1739
  · exact context_14_90481_74995
  · exact context_14_90482_75018
  · exact context_14_90483_75041

theorem selected_cut_02293 : selected 7 ⟨75053, by decide⟩
    (prefixPartial 14 90484) = some ⟨14, 2, 0, 75053, 90484, 973, 4096⟩ := by
  decide +kernel

theorem context_14_90484_75053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90484 ⟨75053, by decide⟩ :=
  accepted_of_selected 14 90484 ⟨75053, by decide⟩ ⟨14, 2, 0, 75053, 90484, 973, 4096⟩
    (by decide) selected_cut_02293

theorem selected_cut_02294 : selected 7 ⟨75076, by decide⟩
    (prefixPartial 14 90485) = some ⟨14, 2, 0, 75076, 90485, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_90485_75076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90485 ⟨75076, by decide⟩ :=
  accepted_of_selected 14 90485 ⟨75076, by decide⟩ ⟨14, 2, 0, 75076, 90485, 1321, 4096⟩
    (by decide) selected_cut_02294

theorem selected_cut_02295 : selected 7 ⟨75095, by decide⟩
    (prefixPartial 14 90486) = some ⟨14, 2, 0, 75095, 90486, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_90486_75095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90486 ⟨75095, by decide⟩ :=
  accepted_of_selected 14 90486 ⟨75095, by decide⟩ ⟨14, 2, 0, 75095, 90486, 1133, 4096⟩
    (by decide) selected_cut_02295

theorem selected_cut_02296 : selected 7 ⟨75110, by decide⟩
    (prefixPartial 14 90487) = some ⟨14, 2, 0, 75110, 90487, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_90487_75110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90487 ⟨75110, by decide⟩ :=
  accepted_of_selected 14 90487 ⟨75110, by decide⟩ ⟨14, 2, 0, 75110, 90487, 1077, 4096⟩
    (by decide) selected_cut_02296

theorem unmarked_context_13_22621_75111 : frontier 8 ⟨75111, by decide⟩
    (prefixCache 13 22621) (prefixPartial 13 22621) = false := by
  decide +kernel

theorem node_context_13_22621_75111 : EJMOriginalGlobalDAGData.nodes 8 ⟨75111, by decide⟩ =
    .split (coordinate 13) (![⟨75053, by decide⟩,⟨75076, by decide⟩,⟨75095, by decide⟩,⟨75110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22621_75111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22621 ⟨75111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22621
    ⟨75111, by decide⟩ (by decide) (![⟨75053, by decide⟩,⟨75076, by decide⟩,⟨75095, by decide⟩,⟨75110, by decide⟩]) unmarked_context_13_22621_75111 node_context_13_22621_75111
  intro a
  fin_cases a
  · exact context_14_90484_75053
  · exact context_14_90485_75076
  · exact context_14_90486_75095
  · exact context_14_90487_75110

theorem selected_cut_02297 : selected 8 ⟨75155, by decide⟩
    (prefixPartial 13 22622) = some ⟨13, 2, 0, 75155, 22622, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_22622_75155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22622 ⟨75155, by decide⟩ :=
  accepted_of_selected 13 22622 ⟨75155, by decide⟩ ⟨13, 2, 0, 75155, 22622, 3085, 16384⟩
    (by decide) selected_cut_02297

theorem selected_cut_02298 : selected 8 ⟨75182, by decide⟩
    (prefixPartial 13 22623) = some ⟨13, 2, 0, 75182, 22623, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_22623_75182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22623 ⟨75182, by decide⟩ :=
  accepted_of_selected 13 22623 ⟨75182, by decide⟩ ⟨13, 2, 0, 75182, 22623, 1553, 16384⟩
    (by decide) selected_cut_02298

theorem unmarked_context_12_5655_75183 : frontier 9 ⟨75183, by decide⟩
    (prefixCache 12 5655) (prefixPartial 12 5655) = false := by
  decide +kernel

theorem node_context_12_5655_75183 : EJMOriginalGlobalDAGData.nodes 9 ⟨75183, by decide⟩ =
    .split (coordinate 12) (![⟨75042, by decide⟩,⟨75111, by decide⟩,⟨75155, by decide⟩,⟨75182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5655_75183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5655 ⟨75183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5655
    ⟨75183, by decide⟩ (by decide) (![⟨75042, by decide⟩,⟨75111, by decide⟩,⟨75155, by decide⟩,⟨75182, by decide⟩]) unmarked_context_12_5655_75183 node_context_12_5655_75183
  intro a
  fin_cases a
  · exact context_13_22620_75042
  · exact context_13_22621_75111
  · exact context_13_22622_75155
  · exact context_13_22623_75182

theorem unmarked_context_11_1413_75184 : frontier 10 ⟨75184, by decide⟩
    (prefixCache 11 1413) (prefixPartial 11 1413) = false := by
  decide +kernel

theorem node_context_11_1413_75184 : EJMOriginalGlobalDAGData.nodes 10 ⟨75184, by decide⟩ =
    .split (coordinate 11) (![⟨74654, by decide⟩,⟨74828, by decide⟩,⟨74984, by decide⟩,⟨75183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1413_75184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1413 ⟨75184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1413
    ⟨75184, by decide⟩ (by decide) (![⟨74654, by decide⟩,⟨74828, by decide⟩,⟨74984, by decide⟩,⟨75183, by decide⟩]) unmarked_context_11_1413_75184 node_context_11_1413_75184
  intro a
  fin_cases a
  · exact context_12_5652_74654
  · exact context_12_5653_74828
  · exact context_12_5654_74984
  · exact context_12_5655_75183

theorem selected_cut_02299 : selected 8 ⟨75224, by decide⟩
    (prefixPartial 13 22624) = some ⟨13, 2, 0, 75224, 22624, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_22624_75224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22624 ⟨75224, by decide⟩ :=
  accepted_of_selected 13 22624 ⟨75224, by decide⟩ ⟨13, 2, 0, 75224, 22624, 2433, 16384⟩
    (by decide) selected_cut_02299

theorem selected_cut_02300 : selected 8 ⟨75261, by decide⟩
    (prefixPartial 13 22625) = some ⟨13, 2, 0, 75261, 22625, 3129, 16384⟩ := by
  decide +kernel

theorem context_13_22625_75261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22625 ⟨75261, by decide⟩ :=
  accepted_of_selected 13 22625 ⟨75261, by decide⟩ ⟨13, 2, 0, 75261, 22625, 3129, 16384⟩
    (by decide) selected_cut_02300

theorem selected_cut_02301 : selected 8 ⟨75290, by decide⟩
    (prefixPartial 13 22626) = some ⟨13, 2, 0, 75290, 22626, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_22626_75290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22626 ⟨75290, by decide⟩ :=
  accepted_of_selected 13 22626 ⟨75290, by decide⟩ ⟨13, 2, 0, 75290, 22626, 2377, 16384⟩
    (by decide) selected_cut_02301

theorem selected_cut_02302 : selected 8 ⟨75317, by decide⟩
    (prefixPartial 13 22627) = some ⟨13, 2, 0, 75317, 22627, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_22627_75317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22627 ⟨75317, by decide⟩ :=
  accepted_of_selected 13 22627 ⟨75317, by decide⟩ ⟨13, 2, 0, 75317, 22627, 1373, 16384⟩
    (by decide) selected_cut_02302

theorem unmarked_context_12_5656_75318 : frontier 9 ⟨75318, by decide⟩
    (prefixCache 12 5656) (prefixPartial 12 5656) = false := by
  decide +kernel

theorem node_context_12_5656_75318 : EJMOriginalGlobalDAGData.nodes 9 ⟨75318, by decide⟩ =
    .split (coordinate 12) (![⟨75224, by decide⟩,⟨75261, by decide⟩,⟨75290, by decide⟩,⟨75317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5656_75318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5656 ⟨75318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5656
    ⟨75318, by decide⟩ (by decide) (![⟨75224, by decide⟩,⟨75261, by decide⟩,⟨75290, by decide⟩,⟨75317, by decide⟩]) unmarked_context_12_5656_75318 node_context_12_5656_75318
  intro a
  fin_cases a
  · exact context_13_22624_75224
  · exact context_13_22625_75261
  · exact context_13_22626_75290
  · exact context_13_22627_75317

theorem selected_cut_02303 : selected 8 ⟨75361, by decide⟩
    (prefixPartial 13 22628) = some ⟨13, 2, 0, 75361, 22628, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_22628_75361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22628 ⟨75361, by decide⟩ :=
  accepted_of_selected 13 22628 ⟨75361, by decide⟩ ⟨13, 2, 0, 75361, 22628, 2273, 16384⟩
    (by decide) selected_cut_02303

theorem selected_cut_02304 : selected 8 ⟨75392, by decide⟩
    (prefixPartial 13 22629) = some ⟨13, 2, 0, 75392, 22629, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_22629_75392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22629 ⟨75392, by decide⟩ :=
  accepted_of_selected 13 22629 ⟨75392, by decide⟩ ⟨13, 2, 0, 75392, 22629, 2201, 16384⟩
    (by decide) selected_cut_02304

theorem selected_cut_02305 : selected 8 ⟨75418, by decide⟩
    (prefixPartial 13 22630) = some ⟨13, 2, 0, 75418, 22630, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_22630_75418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22630 ⟨75418, by decide⟩ :=
  accepted_of_selected 13 22630 ⟨75418, by decide⟩ ⟨13, 2, 0, 75418, 22630, 1809, 16384⟩
    (by decide) selected_cut_02305

theorem selected_cut_02306 : selected 8 ⟨75431, by decide⟩
    (prefixPartial 13 22631) = some ⟨13, 2, 0, 75431, 22631, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_22631_75431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22631 ⟨75431, by decide⟩ :=
  accepted_of_selected 13 22631 ⟨75431, by decide⟩ ⟨13, 2, 0, 75431, 22631, 1165, 16384⟩
    (by decide) selected_cut_02306

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
