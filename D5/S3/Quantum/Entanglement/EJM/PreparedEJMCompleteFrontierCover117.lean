/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover116
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_6381_301194 : frontier 10 ⟨301194, by decide⟩
    (prefixCache 11 6381) (prefixPartial 11 6381) = false := by
  decide +kernel

theorem node_context_11_6381_301194 : EJMOriginalGlobalDAGData.nodes 10 ⟨301194, by decide⟩ =
    .split (coordinate 11) (![⟨301155, by decide⟩,⟨301173, by decide⟩,⟨301184, by decide⟩,⟨301193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6381_301194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6381 ⟨301194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6381
    ⟨301194, by decide⟩ (by decide) (![⟨301155, by decide⟩,⟨301173, by decide⟩,⟨301184, by decide⟩,⟨301193, by decide⟩]) unmarked_context_11_6381_301194 node_context_11_6381_301194
  intro a
  fin_cases a
  · exact context_12_25524_301155
  · exact context_12_25525_301173
  · exact context_12_25526_301184
  · exact context_12_25527_301193

theorem selected_cut_11236 : selected 9 ⟨301205, by decide⟩
    (prefixPartial 12 25528) = some ⟨12, 2, 0, 301205, 25528, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_25528_301205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25528 ⟨301205, by decide⟩ :=
  accepted_of_selected 12 25528 ⟨301205, by decide⟩ ⟨12, 2, 0, 301205, 25528, 1201, 65536⟩
    (by decide) selected_cut_11236

theorem selected_cut_11237 : selected 9 ⟨301223, by decide⟩
    (prefixPartial 12 25529) = some ⟨12, 2, 0, 301223, 25529, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_25529_301223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25529 ⟨301223, by decide⟩ :=
  accepted_of_selected 12 25529 ⟨301223, by decide⟩ ⟨12, 2, 0, 301223, 25529, 1245, 65536⟩
    (by decide) selected_cut_11237

theorem selected_cut_11238 : selected 9 ⟨301238, by decide⟩
    (prefixPartial 12 25530) = some ⟨12, 2, 0, 301238, 25530, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_25530_301238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25530 ⟨301238, by decide⟩ :=
  accepted_of_selected 12 25530 ⟨301238, by decide⟩ ⟨12, 2, 0, 301238, 25530, 1157, 65536⟩
    (by decide) selected_cut_11238

theorem selected_cut_11239 : selected 9 ⟨301253, by decide⟩
    (prefixPartial 12 25531) = some ⟨12, 2, 0, 301253, 25531, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_25531_301253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25531 ⟨301253, by decide⟩ :=
  accepted_of_selected 12 25531 ⟨301253, by decide⟩ ⟨12, 2, 0, 301253, 25531, 1161, 65536⟩
    (by decide) selected_cut_11239

theorem unmarked_context_11_6382_301254 : frontier 10 ⟨301254, by decide⟩
    (prefixCache 11 6382) (prefixPartial 11 6382) = false := by
  decide +kernel

theorem node_context_11_6382_301254 : EJMOriginalGlobalDAGData.nodes 10 ⟨301254, by decide⟩ =
    .split (coordinate 11) (![⟨301205, by decide⟩,⟨301223, by decide⟩,⟨301238, by decide⟩,⟨301253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6382_301254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6382 ⟨301254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6382
    ⟨301254, by decide⟩ (by decide) (![⟨301205, by decide⟩,⟨301223, by decide⟩,⟨301238, by decide⟩,⟨301253, by decide⟩]) unmarked_context_11_6382_301254 node_context_11_6382_301254
  intro a
  fin_cases a
  · exact context_12_25528_301205
  · exact context_12_25529_301223
  · exact context_12_25530_301238
  · exact context_12_25531_301253

theorem selected_cut_11240 : selected 9 ⟨301268, by decide⟩
    (prefixPartial 12 25532) = some ⟨12, 2, 0, 301268, 25532, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_25532_301268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25532 ⟨301268, by decide⟩ :=
  accepted_of_selected 12 25532 ⟨301268, by decide⟩ ⟨12, 2, 0, 301268, 25532, 1049, 65536⟩
    (by decide) selected_cut_11240

theorem selected_cut_11241 : selected 9 ⟨301282, by decide⟩
    (prefixPartial 12 25533) = some ⟨12, 2, 0, 301282, 25533, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_25533_301282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25533 ⟨301282, by decide⟩ :=
  accepted_of_selected 12 25533 ⟨301282, by decide⟩ ⟨12, 2, 0, 301282, 25533, 1041, 65536⟩
    (by decide) selected_cut_11241

theorem selected_cut_11242 : selected 9 ⟨301292, by decide⟩
    (prefixPartial 12 25534) = some ⟨12, 2, 0, 301292, 25534, 993, 65536⟩ := by
  decide +kernel

theorem context_12_25534_301292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25534 ⟨301292, by decide⟩ :=
  accepted_of_selected 12 25534 ⟨301292, by decide⟩ ⟨12, 2, 0, 301292, 25534, 993, 65536⟩
    (by decide) selected_cut_11242

theorem selected_cut_11243 : selected 9 ⟨301346, by decide⟩
    (prefixPartial 12 25535) = some ⟨12, 2, 0, 301346, 25535, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_25535_301346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25535 ⟨301346, by decide⟩ :=
  accepted_of_selected 12 25535 ⟨301346, by decide⟩ ⟨12, 2, 0, 301346, 25535, 1617, 65536⟩
    (by decide) selected_cut_11243

theorem unmarked_context_11_6383_301347 : frontier 10 ⟨301347, by decide⟩
    (prefixCache 11 6383) (prefixPartial 11 6383) = false := by
  decide +kernel

theorem node_context_11_6383_301347 : EJMOriginalGlobalDAGData.nodes 10 ⟨301347, by decide⟩ =
    .split (coordinate 11) (![⟨301268, by decide⟩,⟨301282, by decide⟩,⟨301292, by decide⟩,⟨301346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6383_301347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6383 ⟨301347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6383
    ⟨301347, by decide⟩ (by decide) (![⟨301268, by decide⟩,⟨301282, by decide⟩,⟨301292, by decide⟩,⟨301346, by decide⟩]) unmarked_context_11_6383_301347 node_context_11_6383_301347
  intro a
  fin_cases a
  · exact context_12_25532_301268
  · exact context_12_25533_301282
  · exact context_12_25534_301292
  · exact context_12_25535_301346

theorem unmarked_context_10_1595_301348 : frontier 11 ⟨301348, by decide⟩
    (prefixCache 10 1595) (prefixPartial 10 1595) = false := by
  decide +kernel

theorem node_context_10_1595_301348 : EJMOriginalGlobalDAGData.nodes 11 ⟨301348, by decide⟩ =
    .split (coordinate 10) (![⟨301138, by decide⟩,⟨301194, by decide⟩,⟨301254, by decide⟩,⟨301347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1595_301348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1595 ⟨301348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1595
    ⟨301348, by decide⟩ (by decide) (![⟨301138, by decide⟩,⟨301194, by decide⟩,⟨301254, by decide⟩,⟨301347, by decide⟩]) unmarked_context_10_1595_301348 node_context_10_1595_301348
  intro a
  fin_cases a
  · exact context_11_6380_301138
  · exact context_11_6381_301194
  · exact context_11_6382_301254
  · exact context_11_6383_301347

theorem unmarked_context_9_398_301349 : frontier 12 ⟨301349, by decide⟩
    (prefixCache 9 398) (prefixPartial 9 398) = false := by
  decide +kernel

theorem node_context_9_398_301349 : EJMOriginalGlobalDAGData.nodes 12 ⟨301349, by decide⟩ =
    .split (coordinate 9) (![⟨300438, by decide⟩,⟨300826, by decide⟩,⟨301073, by decide⟩,⟨301348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_398_301349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 398 ⟨301349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 398
    ⟨301349, by decide⟩ (by decide) (![⟨300438, by decide⟩,⟨300826, by decide⟩,⟨301073, by decide⟩,⟨301348, by decide⟩]) unmarked_context_9_398_301349 node_context_9_398_301349
  intro a
  fin_cases a
  · exact context_10_1592_300438
  · exact context_10_1593_300826
  · exact context_10_1594_301073
  · exact context_10_1595_301348

theorem selected_cut_11244 : selected 10 ⟨301371, by decide⟩
    (prefixPartial 11 6384) = some ⟨11, 2, 0, 301371, 6384, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_6384_301371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6384 ⟨301371, by decide⟩ :=
  accepted_of_selected 11 6384 ⟨301371, by decide⟩ ⟨11, 2, 0, 301371, 6384, 1877, 262144⟩
    (by decide) selected_cut_11244

theorem selected_cut_11245 : selected 10 ⟨301398, by decide⟩
    (prefixPartial 11 6385) = some ⟨11, 2, 0, 301398, 6385, 2305, 262144⟩ := by
  decide +kernel

theorem context_11_6385_301398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6385 ⟨301398, by decide⟩ :=
  accepted_of_selected 11 6385 ⟨301398, by decide⟩ ⟨11, 2, 0, 301398, 6385, 2305, 262144⟩
    (by decide) selected_cut_11245

theorem selected_cut_11246 : selected 10 ⟨301419, by decide⟩
    (prefixPartial 11 6386) = some ⟨11, 2, 0, 301419, 6386, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_6386_301419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6386 ⟨301419, by decide⟩ :=
  accepted_of_selected 11 6386 ⟨301419, by decide⟩ ⟨11, 2, 0, 301419, 6386, 2157, 262144⟩
    (by decide) selected_cut_11246

theorem selected_cut_11247 : selected 10 ⟨301444, by decide⟩
    (prefixPartial 11 6387) = some ⟨11, 2, 0, 301444, 6387, 2281, 262144⟩ := by
  decide +kernel

theorem context_11_6387_301444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6387 ⟨301444, by decide⟩ :=
  accepted_of_selected 11 6387 ⟨301444, by decide⟩ ⟨11, 2, 0, 301444, 6387, 2281, 262144⟩
    (by decide) selected_cut_11247

theorem unmarked_context_10_1596_301445 : frontier 11 ⟨301445, by decide⟩
    (prefixCache 10 1596) (prefixPartial 10 1596) = false := by
  decide +kernel

theorem node_context_10_1596_301445 : EJMOriginalGlobalDAGData.nodes 11 ⟨301445, by decide⟩ =
    .split (coordinate 10) (![⟨301371, by decide⟩,⟨301398, by decide⟩,⟨301419, by decide⟩,⟨301444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1596_301445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1596 ⟨301445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1596
    ⟨301445, by decide⟩ (by decide) (![⟨301371, by decide⟩,⟨301398, by decide⟩,⟨301419, by decide⟩,⟨301444, by decide⟩]) unmarked_context_10_1596_301445 node_context_10_1596_301445
  intro a
  fin_cases a
  · exact context_11_6384_301371
  · exact context_11_6385_301398
  · exact context_11_6386_301419
  · exact context_11_6387_301444

theorem selected_cut_11248 : selected 10 ⟨301465, by decide⟩
    (prefixPartial 11 6388) = some ⟨11, 2, 0, 301465, 6388, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_6388_301465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6388 ⟨301465, by decide⟩ :=
  accepted_of_selected 11 6388 ⟨301465, by decide⟩ ⟨11, 2, 0, 301465, 6388, 1845, 262144⟩
    (by decide) selected_cut_11248

theorem selected_cut_11249 : selected 10 ⟨301486, by decide⟩
    (prefixPartial 11 6389) = some ⟨11, 2, 0, 301486, 6389, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_6389_301486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6389 ⟨301486, by decide⟩ :=
  accepted_of_selected 11 6389 ⟨301486, by decide⟩ ⟨11, 2, 0, 301486, 6389, 2113, 262144⟩
    (by decide) selected_cut_11249

theorem selected_cut_11250 : selected 10 ⟨301508, by decide⟩
    (prefixPartial 11 6390) = some ⟨11, 2, 0, 301508, 6390, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_6390_301508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6390 ⟨301508, by decide⟩ :=
  accepted_of_selected 11 6390 ⟨301508, by decide⟩ ⟨11, 2, 0, 301508, 6390, 1825, 262144⟩
    (by decide) selected_cut_11250

theorem selected_cut_11251 : selected 10 ⟨301527, by decide⟩
    (prefixPartial 11 6391) = some ⟨11, 2, 0, 301527, 6391, 1189, 262144⟩ := by
  decide +kernel

theorem context_11_6391_301527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6391 ⟨301527, by decide⟩ :=
  accepted_of_selected 11 6391 ⟨301527, by decide⟩ ⟨11, 2, 0, 301527, 6391, 1189, 262144⟩
    (by decide) selected_cut_11251

theorem unmarked_context_10_1597_301528 : frontier 11 ⟨301528, by decide⟩
    (prefixCache 10 1597) (prefixPartial 10 1597) = false := by
  decide +kernel

theorem node_context_10_1597_301528 : EJMOriginalGlobalDAGData.nodes 11 ⟨301528, by decide⟩ =
    .split (coordinate 10) (![⟨301465, by decide⟩,⟨301486, by decide⟩,⟨301508, by decide⟩,⟨301527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1597_301528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1597 ⟨301528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1597
    ⟨301528, by decide⟩ (by decide) (![⟨301465, by decide⟩,⟨301486, by decide⟩,⟨301508, by decide⟩,⟨301527, by decide⟩]) unmarked_context_10_1597_301528 node_context_10_1597_301528
  intro a
  fin_cases a
  · exact context_11_6388_301465
  · exact context_11_6389_301486
  · exact context_11_6390_301508
  · exact context_11_6391_301527

theorem selected_cut_11252 : selected 10 ⟨301543, by decide⟩
    (prefixPartial 11 6392) = some ⟨11, 2, 0, 301543, 6392, 1285, 262144⟩ := by
  decide +kernel

theorem context_11_6392_301543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6392 ⟨301543, by decide⟩ :=
  accepted_of_selected 11 6392 ⟨301543, by decide⟩ ⟨11, 2, 0, 301543, 6392, 1285, 262144⟩
    (by decide) selected_cut_11252

theorem selected_cut_11253 : selected 10 ⟨301560, by decide⟩
    (prefixPartial 11 6393) = some ⟨11, 2, 0, 301560, 6393, 1337, 262144⟩ := by
  decide +kernel

theorem context_11_6393_301560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6393 ⟨301560, by decide⟩ :=
  accepted_of_selected 11 6393 ⟨301560, by decide⟩ ⟨11, 2, 0, 301560, 6393, 1337, 262144⟩
    (by decide) selected_cut_11253

theorem selected_cut_11254 : selected 10 ⟨301577, by decide⟩
    (prefixPartial 11 6394) = some ⟨11, 2, 0, 301577, 6394, 1061, 262144⟩ := by
  decide +kernel

theorem context_11_6394_301577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6394 ⟨301577, by decide⟩ :=
  accepted_of_selected 11 6394 ⟨301577, by decide⟩ ⟨11, 2, 0, 301577, 6394, 1061, 262144⟩
    (by decide) selected_cut_11254

theorem selected_cut_11255 : selected 10 ⟨301596, by decide⟩
    (prefixPartial 11 6395) = some ⟨11, 2, 0, 301596, 6395, 937, 262144⟩ := by
  decide +kernel

theorem context_11_6395_301596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6395 ⟨301596, by decide⟩ :=
  accepted_of_selected 11 6395 ⟨301596, by decide⟩ ⟨11, 2, 0, 301596, 6395, 937, 262144⟩
    (by decide) selected_cut_11255

theorem unmarked_context_10_1598_301597 : frontier 11 ⟨301597, by decide⟩
    (prefixCache 10 1598) (prefixPartial 10 1598) = false := by
  decide +kernel

theorem node_context_10_1598_301597 : EJMOriginalGlobalDAGData.nodes 11 ⟨301597, by decide⟩ =
    .split (coordinate 10) (![⟨301543, by decide⟩,⟨301560, by decide⟩,⟨301577, by decide⟩,⟨301596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1598_301597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1598 ⟨301597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1598
    ⟨301597, by decide⟩ (by decide) (![⟨301543, by decide⟩,⟨301560, by decide⟩,⟨301577, by decide⟩,⟨301596, by decide⟩]) unmarked_context_10_1598_301597 node_context_10_1598_301597
  intro a
  fin_cases a
  · exact context_11_6392_301543
  · exact context_11_6393_301560
  · exact context_11_6394_301577
  · exact context_11_6395_301596

theorem selected_cut_11256 : selected 11 ⟨301649, by decide⟩
    (prefixPartial 10 1599) = some ⟨10, 2, 0, 301649, 1599, 1393, 1048576⟩ := by
  decide +kernel

theorem context_10_1599_301649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1599 ⟨301649, by decide⟩ :=
  accepted_of_selected 10 1599 ⟨301649, by decide⟩ ⟨10, 2, 0, 301649, 1599, 1393, 1048576⟩
    (by decide) selected_cut_11256

theorem unmarked_context_9_399_301650 : frontier 12 ⟨301650, by decide⟩
    (prefixCache 9 399) (prefixPartial 9 399) = false := by
  decide +kernel

theorem node_context_9_399_301650 : EJMOriginalGlobalDAGData.nodes 12 ⟨301650, by decide⟩ =
    .split (coordinate 9) (![⟨301445, by decide⟩,⟨301528, by decide⟩,⟨301597, by decide⟩,⟨301649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_399_301650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 399 ⟨301650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 399
    ⟨301650, by decide⟩ (by decide) (![⟨301445, by decide⟩,⟨301528, by decide⟩,⟨301597, by decide⟩,⟨301649, by decide⟩]) unmarked_context_9_399_301650 node_context_9_399_301650
  intro a
  fin_cases a
  · exact context_10_1596_301445
  · exact context_10_1597_301528
  · exact context_10_1598_301597
  · exact context_10_1599_301649

theorem unmarked_context_8_99_301651 : frontier 13 ⟨301651, by decide⟩
    (prefixCache 8 99) (prefixPartial 8 99) = false := by
  decide +kernel

theorem node_context_8_99_301651 : EJMOriginalGlobalDAGData.nodes 13 ⟨301651, by decide⟩ =
    .split (coordinate 8) (![⟨296533, by decide⟩,⟨299838, by decide⟩,⟨301349, by decide⟩,⟨301650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_99_301651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 99 ⟨301651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 99
    ⟨301651, by decide⟩ (by decide) (![⟨296533, by decide⟩,⟨299838, by decide⟩,⟨301349, by decide⟩,⟨301650, by decide⟩]) unmarked_context_8_99_301651 node_context_8_99_301651
  intro a
  fin_cases a
  · exact context_9_396_296533
  · exact context_9_397_299838
  · exact context_9_398_301349
  · exact context_9_399_301650

theorem unmarked_context_7_24_301652 : frontier 14 ⟨301652, by decide⟩
    (prefixCache 7 24) (prefixPartial 7 24) = false := by
  decide +kernel

theorem node_context_7_24_301652 : EJMOriginalGlobalDAGData.nodes 14 ⟨301652, by decide⟩ =
    .split (coordinate 7) (![⟨273133, by decide⟩,⟨282939, by decide⟩,⟨291506, by decide⟩,⟨301651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_24_301652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 24 ⟨301652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 24
    ⟨301652, by decide⟩ (by decide) (![⟨273133, by decide⟩,⟨282939, by decide⟩,⟨291506, by decide⟩,⟨301651, by decide⟩]) unmarked_context_7_24_301652 node_context_7_24_301652
  intro a
  fin_cases a
  · exact context_8_96_273133
  · exact context_8_97_282939
  · exact context_8_98_291506
  · exact context_8_99_301651

theorem selected_cut_11257 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 25600) = some ⟨12, 1, 0, 34034, 25600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25600_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25600 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 25600 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 25600, 1, 65536⟩
    (by decide) selected_cut_11257

theorem selected_cut_11258 : selected 9 ⟨301653, by decide⟩
    (prefixPartial 12 25601) = some ⟨12, 1, 0, 301653, 25601, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25601_301653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25601 ⟨301653, by decide⟩ :=
  accepted_of_selected 12 25601 ⟨301653, by decide⟩ ⟨12, 1, 0, 301653, 25601, 1, 65536⟩
    (by decide) selected_cut_11258

theorem selected_cut_11259 : selected 8 ⟨301725, by decide⟩
    (prefixPartial 13 102408) = some ⟨13, 2, 0, 301725, 102408, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_102408_301725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102408 ⟨301725, by decide⟩ :=
  accepted_of_selected 13 102408 ⟨301725, by decide⟩ ⟨13, 2, 0, 301725, 102408, 2601, 16384⟩
    (by decide) selected_cut_11259

theorem selected_cut_11260 : selected 8 ⟨301782, by decide⟩
    (prefixPartial 13 102409) = some ⟨13, 2, 0, 301782, 102409, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_102409_301782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102409 ⟨301782, by decide⟩ :=
  accepted_of_selected 13 102409 ⟨301782, by decide⟩ ⟨13, 2, 0, 301782, 102409, 1965, 16384⟩
    (by decide) selected_cut_11260

theorem selected_cut_11261 : selected 8 ⟨301807, by decide⟩
    (prefixPartial 13 102410) = some ⟨13, 2, 0, 301807, 102410, 589, 16384⟩ := by
  decide +kernel

theorem context_13_102410_301807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102410 ⟨301807, by decide⟩ :=
  accepted_of_selected 13 102410 ⟨301807, by decide⟩ ⟨13, 2, 0, 301807, 102410, 589, 16384⟩
    (by decide) selected_cut_11261

theorem selected_cut_11262 : selected 8 ⟨301811, by decide⟩
    (prefixPartial 13 102411) = some ⟨13, 2, 0, 301811, 102411, 137, 16384⟩ := by
  decide +kernel

theorem context_13_102411_301811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102411 ⟨301811, by decide⟩ :=
  accepted_of_selected 13 102411 ⟨301811, by decide⟩ ⟨13, 2, 0, 301811, 102411, 137, 16384⟩
    (by decide) selected_cut_11262

theorem unmarked_context_12_25602_301812 : frontier 9 ⟨301812, by decide⟩
    (prefixCache 12 25602) (prefixPartial 12 25602) = false := by
  decide +kernel

theorem node_context_12_25602_301812 : EJMOriginalGlobalDAGData.nodes 9 ⟨301812, by decide⟩ =
    .split (coordinate 12) (![⟨301725, by decide⟩,⟨301782, by decide⟩,⟨301807, by decide⟩,⟨301811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25602_301812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25602 ⟨301812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25602
    ⟨301812, by decide⟩ (by decide) (![⟨301725, by decide⟩,⟨301782, by decide⟩,⟨301807, by decide⟩,⟨301811, by decide⟩]) unmarked_context_12_25602_301812 node_context_12_25602_301812
  intro a
  fin_cases a
  · exact context_13_102408_301725
  · exact context_13_102409_301782
  · exact context_13_102410_301807
  · exact context_13_102411_301811

theorem selected_cut_11263 : selected 8 ⟨301902, by decide⟩
    (prefixPartial 13 102412) = some ⟨13, 2, 0, 301902, 102412, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_102412_301902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102412 ⟨301902, by decide⟩ :=
  accepted_of_selected 13 102412 ⟨301902, by decide⟩ ⟨13, 2, 0, 301902, 102412, 2961, 16384⟩
    (by decide) selected_cut_11263

theorem selected_cut_11264 : selected 8 ⟨301978, by decide⟩
    (prefixPartial 13 102413) = some ⟨13, 2, 0, 301978, 102413, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_102413_301978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102413 ⟨301978, by decide⟩ :=
  accepted_of_selected 13 102413 ⟨301978, by decide⟩ ⟨13, 2, 0, 301978, 102413, 2141, 16384⟩
    (by decide) selected_cut_11264

theorem selected_cut_11265 : selected 8 ⟨302017, by decide⟩
    (prefixPartial 13 102414) = some ⟨13, 2, 0, 302017, 102414, 629, 16384⟩ := by
  decide +kernel

theorem context_13_102414_302017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102414 ⟨302017, by decide⟩ :=
  accepted_of_selected 13 102414 ⟨302017, by decide⟩ ⟨13, 2, 0, 302017, 102414, 629, 16384⟩
    (by decide) selected_cut_11265

theorem selected_cut_11266 : selected 8 ⟨302041, by decide⟩
    (prefixPartial 13 102415) = some ⟨13, 2, 0, 302041, 102415, 157, 16384⟩ := by
  decide +kernel

theorem context_13_102415_302041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102415 ⟨302041, by decide⟩ :=
  accepted_of_selected 13 102415 ⟨302041, by decide⟩ ⟨13, 2, 0, 302041, 102415, 157, 16384⟩
    (by decide) selected_cut_11266

theorem unmarked_context_12_25603_302042 : frontier 9 ⟨302042, by decide⟩
    (prefixCache 12 25603) (prefixPartial 12 25603) = false := by
  decide +kernel

theorem node_context_12_25603_302042 : EJMOriginalGlobalDAGData.nodes 9 ⟨302042, by decide⟩ =
    .split (coordinate 12) (![⟨301902, by decide⟩,⟨301978, by decide⟩,⟨302017, by decide⟩,⟨302041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25603_302042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25603 ⟨302042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25603
    ⟨302042, by decide⟩ (by decide) (![⟨301902, by decide⟩,⟨301978, by decide⟩,⟨302017, by decide⟩,⟨302041, by decide⟩]) unmarked_context_12_25603_302042 node_context_12_25603_302042
  intro a
  fin_cases a
  · exact context_13_102412_301902
  · exact context_13_102413_301978
  · exact context_13_102414_302017
  · exact context_13_102415_302041

theorem unmarked_context_11_6400_302043 : frontier 10 ⟨302043, by decide⟩
    (prefixCache 11 6400) (prefixPartial 11 6400) = false := by
  decide +kernel

theorem node_context_11_6400_302043 : EJMOriginalGlobalDAGData.nodes 10 ⟨302043, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨301812, by decide⟩,⟨302042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6400_302043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6400 ⟨302043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6400
    ⟨302043, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨301812, by decide⟩,⟨302042, by decide⟩]) unmarked_context_11_6400_302043 node_context_11_6400_302043
  intro a
  fin_cases a
  · exact context_12_25600_34034
  · exact context_12_25601_301653
  · exact context_12_25602_301812
  · exact context_12_25603_302042

theorem selected_cut_11267 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 25604) = some ⟨12, 1, 0, 34034, 25604, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25604_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25604 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 25604 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 25604, 1, 65536⟩
    (by decide) selected_cut_11267

theorem selected_cut_11268 : selected 8 ⟨302108, by decide⟩
    (prefixPartial 13 102420) = some ⟨13, 2, 0, 302108, 102420, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_102420_302108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102420 ⟨302108, by decide⟩ :=
  accepted_of_selected 13 102420 ⟨302108, by decide⟩ ⟨13, 2, 0, 302108, 102420, 2917, 16384⟩
    (by decide) selected_cut_11268

theorem selected_cut_11269 : selected 8 ⟨302159, by decide⟩
    (prefixPartial 13 102421) = some ⟨13, 2, 0, 302159, 102421, 3325, 16384⟩ := by
  decide +kernel

theorem context_13_102421_302159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102421 ⟨302159, by decide⟩ :=
  accepted_of_selected 13 102421 ⟨302159, by decide⟩ ⟨13, 2, 0, 302159, 102421, 3325, 16384⟩
    (by decide) selected_cut_11269

theorem selected_cut_11270 : selected 8 ⟨302183, by decide⟩
    (prefixPartial 13 102422) = some ⟨13, 2, 0, 302183, 102422, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_102422_302183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102422 ⟨302183, by decide⟩ :=
  accepted_of_selected 13 102422 ⟨302183, by decide⟩ ⟨13, 2, 0, 302183, 102422, 2273, 16384⟩
    (by decide) selected_cut_11270

theorem selected_cut_11271 : selected 8 ⟨302192, by decide⟩
    (prefixPartial 13 102423) = some ⟨13, 2, 0, 302192, 102423, 981, 16384⟩ := by
  decide +kernel

theorem context_13_102423_302192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102423 ⟨302192, by decide⟩ :=
  accepted_of_selected 13 102423 ⟨302192, by decide⟩ ⟨13, 2, 0, 302192, 102423, 981, 16384⟩
    (by decide) selected_cut_11271

theorem unmarked_context_12_25605_302193 : frontier 9 ⟨302193, by decide⟩
    (prefixCache 12 25605) (prefixPartial 12 25605) = false := by
  decide +kernel

theorem node_context_12_25605_302193 : EJMOriginalGlobalDAGData.nodes 9 ⟨302193, by decide⟩ =
    .split (coordinate 12) (![⟨302108, by decide⟩,⟨302159, by decide⟩,⟨302183, by decide⟩,⟨302192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25605_302193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25605 ⟨302193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25605
    ⟨302193, by decide⟩ (by decide) (![⟨302108, by decide⟩,⟨302159, by decide⟩,⟨302183, by decide⟩,⟨302192, by decide⟩]) unmarked_context_12_25605_302193 node_context_12_25605_302193
  intro a
  fin_cases a
  · exact context_13_102420_302108
  · exact context_13_102421_302159
  · exact context_13_102422_302183
  · exact context_13_102423_302192

theorem selected_cut_11272 : selected 8 ⟨302243, by decide⟩
    (prefixPartial 13 102424) = some ⟨13, 2, 0, 302243, 102424, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_102424_302243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102424 ⟨302243, by decide⟩ :=
  accepted_of_selected 13 102424 ⟨302243, by decide⟩ ⟨13, 2, 0, 302243, 102424, 2933, 16384⟩
    (by decide) selected_cut_11272

theorem selected_cut_11273 : selected 8 ⟨302293, by decide⟩
    (prefixPartial 13 102425) = some ⟨13, 2, 0, 302293, 102425, 3617, 16384⟩ := by
  decide +kernel

theorem context_13_102425_302293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102425 ⟨302293, by decide⟩ :=
  accepted_of_selected 13 102425 ⟨302293, by decide⟩ ⟨13, 2, 0, 302293, 102425, 3617, 16384⟩
    (by decide) selected_cut_11273

theorem selected_cut_11274 : selected 8 ⟨302316, by decide⟩
    (prefixPartial 13 102426) = some ⟨13, 2, 0, 302316, 102426, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_102426_302316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102426 ⟨302316, by decide⟩ :=
  accepted_of_selected 13 102426 ⟨302316, by decide⟩ ⟨13, 2, 0, 302316, 102426, 2177, 16384⟩
    (by decide) selected_cut_11274

theorem selected_cut_11275 : selected 8 ⟨302325, by decide⟩
    (prefixPartial 13 102427) = some ⟨13, 2, 0, 302325, 102427, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_102427_302325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102427 ⟨302325, by decide⟩ :=
  accepted_of_selected 13 102427 ⟨302325, by decide⟩ ⟨13, 2, 0, 302325, 102427, 1161, 16384⟩
    (by decide) selected_cut_11275

theorem unmarked_context_12_25606_302326 : frontier 9 ⟨302326, by decide⟩
    (prefixCache 12 25606) (prefixPartial 12 25606) = false := by
  decide +kernel

theorem node_context_12_25606_302326 : EJMOriginalGlobalDAGData.nodes 9 ⟨302326, by decide⟩ =
    .split (coordinate 12) (![⟨302243, by decide⟩,⟨302293, by decide⟩,⟨302316, by decide⟩,⟨302325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25606_302326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25606 ⟨302326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25606
    ⟨302326, by decide⟩ (by decide) (![⟨302243, by decide⟩,⟨302293, by decide⟩,⟨302316, by decide⟩,⟨302325, by decide⟩]) unmarked_context_12_25606_302326 node_context_12_25606_302326
  intro a
  fin_cases a
  · exact context_13_102424_302243
  · exact context_13_102425_302293
  · exact context_13_102426_302316
  · exact context_13_102427_302325

theorem selected_cut_11276 : selected 8 ⟨302389, by decide⟩
    (prefixPartial 13 102428) = some ⟨13, 2, 0, 302389, 102428, 3341, 16384⟩ := by
  decide +kernel

theorem context_13_102428_302389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102428 ⟨302389, by decide⟩ :=
  accepted_of_selected 13 102428 ⟨302389, by decide⟩ ⟨13, 2, 0, 302389, 102428, 3341, 16384⟩
    (by decide) selected_cut_11276

theorem selected_cut_11277 : selected 8 ⟨302449, by decide⟩
    (prefixPartial 13 102429) = some ⟨13, 2, 0, 302449, 102429, 3901, 16384⟩ := by
  decide +kernel

theorem context_13_102429_302449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102429 ⟨302449, by decide⟩ :=
  accepted_of_selected 13 102429 ⟨302449, by decide⟩ ⟨13, 2, 0, 302449, 102429, 3901, 16384⟩
    (by decide) selected_cut_11277

theorem selected_cut_11278 : selected 8 ⟨302477, by decide⟩
    (prefixPartial 13 102430) = some ⟨13, 2, 0, 302477, 102430, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_102430_302477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102430 ⟨302477, by decide⟩ :=
  accepted_of_selected 13 102430 ⟨302477, by decide⟩ ⟨13, 2, 0, 302477, 102430, 2425, 16384⟩
    (by decide) selected_cut_11278

theorem selected_cut_11279 : selected 8 ⟨302485, by decide⟩
    (prefixPartial 13 102431) = some ⟨13, 2, 0, 302485, 102431, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_102431_302485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102431 ⟨302485, by decide⟩ :=
  accepted_of_selected 13 102431 ⟨302485, by decide⟩ ⟨13, 2, 0, 302485, 102431, 1189, 16384⟩
    (by decide) selected_cut_11279

theorem unmarked_context_12_25607_302486 : frontier 9 ⟨302486, by decide⟩
    (prefixCache 12 25607) (prefixPartial 12 25607) = false := by
  decide +kernel

theorem node_context_12_25607_302486 : EJMOriginalGlobalDAGData.nodes 9 ⟨302486, by decide⟩ =
    .split (coordinate 12) (![⟨302389, by decide⟩,⟨302449, by decide⟩,⟨302477, by decide⟩,⟨302485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25607_302486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25607 ⟨302486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25607
    ⟨302486, by decide⟩ (by decide) (![⟨302389, by decide⟩,⟨302449, by decide⟩,⟨302477, by decide⟩,⟨302485, by decide⟩]) unmarked_context_12_25607_302486 node_context_12_25607_302486
  intro a
  fin_cases a
  · exact context_13_102428_302389
  · exact context_13_102429_302449
  · exact context_13_102430_302477
  · exact context_13_102431_302485

theorem unmarked_context_11_6401_302487 : frontier 10 ⟨302487, by decide⟩
    (prefixCache 11 6401) (prefixPartial 11 6401) = false := by
  decide +kernel

theorem node_context_11_6401_302487 : EJMOriginalGlobalDAGData.nodes 10 ⟨302487, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨302193, by decide⟩,⟨302326, by decide⟩,⟨302486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6401_302487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6401 ⟨302487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6401
    ⟨302487, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨302193, by decide⟩,⟨302326, by decide⟩,⟨302486, by decide⟩]) unmarked_context_11_6401_302487 node_context_11_6401_302487
  intro a
  fin_cases a
  · exact context_12_25604_34034
  · exact context_12_25605_302193
  · exact context_12_25606_302326
  · exact context_12_25607_302486

theorem selected_cut_11280 : selected 8 ⟨302537, by decide⟩
    (prefixPartial 13 102432) = some ⟨13, 2, 0, 302537, 102432, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_102432_302537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102432 ⟨302537, by decide⟩ :=
  accepted_of_selected 13 102432 ⟨302537, by decide⟩ ⟨13, 2, 0, 302537, 102432, 2225, 16384⟩
    (by decide) selected_cut_11280

theorem selected_cut_11281 : selected 8 ⟨302610, by decide⟩
    (prefixPartial 13 102433) = some ⟨13, 2, 0, 302610, 102433, 3821, 16384⟩ := by
  decide +kernel

theorem context_13_102433_302610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102433 ⟨302610, by decide⟩ :=
  accepted_of_selected 13 102433 ⟨302610, by decide⟩ ⟨13, 2, 0, 302610, 102433, 3821, 16384⟩
    (by decide) selected_cut_11281

theorem selected_cut_11282 : selected 8 ⟨302638, by decide⟩
    (prefixPartial 13 102434) = some ⟨13, 2, 0, 302638, 102434, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_102434_302638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102434 ⟨302638, by decide⟩ :=
  accepted_of_selected 13 102434 ⟨302638, by decide⟩ ⟨13, 2, 0, 302638, 102434, 2313, 16384⟩
    (by decide) selected_cut_11282

theorem selected_cut_11283 : selected 8 ⟨302651, by decide⟩
    (prefixPartial 13 102435) = some ⟨13, 2, 0, 302651, 102435, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_102435_302651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102435 ⟨302651, by decide⟩ :=
  accepted_of_selected 13 102435 ⟨302651, by decide⟩ ⟨13, 2, 0, 302651, 102435, 1213, 16384⟩
    (by decide) selected_cut_11283

theorem unmarked_context_12_25608_302652 : frontier 9 ⟨302652, by decide⟩
    (prefixCache 12 25608) (prefixPartial 12 25608) = false := by
  decide +kernel

theorem node_context_12_25608_302652 : EJMOriginalGlobalDAGData.nodes 9 ⟨302652, by decide⟩ =
    .split (coordinate 12) (![⟨302537, by decide⟩,⟨302610, by decide⟩,⟨302638, by decide⟩,⟨302651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25608_302652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25608 ⟨302652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25608
    ⟨302652, by decide⟩ (by decide) (![⟨302537, by decide⟩,⟨302610, by decide⟩,⟨302638, by decide⟩,⟨302651, by decide⟩]) unmarked_context_12_25608_302652 node_context_12_25608_302652
  intro a
  fin_cases a
  · exact context_13_102432_302537
  · exact context_13_102433_302610
  · exact context_13_102434_302638
  · exact context_13_102435_302651

theorem selected_cut_11284 : selected 8 ⟨302719, by decide⟩
    (prefixPartial 13 102436) = some ⟨13, 2, 0, 302719, 102436, 3293, 16384⟩ := by
  decide +kernel

theorem context_13_102436_302719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102436 ⟨302719, by decide⟩ :=
  accepted_of_selected 13 102436 ⟨302719, by decide⟩ ⟨13, 2, 0, 302719, 102436, 3293, 16384⟩
    (by decide) selected_cut_11284

theorem selected_cut_11285 : selected 7 ⟨302746, by decide⟩
    (prefixPartial 14 409748) = some ⟨14, 2, 0, 302746, 409748, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_409748_302746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409748 ⟨302746, by decide⟩ :=
  accepted_of_selected 14 409748 ⟨302746, by decide⟩ ⟨14, 2, 0, 302746, 409748, 1193, 4096⟩
    (by decide) selected_cut_11285

theorem selected_cut_11286 : selected 7 ⟨302768, by decide⟩
    (prefixPartial 14 409749) = some ⟨14, 2, 0, 302768, 409749, 977, 4096⟩ := by
  decide +kernel

theorem context_14_409749_302768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409749 ⟨302768, by decide⟩ :=
  accepted_of_selected 14 409749 ⟨302768, by decide⟩ ⟨14, 2, 0, 302768, 409749, 977, 4096⟩
    (by decide) selected_cut_11286

theorem selected_cut_11287 : selected 7 ⟨302787, by decide⟩
    (prefixPartial 14 409750) = some ⟨14, 2, 0, 302787, 409750, 1109, 4096⟩ := by
  decide +kernel

theorem context_14_409750_302787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409750 ⟨302787, by decide⟩ :=
  accepted_of_selected 14 409750 ⟨302787, by decide⟩ ⟨14, 2, 0, 302787, 409750, 1109, 4096⟩
    (by decide) selected_cut_11287

theorem selected_cut_11288 : selected 7 ⟨302796, by decide⟩
    (prefixPartial 14 409751) = some ⟨14, 2, 0, 302796, 409751, 921, 4096⟩ := by
  decide +kernel

theorem context_14_409751_302796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409751 ⟨302796, by decide⟩ :=
  accepted_of_selected 14 409751 ⟨302796, by decide⟩ ⟨14, 2, 0, 302796, 409751, 921, 4096⟩
    (by decide) selected_cut_11288

theorem unmarked_context_13_102437_302797 : frontier 8 ⟨302797, by decide⟩
    (prefixCache 13 102437) (prefixPartial 13 102437) = false := by
  decide +kernel

theorem node_context_13_102437_302797 : EJMOriginalGlobalDAGData.nodes 8 ⟨302797, by decide⟩ =
    .split (coordinate 13) (![⟨302746, by decide⟩,⟨302768, by decide⟩,⟨302787, by decide⟩,⟨302796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_102437_302797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102437 ⟨302797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 102437
    ⟨302797, by decide⟩ (by decide) (![⟨302746, by decide⟩,⟨302768, by decide⟩,⟨302787, by decide⟩,⟨302796, by decide⟩]) unmarked_context_13_102437_302797 node_context_13_102437_302797
  intro a
  fin_cases a
  · exact context_14_409748_302746
  · exact context_14_409749_302768
  · exact context_14_409750_302787
  · exact context_14_409751_302796

theorem selected_cut_11289 : selected 8 ⟨302823, by decide⟩
    (prefixPartial 13 102438) = some ⟨13, 2, 0, 302823, 102438, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_102438_302823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102438 ⟨302823, by decide⟩ :=
  accepted_of_selected 13 102438 ⟨302823, by decide⟩ ⟨13, 2, 0, 302823, 102438, 2201, 16384⟩
    (by decide) selected_cut_11289

theorem selected_cut_11290 : selected 8 ⟨302837, by decide⟩
    (prefixPartial 13 102439) = some ⟨13, 2, 0, 302837, 102439, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_102439_302837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102439 ⟨302837, by decide⟩ :=
  accepted_of_selected 13 102439 ⟨302837, by decide⟩ ⟨13, 2, 0, 302837, 102439, 1125, 16384⟩
    (by decide) selected_cut_11290

theorem unmarked_context_12_25609_302838 : frontier 9 ⟨302838, by decide⟩
    (prefixCache 12 25609) (prefixPartial 12 25609) = false := by
  decide +kernel

theorem node_context_12_25609_302838 : EJMOriginalGlobalDAGData.nodes 9 ⟨302838, by decide⟩ =
    .split (coordinate 12) (![⟨302719, by decide⟩,⟨302797, by decide⟩,⟨302823, by decide⟩,⟨302837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25609_302838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25609 ⟨302838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25609
    ⟨302838, by decide⟩ (by decide) (![⟨302719, by decide⟩,⟨302797, by decide⟩,⟨302823, by decide⟩,⟨302837, by decide⟩]) unmarked_context_12_25609_302838 node_context_12_25609_302838
  intro a
  fin_cases a
  · exact context_13_102436_302719
  · exact context_13_102437_302797
  · exact context_13_102438_302823
  · exact context_13_102439_302837

theorem selected_cut_11291 : selected 8 ⟨302898, by decide⟩
    (prefixPartial 13 102440) = some ⟨13, 2, 0, 302898, 102440, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_102440_302898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102440 ⟨302898, by decide⟩ :=
  accepted_of_selected 13 102440 ⟨302898, by decide⟩ ⟨13, 2, 0, 302898, 102440, 2761, 16384⟩
    (by decide) selected_cut_11291

theorem selected_cut_11292 : selected 8 ⟨302970, by decide⟩
    (prefixPartial 13 102441) = some ⟨13, 2, 0, 302970, 102441, 3849, 16384⟩ := by
  decide +kernel

theorem context_13_102441_302970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102441 ⟨302970, by decide⟩ :=
  accepted_of_selected 13 102441 ⟨302970, by decide⟩ ⟨13, 2, 0, 302970, 102441, 3849, 16384⟩
    (by decide) selected_cut_11292

theorem selected_cut_11293 : selected 8 ⟨302994, by decide⟩
    (prefixPartial 13 102442) = some ⟨13, 2, 0, 302994, 102442, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_102442_302994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102442 ⟨302994, by decide⟩ :=
  accepted_of_selected 13 102442 ⟨302994, by decide⟩ ⟨13, 2, 0, 302994, 102442, 1933, 16384⟩
    (by decide) selected_cut_11293

theorem selected_cut_11294 : selected 8 ⟨303008, by decide⟩
    (prefixPartial 13 102443) = some ⟨13, 2, 0, 303008, 102443, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_102443_303008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102443 ⟨303008, by decide⟩ :=
  accepted_of_selected 13 102443 ⟨303008, by decide⟩ ⟨13, 2, 0, 303008, 102443, 1265, 16384⟩
    (by decide) selected_cut_11294

theorem unmarked_context_12_25610_303009 : frontier 9 ⟨303009, by decide⟩
    (prefixCache 12 25610) (prefixPartial 12 25610) = false := by
  decide +kernel

theorem node_context_12_25610_303009 : EJMOriginalGlobalDAGData.nodes 9 ⟨303009, by decide⟩ =
    .split (coordinate 12) (![⟨302898, by decide⟩,⟨302970, by decide⟩,⟨302994, by decide⟩,⟨303008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25610_303009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25610 ⟨303009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25610
    ⟨303009, by decide⟩ (by decide) (![⟨302898, by decide⟩,⟨302970, by decide⟩,⟨302994, by decide⟩,⟨303008, by decide⟩]) unmarked_context_12_25610_303009 node_context_12_25610_303009
  intro a
  fin_cases a
  · exact context_13_102440_302898
  · exact context_13_102441_302970
  · exact context_13_102442_302994
  · exact context_13_102443_303008

theorem selected_cut_11295 : selected 8 ⟨303078, by decide⟩
    (prefixPartial 13 102444) = some ⟨13, 2, 0, 303078, 102444, 3257, 16384⟩ := by
  decide +kernel

theorem context_13_102444_303078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102444 ⟨303078, by decide⟩ :=
  accepted_of_selected 13 102444 ⟨303078, by decide⟩ ⟨13, 2, 0, 303078, 102444, 3257, 16384⟩
    (by decide) selected_cut_11295

theorem selected_cut_11296 : selected 7 ⟨303103, by decide⟩
    (prefixPartial 14 409780) = some ⟨14, 2, 0, 303103, 409780, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_409780_303103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409780 ⟨303103, by decide⟩ :=
  accepted_of_selected 14 409780 ⟨303103, by decide⟩ ⟨14, 2, 0, 303103, 409780, 1193, 4096⟩
    (by decide) selected_cut_11296

theorem selected_cut_11297 : selected 7 ⟨303125, by decide⟩
    (prefixPartial 14 409781) = some ⟨14, 2, 0, 303125, 409781, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_409781_303125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409781 ⟨303125, by decide⟩ :=
  accepted_of_selected 14 409781 ⟨303125, by decide⟩ ⟨14, 2, 0, 303125, 409781, 1025, 4096⟩
    (by decide) selected_cut_11297

theorem selected_cut_11298 : selected 7 ⟨303148, by decide⟩
    (prefixPartial 14 409782) = some ⟨14, 2, 0, 303148, 409782, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_409782_303148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409782 ⟨303148, by decide⟩ :=
  accepted_of_selected 14 409782 ⟨303148, by decide⟩ ⟨14, 2, 0, 303148, 409782, 1197, 4096⟩
    (by decide) selected_cut_11298

theorem selected_cut_11299 : selected 7 ⟨303164, by decide⟩
    (prefixPartial 14 409783) = some ⟨14, 2, 0, 303164, 409783, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_409783_303164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 409783 ⟨303164, by decide⟩ :=
  accepted_of_selected 14 409783 ⟨303164, by decide⟩ ⟨14, 2, 0, 303164, 409783, 1057, 4096⟩
    (by decide) selected_cut_11299

theorem unmarked_context_13_102445_303165 : frontier 8 ⟨303165, by decide⟩
    (prefixCache 13 102445) (prefixPartial 13 102445) = false := by
  decide +kernel

theorem node_context_13_102445_303165 : EJMOriginalGlobalDAGData.nodes 8 ⟨303165, by decide⟩ =
    .split (coordinate 13) (![⟨303103, by decide⟩,⟨303125, by decide⟩,⟨303148, by decide⟩,⟨303164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_102445_303165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102445 ⟨303165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 102445
    ⟨303165, by decide⟩ (by decide) (![⟨303103, by decide⟩,⟨303125, by decide⟩,⟨303148, by decide⟩,⟨303164, by decide⟩]) unmarked_context_13_102445_303165 node_context_13_102445_303165
  intro a
  fin_cases a
  · exact context_14_409780_303103
  · exact context_14_409781_303125
  · exact context_14_409782_303148
  · exact context_14_409783_303164

theorem selected_cut_11300 : selected 8 ⟨303190, by decide⟩
    (prefixPartial 13 102446) = some ⟨13, 2, 0, 303190, 102446, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_102446_303190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102446 ⟨303190, by decide⟩ :=
  accepted_of_selected 13 102446 ⟨303190, by decide⟩ ⟨13, 2, 0, 303190, 102446, 2325, 16384⟩
    (by decide) selected_cut_11300

theorem selected_cut_11301 : selected 8 ⟨303204, by decide⟩
    (prefixPartial 13 102447) = some ⟨13, 2, 0, 303204, 102447, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_102447_303204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102447 ⟨303204, by decide⟩ :=
  accepted_of_selected 13 102447 ⟨303204, by decide⟩ ⟨13, 2, 0, 303204, 102447, 1305, 16384⟩
    (by decide) selected_cut_11301

theorem unmarked_context_12_25611_303205 : frontier 9 ⟨303205, by decide⟩
    (prefixCache 12 25611) (prefixPartial 12 25611) = false := by
  decide +kernel

theorem node_context_12_25611_303205 : EJMOriginalGlobalDAGData.nodes 9 ⟨303205, by decide⟩ =
    .split (coordinate 12) (![⟨303078, by decide⟩,⟨303165, by decide⟩,⟨303190, by decide⟩,⟨303204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25611_303205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25611 ⟨303205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25611
    ⟨303205, by decide⟩ (by decide) (![⟨303078, by decide⟩,⟨303165, by decide⟩,⟨303190, by decide⟩,⟨303204, by decide⟩]) unmarked_context_12_25611_303205 node_context_12_25611_303205
  intro a
  fin_cases a
  · exact context_13_102444_303078
  · exact context_13_102445_303165
  · exact context_13_102446_303190
  · exact context_13_102447_303204

theorem unmarked_context_11_6402_303206 : frontier 10 ⟨303206, by decide⟩
    (prefixCache 11 6402) (prefixPartial 11 6402) = false := by
  decide +kernel

theorem node_context_11_6402_303206 : EJMOriginalGlobalDAGData.nodes 10 ⟨303206, by decide⟩ =
    .split (coordinate 11) (![⟨302652, by decide⟩,⟨302838, by decide⟩,⟨303009, by decide⟩,⟨303205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6402_303206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6402 ⟨303206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6402
    ⟨303206, by decide⟩ (by decide) (![⟨302652, by decide⟩,⟨302838, by decide⟩,⟨303009, by decide⟩,⟨303205, by decide⟩]) unmarked_context_11_6402_303206 node_context_11_6402_303206
  intro a
  fin_cases a
  · exact context_12_25608_302652
  · exact context_12_25609_302838
  · exact context_12_25610_303009
  · exact context_12_25611_303205

theorem selected_cut_11302 : selected 8 ⟨303221, by decide⟩
    (prefixPartial 13 102448) = some ⟨13, 2, 0, 303221, 102448, 797, 16384⟩ := by
  decide +kernel

theorem context_13_102448_303221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102448 ⟨303221, by decide⟩ :=
  accepted_of_selected 13 102448 ⟨303221, by decide⟩ ⟨13, 2, 0, 303221, 102448, 797, 16384⟩
    (by decide) selected_cut_11302

theorem selected_cut_11303 : selected 8 ⟨303273, by decide⟩
    (prefixPartial 13 102449) = some ⟨13, 2, 0, 303273, 102449, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_102449_303273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102449 ⟨303273, by decide⟩ :=
  accepted_of_selected 13 102449 ⟨303273, by decide⟩ ⟨13, 2, 0, 303273, 102449, 1685, 16384⟩
    (by decide) selected_cut_11303

theorem selected_cut_11304 : selected 8 ⟨303324, by decide⟩
    (prefixPartial 13 102450) = some ⟨13, 2, 0, 303324, 102450, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_102450_303324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102450 ⟨303324, by decide⟩ :=
  accepted_of_selected 13 102450 ⟨303324, by decide⟩ ⟨13, 2, 0, 303324, 102450, 1709, 16384⟩
    (by decide) selected_cut_11304

theorem selected_cut_11305 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 102451) = some ⟨13, 1, 0, 265883, 102451, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102451_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102451 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 102451 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 102451, 1, 16384⟩
    (by decide) selected_cut_11305

theorem unmarked_context_12_25612_303325 : frontier 9 ⟨303325, by decide⟩
    (prefixCache 12 25612) (prefixPartial 12 25612) = false := by
  decide +kernel

theorem node_context_12_25612_303325 : EJMOriginalGlobalDAGData.nodes 9 ⟨303325, by decide⟩ =
    .split (coordinate 12) (![⟨303221, by decide⟩,⟨303273, by decide⟩,⟨303324, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25612_303325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25612 ⟨303325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25612
    ⟨303325, by decide⟩ (by decide) (![⟨303221, by decide⟩,⟨303273, by decide⟩,⟨303324, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_25612_303325 node_context_12_25612_303325
  intro a
  fin_cases a
  · exact context_13_102448_303221
  · exact context_13_102449_303273
  · exact context_13_102450_303324
  · exact context_13_102451_265883

theorem selected_cut_11306 : selected 8 ⟨303367, by decide⟩
    (prefixPartial 13 102452) = some ⟨13, 2, 0, 303367, 102452, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_102452_303367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102452 ⟨303367, by decide⟩ :=
  accepted_of_selected 13 102452 ⟨303367, by decide⟩ ⟨13, 2, 0, 303367, 102452, 2737, 16384⟩
    (by decide) selected_cut_11306

theorem selected_cut_11307 : selected 8 ⟨303439, by decide⟩
    (prefixPartial 13 102453) = some ⟨13, 2, 0, 303439, 102453, 3801, 16384⟩ := by
  decide +kernel

theorem context_13_102453_303439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102453 ⟨303439, by decide⟩ :=
  accepted_of_selected 13 102453 ⟨303439, by decide⟩ ⟨13, 2, 0, 303439, 102453, 3801, 16384⟩
    (by decide) selected_cut_11307

theorem selected_cut_11308 : selected 8 ⟨303460, by decide⟩
    (prefixPartial 13 102454) = some ⟨13, 2, 0, 303460, 102454, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_102454_303460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102454 ⟨303460, by decide⟩ :=
  accepted_of_selected 13 102454 ⟨303460, by decide⟩ ⟨13, 2, 0, 303460, 102454, 2061, 16384⟩
    (by decide) selected_cut_11308

theorem selected_cut_11309 : selected 8 ⟨303472, by decide⟩
    (prefixPartial 13 102455) = some ⟨13, 2, 0, 303472, 102455, 893, 16384⟩ := by
  decide +kernel

theorem context_13_102455_303472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102455 ⟨303472, by decide⟩ :=
  accepted_of_selected 13 102455 ⟨303472, by decide⟩ ⟨13, 2, 0, 303472, 102455, 893, 16384⟩
    (by decide) selected_cut_11309

theorem unmarked_context_12_25613_303473 : frontier 9 ⟨303473, by decide⟩
    (prefixCache 12 25613) (prefixPartial 12 25613) = false := by
  decide +kernel

theorem node_context_12_25613_303473 : EJMOriginalGlobalDAGData.nodes 9 ⟨303473, by decide⟩ =
    .split (coordinate 12) (![⟨303367, by decide⟩,⟨303439, by decide⟩,⟨303460, by decide⟩,⟨303472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25613_303473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25613 ⟨303473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25613
    ⟨303473, by decide⟩ (by decide) (![⟨303367, by decide⟩,⟨303439, by decide⟩,⟨303460, by decide⟩,⟨303472, by decide⟩]) unmarked_context_12_25613_303473 node_context_12_25613_303473
  intro a
  fin_cases a
  · exact context_13_102452_303367
  · exact context_13_102453_303439
  · exact context_13_102454_303460
  · exact context_13_102455_303472

theorem selected_cut_11310 : selected 8 ⟨303517, by decide⟩
    (prefixPartial 13 102456) = some ⟨13, 2, 0, 303517, 102456, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_102456_303517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102456 ⟨303517, by decide⟩ :=
  accepted_of_selected 13 102456 ⟨303517, by decide⟩ ⟨13, 2, 0, 303517, 102456, 2549, 16384⟩
    (by decide) selected_cut_11310

theorem selected_cut_11311 : selected 8 ⟨303577, by decide⟩
    (prefixPartial 13 102457) = some ⟨13, 2, 0, 303577, 102457, 3653, 16384⟩ := by
  decide +kernel

theorem context_13_102457_303577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102457 ⟨303577, by decide⟩ :=
  accepted_of_selected 13 102457 ⟨303577, by decide⟩ ⟨13, 2, 0, 303577, 102457, 3653, 16384⟩
    (by decide) selected_cut_11311

theorem selected_cut_11312 : selected 8 ⟨303605, by decide⟩
    (prefixPartial 13 102458) = some ⟨13, 2, 0, 303605, 102458, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_102458_303605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102458 ⟨303605, by decide⟩ :=
  accepted_of_selected 13 102458 ⟨303605, by decide⟩ ⟨13, 2, 0, 303605, 102458, 2057, 16384⟩
    (by decide) selected_cut_11312

theorem selected_cut_11313 : selected 8 ⟨303618, by decide⟩
    (prefixPartial 13 102459) = some ⟨13, 2, 0, 303618, 102459, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_102459_303618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102459 ⟨303618, by decide⟩ :=
  accepted_of_selected 13 102459 ⟨303618, by decide⟩ ⟨13, 2, 0, 303618, 102459, 1057, 16384⟩
    (by decide) selected_cut_11313

theorem unmarked_context_12_25614_303619 : frontier 9 ⟨303619, by decide⟩
    (prefixCache 12 25614) (prefixPartial 12 25614) = false := by
  decide +kernel

theorem node_context_12_25614_303619 : EJMOriginalGlobalDAGData.nodes 9 ⟨303619, by decide⟩ =
    .split (coordinate 12) (![⟨303517, by decide⟩,⟨303577, by decide⟩,⟨303605, by decide⟩,⟨303618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25614_303619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25614 ⟨303619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25614
    ⟨303619, by decide⟩ (by decide) (![⟨303517, by decide⟩,⟨303577, by decide⟩,⟨303605, by decide⟩,⟨303618, by decide⟩]) unmarked_context_12_25614_303619 node_context_12_25614_303619
  intro a
  fin_cases a
  · exact context_13_102456_303517
  · exact context_13_102457_303577
  · exact context_13_102458_303605
  · exact context_13_102459_303618

theorem selected_cut_11314 : selected 8 ⟨303671, by decide⟩
    (prefixPartial 13 102460) = some ⟨13, 2, 0, 303671, 102460, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_102460_303671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102460 ⟨303671, by decide⟩ :=
  accepted_of_selected 13 102460 ⟨303671, by decide⟩ ⟨13, 2, 0, 303671, 102460, 2613, 16384⟩
    (by decide) selected_cut_11314

theorem selected_cut_11315 : selected 8 ⟨303743, by decide⟩
    (prefixPartial 13 102461) = some ⟨13, 2, 0, 303743, 102461, 3913, 16384⟩ := by
  decide +kernel

theorem context_13_102461_303743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102461 ⟨303743, by decide⟩ :=
  accepted_of_selected 13 102461 ⟨303743, by decide⟩ ⟨13, 2, 0, 303743, 102461, 3913, 16384⟩
    (by decide) selected_cut_11315

theorem selected_cut_11316 : selected 8 ⟨303773, by decide⟩
    (prefixPartial 13 102462) = some ⟨13, 2, 0, 303773, 102462, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_102462_303773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102462 ⟨303773, by decide⟩ :=
  accepted_of_selected 13 102462 ⟨303773, by decide⟩ ⟨13, 2, 0, 303773, 102462, 2129, 16384⟩
    (by decide) selected_cut_11316

theorem selected_cut_11317 : selected 8 ⟨303788, by decide⟩
    (prefixPartial 13 102463) = some ⟨13, 2, 0, 303788, 102463, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_102463_303788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102463 ⟨303788, by decide⟩ :=
  accepted_of_selected 13 102463 ⟨303788, by decide⟩ ⟨13, 2, 0, 303788, 102463, 1009, 16384⟩
    (by decide) selected_cut_11317

theorem unmarked_context_12_25615_303789 : frontier 9 ⟨303789, by decide⟩
    (prefixCache 12 25615) (prefixPartial 12 25615) = false := by
  decide +kernel

theorem node_context_12_25615_303789 : EJMOriginalGlobalDAGData.nodes 9 ⟨303789, by decide⟩ =
    .split (coordinate 12) (![⟨303671, by decide⟩,⟨303743, by decide⟩,⟨303773, by decide⟩,⟨303788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25615_303789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25615 ⟨303789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25615
    ⟨303789, by decide⟩ (by decide) (![⟨303671, by decide⟩,⟨303743, by decide⟩,⟨303773, by decide⟩,⟨303788, by decide⟩]) unmarked_context_12_25615_303789 node_context_12_25615_303789
  intro a
  fin_cases a
  · exact context_13_102460_303671
  · exact context_13_102461_303743
  · exact context_13_102462_303773
  · exact context_13_102463_303788

theorem unmarked_context_11_6403_303790 : frontier 10 ⟨303790, by decide⟩
    (prefixCache 11 6403) (prefixPartial 11 6403) = false := by
  decide +kernel

theorem node_context_11_6403_303790 : EJMOriginalGlobalDAGData.nodes 10 ⟨303790, by decide⟩ =
    .split (coordinate 11) (![⟨303325, by decide⟩,⟨303473, by decide⟩,⟨303619, by decide⟩,⟨303789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6403_303790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6403 ⟨303790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6403
    ⟨303790, by decide⟩ (by decide) (![⟨303325, by decide⟩,⟨303473, by decide⟩,⟨303619, by decide⟩,⟨303789, by decide⟩]) unmarked_context_11_6403_303790 node_context_11_6403_303790
  intro a
  fin_cases a
  · exact context_12_25612_303325
  · exact context_12_25613_303473
  · exact context_12_25614_303619
  · exact context_12_25615_303789

theorem unmarked_context_10_1600_303791 : frontier 11 ⟨303791, by decide⟩
    (prefixCache 10 1600) (prefixPartial 10 1600) = false := by
  decide +kernel

theorem node_context_10_1600_303791 : EJMOriginalGlobalDAGData.nodes 11 ⟨303791, by decide⟩ =
    .split (coordinate 10) (![⟨302043, by decide⟩,⟨302487, by decide⟩,⟨303206, by decide⟩,⟨303790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1600_303791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1600 ⟨303791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1600
    ⟨303791, by decide⟩ (by decide) (![⟨302043, by decide⟩,⟨302487, by decide⟩,⟨303206, by decide⟩,⟨303790, by decide⟩]) unmarked_context_10_1600_303791 node_context_10_1600_303791
  intro a
  fin_cases a
  · exact context_11_6400_302043
  · exact context_11_6401_302487
  · exact context_11_6402_303206
  · exact context_11_6403_303790

theorem selected_cut_11318 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 25616) = some ⟨12, 1, 0, 266170, 25616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25616_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25616 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 25616 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 25616, 1, 65536⟩
    (by decide) selected_cut_11318

theorem selected_cut_11319 : selected 8 ⟨303810, by decide⟩
    (prefixPartial 13 102468) = some ⟨13, 2, 0, 303810, 102468, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_102468_303810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102468 ⟨303810, by decide⟩ :=
  accepted_of_selected 13 102468 ⟨303810, by decide⟩ ⟨13, 2, 0, 303810, 102468, 1361, 16384⟩
    (by decide) selected_cut_11319

theorem selected_cut_11320 : selected 8 ⟨303840, by decide⟩
    (prefixPartial 13 102469) = some ⟨13, 2, 0, 303840, 102469, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_102469_303840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102469 ⟨303840, by decide⟩ :=
  accepted_of_selected 13 102469 ⟨303840, by decide⟩ ⟨13, 2, 0, 303840, 102469, 1157, 16384⟩
    (by decide) selected_cut_11320

theorem selected_cut_11321 : selected 8 ⟨303863, by decide⟩
    (prefixPartial 13 102470) = some ⟨13, 2, 0, 303863, 102470, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_102470_303863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102470 ⟨303863, by decide⟩ :=
  accepted_of_selected 13 102470 ⟨303863, by decide⟩ ⟨13, 2, 0, 303863, 102470, 1117, 16384⟩
    (by decide) selected_cut_11321

theorem selected_cut_11322 : selected 8 ⟨303872, by decide⟩
    (prefixPartial 13 102471) = some ⟨13, 2, 0, 303872, 102471, 725, 16384⟩ := by
  decide +kernel

theorem context_13_102471_303872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102471 ⟨303872, by decide⟩ :=
  accepted_of_selected 13 102471 ⟨303872, by decide⟩ ⟨13, 2, 0, 303872, 102471, 725, 16384⟩
    (by decide) selected_cut_11322

theorem unmarked_context_12_25617_303873 : frontier 9 ⟨303873, by decide⟩
    (prefixCache 12 25617) (prefixPartial 12 25617) = false := by
  decide +kernel

theorem node_context_12_25617_303873 : EJMOriginalGlobalDAGData.nodes 9 ⟨303873, by decide⟩ =
    .split (coordinate 12) (![⟨303810, by decide⟩,⟨303840, by decide⟩,⟨303863, by decide⟩,⟨303872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25617_303873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25617 ⟨303873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25617
    ⟨303873, by decide⟩ (by decide) (![⟨303810, by decide⟩,⟨303840, by decide⟩,⟨303863, by decide⟩,⟨303872, by decide⟩]) unmarked_context_12_25617_303873 node_context_12_25617_303873
  intro a
  fin_cases a
  · exact context_13_102468_303810
  · exact context_13_102469_303840
  · exact context_13_102470_303863
  · exact context_13_102471_303872

theorem selected_cut_11323 : selected 8 ⟨303895, by decide⟩
    (prefixPartial 13 102472) = some ⟨13, 2, 0, 303895, 102472, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_102472_303895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102472 ⟨303895, by decide⟩ :=
  accepted_of_selected 13 102472 ⟨303895, by decide⟩ ⟨13, 2, 0, 303895, 102472, 1357, 16384⟩
    (by decide) selected_cut_11323

theorem selected_cut_11324 : selected 8 ⟨303923, by decide⟩
    (prefixPartial 13 102473) = some ⟨13, 2, 0, 303923, 102473, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_102473_303923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102473 ⟨303923, by decide⟩ :=
  accepted_of_selected 13 102473 ⟨303923, by decide⟩ ⟨13, 2, 0, 303923, 102473, 1521, 16384⟩
    (by decide) selected_cut_11324

theorem selected_cut_11325 : selected 8 ⟨303941, by decide⟩
    (prefixPartial 13 102474) = some ⟨13, 2, 0, 303941, 102474, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_102474_303941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102474 ⟨303941, by decide⟩ :=
  accepted_of_selected 13 102474 ⟨303941, by decide⟩ ⟨13, 2, 0, 303941, 102474, 1153, 16384⟩
    (by decide) selected_cut_11325

theorem selected_cut_11326 : selected 8 ⟨303955, by decide⟩
    (prefixPartial 13 102475) = some ⟨13, 2, 0, 303955, 102475, 897, 16384⟩ := by
  decide +kernel

theorem context_13_102475_303955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102475 ⟨303955, by decide⟩ :=
  accepted_of_selected 13 102475 ⟨303955, by decide⟩ ⟨13, 2, 0, 303955, 102475, 897, 16384⟩
    (by decide) selected_cut_11326

theorem unmarked_context_12_25618_303956 : frontier 9 ⟨303956, by decide⟩
    (prefixCache 12 25618) (prefixPartial 12 25618) = false := by
  decide +kernel

theorem node_context_12_25618_303956 : EJMOriginalGlobalDAGData.nodes 9 ⟨303956, by decide⟩ =
    .split (coordinate 12) (![⟨303895, by decide⟩,⟨303923, by decide⟩,⟨303941, by decide⟩,⟨303955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25618_303956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25618 ⟨303956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25618
    ⟨303956, by decide⟩ (by decide) (![⟨303895, by decide⟩,⟨303923, by decide⟩,⟨303941, by decide⟩,⟨303955, by decide⟩]) unmarked_context_12_25618_303956 node_context_12_25618_303956
  intro a
  fin_cases a
  · exact context_13_102472_303895
  · exact context_13_102473_303923
  · exact context_13_102474_303941
  · exact context_13_102475_303955

theorem selected_cut_11327 : selected 8 ⟨303975, by decide⟩
    (prefixPartial 13 102476) = some ⟨13, 2, 0, 303975, 102476, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_102476_303975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102476 ⟨303975, by decide⟩ :=
  accepted_of_selected 13 102476 ⟨303975, by decide⟩ ⟨13, 2, 0, 303975, 102476, 1417, 16384⟩
    (by decide) selected_cut_11327

theorem selected_cut_11328 : selected 8 ⟨304003, by decide⟩
    (prefixPartial 13 102477) = some ⟨13, 2, 0, 304003, 102477, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_102477_304003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102477 ⟨304003, by decide⟩ :=
  accepted_of_selected 13 102477 ⟨304003, by decide⟩ ⟨13, 2, 0, 304003, 102477, 1641, 16384⟩
    (by decide) selected_cut_11328

theorem selected_cut_11329 : selected 8 ⟨304025, by decide⟩
    (prefixPartial 13 102478) = some ⟨13, 2, 0, 304025, 102478, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_102478_304025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102478 ⟨304025, by decide⟩ :=
  accepted_of_selected 13 102478 ⟨304025, by decide⟩ ⟨13, 2, 0, 304025, 102478, 1297, 16384⟩
    (by decide) selected_cut_11329

theorem selected_cut_11330 : selected 8 ⟨304033, by decide⟩
    (prefixPartial 13 102479) = some ⟨13, 2, 0, 304033, 102479, 777, 16384⟩ := by
  decide +kernel

theorem context_13_102479_304033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102479 ⟨304033, by decide⟩ :=
  accepted_of_selected 13 102479 ⟨304033, by decide⟩ ⟨13, 2, 0, 304033, 102479, 777, 16384⟩
    (by decide) selected_cut_11330

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
