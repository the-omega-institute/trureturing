/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover078
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07587 : selected 8 ⟨219154, by decide⟩
    (prefixPartial 13 90354) = some ⟨13, 2, 0, 219154, 90354, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_90354_219154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90354 ⟨219154, by decide⟩ :=
  accepted_of_selected 13 90354 ⟨219154, by decide⟩ ⟨13, 2, 0, 219154, 90354, 1341, 16384⟩
    (by decide) selected_cut_07587

theorem selected_cut_07588 : selected 8 ⟨219162, by decide⟩
    (prefixPartial 13 90355) = some ⟨13, 2, 0, 219162, 90355, 725, 16384⟩ := by
  decide +kernel

theorem context_13_90355_219162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90355 ⟨219162, by decide⟩ :=
  accepted_of_selected 13 90355 ⟨219162, by decide⟩ ⟨13, 2, 0, 219162, 90355, 725, 16384⟩
    (by decide) selected_cut_07588

theorem unmarked_context_12_22588_219163 : frontier 9 ⟨219163, by decide⟩
    (prefixCache 12 22588) (prefixPartial 12 22588) = false := by
  decide +kernel

theorem node_context_12_22588_219163 : EJMOriginalGlobalDAGData.nodes 9 ⟨219163, by decide⟩ =
    .split (coordinate 12) (![⟨219099, by decide⟩,⟨219136, by decide⟩,⟨219154, by decide⟩,⟨219162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22588_219163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22588 ⟨219163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22588
    ⟨219163, by decide⟩ (by decide) (![⟨219099, by decide⟩,⟨219136, by decide⟩,⟨219154, by decide⟩,⟨219162, by decide⟩]) unmarked_context_12_22588_219163 node_context_12_22588_219163
  intro a
  fin_cases a
  · exact context_13_90352_219099
  · exact context_13_90353_219136
  · exact context_13_90354_219154
  · exact context_13_90355_219162

theorem selected_cut_07589 : selected 8 ⟨219166, by decide⟩
    (prefixPartial 13 90356) = some ⟨13, 2, 0, 219166, 90356, 105, 16384⟩ := by
  decide +kernel

theorem context_13_90356_219166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90356 ⟨219166, by decide⟩ :=
  accepted_of_selected 13 90356 ⟨219166, by decide⟩ ⟨13, 2, 0, 219166, 90356, 105, 16384⟩
    (by decide) selected_cut_07589

theorem selected_cut_07590 : selected 8 ⟨219194, by decide⟩
    (prefixPartial 13 90357) = some ⟨13, 2, 0, 219194, 90357, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_90357_219194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90357 ⟨219194, by decide⟩ :=
  accepted_of_selected 13 90357 ⟨219194, by decide⟩ ⟨13, 2, 0, 219194, 90357, 2069, 16384⟩
    (by decide) selected_cut_07590

theorem selected_cut_07591 : selected 8 ⟨219212, by decide⟩
    (prefixPartial 13 90358) = some ⟨13, 2, 0, 219212, 90358, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_90358_219212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90358 ⟨219212, by decide⟩ :=
  accepted_of_selected 13 90358 ⟨219212, by decide⟩ ⟨13, 2, 0, 219212, 90358, 1521, 16384⟩
    (by decide) selected_cut_07591

theorem selected_cut_07592 : selected 8 ⟨219219, by decide⟩
    (prefixPartial 13 90359) = some ⟨13, 2, 0, 219219, 90359, 701, 16384⟩ := by
  decide +kernel

theorem context_13_90359_219219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90359 ⟨219219, by decide⟩ :=
  accepted_of_selected 13 90359 ⟨219219, by decide⟩ ⟨13, 2, 0, 219219, 90359, 701, 16384⟩
    (by decide) selected_cut_07592

theorem unmarked_context_12_22589_219220 : frontier 9 ⟨219220, by decide⟩
    (prefixCache 12 22589) (prefixPartial 12 22589) = false := by
  decide +kernel

theorem node_context_12_22589_219220 : EJMOriginalGlobalDAGData.nodes 9 ⟨219220, by decide⟩ =
    .split (coordinate 12) (![⟨219166, by decide⟩,⟨219194, by decide⟩,⟨219212, by decide⟩,⟨219219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22589_219220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22589 ⟨219220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22589
    ⟨219220, by decide⟩ (by decide) (![⟨219166, by decide⟩,⟨219194, by decide⟩,⟨219212, by decide⟩,⟨219219, by decide⟩]) unmarked_context_12_22589_219220 node_context_12_22589_219220
  intro a
  fin_cases a
  · exact context_13_90356_219166
  · exact context_13_90357_219194
  · exact context_13_90358_219212
  · exact context_13_90359_219219

theorem selected_cut_07593 : selected 8 ⟨219223, by decide⟩
    (prefixPartial 13 90360) = some ⟨13, 2, 0, 219223, 90360, 73, 16384⟩ := by
  decide +kernel

theorem context_13_90360_219223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90360 ⟨219223, by decide⟩ :=
  accepted_of_selected 13 90360 ⟨219223, by decide⟩ ⟨13, 2, 0, 219223, 90360, 73, 16384⟩
    (by decide) selected_cut_07593

theorem selected_cut_07594 : selected 8 ⟨219263, by decide⟩
    (prefixPartial 13 90361) = some ⟨13, 2, 0, 219263, 90361, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_90361_219263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90361 ⟨219263, by decide⟩ :=
  accepted_of_selected 13 90361 ⟨219263, by decide⟩ ⟨13, 2, 0, 219263, 90361, 2661, 16384⟩
    (by decide) selected_cut_07594

theorem selected_cut_07595 : selected 8 ⟨219285, by decide⟩
    (prefixPartial 13 90362) = some ⟨13, 2, 0, 219285, 90362, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_90362_219285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90362 ⟨219285, by decide⟩ :=
  accepted_of_selected 13 90362 ⟨219285, by decide⟩ ⟨13, 2, 0, 219285, 90362, 1617, 16384⟩
    (by decide) selected_cut_07595

theorem selected_cut_07596 : selected 8 ⟨219291, by decide⟩
    (prefixPartial 13 90363) = some ⟨13, 2, 0, 219291, 90363, 653, 16384⟩ := by
  decide +kernel

theorem context_13_90363_219291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90363 ⟨219291, by decide⟩ :=
  accepted_of_selected 13 90363 ⟨219291, by decide⟩ ⟨13, 2, 0, 219291, 90363, 653, 16384⟩
    (by decide) selected_cut_07596

theorem unmarked_context_12_22590_219292 : frontier 9 ⟨219292, by decide⟩
    (prefixCache 12 22590) (prefixPartial 12 22590) = false := by
  decide +kernel

theorem node_context_12_22590_219292 : EJMOriginalGlobalDAGData.nodes 9 ⟨219292, by decide⟩ =
    .split (coordinate 12) (![⟨219223, by decide⟩,⟨219263, by decide⟩,⟨219285, by decide⟩,⟨219291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22590_219292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22590 ⟨219292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22590
    ⟨219292, by decide⟩ (by decide) (![⟨219223, by decide⟩,⟨219263, by decide⟩,⟨219285, by decide⟩,⟨219291, by decide⟩]) unmarked_context_12_22590_219292 node_context_12_22590_219292
  intro a
  fin_cases a
  · exact context_13_90360_219223
  · exact context_13_90361_219263
  · exact context_13_90362_219285
  · exact context_13_90363_219291

theorem selected_cut_07597 : selected 8 ⟨219296, by decide⟩
    (prefixPartial 13 90364) = some ⟨13, 2, 0, 219296, 90364, 53, 16384⟩ := by
  decide +kernel

theorem context_13_90364_219296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90364 ⟨219296, by decide⟩ :=
  accepted_of_selected 13 90364 ⟨219296, by decide⟩ ⟨13, 2, 0, 219296, 90364, 53, 16384⟩
    (by decide) selected_cut_07597

theorem selected_cut_07598 : selected 8 ⟨219335, by decide⟩
    (prefixPartial 13 90365) = some ⟨13, 2, 0, 219335, 90365, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_90365_219335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90365 ⟨219335, by decide⟩ :=
  accepted_of_selected 13 90365 ⟨219335, by decide⟩ ⟨13, 2, 0, 219335, 90365, 2765, 16384⟩
    (by decide) selected_cut_07598

theorem selected_cut_07599 : selected 8 ⟨219355, by decide⟩
    (prefixPartial 13 90366) = some ⟨13, 2, 0, 219355, 90366, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_90366_219355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90366 ⟨219355, by decide⟩ :=
  accepted_of_selected 13 90366 ⟨219355, by decide⟩ ⟨13, 2, 0, 219355, 90366, 1429, 16384⟩
    (by decide) selected_cut_07599

theorem selected_cut_07600 : selected 8 ⟨219361, by decide⟩
    (prefixPartial 13 90367) = some ⟨13, 2, 0, 219361, 90367, 669, 16384⟩ := by
  decide +kernel

theorem context_13_90367_219361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90367 ⟨219361, by decide⟩ :=
  accepted_of_selected 13 90367 ⟨219361, by decide⟩ ⟨13, 2, 0, 219361, 90367, 669, 16384⟩
    (by decide) selected_cut_07600

theorem unmarked_context_12_22591_219362 : frontier 9 ⟨219362, by decide⟩
    (prefixCache 12 22591) (prefixPartial 12 22591) = false := by
  decide +kernel

theorem node_context_12_22591_219362 : EJMOriginalGlobalDAGData.nodes 9 ⟨219362, by decide⟩ =
    .split (coordinate 12) (![⟨219296, by decide⟩,⟨219335, by decide⟩,⟨219355, by decide⟩,⟨219361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22591_219362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22591 ⟨219362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22591
    ⟨219362, by decide⟩ (by decide) (![⟨219296, by decide⟩,⟨219335, by decide⟩,⟨219355, by decide⟩,⟨219361, by decide⟩]) unmarked_context_12_22591_219362 node_context_12_22591_219362
  intro a
  fin_cases a
  · exact context_13_90364_219296
  · exact context_13_90365_219335
  · exact context_13_90366_219355
  · exact context_13_90367_219361

theorem unmarked_context_11_5647_219363 : frontier 10 ⟨219363, by decide⟩
    (prefixCache 11 5647) (prefixPartial 11 5647) = false := by
  decide +kernel

theorem node_context_11_5647_219363 : EJMOriginalGlobalDAGData.nodes 10 ⟨219363, by decide⟩ =
    .split (coordinate 11) (![⟨219163, by decide⟩,⟨219220, by decide⟩,⟨219292, by decide⟩,⟨219362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5647_219363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5647 ⟨219363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5647
    ⟨219363, by decide⟩ (by decide) (![⟨219163, by decide⟩,⟨219220, by decide⟩,⟨219292, by decide⟩,⟨219362, by decide⟩]) unmarked_context_11_5647_219363 node_context_11_5647_219363
  intro a
  fin_cases a
  · exact context_12_22588_219163
  · exact context_12_22589_219220
  · exact context_12_22590_219292
  · exact context_12_22591_219362

theorem unmarked_context_10_1411_219364 : frontier 11 ⟨219364, by decide⟩
    (prefixCache 10 1411) (prefixPartial 10 1411) = false := by
  decide +kernel

theorem node_context_10_1411_219364 : EJMOriginalGlobalDAGData.nodes 11 ⟨219364, by decide⟩ =
    .split (coordinate 10) (![⟨218507, by decide⟩,⟨218793, by decide⟩,⟨219096, by decide⟩,⟨219363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1411_219364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1411 ⟨219364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1411
    ⟨219364, by decide⟩ (by decide) (![⟨218507, by decide⟩,⟨218793, by decide⟩,⟨219096, by decide⟩,⟨219363, by decide⟩]) unmarked_context_10_1411_219364 node_context_10_1411_219364
  intro a
  fin_cases a
  · exact context_11_5644_218507
  · exact context_11_5645_218793
  · exact context_11_5646_219096
  · exact context_11_5647_219363

theorem unmarked_context_9_352_219365 : frontier 12 ⟨219365, by decide⟩
    (prefixCache 9 352) (prefixPartial 9 352) = false := by
  decide +kernel

theorem node_context_9_352_219365 : EJMOriginalGlobalDAGData.nodes 12 ⟨219365, by decide⟩ =
    .split (coordinate 9) (![⟨215290, by decide⟩,⟨216880, by decide⟩,⟨218181, by decide⟩,⟨219364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_352_219365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 352 ⟨219365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 352
    ⟨219365, by decide⟩ (by decide) (![⟨215290, by decide⟩,⟨216880, by decide⟩,⟨218181, by decide⟩,⟨219364, by decide⟩]) unmarked_context_9_352_219365 node_context_9_352_219365
  intro a
  fin_cases a
  · exact context_10_1408_215290
  · exact context_10_1409_216880
  · exact context_10_1410_218181
  · exact context_10_1411_219364

theorem selected_cut_07601 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90368) = some ⟨13, 1, 0, 3444, 90368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90368, 1, 16384⟩
    (by decide) selected_cut_07601

theorem selected_cut_07602 : selected 7 ⟨219392, by decide⟩
    (prefixPartial 14 361476) = some ⟨14, 2, 0, 219392, 361476, 1345, 4096⟩ := by
  decide +kernel

theorem context_14_361476_219392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361476 ⟨219392, by decide⟩ :=
  accepted_of_selected 14 361476 ⟨219392, by decide⟩ ⟨14, 2, 0, 219392, 361476, 1345, 4096⟩
    (by decide) selected_cut_07602

theorem selected_cut_07603 : selected 7 ⟨219409, by decide⟩
    (prefixPartial 14 361477) = some ⟨14, 2, 0, 219409, 361477, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_361477_219409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361477 ⟨219409, by decide⟩ :=
  accepted_of_selected 14 361477 ⟨219409, by decide⟩ ⟨14, 2, 0, 219409, 361477, 1065, 4096⟩
    (by decide) selected_cut_07603

theorem selected_cut_07604 : selected 7 ⟨219429, by decide⟩
    (prefixPartial 14 361478) = some ⟨14, 2, 0, 219429, 361478, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_361478_219429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361478 ⟨219429, by decide⟩ :=
  accepted_of_selected 14 361478 ⟨219429, by decide⟩ ⟨14, 2, 0, 219429, 361478, 1205, 4096⟩
    (by decide) selected_cut_07604

theorem selected_cut_07605 : selected 7 ⟨219446, by decide⟩
    (prefixPartial 14 361479) = some ⟨14, 2, 0, 219446, 361479, 985, 4096⟩ := by
  decide +kernel

theorem context_14_361479_219446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361479 ⟨219446, by decide⟩ :=
  accepted_of_selected 14 361479 ⟨219446, by decide⟩ ⟨14, 2, 0, 219446, 361479, 985, 4096⟩
    (by decide) selected_cut_07605

theorem unmarked_context_13_90369_219447 : frontier 8 ⟨219447, by decide⟩
    (prefixCache 13 90369) (prefixPartial 13 90369) = false := by
  decide +kernel

theorem node_context_13_90369_219447 : EJMOriginalGlobalDAGData.nodes 8 ⟨219447, by decide⟩ =
    .split (coordinate 13) (![⟨219392, by decide⟩,⟨219409, by decide⟩,⟨219429, by decide⟩,⟨219446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90369_219447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90369 ⟨219447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90369
    ⟨219447, by decide⟩ (by decide) (![⟨219392, by decide⟩,⟨219409, by decide⟩,⟨219429, by decide⟩,⟨219446, by decide⟩]) unmarked_context_13_90369_219447 node_context_13_90369_219447
  intro a
  fin_cases a
  · exact context_14_361476_219392
  · exact context_14_361477_219409
  · exact context_14_361478_219429
  · exact context_14_361479_219446

theorem selected_cut_07606 : selected 8 ⟨219473, by decide⟩
    (prefixPartial 13 90370) = some ⟨13, 2, 0, 219473, 90370, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_90370_219473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90370 ⟨219473, by decide⟩ :=
  accepted_of_selected 13 90370 ⟨219473, by decide⟩ ⟨13, 2, 0, 219473, 90370, 2185, 16384⟩
    (by decide) selected_cut_07606

theorem selected_cut_07607 : selected 8 ⟨219489, by decide⟩
    (prefixPartial 13 90371) = some ⟨13, 2, 0, 219489, 90371, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_90371_219489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90371 ⟨219489, by decide⟩ :=
  accepted_of_selected 13 90371 ⟨219489, by decide⟩ ⟨13, 2, 0, 219489, 90371, 1257, 16384⟩
    (by decide) selected_cut_07607

theorem unmarked_context_12_22592_219490 : frontier 9 ⟨219490, by decide⟩
    (prefixCache 12 22592) (prefixPartial 12 22592) = false := by
  decide +kernel

theorem node_context_12_22592_219490 : EJMOriginalGlobalDAGData.nodes 9 ⟨219490, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219447, by decide⟩,⟨219473, by decide⟩,⟨219489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22592_219490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22592 ⟨219490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22592
    ⟨219490, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219447, by decide⟩,⟨219473, by decide⟩,⟨219489, by decide⟩]) unmarked_context_12_22592_219490 node_context_12_22592_219490
  intro a
  fin_cases a
  · exact context_13_90368_3444
  · exact context_13_90369_219447
  · exact context_13_90370_219473
  · exact context_13_90371_219489

theorem selected_cut_07608 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90372) = some ⟨13, 1, 0, 3444, 90372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90372, 1, 16384⟩
    (by decide) selected_cut_07608

theorem selected_cut_07609 : selected 8 ⟨219551, by decide⟩
    (prefixPartial 13 90373) = some ⟨13, 2, 0, 219551, 90373, 3605, 16384⟩ := by
  decide +kernel

theorem context_13_90373_219551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90373 ⟨219551, by decide⟩ :=
  accepted_of_selected 13 90373 ⟨219551, by decide⟩ ⟨13, 2, 0, 219551, 90373, 3605, 16384⟩
    (by decide) selected_cut_07609

theorem selected_cut_07610 : selected 8 ⟨219579, by decide⟩
    (prefixPartial 13 90374) = some ⟨13, 2, 0, 219579, 90374, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_90374_219579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90374 ⟨219579, by decide⟩ :=
  accepted_of_selected 13 90374 ⟨219579, by decide⟩ ⟨13, 2, 0, 219579, 90374, 1765, 16384⟩
    (by decide) selected_cut_07610

theorem selected_cut_07611 : selected 8 ⟨219595, by decide⟩
    (prefixPartial 13 90375) = some ⟨13, 2, 0, 219595, 90375, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_90375_219595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90375 ⟨219595, by decide⟩ :=
  accepted_of_selected 13 90375 ⟨219595, by decide⟩ ⟨13, 2, 0, 219595, 90375, 1097, 16384⟩
    (by decide) selected_cut_07611

theorem unmarked_context_12_22593_219596 : frontier 9 ⟨219596, by decide⟩
    (prefixCache 12 22593) (prefixPartial 12 22593) = false := by
  decide +kernel

theorem node_context_12_22593_219596 : EJMOriginalGlobalDAGData.nodes 9 ⟨219596, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219551, by decide⟩,⟨219579, by decide⟩,⟨219595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22593_219596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22593 ⟨219596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22593
    ⟨219596, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219551, by decide⟩,⟨219579, by decide⟩,⟨219595, by decide⟩]) unmarked_context_12_22593_219596 node_context_12_22593_219596
  intro a
  fin_cases a
  · exact context_13_90372_3444
  · exact context_13_90373_219551
  · exact context_13_90374_219579
  · exact context_13_90375_219595

theorem selected_cut_07612 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90376) = some ⟨13, 1, 0, 3444, 90376, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90376_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90376 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90376 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90376, 1, 16384⟩
    (by decide) selected_cut_07612

theorem selected_cut_07613 : selected 8 ⟨219628, by decide⟩
    (prefixPartial 13 90377) = some ⟨13, 2, 0, 219628, 90377, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_90377_219628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90377 ⟨219628, by decide⟩ :=
  accepted_of_selected 13 90377 ⟨219628, by decide⟩ ⟨13, 2, 0, 219628, 90377, 2757, 16384⟩
    (by decide) selected_cut_07613

theorem selected_cut_07614 : selected 8 ⟨219652, by decide⟩
    (prefixPartial 13 90378) = some ⟨13, 2, 0, 219652, 90378, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_90378_219652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90378 ⟨219652, by decide⟩ :=
  accepted_of_selected 13 90378 ⟨219652, by decide⟩ ⟨13, 2, 0, 219652, 90378, 1505, 16384⟩
    (by decide) selected_cut_07614

theorem selected_cut_07615 : selected 8 ⟨219659, by decide⟩
    (prefixPartial 13 90379) = some ⟨13, 2, 0, 219659, 90379, 825, 16384⟩ := by
  decide +kernel

theorem context_13_90379_219659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90379 ⟨219659, by decide⟩ :=
  accepted_of_selected 13 90379 ⟨219659, by decide⟩ ⟨13, 2, 0, 219659, 90379, 825, 16384⟩
    (by decide) selected_cut_07615

theorem unmarked_context_12_22594_219660 : frontier 9 ⟨219660, by decide⟩
    (prefixCache 12 22594) (prefixPartial 12 22594) = false := by
  decide +kernel

theorem node_context_12_22594_219660 : EJMOriginalGlobalDAGData.nodes 9 ⟨219660, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219628, by decide⟩,⟨219652, by decide⟩,⟨219659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22594_219660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22594 ⟨219660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22594
    ⟨219660, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219628, by decide⟩,⟨219652, by decide⟩,⟨219659, by decide⟩]) unmarked_context_12_22594_219660 node_context_12_22594_219660
  intro a
  fin_cases a
  · exact context_13_90376_3444
  · exact context_13_90377_219628
  · exact context_13_90378_219652
  · exact context_13_90379_219659

theorem selected_cut_07616 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90380) = some ⟨13, 1, 0, 3444, 90380, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90380_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90380 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90380 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90380, 1, 16384⟩
    (by decide) selected_cut_07616

theorem selected_cut_07617 : selected 8 ⟨219695, by decide⟩
    (prefixPartial 13 90381) = some ⟨13, 2, 0, 219695, 90381, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_90381_219695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90381 ⟨219695, by decide⟩ :=
  accepted_of_selected 13 90381 ⟨219695, by decide⟩ ⟨13, 2, 0, 219695, 90381, 2901, 16384⟩
    (by decide) selected_cut_07617

theorem selected_cut_07618 : selected 8 ⟨219714, by decide⟩
    (prefixPartial 13 90382) = some ⟨13, 2, 0, 219714, 90382, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_90382_219714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90382 ⟨219714, by decide⟩ :=
  accepted_of_selected 13 90382 ⟨219714, by decide⟩ ⟨13, 2, 0, 219714, 90382, 1485, 16384⟩
    (by decide) selected_cut_07618

theorem selected_cut_07619 : selected 8 ⟨219722, by decide⟩
    (prefixPartial 13 90383) = some ⟨13, 2, 0, 219722, 90383, 769, 16384⟩ := by
  decide +kernel

theorem context_13_90383_219722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90383 ⟨219722, by decide⟩ :=
  accepted_of_selected 13 90383 ⟨219722, by decide⟩ ⟨13, 2, 0, 219722, 90383, 769, 16384⟩
    (by decide) selected_cut_07619

theorem unmarked_context_12_22595_219723 : frontier 9 ⟨219723, by decide⟩
    (prefixCache 12 22595) (prefixPartial 12 22595) = false := by
  decide +kernel

theorem node_context_12_22595_219723 : EJMOriginalGlobalDAGData.nodes 9 ⟨219723, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219695, by decide⟩,⟨219714, by decide⟩,⟨219722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22595_219723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22595 ⟨219723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22595
    ⟨219723, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219695, by decide⟩,⟨219714, by decide⟩,⟨219722, by decide⟩]) unmarked_context_12_22595_219723 node_context_12_22595_219723
  intro a
  fin_cases a
  · exact context_13_90380_3444
  · exact context_13_90381_219695
  · exact context_13_90382_219714
  · exact context_13_90383_219722

theorem unmarked_context_11_5648_219724 : frontier 10 ⟨219724, by decide⟩
    (prefixCache 11 5648) (prefixPartial 11 5648) = false := by
  decide +kernel

theorem node_context_11_5648_219724 : EJMOriginalGlobalDAGData.nodes 10 ⟨219724, by decide⟩ =
    .split (coordinate 11) (![⟨219490, by decide⟩,⟨219596, by decide⟩,⟨219660, by decide⟩,⟨219723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5648_219724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5648 ⟨219724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5648
    ⟨219724, by decide⟩ (by decide) (![⟨219490, by decide⟩,⟨219596, by decide⟩,⟨219660, by decide⟩,⟨219723, by decide⟩]) unmarked_context_11_5648_219724 node_context_11_5648_219724
  intro a
  fin_cases a
  · exact context_12_22592_219490
  · exact context_12_22593_219596
  · exact context_12_22594_219660
  · exact context_12_22595_219723

theorem selected_cut_07620 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90384) = some ⟨13, 1, 0, 3444, 90384, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90384_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90384 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90384 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90384, 1, 16384⟩
    (by decide) selected_cut_07620

theorem selected_cut_07621 : selected 8 ⟨219771, by decide⟩
    (prefixPartial 13 90385) = some ⟨13, 2, 0, 219771, 90385, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_90385_219771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90385 ⟨219771, by decide⟩ :=
  accepted_of_selected 13 90385 ⟨219771, by decide⟩ ⟨13, 2, 0, 219771, 90385, 2857, 16384⟩
    (by decide) selected_cut_07621

theorem selected_cut_07622 : selected 8 ⟨219795, by decide⟩
    (prefixPartial 13 90386) = some ⟨13, 2, 0, 219795, 90386, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_90386_219795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90386 ⟨219795, by decide⟩ :=
  accepted_of_selected 13 90386 ⟨219795, by decide⟩ ⟨13, 2, 0, 219795, 90386, 1409, 16384⟩
    (by decide) selected_cut_07622

theorem selected_cut_07623 : selected 8 ⟨219806, by decide⟩
    (prefixPartial 13 90387) = some ⟨13, 2, 0, 219806, 90387, 929, 16384⟩ := by
  decide +kernel

theorem context_13_90387_219806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90387 ⟨219806, by decide⟩ :=
  accepted_of_selected 13 90387 ⟨219806, by decide⟩ ⟨13, 2, 0, 219806, 90387, 929, 16384⟩
    (by decide) selected_cut_07623

theorem unmarked_context_12_22596_219807 : frontier 9 ⟨219807, by decide⟩
    (prefixCache 12 22596) (prefixPartial 12 22596) = false := by
  decide +kernel

theorem node_context_12_22596_219807 : EJMOriginalGlobalDAGData.nodes 9 ⟨219807, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219771, by decide⟩,⟨219795, by decide⟩,⟨219806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22596_219807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22596 ⟨219807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22596
    ⟨219807, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219771, by decide⟩,⟨219795, by decide⟩,⟨219806, by decide⟩]) unmarked_context_12_22596_219807 node_context_12_22596_219807
  intro a
  fin_cases a
  · exact context_13_90384_3444
  · exact context_13_90385_219771
  · exact context_13_90386_219795
  · exact context_13_90387_219806

theorem selected_cut_07624 : selected 9 ⟨219808, by decide⟩
    (prefixPartial 12 22597) = some ⟨12, 1, 0, 219808, 22597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22597_219808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22597 ⟨219808, by decide⟩ :=
  accepted_of_selected 12 22597 ⟨219808, by decide⟩ ⟨12, 1, 0, 219808, 22597, 1, 65536⟩
    (by decide) selected_cut_07624

theorem selected_cut_07625 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90392) = some ⟨13, 1, 0, 3444, 90392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90392, 1, 16384⟩
    (by decide) selected_cut_07625

theorem selected_cut_07626 : selected 8 ⟨219841, by decide⟩
    (prefixPartial 13 90393) = some ⟨13, 2, 0, 219841, 90393, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_90393_219841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90393 ⟨219841, by decide⟩ :=
  accepted_of_selected 13 90393 ⟨219841, by decide⟩ ⟨13, 2, 0, 219841, 90393, 2785, 16384⟩
    (by decide) selected_cut_07626

theorem selected_cut_07627 : selected 8 ⟨219863, by decide⟩
    (prefixPartial 13 90394) = some ⟨13, 2, 0, 219863, 90394, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_90394_219863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90394 ⟨219863, by decide⟩ :=
  accepted_of_selected 13 90394 ⟨219863, by decide⟩ ⟨13, 2, 0, 219863, 90394, 1713, 16384⟩
    (by decide) selected_cut_07627

theorem selected_cut_07628 : selected 8 ⟨219871, by decide⟩
    (prefixPartial 13 90395) = some ⟨13, 2, 0, 219871, 90395, 861, 16384⟩ := by
  decide +kernel

theorem context_13_90395_219871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90395 ⟨219871, by decide⟩ :=
  accepted_of_selected 13 90395 ⟨219871, by decide⟩ ⟨13, 2, 0, 219871, 90395, 861, 16384⟩
    (by decide) selected_cut_07628

theorem unmarked_context_12_22598_219872 : frontier 9 ⟨219872, by decide⟩
    (prefixCache 12 22598) (prefixPartial 12 22598) = false := by
  decide +kernel

theorem node_context_12_22598_219872 : EJMOriginalGlobalDAGData.nodes 9 ⟨219872, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219841, by decide⟩,⟨219863, by decide⟩,⟨219871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22598_219872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22598 ⟨219872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22598
    ⟨219872, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219841, by decide⟩,⟨219863, by decide⟩,⟨219871, by decide⟩]) unmarked_context_12_22598_219872 node_context_12_22598_219872
  intro a
  fin_cases a
  · exact context_13_90392_3444
  · exact context_13_90393_219841
  · exact context_13_90394_219863
  · exact context_13_90395_219871

theorem selected_cut_07629 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90396) = some ⟨13, 1, 0, 3444, 90396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90396, 1, 16384⟩
    (by decide) selected_cut_07629

theorem selected_cut_07630 : selected 8 ⟨219909, by decide⟩
    (prefixPartial 13 90397) = some ⟨13, 2, 0, 219909, 90397, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_90397_219909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90397 ⟨219909, by decide⟩ :=
  accepted_of_selected 13 90397 ⟨219909, by decide⟩ ⟨13, 2, 0, 219909, 90397, 2781, 16384⟩
    (by decide) selected_cut_07630

theorem selected_cut_07631 : selected 8 ⟨219931, by decide⟩
    (prefixPartial 13 90398) = some ⟨13, 2, 0, 219931, 90398, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_90398_219931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90398 ⟨219931, by decide⟩ :=
  accepted_of_selected 13 90398 ⟨219931, by decide⟩ ⟨13, 2, 0, 219931, 90398, 1573, 16384⟩
    (by decide) selected_cut_07631

theorem selected_cut_07632 : selected 8 ⟨219944, by decide⟩
    (prefixPartial 13 90399) = some ⟨13, 2, 0, 219944, 90399, 953, 16384⟩ := by
  decide +kernel

theorem context_13_90399_219944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90399 ⟨219944, by decide⟩ :=
  accepted_of_selected 13 90399 ⟨219944, by decide⟩ ⟨13, 2, 0, 219944, 90399, 953, 16384⟩
    (by decide) selected_cut_07632

theorem unmarked_context_12_22599_219945 : frontier 9 ⟨219945, by decide⟩
    (prefixCache 12 22599) (prefixPartial 12 22599) = false := by
  decide +kernel

theorem node_context_12_22599_219945 : EJMOriginalGlobalDAGData.nodes 9 ⟨219945, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219909, by decide⟩,⟨219931, by decide⟩,⟨219944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22599_219945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22599 ⟨219945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22599
    ⟨219945, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219909, by decide⟩,⟨219931, by decide⟩,⟨219944, by decide⟩]) unmarked_context_12_22599_219945 node_context_12_22599_219945
  intro a
  fin_cases a
  · exact context_13_90396_3444
  · exact context_13_90397_219909
  · exact context_13_90398_219931
  · exact context_13_90399_219944

theorem unmarked_context_11_5649_219946 : frontier 10 ⟨219946, by decide⟩
    (prefixCache 11 5649) (prefixPartial 11 5649) = false := by
  decide +kernel

theorem node_context_11_5649_219946 : EJMOriginalGlobalDAGData.nodes 10 ⟨219946, by decide⟩ =
    .split (coordinate 11) (![⟨219807, by decide⟩,⟨219808, by decide⟩,⟨219872, by decide⟩,⟨219945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5649_219946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5649 ⟨219946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5649
    ⟨219946, by decide⟩ (by decide) (![⟨219807, by decide⟩,⟨219808, by decide⟩,⟨219872, by decide⟩,⟨219945, by decide⟩]) unmarked_context_11_5649_219946 node_context_11_5649_219946
  intro a
  fin_cases a
  · exact context_12_22596_219807
  · exact context_12_22597_219808
  · exact context_12_22598_219872
  · exact context_12_22599_219945

theorem selected_cut_07633 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90400) = some ⟨13, 1, 0, 3444, 90400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90400, 1, 16384⟩
    (by decide) selected_cut_07633

theorem selected_cut_07634 : selected 8 ⟨219974, by decide⟩
    (prefixPartial 13 90401) = some ⟨13, 2, 0, 219974, 90401, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_90401_219974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90401 ⟨219974, by decide⟩ :=
  accepted_of_selected 13 90401 ⟨219974, by decide⟩ ⟨13, 2, 0, 219974, 90401, 2353, 16384⟩
    (by decide) selected_cut_07634

theorem selected_cut_07635 : selected 8 ⟨219994, by decide⟩
    (prefixPartial 13 90402) = some ⟨13, 2, 0, 219994, 90402, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_90402_219994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90402 ⟨219994, by decide⟩ :=
  accepted_of_selected 13 90402 ⟨219994, by decide⟩ ⟨13, 2, 0, 219994, 90402, 1577, 16384⟩
    (by decide) selected_cut_07635

theorem selected_cut_07636 : selected 8 ⟨220006, by decide⟩
    (prefixPartial 13 90403) = some ⟨13, 2, 0, 220006, 90403, 825, 16384⟩ := by
  decide +kernel

theorem context_13_90403_220006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90403 ⟨220006, by decide⟩ :=
  accepted_of_selected 13 90403 ⟨220006, by decide⟩ ⟨13, 2, 0, 220006, 90403, 825, 16384⟩
    (by decide) selected_cut_07636

theorem unmarked_context_12_22600_220007 : frontier 9 ⟨220007, by decide⟩
    (prefixCache 12 22600) (prefixPartial 12 22600) = false := by
  decide +kernel

theorem node_context_12_22600_220007 : EJMOriginalGlobalDAGData.nodes 9 ⟨220007, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨219974, by decide⟩,⟨219994, by decide⟩,⟨220006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22600_220007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22600 ⟨220007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22600
    ⟨220007, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨219974, by decide⟩,⟨219994, by decide⟩,⟨220006, by decide⟩]) unmarked_context_12_22600_220007 node_context_12_22600_220007
  intro a
  fin_cases a
  · exact context_13_90400_3444
  · exact context_13_90401_219974
  · exact context_13_90402_219994
  · exact context_13_90403_220006

theorem selected_cut_07637 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90404) = some ⟨13, 1, 0, 3444, 90404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90404, 1, 16384⟩
    (by decide) selected_cut_07637

theorem selected_cut_07638 : selected 8 ⟨220059, by decide⟩
    (prefixPartial 13 90405) = some ⟨13, 2, 0, 220059, 90405, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_90405_220059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90405 ⟨220059, by decide⟩ :=
  accepted_of_selected 13 90405 ⟨220059, by decide⟩ ⟨13, 2, 0, 220059, 90405, 3221, 16384⟩
    (by decide) selected_cut_07638

theorem selected_cut_07639 : selected 8 ⟨220088, by decide⟩
    (prefixPartial 13 90406) = some ⟨13, 2, 0, 220088, 90406, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_90406_220088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90406 ⟨220088, by decide⟩ :=
  accepted_of_selected 13 90406 ⟨220088, by decide⟩ ⟨13, 2, 0, 220088, 90406, 2161, 16384⟩
    (by decide) selected_cut_07639

theorem selected_cut_07640 : selected 8 ⟨220102, by decide⟩
    (prefixPartial 13 90407) = some ⟨13, 2, 0, 220102, 90407, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_90407_220102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90407 ⟨220102, by decide⟩ :=
  accepted_of_selected 13 90407 ⟨220102, by decide⟩ ⟨13, 2, 0, 220102, 90407, 1121, 16384⟩
    (by decide) selected_cut_07640

theorem unmarked_context_12_22601_220103 : frontier 9 ⟨220103, by decide⟩
    (prefixCache 12 22601) (prefixPartial 12 22601) = false := by
  decide +kernel

theorem node_context_12_22601_220103 : EJMOriginalGlobalDAGData.nodes 9 ⟨220103, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220059, by decide⟩,⟨220088, by decide⟩,⟨220102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22601_220103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22601 ⟨220103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22601
    ⟨220103, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220059, by decide⟩,⟨220088, by decide⟩,⟨220102, by decide⟩]) unmarked_context_12_22601_220103 node_context_12_22601_220103
  intro a
  fin_cases a
  · exact context_13_90404_3444
  · exact context_13_90405_220059
  · exact context_13_90406_220088
  · exact context_13_90407_220102

theorem selected_cut_07641 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90408) = some ⟨13, 1, 0, 3444, 90408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90408, 1, 16384⟩
    (by decide) selected_cut_07641

theorem selected_cut_07642 : selected 8 ⟨220135, by decide⟩
    (prefixPartial 13 90409) = some ⟨13, 2, 0, 220135, 90409, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_90409_220135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90409 ⟨220135, by decide⟩ :=
  accepted_of_selected 13 90409 ⟨220135, by decide⟩ ⟨13, 2, 0, 220135, 90409, 2445, 16384⟩
    (by decide) selected_cut_07642

theorem selected_cut_07643 : selected 8 ⟨220165, by decide⟩
    (prefixPartial 13 90410) = some ⟨13, 2, 0, 220165, 90410, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_90410_220165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90410 ⟨220165, by decide⟩ :=
  accepted_of_selected 13 90410 ⟨220165, by decide⟩ ⟨13, 2, 0, 220165, 90410, 1797, 16384⟩
    (by decide) selected_cut_07643

theorem selected_cut_07644 : selected 8 ⟨220173, by decide⟩
    (prefixPartial 13 90411) = some ⟨13, 2, 0, 220173, 90411, 773, 16384⟩ := by
  decide +kernel

theorem context_13_90411_220173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90411 ⟨220173, by decide⟩ :=
  accepted_of_selected 13 90411 ⟨220173, by decide⟩ ⟨13, 2, 0, 220173, 90411, 773, 16384⟩
    (by decide) selected_cut_07644

theorem unmarked_context_12_22602_220174 : frontier 9 ⟨220174, by decide⟩
    (prefixCache 12 22602) (prefixPartial 12 22602) = false := by
  decide +kernel

theorem node_context_12_22602_220174 : EJMOriginalGlobalDAGData.nodes 9 ⟨220174, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220135, by decide⟩,⟨220165, by decide⟩,⟨220173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22602_220174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22602 ⟨220174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22602
    ⟨220174, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220135, by decide⟩,⟨220165, by decide⟩,⟨220173, by decide⟩]) unmarked_context_12_22602_220174 node_context_12_22602_220174
  intro a
  fin_cases a
  · exact context_13_90408_3444
  · exact context_13_90409_220135
  · exact context_13_90410_220165
  · exact context_13_90411_220173

theorem selected_cut_07645 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90412) = some ⟨13, 1, 0, 3444, 90412, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90412_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90412 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90412 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90412, 1, 16384⟩
    (by decide) selected_cut_07645

theorem selected_cut_07646 : selected 8 ⟨220201, by decide⟩
    (prefixPartial 13 90413) = some ⟨13, 2, 0, 220201, 90413, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_90413_220201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90413 ⟨220201, by decide⟩ :=
  accepted_of_selected 13 90413 ⟨220201, by decide⟩ ⟨13, 2, 0, 220201, 90413, 2453, 16384⟩
    (by decide) selected_cut_07646

theorem selected_cut_07647 : selected 8 ⟨220227, by decide⟩
    (prefixPartial 13 90414) = some ⟨13, 2, 0, 220227, 90414, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_90414_220227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90414 ⟨220227, by decide⟩ :=
  accepted_of_selected 13 90414 ⟨220227, by decide⟩ ⟨13, 2, 0, 220227, 90414, 1989, 16384⟩
    (by decide) selected_cut_07647

theorem selected_cut_07648 : selected 8 ⟨220239, by decide⟩
    (prefixPartial 13 90415) = some ⟨13, 2, 0, 220239, 90415, 885, 16384⟩ := by
  decide +kernel

theorem context_13_90415_220239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90415 ⟨220239, by decide⟩ :=
  accepted_of_selected 13 90415 ⟨220239, by decide⟩ ⟨13, 2, 0, 220239, 90415, 885, 16384⟩
    (by decide) selected_cut_07648

theorem unmarked_context_12_22603_220240 : frontier 9 ⟨220240, by decide⟩
    (prefixCache 12 22603) (prefixPartial 12 22603) = false := by
  decide +kernel

theorem node_context_12_22603_220240 : EJMOriginalGlobalDAGData.nodes 9 ⟨220240, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220201, by decide⟩,⟨220227, by decide⟩,⟨220239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22603_220240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22603 ⟨220240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22603
    ⟨220240, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220201, by decide⟩,⟨220227, by decide⟩,⟨220239, by decide⟩]) unmarked_context_12_22603_220240 node_context_12_22603_220240
  intro a
  fin_cases a
  · exact context_13_90412_3444
  · exact context_13_90413_220201
  · exact context_13_90414_220227
  · exact context_13_90415_220239

theorem unmarked_context_11_5650_220241 : frontier 10 ⟨220241, by decide⟩
    (prefixCache 11 5650) (prefixPartial 11 5650) = false := by
  decide +kernel

theorem node_context_11_5650_220241 : EJMOriginalGlobalDAGData.nodes 10 ⟨220241, by decide⟩ =
    .split (coordinate 11) (![⟨220007, by decide⟩,⟨220103, by decide⟩,⟨220174, by decide⟩,⟨220240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5650_220241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5650 ⟨220241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5650
    ⟨220241, by decide⟩ (by decide) (![⟨220007, by decide⟩,⟨220103, by decide⟩,⟨220174, by decide⟩,⟨220240, by decide⟩]) unmarked_context_11_5650_220241 node_context_11_5650_220241
  intro a
  fin_cases a
  · exact context_12_22600_220007
  · exact context_12_22601_220103
  · exact context_12_22602_220174
  · exact context_12_22603_220240

theorem selected_cut_07649 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90416) = some ⟨13, 1, 0, 3444, 90416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90416, 1, 16384⟩
    (by decide) selected_cut_07649

theorem selected_cut_07650 : selected 8 ⟨220265, by decide⟩
    (prefixPartial 13 90417) = some ⟨13, 2, 0, 220265, 90417, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_90417_220265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90417 ⟨220265, by decide⟩ :=
  accepted_of_selected 13 90417 ⟨220265, by decide⟩ ⟨13, 2, 0, 220265, 90417, 2265, 16384⟩
    (by decide) selected_cut_07650

theorem selected_cut_07651 : selected 8 ⟨220288, by decide⟩
    (prefixPartial 13 90418) = some ⟨13, 2, 0, 220288, 90418, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_90418_220288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90418 ⟨220288, by decide⟩ :=
  accepted_of_selected 13 90418 ⟨220288, by decide⟩ ⟨13, 2, 0, 220288, 90418, 1489, 16384⟩
    (by decide) selected_cut_07651

theorem selected_cut_07652 : selected 8 ⟨220300, by decide⟩
    (prefixPartial 13 90419) = some ⟨13, 2, 0, 220300, 90419, 989, 16384⟩ := by
  decide +kernel

theorem context_13_90419_220300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90419 ⟨220300, by decide⟩ :=
  accepted_of_selected 13 90419 ⟨220300, by decide⟩ ⟨13, 2, 0, 220300, 90419, 989, 16384⟩
    (by decide) selected_cut_07652

theorem unmarked_context_12_22604_220301 : frontier 9 ⟨220301, by decide⟩
    (prefixCache 12 22604) (prefixPartial 12 22604) = false := by
  decide +kernel

theorem node_context_12_22604_220301 : EJMOriginalGlobalDAGData.nodes 9 ⟨220301, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220265, by decide⟩,⟨220288, by decide⟩,⟨220300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22604_220301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22604 ⟨220301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22604
    ⟨220301, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220265, by decide⟩,⟨220288, by decide⟩,⟨220300, by decide⟩]) unmarked_context_12_22604_220301 node_context_12_22604_220301
  intro a
  fin_cases a
  · exact context_13_90416_3444
  · exact context_13_90417_220265
  · exact context_13_90418_220288
  · exact context_13_90419_220300

theorem selected_cut_07653 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90420) = some ⟨13, 1, 0, 3444, 90420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90420, 1, 16384⟩
    (by decide) selected_cut_07653

theorem selected_cut_07654 : selected 8 ⟨220357, by decide⟩
    (prefixPartial 13 90421) = some ⟨13, 2, 0, 220357, 90421, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_90421_220357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90421 ⟨220357, by decide⟩ :=
  accepted_of_selected 13 90421 ⟨220357, by decide⟩ ⟨13, 2, 0, 220357, 90421, 3173, 16384⟩
    (by decide) selected_cut_07654

theorem selected_cut_07655 : selected 8 ⟨220386, by decide⟩
    (prefixPartial 13 90422) = some ⟨13, 2, 0, 220386, 90422, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_90422_220386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90422 ⟨220386, by decide⟩ :=
  accepted_of_selected 13 90422 ⟨220386, by decide⟩ ⟨13, 2, 0, 220386, 90422, 2105, 16384⟩
    (by decide) selected_cut_07655

theorem selected_cut_07656 : selected 8 ⟨220399, by decide⟩
    (prefixPartial 13 90423) = some ⟨13, 2, 0, 220399, 90423, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_90423_220399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90423 ⟨220399, by decide⟩ :=
  accepted_of_selected 13 90423 ⟨220399, by decide⟩ ⟨13, 2, 0, 220399, 90423, 1217, 16384⟩
    (by decide) selected_cut_07656

theorem unmarked_context_12_22605_220400 : frontier 9 ⟨220400, by decide⟩
    (prefixCache 12 22605) (prefixPartial 12 22605) = false := by
  decide +kernel

theorem node_context_12_22605_220400 : EJMOriginalGlobalDAGData.nodes 9 ⟨220400, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220357, by decide⟩,⟨220386, by decide⟩,⟨220399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22605_220400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22605 ⟨220400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22605
    ⟨220400, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220357, by decide⟩,⟨220386, by decide⟩,⟨220399, by decide⟩]) unmarked_context_12_22605_220400 node_context_12_22605_220400
  intro a
  fin_cases a
  · exact context_13_90420_3444
  · exact context_13_90421_220357
  · exact context_13_90422_220386
  · exact context_13_90423_220399

theorem selected_cut_07657 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90424) = some ⟨13, 1, 0, 3444, 90424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90424, 1, 16384⟩
    (by decide) selected_cut_07657

theorem selected_cut_07658 : selected 8 ⟨220427, by decide⟩
    (prefixPartial 13 90425) = some ⟨13, 2, 0, 220427, 90425, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_90425_220427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90425 ⟨220427, by decide⟩ :=
  accepted_of_selected 13 90425 ⟨220427, by decide⟩ ⟨13, 2, 0, 220427, 90425, 2349, 16384⟩
    (by decide) selected_cut_07658

theorem selected_cut_07659 : selected 8 ⟨220451, by decide⟩
    (prefixPartial 13 90426) = some ⟨13, 2, 0, 220451, 90426, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_90426_220451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90426 ⟨220451, by decide⟩ :=
  accepted_of_selected 13 90426 ⟨220451, by decide⟩ ⟨13, 2, 0, 220451, 90426, 1845, 16384⟩
    (by decide) selected_cut_07659

theorem selected_cut_07660 : selected 8 ⟨220457, by decide⟩
    (prefixPartial 13 90427) = some ⟨13, 2, 0, 220457, 90427, 921, 16384⟩ := by
  decide +kernel

theorem context_13_90427_220457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90427 ⟨220457, by decide⟩ :=
  accepted_of_selected 13 90427 ⟨220457, by decide⟩ ⟨13, 2, 0, 220457, 90427, 921, 16384⟩
    (by decide) selected_cut_07660

theorem unmarked_context_12_22606_220458 : frontier 9 ⟨220458, by decide⟩
    (prefixCache 12 22606) (prefixPartial 12 22606) = false := by
  decide +kernel

theorem node_context_12_22606_220458 : EJMOriginalGlobalDAGData.nodes 9 ⟨220458, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220427, by decide⟩,⟨220451, by decide⟩,⟨220457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22606_220458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22606 ⟨220458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22606
    ⟨220458, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220427, by decide⟩,⟨220451, by decide⟩,⟨220457, by decide⟩]) unmarked_context_12_22606_220458 node_context_12_22606_220458
  intro a
  fin_cases a
  · exact context_13_90424_3444
  · exact context_13_90425_220427
  · exact context_13_90426_220451
  · exact context_13_90427_220457

theorem selected_cut_07661 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90428) = some ⟨13, 1, 0, 3444, 90428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90428, 1, 16384⟩
    (by decide) selected_cut_07661

theorem selected_cut_07662 : selected 8 ⟨220484, by decide⟩
    (prefixPartial 13 90429) = some ⟨13, 2, 0, 220484, 90429, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_90429_220484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90429 ⟨220484, by decide⟩ :=
  accepted_of_selected 13 90429 ⟨220484, by decide⟩ ⟨13, 2, 0, 220484, 90429, 2389, 16384⟩
    (by decide) selected_cut_07662

theorem selected_cut_07663 : selected 8 ⟨220506, by decide⟩
    (prefixPartial 13 90430) = some ⟨13, 2, 0, 220506, 90430, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_90430_220506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90430 ⟨220506, by decide⟩ :=
  accepted_of_selected 13 90430 ⟨220506, by decide⟩ ⟨13, 2, 0, 220506, 90430, 1741, 16384⟩
    (by decide) selected_cut_07663

theorem selected_cut_07664 : selected 8 ⟨220516, by decide⟩
    (prefixPartial 13 90431) = some ⟨13, 2, 0, 220516, 90431, 889, 16384⟩ := by
  decide +kernel

theorem context_13_90431_220516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90431 ⟨220516, by decide⟩ :=
  accepted_of_selected 13 90431 ⟨220516, by decide⟩ ⟨13, 2, 0, 220516, 90431, 889, 16384⟩
    (by decide) selected_cut_07664

theorem unmarked_context_12_22607_220517 : frontier 9 ⟨220517, by decide⟩
    (prefixCache 12 22607) (prefixPartial 12 22607) = false := by
  decide +kernel

theorem node_context_12_22607_220517 : EJMOriginalGlobalDAGData.nodes 9 ⟨220517, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220484, by decide⟩,⟨220506, by decide⟩,⟨220516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22607_220517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22607 ⟨220517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22607
    ⟨220517, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220484, by decide⟩,⟨220506, by decide⟩,⟨220516, by decide⟩]) unmarked_context_12_22607_220517 node_context_12_22607_220517
  intro a
  fin_cases a
  · exact context_13_90428_3444
  · exact context_13_90429_220484
  · exact context_13_90430_220506
  · exact context_13_90431_220516

theorem unmarked_context_11_5651_220518 : frontier 10 ⟨220518, by decide⟩
    (prefixCache 11 5651) (prefixPartial 11 5651) = false := by
  decide +kernel

theorem node_context_11_5651_220518 : EJMOriginalGlobalDAGData.nodes 10 ⟨220518, by decide⟩ =
    .split (coordinate 11) (![⟨220301, by decide⟩,⟨220400, by decide⟩,⟨220458, by decide⟩,⟨220517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5651_220518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5651 ⟨220518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5651
    ⟨220518, by decide⟩ (by decide) (![⟨220301, by decide⟩,⟨220400, by decide⟩,⟨220458, by decide⟩,⟨220517, by decide⟩]) unmarked_context_11_5651_220518 node_context_11_5651_220518
  intro a
  fin_cases a
  · exact context_12_22604_220301
  · exact context_12_22605_220400
  · exact context_12_22606_220458
  · exact context_12_22607_220517

theorem unmarked_context_10_1412_220519 : frontier 11 ⟨220519, by decide⟩
    (prefixCache 10 1412) (prefixPartial 10 1412) = false := by
  decide +kernel

theorem node_context_10_1412_220519 : EJMOriginalGlobalDAGData.nodes 11 ⟨220519, by decide⟩ =
    .split (coordinate 10) (![⟨219724, by decide⟩,⟨219946, by decide⟩,⟨220241, by decide⟩,⟨220518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1412_220519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1412 ⟨220519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1412
    ⟨220519, by decide⟩ (by decide) (![⟨219724, by decide⟩,⟨219946, by decide⟩,⟨220241, by decide⟩,⟨220518, by decide⟩]) unmarked_context_10_1412_220519 node_context_10_1412_220519
  intro a
  fin_cases a
  · exact context_11_5648_219724
  · exact context_11_5649_219946
  · exact context_11_5650_220241
  · exact context_11_5651_220518

theorem selected_cut_07665 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90432) = some ⟨13, 1, 0, 3444, 90432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90432, 1, 16384⟩
    (by decide) selected_cut_07665

theorem selected_cut_07666 : selected 8 ⟨220607, by decide⟩
    (prefixPartial 13 90433) = some ⟨13, 2, 0, 220607, 90433, 3737, 16384⟩ := by
  decide +kernel

theorem context_13_90433_220607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90433 ⟨220607, by decide⟩ :=
  accepted_of_selected 13 90433 ⟨220607, by decide⟩ ⟨13, 2, 0, 220607, 90433, 3737, 16384⟩
    (by decide) selected_cut_07666

theorem selected_cut_07667 : selected 8 ⟨220645, by decide⟩
    (prefixPartial 13 90434) = some ⟨13, 2, 0, 220645, 90434, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_90434_220645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90434 ⟨220645, by decide⟩ :=
  accepted_of_selected 13 90434 ⟨220645, by decide⟩ ⟨13, 2, 0, 220645, 90434, 2561, 16384⟩
    (by decide) selected_cut_07667

theorem selected_cut_07668 : selected 8 ⟨220669, by decide⟩
    (prefixPartial 13 90435) = some ⟨13, 2, 0, 220669, 90435, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_90435_220669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90435 ⟨220669, by decide⟩ :=
  accepted_of_selected 13 90435 ⟨220669, by decide⟩ ⟨13, 2, 0, 220669, 90435, 1501, 16384⟩
    (by decide) selected_cut_07668

theorem unmarked_context_12_22608_220670 : frontier 9 ⟨220670, by decide⟩
    (prefixCache 12 22608) (prefixPartial 12 22608) = false := by
  decide +kernel

theorem node_context_12_22608_220670 : EJMOriginalGlobalDAGData.nodes 9 ⟨220670, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220607, by decide⟩,⟨220645, by decide⟩,⟨220669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22608_220670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22608 ⟨220670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22608
    ⟨220670, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220607, by decide⟩,⟨220645, by decide⟩,⟨220669, by decide⟩]) unmarked_context_12_22608_220670 node_context_12_22608_220670
  intro a
  fin_cases a
  · exact context_13_90432_3444
  · exact context_13_90433_220607
  · exact context_13_90434_220645
  · exact context_13_90435_220669

theorem selected_cut_07669 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 22609) = some ⟨12, 1, 0, 126371, 22609, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22609_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22609 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 22609 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 22609, 1, 65536⟩
    (by decide) selected_cut_07669

theorem selected_cut_07670 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90440) = some ⟨13, 1, 0, 3444, 90440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90440, 1, 16384⟩
    (by decide) selected_cut_07670

theorem selected_cut_07671 : selected 8 ⟨220697, by decide⟩
    (prefixPartial 13 90441) = some ⟨13, 2, 0, 220697, 90441, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_90441_220697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90441 ⟨220697, by decide⟩ :=
  accepted_of_selected 13 90441 ⟨220697, by decide⟩ ⟨13, 2, 0, 220697, 90441, 2349, 16384⟩
    (by decide) selected_cut_07671

theorem selected_cut_07672 : selected 8 ⟨220721, by decide⟩
    (prefixPartial 13 90442) = some ⟨13, 2, 0, 220721, 90442, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_90442_220721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90442 ⟨220721, by decide⟩ :=
  accepted_of_selected 13 90442 ⟨220721, by decide⟩ ⟨13, 2, 0, 220721, 90442, 1945, 16384⟩
    (by decide) selected_cut_07672

theorem selected_cut_07673 : selected 8 ⟨220732, by decide⟩
    (prefixPartial 13 90443) = some ⟨13, 2, 0, 220732, 90443, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_90443_220732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90443 ⟨220732, by decide⟩ :=
  accepted_of_selected 13 90443 ⟨220732, by decide⟩ ⟨13, 2, 0, 220732, 90443, 1105, 16384⟩
    (by decide) selected_cut_07673

theorem unmarked_context_12_22610_220733 : frontier 9 ⟨220733, by decide⟩
    (prefixCache 12 22610) (prefixPartial 12 22610) = false := by
  decide +kernel

theorem node_context_12_22610_220733 : EJMOriginalGlobalDAGData.nodes 9 ⟨220733, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220697, by decide⟩,⟨220721, by decide⟩,⟨220732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22610_220733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22610 ⟨220733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22610
    ⟨220733, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220697, by decide⟩,⟨220721, by decide⟩,⟨220732, by decide⟩]) unmarked_context_12_22610_220733 node_context_12_22610_220733
  intro a
  fin_cases a
  · exact context_13_90440_3444
  · exact context_13_90441_220697
  · exact context_13_90442_220721
  · exact context_13_90443_220732

theorem selected_cut_07674 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90444) = some ⟨13, 1, 0, 3444, 90444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90444, 1, 16384⟩
    (by decide) selected_cut_07674

theorem selected_cut_07675 : selected 8 ⟨220761, by decide⟩
    (prefixPartial 13 90445) = some ⟨13, 2, 0, 220761, 90445, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_90445_220761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90445 ⟨220761, by decide⟩ :=
  accepted_of_selected 13 90445 ⟨220761, by decide⟩ ⟨13, 2, 0, 220761, 90445, 2457, 16384⟩
    (by decide) selected_cut_07675

theorem selected_cut_07676 : selected 8 ⟨220783, by decide⟩
    (prefixPartial 13 90446) = some ⟨13, 2, 0, 220783, 90446, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_90446_220783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90446 ⟨220783, by decide⟩ :=
  accepted_of_selected 13 90446 ⟨220783, by decide⟩ ⟨13, 2, 0, 220783, 90446, 2021, 16384⟩
    (by decide) selected_cut_07676

theorem selected_cut_07677 : selected 8 ⟨220793, by decide⟩
    (prefixPartial 13 90447) = some ⟨13, 2, 0, 220793, 90447, 913, 16384⟩ := by
  decide +kernel

theorem context_13_90447_220793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90447 ⟨220793, by decide⟩ :=
  accepted_of_selected 13 90447 ⟨220793, by decide⟩ ⟨13, 2, 0, 220793, 90447, 913, 16384⟩
    (by decide) selected_cut_07677

theorem unmarked_context_12_22611_220794 : frontier 9 ⟨220794, by decide⟩
    (prefixCache 12 22611) (prefixPartial 12 22611) = false := by
  decide +kernel

theorem node_context_12_22611_220794 : EJMOriginalGlobalDAGData.nodes 9 ⟨220794, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220761, by decide⟩,⟨220783, by decide⟩,⟨220793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22611_220794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22611 ⟨220794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22611
    ⟨220794, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220761, by decide⟩,⟨220783, by decide⟩,⟨220793, by decide⟩]) unmarked_context_12_22611_220794 node_context_12_22611_220794
  intro a
  fin_cases a
  · exact context_13_90444_3444
  · exact context_13_90445_220761
  · exact context_13_90446_220783
  · exact context_13_90447_220793

theorem unmarked_context_11_5652_220795 : frontier 10 ⟨220795, by decide⟩
    (prefixCache 11 5652) (prefixPartial 11 5652) = false := by
  decide +kernel

theorem node_context_11_5652_220795 : EJMOriginalGlobalDAGData.nodes 10 ⟨220795, by decide⟩ =
    .split (coordinate 11) (![⟨220670, by decide⟩,⟨126371, by decide⟩,⟨220733, by decide⟩,⟨220794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5652_220795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5652 ⟨220795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5652
    ⟨220795, by decide⟩ (by decide) (![⟨220670, by decide⟩,⟨126371, by decide⟩,⟨220733, by decide⟩,⟨220794, by decide⟩]) unmarked_context_11_5652_220795 node_context_11_5652_220795
  intro a
  fin_cases a
  · exact context_12_22608_220670
  · exact context_12_22609_126371
  · exact context_12_22610_220733
  · exact context_12_22611_220794

theorem selected_cut_07678 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90448) = some ⟨13, 1, 0, 3444, 90448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90448, 1, 16384⟩
    (by decide) selected_cut_07678

theorem selected_cut_07679 : selected 8 ⟨220815, by decide⟩
    (prefixPartial 13 90449) = some ⟨13, 2, 0, 220815, 90449, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_90449_220815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90449 ⟨220815, by decide⟩ :=
  accepted_of_selected 13 90449 ⟨220815, by decide⟩ ⟨13, 2, 0, 220815, 90449, 2185, 16384⟩
    (by decide) selected_cut_07679

theorem selected_cut_07680 : selected 8 ⟨220835, by decide⟩
    (prefixPartial 13 90450) = some ⟨13, 2, 0, 220835, 90450, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_90450_220835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90450 ⟨220835, by decide⟩ :=
  accepted_of_selected 13 90450 ⟨220835, by decide⟩ ⟨13, 2, 0, 220835, 90450, 1565, 16384⟩
    (by decide) selected_cut_07680

theorem selected_cut_07681 : selected 8 ⟨220847, by decide⟩
    (prefixPartial 13 90451) = some ⟨13, 2, 0, 220847, 90451, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_90451_220847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90451 ⟨220847, by decide⟩ :=
  accepted_of_selected 13 90451 ⟨220847, by decide⟩ ⟨13, 2, 0, 220847, 90451, 1089, 16384⟩
    (by decide) selected_cut_07681

theorem unmarked_context_12_22612_220848 : frontier 9 ⟨220848, by decide⟩
    (prefixCache 12 22612) (prefixPartial 12 22612) = false := by
  decide +kernel

theorem node_context_12_22612_220848 : EJMOriginalGlobalDAGData.nodes 9 ⟨220848, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220815, by decide⟩,⟨220835, by decide⟩,⟨220847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22612_220848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22612 ⟨220848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22612
    ⟨220848, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220815, by decide⟩,⟨220835, by decide⟩,⟨220847, by decide⟩]) unmarked_context_12_22612_220848 node_context_12_22612_220848
  intro a
  fin_cases a
  · exact context_13_90448_3444
  · exact context_13_90449_220815
  · exact context_13_90450_220835
  · exact context_13_90451_220847

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
