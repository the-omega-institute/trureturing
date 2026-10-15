/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover182
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17571 : selected 9 ⟨447731, by decide⟩
    (prefixPartial 12 70251) = some ⟨12, 2, 0, 447731, 70251, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_70251_447731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70251 ⟨447731, by decide⟩ :=
  accepted_of_selected 12 70251 ⟨447731, by decide⟩ ⟨12, 2, 0, 447731, 70251, 2645, 65536⟩
    (by decide) selected_cut_17571

theorem unmarked_context_11_17562_447732 : frontier 10 ⟨447732, by decide⟩
    (prefixCache 11 17562) (prefixPartial 11 17562) = false := by
  decide +kernel

theorem node_context_11_17562_447732 : EJMOriginalGlobalDAGData.nodes 10 ⟨447732, by decide⟩ =
    .split (coordinate 11) (![⟨447654, by decide⟩,⟨447693, by decide⟩,⟨445248, by decide⟩,⟨447731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17562_447732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17562 ⟨447732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17562
    ⟨447732, by decide⟩ (by decide) (![⟨447654, by decide⟩,⟨447693, by decide⟩,⟨445248, by decide⟩,⟨447731, by decide⟩]) unmarked_context_11_17562_447732 node_context_11_17562_447732
  intro a
  fin_cases a
  · exact context_12_70248_447654
  · exact context_12_70249_447693
  · exact context_12_70250_445248
  · exact context_12_70251_447731

theorem selected_cut_17572 : selected 9 ⟨447773, by decide⟩
    (prefixPartial 12 70252) = some ⟨12, 2, 0, 447773, 70252, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_70252_447773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70252 ⟨447773, by decide⟩ :=
  accepted_of_selected 12 70252 ⟨447773, by decide⟩ ⟨12, 2, 0, 447773, 70252, 2505, 65536⟩
    (by decide) selected_cut_17572

theorem selected_cut_17573 : selected 9 ⟨447828, by decide⟩
    (prefixPartial 12 70253) = some ⟨12, 2, 0, 447828, 70253, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_70253_447828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70253 ⟨447828, by decide⟩ :=
  accepted_of_selected 12 70253 ⟨447828, by decide⟩ ⟨12, 2, 0, 447828, 70253, 2713, 65536⟩
    (by decide) selected_cut_17573

theorem selected_cut_17574 : selected 9 ⟨447863, by decide⟩
    (prefixPartial 12 70254) = some ⟨12, 2, 0, 447863, 70254, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_70254_447863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70254 ⟨447863, by decide⟩ :=
  accepted_of_selected 12 70254 ⟨447863, by decide⟩ ⟨12, 2, 0, 447863, 70254, 2321, 65536⟩
    (by decide) selected_cut_17574

theorem selected_cut_17575 : selected 9 ⟨447891, by decide⟩
    (prefixPartial 12 70255) = some ⟨12, 2, 0, 447891, 70255, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_70255_447891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70255 ⟨447891, by decide⟩ :=
  accepted_of_selected 12 70255 ⟨447891, by decide⟩ ⟨12, 2, 0, 447891, 70255, 2445, 65536⟩
    (by decide) selected_cut_17575

theorem unmarked_context_11_17563_447892 : frontier 10 ⟨447892, by decide⟩
    (prefixCache 11 17563) (prefixPartial 11 17563) = false := by
  decide +kernel

theorem node_context_11_17563_447892 : EJMOriginalGlobalDAGData.nodes 10 ⟨447892, by decide⟩ =
    .split (coordinate 11) (![⟨447773, by decide⟩,⟨447828, by decide⟩,⟨447863, by decide⟩,⟨447891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17563_447892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17563 ⟨447892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17563
    ⟨447892, by decide⟩ (by decide) (![⟨447773, by decide⟩,⟨447828, by decide⟩,⟨447863, by decide⟩,⟨447891, by decide⟩]) unmarked_context_11_17563_447892 node_context_11_17563_447892
  intro a
  fin_cases a
  · exact context_12_70252_447773
  · exact context_12_70253_447828
  · exact context_12_70254_447863
  · exact context_12_70255_447891

theorem unmarked_context_10_4390_447893 : frontier 11 ⟨447893, by decide⟩
    (prefixCache 10 4390) (prefixPartial 10 4390) = false := by
  decide +kernel

theorem node_context_10_4390_447893 : EJMOriginalGlobalDAGData.nodes 11 ⟨447893, by decide⟩ =
    .split (coordinate 10) (![⟨447461, by decide⟩,⟨447617, by decide⟩,⟨447732, by decide⟩,⟨447892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4390_447893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4390 ⟨447893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4390
    ⟨447893, by decide⟩ (by decide) (![⟨447461, by decide⟩,⟨447617, by decide⟩,⟨447732, by decide⟩,⟨447892, by decide⟩]) unmarked_context_10_4390_447893 node_context_10_4390_447893
  intro a
  fin_cases a
  · exact context_11_17560_447461
  · exact context_11_17561_447617
  · exact context_11_17562_447732
  · exact context_11_17563_447892

theorem selected_cut_17576 : selected 9 ⟨447921, by decide⟩
    (prefixPartial 12 70256) = some ⟨12, 2, 0, 447921, 70256, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_70256_447921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70256 ⟨447921, by decide⟩ :=
  accepted_of_selected 12 70256 ⟨447921, by decide⟩ ⟨12, 2, 0, 447921, 70256, 1457, 65536⟩
    (by decide) selected_cut_17576

theorem selected_cut_17577 : selected 9 ⟨447954, by decide⟩
    (prefixPartial 12 70257) = some ⟨12, 2, 0, 447954, 70257, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_70257_447954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70257 ⟨447954, by decide⟩ :=
  accepted_of_selected 12 70257 ⟨447954, by decide⟩ ⟨12, 2, 0, 447954, 70257, 1865, 65536⟩
    (by decide) selected_cut_17577

theorem selected_cut_17578 : selected 9 ⟨447983, by decide⟩
    (prefixPartial 12 70258) = some ⟨12, 2, 0, 447983, 70258, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_70258_447983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70258 ⟨447983, by decide⟩ :=
  accepted_of_selected 12 70258 ⟨447983, by decide⟩ ⟨12, 2, 0, 447983, 70258, 1585, 65536⟩
    (by decide) selected_cut_17578

theorem selected_cut_17579 : selected 9 ⟨448021, by decide⟩
    (prefixPartial 12 70259) = some ⟨12, 2, 0, 448021, 70259, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_70259_448021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70259 ⟨448021, by decide⟩ :=
  accepted_of_selected 12 70259 ⟨448021, by decide⟩ ⟨12, 2, 0, 448021, 70259, 1725, 65536⟩
    (by decide) selected_cut_17579

theorem unmarked_context_11_17564_448022 : frontier 10 ⟨448022, by decide⟩
    (prefixCache 11 17564) (prefixPartial 11 17564) = false := by
  decide +kernel

theorem node_context_11_17564_448022 : EJMOriginalGlobalDAGData.nodes 10 ⟨448022, by decide⟩ =
    .split (coordinate 11) (![⟨447921, by decide⟩,⟨447954, by decide⟩,⟨447983, by decide⟩,⟨448021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17564_448022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17564 ⟨448022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17564
    ⟨448022, by decide⟩ (by decide) (![⟨447921, by decide⟩,⟨447954, by decide⟩,⟨447983, by decide⟩,⟨448021, by decide⟩]) unmarked_context_11_17564_448022 node_context_11_17564_448022
  intro a
  fin_cases a
  · exact context_12_70256_447921
  · exact context_12_70257_447954
  · exact context_12_70258_447983
  · exact context_12_70259_448021

theorem selected_cut_17580 : selected 9 ⟨448055, by decide⟩
    (prefixPartial 12 70260) = some ⟨12, 2, 0, 448055, 70260, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_70260_448055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70260 ⟨448055, by decide⟩ :=
  accepted_of_selected 12 70260 ⟨448055, by decide⟩ ⟨12, 2, 0, 448055, 70260, 1769, 65536⟩
    (by decide) selected_cut_17580

theorem selected_cut_17581 : selected 9 ⟨448086, by decide⟩
    (prefixPartial 12 70261) = some ⟨12, 2, 0, 448086, 70261, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_70261_448086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70261 ⟨448086, by decide⟩ :=
  accepted_of_selected 12 70261 ⟨448086, by decide⟩ ⟨12, 2, 0, 448086, 70261, 1765, 65536⟩
    (by decide) selected_cut_17581

theorem selected_cut_17582 : selected 9 ⟨448111, by decide⟩
    (prefixPartial 12 70262) = some ⟨12, 2, 0, 448111, 70262, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_70262_448111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70262 ⟨448111, by decide⟩ :=
  accepted_of_selected 12 70262 ⟨448111, by decide⟩ ⟨12, 2, 0, 448111, 70262, 1765, 65536⟩
    (by decide) selected_cut_17582

theorem selected_cut_17583 : selected 9 ⟨448147, by decide⟩
    (prefixPartial 12 70263) = some ⟨12, 2, 0, 448147, 70263, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_70263_448147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70263 ⟨448147, by decide⟩ :=
  accepted_of_selected 12 70263 ⟨448147, by decide⟩ ⟨12, 2, 0, 448147, 70263, 1749, 65536⟩
    (by decide) selected_cut_17583

theorem unmarked_context_11_17565_448148 : frontier 10 ⟨448148, by decide⟩
    (prefixCache 11 17565) (prefixPartial 11 17565) = false := by
  decide +kernel

theorem node_context_11_17565_448148 : EJMOriginalGlobalDAGData.nodes 10 ⟨448148, by decide⟩ =
    .split (coordinate 11) (![⟨448055, by decide⟩,⟨448086, by decide⟩,⟨448111, by decide⟩,⟨448147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17565_448148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17565 ⟨448148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17565
    ⟨448148, by decide⟩ (by decide) (![⟨448055, by decide⟩,⟨448086, by decide⟩,⟨448111, by decide⟩,⟨448147, by decide⟩]) unmarked_context_11_17565_448148 node_context_11_17565_448148
  intro a
  fin_cases a
  · exact context_12_70260_448055
  · exact context_12_70261_448086
  · exact context_12_70262_448111
  · exact context_12_70263_448147

theorem selected_cut_17584 : selected 9 ⟨448174, by decide⟩
    (prefixPartial 12 70264) = some ⟨12, 2, 0, 448174, 70264, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_70264_448174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70264 ⟨448174, by decide⟩ :=
  accepted_of_selected 12 70264 ⟨448174, by decide⟩ ⟨12, 2, 0, 448174, 70264, 1517, 65536⟩
    (by decide) selected_cut_17584

theorem selected_cut_17585 : selected 9 ⟨448201, by decide⟩
    (prefixPartial 12 70265) = some ⟨12, 2, 0, 448201, 70265, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_70265_448201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70265 ⟨448201, by decide⟩ :=
  accepted_of_selected 12 70265 ⟨448201, by decide⟩ ⟨12, 2, 0, 448201, 70265, 1713, 65536⟩
    (by decide) selected_cut_17585

theorem selected_cut_17586 : selected 9 ⟨448271, by decide⟩
    (prefixPartial 12 70266) = some ⟨12, 2, 0, 448271, 70266, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_70266_448271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70266 ⟨448271, by decide⟩ :=
  accepted_of_selected 12 70266 ⟨448271, by decide⟩ ⟨12, 2, 0, 448271, 70266, 2201, 65536⟩
    (by decide) selected_cut_17586

theorem selected_cut_17587 : selected 9 ⟨448298, by decide⟩
    (prefixPartial 12 70267) = some ⟨12, 2, 0, 448298, 70267, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_70267_448298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70267 ⟨448298, by decide⟩ :=
  accepted_of_selected 12 70267 ⟨448298, by decide⟩ ⟨12, 2, 0, 448298, 70267, 1445, 65536⟩
    (by decide) selected_cut_17587

theorem unmarked_context_11_17566_448299 : frontier 10 ⟨448299, by decide⟩
    (prefixCache 11 17566) (prefixPartial 11 17566) = false := by
  decide +kernel

theorem node_context_11_17566_448299 : EJMOriginalGlobalDAGData.nodes 10 ⟨448299, by decide⟩ =
    .split (coordinate 11) (![⟨448174, by decide⟩,⟨448201, by decide⟩,⟨448271, by decide⟩,⟨448298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17566_448299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17566 ⟨448299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17566
    ⟨448299, by decide⟩ (by decide) (![⟨448174, by decide⟩,⟨448201, by decide⟩,⟨448271, by decide⟩,⟨448298, by decide⟩]) unmarked_context_11_17566_448299 node_context_11_17566_448299
  intro a
  fin_cases a
  · exact context_12_70264_448174
  · exact context_12_70265_448201
  · exact context_12_70266_448271
  · exact context_12_70267_448298

theorem selected_cut_17588 : selected 9 ⟨448318, by decide⟩
    (prefixPartial 12 70268) = some ⟨12, 2, 0, 448318, 70268, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_70268_448318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70268 ⟨448318, by decide⟩ :=
  accepted_of_selected 12 70268 ⟨448318, by decide⟩ ⟨12, 2, 0, 448318, 70268, 1373, 65536⟩
    (by decide) selected_cut_17588

theorem selected_cut_17589 : selected 9 ⟨448339, by decide⟩
    (prefixPartial 12 70269) = some ⟨12, 2, 0, 448339, 70269, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_70269_448339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70269 ⟨448339, by decide⟩ :=
  accepted_of_selected 12 70269 ⟨448339, by decide⟩ ⟨12, 2, 0, 448339, 70269, 1533, 65536⟩
    (by decide) selected_cut_17589

theorem selected_cut_17590 : selected 9 ⟨448359, by decide⟩
    (prefixPartial 12 70270) = some ⟨12, 2, 0, 448359, 70270, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_70270_448359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70270 ⟨448359, by decide⟩ :=
  accepted_of_selected 12 70270 ⟨448359, by decide⟩ ⟨12, 2, 0, 448359, 70270, 1313, 65536⟩
    (by decide) selected_cut_17590

theorem selected_cut_17591 : selected 9 ⟨448372, by decide⟩
    (prefixPartial 12 70271) = some ⟨12, 2, 0, 448372, 70271, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_70271_448372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70271 ⟨448372, by decide⟩ :=
  accepted_of_selected 12 70271 ⟨448372, by decide⟩ ⟨12, 2, 0, 448372, 70271, 1361, 65536⟩
    (by decide) selected_cut_17591

theorem unmarked_context_11_17567_448373 : frontier 10 ⟨448373, by decide⟩
    (prefixCache 11 17567) (prefixPartial 11 17567) = false := by
  decide +kernel

theorem node_context_11_17567_448373 : EJMOriginalGlobalDAGData.nodes 10 ⟨448373, by decide⟩ =
    .split (coordinate 11) (![⟨448318, by decide⟩,⟨448339, by decide⟩,⟨448359, by decide⟩,⟨448372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17567_448373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17567 ⟨448373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17567
    ⟨448373, by decide⟩ (by decide) (![⟨448318, by decide⟩,⟨448339, by decide⟩,⟨448359, by decide⟩,⟨448372, by decide⟩]) unmarked_context_11_17567_448373 node_context_11_17567_448373
  intro a
  fin_cases a
  · exact context_12_70268_448318
  · exact context_12_70269_448339
  · exact context_12_70270_448359
  · exact context_12_70271_448372

theorem unmarked_context_10_4391_448374 : frontier 11 ⟨448374, by decide⟩
    (prefixCache 10 4391) (prefixPartial 10 4391) = false := by
  decide +kernel

theorem node_context_10_4391_448374 : EJMOriginalGlobalDAGData.nodes 11 ⟨448374, by decide⟩ =
    .split (coordinate 10) (![⟨448022, by decide⟩,⟨448148, by decide⟩,⟨448299, by decide⟩,⟨448373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4391_448374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4391 ⟨448374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4391
    ⟨448374, by decide⟩ (by decide) (![⟨448022, by decide⟩,⟨448148, by decide⟩,⟨448299, by decide⟩,⟨448373, by decide⟩]) unmarked_context_10_4391_448374 node_context_10_4391_448374
  intro a
  fin_cases a
  · exact context_11_17564_448022
  · exact context_11_17565_448148
  · exact context_11_17566_448299
  · exact context_11_17567_448373

theorem unmarked_context_9_1097_448375 : frontier 12 ⟨448375, by decide⟩
    (prefixCache 9 1097) (prefixPartial 9 1097) = false := by
  decide +kernel

theorem node_context_9_1097_448375 : EJMOriginalGlobalDAGData.nodes 12 ⟨448375, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨447260, by decide⟩,⟨447893, by decide⟩,⟨448374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1097_448375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1097 ⟨448375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1097
    ⟨448375, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨447260, by decide⟩,⟨447893, by decide⟩,⟨448374, by decide⟩]) unmarked_context_9_1097_448375 node_context_9_1097_448375
  intro a
  fin_cases a
  · exact context_10_4388_3442
  · exact context_10_4389_447260
  · exact context_10_4390_447893
  · exact context_10_4391_448374

theorem selected_cut_17592 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4392) = some ⟨10, 1, 0, 3442, 4392, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4392_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4392 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4392 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4392, 1, 1048576⟩
    (by decide) selected_cut_17592

theorem selected_cut_17593 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4393) = some ⟨10, 1, 0, 3442, 4393, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4393_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4393 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4393 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4393, 1, 1048576⟩
    (by decide) selected_cut_17593

theorem selected_cut_17594 : selected 10 ⟨448442, by decide⟩
    (prefixPartial 11 17576) = some ⟨11, 2, 0, 448442, 17576, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_17576_448442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17576 ⟨448442, by decide⟩ :=
  accepted_of_selected 11 17576 ⟨448442, by decide⟩ ⟨11, 2, 0, 448442, 17576, 3233, 262144⟩
    (by decide) selected_cut_17594

theorem selected_cut_17595 : selected 10 ⟨448487, by decide⟩
    (prefixPartial 11 17577) = some ⟨11, 2, 0, 448487, 17577, 2581, 262144⟩ := by
  decide +kernel

theorem context_11_17577_448487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17577 ⟨448487, by decide⟩ :=
  accepted_of_selected 11 17577 ⟨448487, by decide⟩ ⟨11, 2, 0, 448487, 17577, 2581, 262144⟩
    (by decide) selected_cut_17595

theorem selected_cut_17596 : selected 10 ⟨448500, by decide⟩
    (prefixPartial 11 17578) = some ⟨11, 2, 0, 448500, 17578, 821, 262144⟩ := by
  decide +kernel

theorem context_11_17578_448500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17578 ⟨448500, by decide⟩ :=
  accepted_of_selected 11 17578 ⟨448500, by decide⟩ ⟨11, 2, 0, 448500, 17578, 821, 262144⟩
    (by decide) selected_cut_17596

theorem selected_cut_17597 : selected 10 ⟨448507, by decide⟩
    (prefixPartial 11 17579) = some ⟨11, 2, 0, 448507, 17579, 561, 262144⟩ := by
  decide +kernel

theorem context_11_17579_448507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17579 ⟨448507, by decide⟩ :=
  accepted_of_selected 11 17579 ⟨448507, by decide⟩ ⟨11, 2, 0, 448507, 17579, 561, 262144⟩
    (by decide) selected_cut_17597

theorem unmarked_context_10_4394_448508 : frontier 11 ⟨448508, by decide⟩
    (prefixCache 10 4394) (prefixPartial 10 4394) = false := by
  decide +kernel

theorem node_context_10_4394_448508 : EJMOriginalGlobalDAGData.nodes 11 ⟨448508, by decide⟩ =
    .split (coordinate 10) (![⟨448442, by decide⟩,⟨448487, by decide⟩,⟨448500, by decide⟩,⟨448507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4394_448508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4394 ⟨448508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4394
    ⟨448508, by decide⟩ (by decide) (![⟨448442, by decide⟩,⟨448487, by decide⟩,⟨448500, by decide⟩,⟨448507, by decide⟩]) unmarked_context_10_4394_448508 node_context_10_4394_448508
  intro a
  fin_cases a
  · exact context_11_17576_448442
  · exact context_11_17577_448487
  · exact context_11_17578_448500
  · exact context_11_17579_448507

theorem selected_cut_17598 : selected 10 ⟨448570, by decide⟩
    (prefixPartial 11 17580) = some ⟨11, 2, 0, 448570, 17580, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_17580_448570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17580 ⟨448570, by decide⟩ :=
  accepted_of_selected 11 17580 ⟨448570, by decide⟩ ⟨11, 2, 0, 448570, 17580, 2545, 262144⟩
    (by decide) selected_cut_17598

theorem selected_cut_17599 : selected 10 ⟨448639, by decide⟩
    (prefixPartial 11 17581) = some ⟨11, 2, 0, 448639, 17581, 2301, 262144⟩ := by
  decide +kernel

theorem context_11_17581_448639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17581 ⟨448639, by decide⟩ :=
  accepted_of_selected 11 17581 ⟨448639, by decide⟩ ⟨11, 2, 0, 448639, 17581, 2301, 262144⟩
    (by decide) selected_cut_17599

theorem selected_cut_17600 : selected 10 ⟨448674, by decide⟩
    (prefixPartial 11 17582) = some ⟨11, 2, 0, 448674, 17582, 1197, 262144⟩ := by
  decide +kernel

theorem context_11_17582_448674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17582 ⟨448674, by decide⟩ :=
  accepted_of_selected 11 17582 ⟨448674, by decide⟩ ⟨11, 2, 0, 448674, 17582, 1197, 262144⟩
    (by decide) selected_cut_17600

theorem selected_cut_17601 : selected 10 ⟨448708, by decide⟩
    (prefixPartial 11 17583) = some ⟨11, 2, 0, 448708, 17583, 1201, 262144⟩ := by
  decide +kernel

theorem context_11_17583_448708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17583 ⟨448708, by decide⟩ :=
  accepted_of_selected 11 17583 ⟨448708, by decide⟩ ⟨11, 2, 0, 448708, 17583, 1201, 262144⟩
    (by decide) selected_cut_17601

theorem unmarked_context_10_4395_448709 : frontier 11 ⟨448709, by decide⟩
    (prefixCache 10 4395) (prefixPartial 10 4395) = false := by
  decide +kernel

theorem node_context_10_4395_448709 : EJMOriginalGlobalDAGData.nodes 11 ⟨448709, by decide⟩ =
    .split (coordinate 10) (![⟨448570, by decide⟩,⟨448639, by decide⟩,⟨448674, by decide⟩,⟨448708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4395_448709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4395 ⟨448709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4395
    ⟨448709, by decide⟩ (by decide) (![⟨448570, by decide⟩,⟨448639, by decide⟩,⟨448674, by decide⟩,⟨448708, by decide⟩]) unmarked_context_10_4395_448709 node_context_10_4395_448709
  intro a
  fin_cases a
  · exact context_11_17580_448570
  · exact context_11_17581_448639
  · exact context_11_17582_448674
  · exact context_11_17583_448708

theorem unmarked_context_9_1098_448710 : frontier 12 ⟨448710, by decide⟩
    (prefixCache 9 1098) (prefixPartial 9 1098) = false := by
  decide +kernel

theorem node_context_9_1098_448710 : EJMOriginalGlobalDAGData.nodes 12 ⟨448710, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨448508, by decide⟩,⟨448709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1098_448710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1098 ⟨448710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1098
    ⟨448710, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨448508, by decide⟩,⟨448709, by decide⟩]) unmarked_context_9_1098_448710 node_context_9_1098_448710
  intro a
  fin_cases a
  · exact context_10_4392_3442
  · exact context_10_4393_3442
  · exact context_10_4394_448508
  · exact context_10_4395_448709

theorem selected_cut_17602 : selected 12 ⟨448745, by decide⟩
    (prefixPartial 9 1099) = some ⟨9, 2, 0, 448745, 1099, 933, 4194304⟩ := by
  decide +kernel

theorem context_9_1099_448745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1099 ⟨448745, by decide⟩ :=
  accepted_of_selected 9 1099 ⟨448745, by decide⟩ ⟨9, 2, 0, 448745, 1099, 933, 4194304⟩
    (by decide) selected_cut_17602

theorem unmarked_context_8_274_448746 : frontier 13 ⟨448746, by decide⟩
    (prefixCache 8 274) (prefixPartial 8 274) = false := by
  decide +kernel

theorem node_context_8_274_448746 : EJMOriginalGlobalDAGData.nodes 13 ⟨448746, by decide⟩ =
    .split (coordinate 8) (![⟨446684, by decide⟩,⟨448375, by decide⟩,⟨448710, by decide⟩,⟨448745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_274_448746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 274 ⟨448746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 274
    ⟨448746, by decide⟩ (by decide) (![⟨446684, by decide⟩,⟨448375, by decide⟩,⟨448710, by decide⟩,⟨448745, by decide⟩]) unmarked_context_8_274_448746 node_context_8_274_448746
  intro a
  fin_cases a
  · exact context_9_1096_446684
  · exact context_9_1097_448375
  · exact context_9_1098_448710
  · exact context_9_1099_448745

theorem selected_cut_17603 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 275) = some ⟨8, 1, 0, 14298, 275, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_275_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 275 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 275 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 275, 1, 16777216⟩
    (by decide) selected_cut_17603

theorem unmarked_context_7_68_448747 : frontier 14 ⟨448747, by decide⟩
    (prefixCache 7 68) (prefixPartial 7 68) = false := by
  decide +kernel

theorem node_context_7_68_448747 : EJMOriginalGlobalDAGData.nodes 14 ⟨448747, by decide⟩ =
    .split (coordinate 7) (![⟨437996, by decide⟩,⟨442539, by decide⟩,⟨448746, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_68_448747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 68 ⟨448747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 68
    ⟨448747, by decide⟩ (by decide) (![⟨437996, by decide⟩,⟨442539, by decide⟩,⟨448746, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_68_448747 node_context_7_68_448747
  intro a
  fin_cases a
  · exact context_8_272_437996
  · exact context_8_273_442539
  · exact context_8_274_448746
  · exact context_8_275_14298

theorem selected_cut_17604 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17664) = some ⟨11, 1, 0, 434745, 17664, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17664_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17664 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17664 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17664, 1, 262144⟩
    (by decide) selected_cut_17604

theorem selected_cut_17605 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 70660) = some ⟨12, 1, 0, 448748, 70660, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70660_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70660 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 70660 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 70660, 1, 65536⟩
    (by decide) selected_cut_17605

theorem selected_cut_17606 : selected 9 ⟨448846, by decide⟩
    (prefixPartial 12 70661) = some ⟨12, 2, 0, 448846, 70661, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_70661_448846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70661 ⟨448846, by decide⟩ :=
  accepted_of_selected 12 70661 ⟨448846, by decide⟩ ⟨12, 2, 0, 448846, 70661, 3233, 65536⟩
    (by decide) selected_cut_17606

theorem selected_cut_17607 : selected 8 ⟨448907, by decide⟩
    (prefixPartial 13 282648) = some ⟨13, 2, 0, 448907, 282648, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_282648_448907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282648 ⟨448907, by decide⟩ :=
  accepted_of_selected 13 282648 ⟨448907, by decide⟩ ⟨13, 2, 0, 448907, 282648, 2345, 16384⟩
    (by decide) selected_cut_17607

theorem selected_cut_17608 : selected 8 ⟨448937, by decide⟩
    (prefixPartial 13 282649) = some ⟨13, 2, 0, 448937, 282649, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_282649_448937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282649 ⟨448937, by decide⟩ :=
  accepted_of_selected 13 282649 ⟨448937, by decide⟩ ⟨13, 2, 0, 448937, 282649, 2205, 16384⟩
    (by decide) selected_cut_17608

theorem selected_cut_17609 : selected 8 ⟨448961, by decide⟩
    (prefixPartial 13 282650) = some ⟨13, 2, 0, 448961, 282650, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_282650_448961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282650 ⟨448961, by decide⟩ :=
  accepted_of_selected 13 282650 ⟨448961, by decide⟩ ⟨13, 2, 0, 448961, 282650, 1689, 16384⟩
    (by decide) selected_cut_17609

theorem selected_cut_17610 : selected 8 ⟨448979, by decide⟩
    (prefixPartial 13 282651) = some ⟨13, 2, 0, 448979, 282651, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_282651_448979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282651 ⟨448979, by decide⟩ :=
  accepted_of_selected 13 282651 ⟨448979, by decide⟩ ⟨13, 2, 0, 448979, 282651, 1053, 16384⟩
    (by decide) selected_cut_17610

theorem unmarked_context_12_70662_448980 : frontier 9 ⟨448980, by decide⟩
    (prefixCache 12 70662) (prefixPartial 12 70662) = false := by
  decide +kernel

theorem node_context_12_70662_448980 : EJMOriginalGlobalDAGData.nodes 9 ⟨448980, by decide⟩ =
    .split (coordinate 12) (![⟨448907, by decide⟩,⟨448937, by decide⟩,⟨448961, by decide⟩,⟨448979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70662_448980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70662 ⟨448980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70662
    ⟨448980, by decide⟩ (by decide) (![⟨448907, by decide⟩,⟨448937, by decide⟩,⟨448961, by decide⟩,⟨448979, by decide⟩]) unmarked_context_12_70662_448980 node_context_12_70662_448980
  intro a
  fin_cases a
  · exact context_13_282648_448907
  · exact context_13_282649_448937
  · exact context_13_282650_448961
  · exact context_13_282651_448979

theorem selected_cut_17611 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70663) = some ⟨12, 1, 0, 893, 70663, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70663_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70663 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70663 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70663, 1, 65536⟩
    (by decide) selected_cut_17611

theorem unmarked_context_11_17665_448981 : frontier 10 ⟨448981, by decide⟩
    (prefixCache 11 17665) (prefixPartial 11 17665) = false := by
  decide +kernel

theorem node_context_11_17665_448981 : EJMOriginalGlobalDAGData.nodes 10 ⟨448981, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448846, by decide⟩,⟨448980, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17665_448981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17665 ⟨448981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17665
    ⟨448981, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448846, by decide⟩,⟨448980, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17665_448981 node_context_11_17665_448981
  intro a
  fin_cases a
  · exact context_12_70660_448748
  · exact context_12_70661_448846
  · exact context_12_70662_448980
  · exact context_12_70663_893

theorem selected_cut_17612 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 70664) = some ⟨12, 1, 0, 448748, 70664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70664_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70664 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 70664 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 70664, 1, 65536⟩
    (by decide) selected_cut_17612

theorem selected_cut_17613 : selected 8 ⟨449043, by decide⟩
    (prefixPartial 13 282660) = some ⟨13, 2, 0, 449043, 282660, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_282660_449043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282660 ⟨449043, by decide⟩ :=
  accepted_of_selected 13 282660 ⟨449043, by decide⟩ ⟨13, 2, 0, 449043, 282660, 1965, 16384⟩
    (by decide) selected_cut_17613

theorem selected_cut_17614 : selected 8 ⟨449094, by decide⟩
    (prefixPartial 13 282661) = some ⟨13, 2, 0, 449094, 282661, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_282661_449094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282661 ⟨449094, by decide⟩ :=
  accepted_of_selected 13 282661 ⟨449094, by decide⟩ ⟨13, 2, 0, 449094, 282661, 2561, 16384⟩
    (by decide) selected_cut_17614

theorem selected_cut_17615 : selected 8 ⟨449117, by decide⟩
    (prefixPartial 13 282662) = some ⟨13, 2, 0, 449117, 282662, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_282662_449117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282662 ⟨449117, by decide⟩ :=
  accepted_of_selected 13 282662 ⟨449117, by decide⟩ ⟨13, 2, 0, 449117, 282662, 1857, 16384⟩
    (by decide) selected_cut_17615

theorem selected_cut_17616 : selected 8 ⟨449128, by decide⟩
    (prefixPartial 13 282663) = some ⟨13, 2, 0, 449128, 282663, 929, 16384⟩ := by
  decide +kernel

theorem context_13_282663_449128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282663 ⟨449128, by decide⟩ :=
  accepted_of_selected 13 282663 ⟨449128, by decide⟩ ⟨13, 2, 0, 449128, 282663, 929, 16384⟩
    (by decide) selected_cut_17616

theorem unmarked_context_12_70665_449129 : frontier 9 ⟨449129, by decide⟩
    (prefixCache 12 70665) (prefixPartial 12 70665) = false := by
  decide +kernel

theorem node_context_12_70665_449129 : EJMOriginalGlobalDAGData.nodes 9 ⟨449129, by decide⟩ =
    .split (coordinate 12) (![⟨449043, by decide⟩,⟨449094, by decide⟩,⟨449117, by decide⟩,⟨449128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70665_449129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70665 ⟨449129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70665
    ⟨449129, by decide⟩ (by decide) (![⟨449043, by decide⟩,⟨449094, by decide⟩,⟨449117, by decide⟩,⟨449128, by decide⟩]) unmarked_context_12_70665_449129 node_context_12_70665_449129
  intro a
  fin_cases a
  · exact context_13_282660_449043
  · exact context_13_282661_449094
  · exact context_13_282662_449117
  · exact context_13_282663_449128

theorem selected_cut_17617 : selected 8 ⟨449189, by decide⟩
    (prefixPartial 13 282664) = some ⟨13, 2, 0, 449189, 282664, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_282664_449189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282664 ⟨449189, by decide⟩ :=
  accepted_of_selected 13 282664 ⟨449189, by decide⟩ ⟨13, 2, 0, 449189, 282664, 2093, 16384⟩
    (by decide) selected_cut_17617

theorem selected_cut_17618 : selected 8 ⟨449224, by decide⟩
    (prefixPartial 13 282665) = some ⟨13, 2, 0, 449224, 282665, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_282665_449224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282665 ⟨449224, by decide⟩ :=
  accepted_of_selected 13 282665 ⟨449224, by decide⟩ ⟨13, 2, 0, 449224, 282665, 2349, 16384⟩
    (by decide) selected_cut_17618

theorem selected_cut_17619 : selected 8 ⟨449246, by decide⟩
    (prefixPartial 13 282666) = some ⟨13, 2, 0, 449246, 282666, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_282666_449246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282666 ⟨449246, by decide⟩ :=
  accepted_of_selected 13 282666 ⟨449246, by decide⟩ ⟨13, 2, 0, 449246, 282666, 1681, 16384⟩
    (by decide) selected_cut_17619

theorem selected_cut_17620 : selected 8 ⟨449256, by decide⟩
    (prefixPartial 13 282667) = some ⟨13, 2, 0, 449256, 282667, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_282667_449256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282667 ⟨449256, by decide⟩ :=
  accepted_of_selected 13 282667 ⟨449256, by decide⟩ ⟨13, 2, 0, 449256, 282667, 1045, 16384⟩
    (by decide) selected_cut_17620

theorem unmarked_context_12_70666_449257 : frontier 9 ⟨449257, by decide⟩
    (prefixCache 12 70666) (prefixPartial 12 70666) = false := by
  decide +kernel

theorem node_context_12_70666_449257 : EJMOriginalGlobalDAGData.nodes 9 ⟨449257, by decide⟩ =
    .split (coordinate 12) (![⟨449189, by decide⟩,⟨449224, by decide⟩,⟨449246, by decide⟩,⟨449256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70666_449257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70666 ⟨449257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70666
    ⟨449257, by decide⟩ (by decide) (![⟨449189, by decide⟩,⟨449224, by decide⟩,⟨449246, by decide⟩,⟨449256, by decide⟩]) unmarked_context_12_70666_449257 node_context_12_70666_449257
  intro a
  fin_cases a
  · exact context_13_282664_449189
  · exact context_13_282665_449224
  · exact context_13_282666_449246
  · exact context_13_282667_449256

theorem selected_cut_17621 : selected 8 ⟨449316, by decide⟩
    (prefixPartial 13 282668) = some ⟨13, 2, 0, 449316, 282668, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_282668_449316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282668 ⟨449316, by decide⟩ :=
  accepted_of_selected 13 282668 ⟨449316, by decide⟩ ⟨13, 2, 0, 449316, 282668, 2381, 16384⟩
    (by decide) selected_cut_17621

theorem selected_cut_17622 : selected 8 ⟨449352, by decide⟩
    (prefixPartial 13 282669) = some ⟨13, 2, 0, 449352, 282669, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_282669_449352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282669 ⟨449352, by decide⟩ :=
  accepted_of_selected 13 282669 ⟨449352, by decide⟩ ⟨13, 2, 0, 449352, 282669, 2485, 16384⟩
    (by decide) selected_cut_17622

theorem selected_cut_17623 : selected 8 ⟨449379, by decide⟩
    (prefixPartial 13 282670) = some ⟨13, 2, 0, 449379, 282670, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_282670_449379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282670 ⟨449379, by decide⟩ :=
  accepted_of_selected 13 282670 ⟨449379, by decide⟩ ⟨13, 2, 0, 449379, 282670, 1957, 16384⟩
    (by decide) selected_cut_17623

theorem selected_cut_17624 : selected 8 ⟨449389, by decide⟩
    (prefixPartial 13 282671) = some ⟨13, 2, 0, 449389, 282671, 977, 16384⟩ := by
  decide +kernel

theorem context_13_282671_449389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282671 ⟨449389, by decide⟩ :=
  accepted_of_selected 13 282671 ⟨449389, by decide⟩ ⟨13, 2, 0, 449389, 282671, 977, 16384⟩
    (by decide) selected_cut_17624

theorem unmarked_context_12_70667_449390 : frontier 9 ⟨449390, by decide⟩
    (prefixCache 12 70667) (prefixPartial 12 70667) = false := by
  decide +kernel

theorem node_context_12_70667_449390 : EJMOriginalGlobalDAGData.nodes 9 ⟨449390, by decide⟩ =
    .split (coordinate 12) (![⟨449316, by decide⟩,⟨449352, by decide⟩,⟨449379, by decide⟩,⟨449389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70667_449390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70667 ⟨449390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70667
    ⟨449390, by decide⟩ (by decide) (![⟨449316, by decide⟩,⟨449352, by decide⟩,⟨449379, by decide⟩,⟨449389, by decide⟩]) unmarked_context_12_70667_449390 node_context_12_70667_449390
  intro a
  fin_cases a
  · exact context_13_282668_449316
  · exact context_13_282669_449352
  · exact context_13_282670_449379
  · exact context_13_282671_449389

theorem unmarked_context_11_17666_449391 : frontier 10 ⟨449391, by decide⟩
    (prefixCache 11 17666) (prefixPartial 11 17666) = false := by
  decide +kernel

theorem node_context_11_17666_449391 : EJMOriginalGlobalDAGData.nodes 10 ⟨449391, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨449129, by decide⟩,⟨449257, by decide⟩,⟨449390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17666_449391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17666 ⟨449391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17666
    ⟨449391, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨449129, by decide⟩,⟨449257, by decide⟩,⟨449390, by decide⟩]) unmarked_context_11_17666_449391 node_context_11_17666_449391
  intro a
  fin_cases a
  · exact context_12_70664_448748
  · exact context_12_70665_449129
  · exact context_12_70666_449257
  · exact context_12_70667_449390

theorem selected_cut_17625 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17667) = some ⟨11, 1, 0, 1736, 17667, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17667_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17667 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17667 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17667, 1, 262144⟩
    (by decide) selected_cut_17625

theorem unmarked_context_10_4416_449392 : frontier 11 ⟨449392, by decide⟩
    (prefixCache 10 4416) (prefixPartial 10 4416) = false := by
  decide +kernel

theorem node_context_10_4416_449392 : EJMOriginalGlobalDAGData.nodes 11 ⟨449392, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨448981, by decide⟩,⟨449391, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4416_449392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4416 ⟨449392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4416
    ⟨449392, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨448981, by decide⟩,⟨449391, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4416_449392 node_context_10_4416_449392
  intro a
  fin_cases a
  · exact context_11_17664_434745
  · exact context_11_17665_448981
  · exact context_11_17666_449391
  · exact context_11_17667_1736

theorem selected_cut_17626 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 70672) = some ⟨12, 1, 0, 435160, 70672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70672_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70672 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 70672 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 70672, 1, 65536⟩
    (by decide) selected_cut_17626

theorem selected_cut_17627 : selected 9 ⟨449441, by decide⟩
    (prefixPartial 12 70673) = some ⟨12, 2, 0, 449441, 70673, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_70673_449441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70673 ⟨449441, by decide⟩ :=
  accepted_of_selected 12 70673 ⟨449441, by decide⟩ ⟨12, 2, 0, 449441, 70673, 2045, 65536⟩
    (by decide) selected_cut_17627

theorem selected_cut_17628 : selected 8 ⟨449463, by decide⟩
    (prefixPartial 13 282696) = some ⟨13, 2, 0, 449463, 282696, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_282696_449463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282696 ⟨449463, by decide⟩ :=
  accepted_of_selected 13 282696 ⟨449463, by decide⟩ ⟨13, 2, 0, 449463, 282696, 1081, 16384⟩
    (by decide) selected_cut_17628

theorem selected_cut_17629 : selected 8 ⟨449482, by decide⟩
    (prefixPartial 13 282697) = some ⟨13, 2, 0, 449482, 282697, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_282697_449482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282697 ⟨449482, by decide⟩ :=
  accepted_of_selected 13 282697 ⟨449482, by decide⟩ ⟨13, 2, 0, 449482, 282697, 1425, 16384⟩
    (by decide) selected_cut_17629

theorem selected_cut_17630 : selected 8 ⟨449496, by decide⟩
    (prefixPartial 13 282698) = some ⟨13, 2, 0, 449496, 282698, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_282698_449496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282698 ⟨449496, by decide⟩ :=
  accepted_of_selected 13 282698 ⟨449496, by decide⟩ ⟨13, 2, 0, 449496, 282698, 1117, 16384⟩
    (by decide) selected_cut_17630

theorem selected_cut_17631 : selected 8 ⟨449502, by decide⟩
    (prefixPartial 13 282699) = some ⟨13, 2, 0, 449502, 282699, 729, 16384⟩ := by
  decide +kernel

theorem context_13_282699_449502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282699 ⟨449502, by decide⟩ :=
  accepted_of_selected 13 282699 ⟨449502, by decide⟩ ⟨13, 2, 0, 449502, 282699, 729, 16384⟩
    (by decide) selected_cut_17631

theorem unmarked_context_12_70674_449503 : frontier 9 ⟨449503, by decide⟩
    (prefixCache 12 70674) (prefixPartial 12 70674) = false := by
  decide +kernel

theorem node_context_12_70674_449503 : EJMOriginalGlobalDAGData.nodes 9 ⟨449503, by decide⟩ =
    .split (coordinate 12) (![⟨449463, by decide⟩,⟨449482, by decide⟩,⟨449496, by decide⟩,⟨449502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70674_449503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70674 ⟨449503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70674
    ⟨449503, by decide⟩ (by decide) (![⟨449463, by decide⟩,⟨449482, by decide⟩,⟨449496, by decide⟩,⟨449502, by decide⟩]) unmarked_context_12_70674_449503 node_context_12_70674_449503
  intro a
  fin_cases a
  · exact context_13_282696_449463
  · exact context_13_282697_449482
  · exact context_13_282698_449496
  · exact context_13_282699_449502

theorem selected_cut_17632 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70675) = some ⟨12, 1, 0, 893, 70675, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70675_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70675 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70675 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70675, 1, 65536⟩
    (by decide) selected_cut_17632

theorem unmarked_context_11_17668_449504 : frontier 10 ⟨449504, by decide⟩
    (prefixCache 11 17668) (prefixPartial 11 17668) = false := by
  decide +kernel

theorem node_context_11_17668_449504 : EJMOriginalGlobalDAGData.nodes 10 ⟨449504, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨449441, by decide⟩,⟨449503, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17668_449504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17668 ⟨449504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17668
    ⟨449504, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨449441, by decide⟩,⟨449503, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17668_449504 node_context_11_17668_449504
  intro a
  fin_cases a
  · exact context_12_70672_435160
  · exact context_12_70673_449441
  · exact context_12_70674_449503
  · exact context_12_70675_893

theorem selected_cut_17633 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 70676) = some ⟨12, 1, 0, 449505, 70676, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70676_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70676 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 70676 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 70676, 1, 65536⟩
    (by decide) selected_cut_17633

theorem selected_cut_17634 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 70677) = some ⟨12, 1, 0, 449506, 70677, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70677_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70677 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 70677 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 70677, 1, 65536⟩
    (by decide) selected_cut_17634

theorem selected_cut_17635 : selected 8 ⟨449561, by decide⟩
    (prefixPartial 13 282712) = some ⟨13, 2, 0, 449561, 282712, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_282712_449561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282712 ⟨449561, by decide⟩ :=
  accepted_of_selected 13 282712 ⟨449561, by decide⟩ ⟨13, 2, 0, 449561, 282712, 2321, 16384⟩
    (by decide) selected_cut_17635

theorem selected_cut_17636 : selected 8 ⟨449602, by decide⟩
    (prefixPartial 13 282713) = some ⟨13, 2, 0, 449602, 282713, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_282713_449602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282713 ⟨449602, by decide⟩ :=
  accepted_of_selected 13 282713 ⟨449602, by decide⟩ ⟨13, 2, 0, 449602, 282713, 2517, 16384⟩
    (by decide) selected_cut_17636

theorem selected_cut_17637 : selected 8 ⟨449628, by decide⟩
    (prefixPartial 13 282714) = some ⟨13, 2, 0, 449628, 282714, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_282714_449628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282714 ⟨449628, by decide⟩ :=
  accepted_of_selected 13 282714 ⟨449628, by decide⟩ ⟨13, 2, 0, 449628, 282714, 1937, 16384⟩
    (by decide) selected_cut_17637

theorem selected_cut_17638 : selected 8 ⟨449638, by decide⟩
    (prefixPartial 13 282715) = some ⟨13, 2, 0, 449638, 282715, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_282715_449638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282715 ⟨449638, by decide⟩ :=
  accepted_of_selected 13 282715 ⟨449638, by decide⟩ ⟨13, 2, 0, 449638, 282715, 1085, 16384⟩
    (by decide) selected_cut_17638

theorem unmarked_context_12_70678_449639 : frontier 9 ⟨449639, by decide⟩
    (prefixCache 12 70678) (prefixPartial 12 70678) = false := by
  decide +kernel

theorem node_context_12_70678_449639 : EJMOriginalGlobalDAGData.nodes 9 ⟨449639, by decide⟩ =
    .split (coordinate 12) (![⟨449561, by decide⟩,⟨449602, by decide⟩,⟨449628, by decide⟩,⟨449638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70678_449639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70678 ⟨449639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70678
    ⟨449639, by decide⟩ (by decide) (![⟨449561, by decide⟩,⟨449602, by decide⟩,⟨449628, by decide⟩,⟨449638, by decide⟩]) unmarked_context_12_70678_449639 node_context_12_70678_449639
  intro a
  fin_cases a
  · exact context_13_282712_449561
  · exact context_13_282713_449602
  · exact context_13_282714_449628
  · exact context_13_282715_449638

theorem selected_cut_17639 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70679) = some ⟨12, 1, 0, 893, 70679, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70679_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70679 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70679 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70679, 1, 65536⟩
    (by decide) selected_cut_17639

theorem unmarked_context_11_17669_449640 : frontier 10 ⟨449640, by decide⟩
    (prefixCache 11 17669) (prefixPartial 11 17669) = false := by
  decide +kernel

theorem node_context_11_17669_449640 : EJMOriginalGlobalDAGData.nodes 10 ⟨449640, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨449506, by decide⟩,⟨449639, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17669_449640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17669 ⟨449640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17669
    ⟨449640, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨449506, by decide⟩,⟨449639, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17669_449640 node_context_11_17669_449640
  intro a
  fin_cases a
  · exact context_12_70676_449505
  · exact context_12_70677_449506
  · exact context_12_70678_449639
  · exact context_12_70679_893

theorem selected_cut_17640 : selected 8 ⟨449676, by decide⟩
    (prefixPartial 13 282720) = some ⟨13, 2, 0, 449676, 282720, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_282720_449676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282720 ⟨449676, by decide⟩ :=
  accepted_of_selected 13 282720 ⟨449676, by decide⟩ ⟨13, 2, 0, 449676, 282720, 1369, 16384⟩
    (by decide) selected_cut_17640

theorem selected_cut_17641 : selected 8 ⟨449710, by decide⟩
    (prefixPartial 13 282721) = some ⟨13, 2, 0, 449710, 282721, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_282721_449710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282721 ⟨449710, by decide⟩ :=
  accepted_of_selected 13 282721 ⟨449710, by decide⟩ ⟨13, 2, 0, 449710, 282721, 2693, 16384⟩
    (by decide) selected_cut_17641

theorem selected_cut_17642 : selected 8 ⟨449730, by decide⟩
    (prefixPartial 13 282722) = some ⟨13, 2, 0, 449730, 282722, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_282722_449730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282722 ⟨449730, by decide⟩ :=
  accepted_of_selected 13 282722 ⟨449730, by decide⟩ ⟨13, 2, 0, 449730, 282722, 1861, 16384⟩
    (by decide) selected_cut_17642

theorem selected_cut_17643 : selected 8 ⟨449737, by decide⟩
    (prefixPartial 13 282723) = some ⟨13, 2, 0, 449737, 282723, 941, 16384⟩ := by
  decide +kernel

theorem context_13_282723_449737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282723 ⟨449737, by decide⟩ :=
  accepted_of_selected 13 282723 ⟨449737, by decide⟩ ⟨13, 2, 0, 449737, 282723, 941, 16384⟩
    (by decide) selected_cut_17643

theorem unmarked_context_12_70680_449738 : frontier 9 ⟨449738, by decide⟩
    (prefixCache 12 70680) (prefixPartial 12 70680) = false := by
  decide +kernel

theorem node_context_12_70680_449738 : EJMOriginalGlobalDAGData.nodes 9 ⟨449738, by decide⟩ =
    .split (coordinate 12) (![⟨449676, by decide⟩,⟨449710, by decide⟩,⟨449730, by decide⟩,⟨449737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70680_449738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70680 ⟨449738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70680
    ⟨449738, by decide⟩ (by decide) (![⟨449676, by decide⟩,⟨449710, by decide⟩,⟨449730, by decide⟩,⟨449737, by decide⟩]) unmarked_context_12_70680_449738 node_context_12_70680_449738
  intro a
  fin_cases a
  · exact context_13_282720_449676
  · exact context_13_282721_449710
  · exact context_13_282722_449730
  · exact context_13_282723_449737

theorem selected_cut_17644 : selected 8 ⟨449762, by decide⟩
    (prefixPartial 13 282724) = some ⟨13, 2, 0, 449762, 282724, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_282724_449762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282724 ⟨449762, by decide⟩ :=
  accepted_of_selected 13 282724 ⟨449762, by decide⟩ ⟨13, 2, 0, 449762, 282724, 1041, 16384⟩
    (by decide) selected_cut_17644

theorem selected_cut_17645 : selected 8 ⟨449790, by decide⟩
    (prefixPartial 13 282725) = some ⟨13, 2, 0, 449790, 282725, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_282725_449790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282725 ⟨449790, by decide⟩ :=
  accepted_of_selected 13 282725 ⟨449790, by decide⟩ ⟨13, 2, 0, 449790, 282725, 1721, 16384⟩
    (by decide) selected_cut_17645

theorem selected_cut_17646 : selected 8 ⟨449808, by decide⟩
    (prefixPartial 13 282726) = some ⟨13, 2, 0, 449808, 282726, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_282726_449808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282726 ⟨449808, by decide⟩ :=
  accepted_of_selected 13 282726 ⟨449808, by decide⟩ ⟨13, 2, 0, 449808, 282726, 1449, 16384⟩
    (by decide) selected_cut_17646

theorem selected_cut_17647 : selected 8 ⟨449815, by decide⟩
    (prefixPartial 13 282727) = some ⟨13, 2, 0, 449815, 282727, 753, 16384⟩ := by
  decide +kernel

theorem context_13_282727_449815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282727 ⟨449815, by decide⟩ :=
  accepted_of_selected 13 282727 ⟨449815, by decide⟩ ⟨13, 2, 0, 449815, 282727, 753, 16384⟩
    (by decide) selected_cut_17647

theorem unmarked_context_12_70681_449816 : frontier 9 ⟨449816, by decide⟩
    (prefixCache 12 70681) (prefixPartial 12 70681) = false := by
  decide +kernel

theorem node_context_12_70681_449816 : EJMOriginalGlobalDAGData.nodes 9 ⟨449816, by decide⟩ =
    .split (coordinate 12) (![⟨449762, by decide⟩,⟨449790, by decide⟩,⟨449808, by decide⟩,⟨449815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70681_449816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70681 ⟨449816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70681
    ⟨449816, by decide⟩ (by decide) (![⟨449762, by decide⟩,⟨449790, by decide⟩,⟨449808, by decide⟩,⟨449815, by decide⟩]) unmarked_context_12_70681_449816 node_context_12_70681_449816
  intro a
  fin_cases a
  · exact context_13_282724_449762
  · exact context_13_282725_449790
  · exact context_13_282726_449808
  · exact context_13_282727_449815

theorem selected_cut_17648 : selected 8 ⟨449836, by decide⟩
    (prefixPartial 13 282728) = some ⟨13, 2, 0, 449836, 282728, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_282728_449836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282728 ⟨449836, by decide⟩ :=
  accepted_of_selected 13 282728 ⟨449836, by decide⟩ ⟨13, 2, 0, 449836, 282728, 1069, 16384⟩
    (by decide) selected_cut_17648

theorem selected_cut_17649 : selected 8 ⟨449868, by decide⟩
    (prefixPartial 13 282729) = some ⟨13, 2, 0, 449868, 282729, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_282729_449868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282729 ⟨449868, by decide⟩ :=
  accepted_of_selected 13 282729 ⟨449868, by decide⟩ ⟨13, 2, 0, 449868, 282729, 1965, 16384⟩
    (by decide) selected_cut_17649

theorem selected_cut_17650 : selected 8 ⟨449884, by decide⟩
    (prefixPartial 13 282730) = some ⟨13, 2, 0, 449884, 282730, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_282730_449884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282730 ⟨449884, by decide⟩ :=
  accepted_of_selected 13 282730 ⟨449884, by decide⟩ ⟨13, 2, 0, 449884, 282730, 1413, 16384⟩
    (by decide) selected_cut_17650

theorem selected_cut_17651 : selected 8 ⟨449890, by decide⟩
    (prefixPartial 13 282731) = some ⟨13, 2, 0, 449890, 282731, 889, 16384⟩ := by
  decide +kernel

theorem context_13_282731_449890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282731 ⟨449890, by decide⟩ :=
  accepted_of_selected 13 282731 ⟨449890, by decide⟩ ⟨13, 2, 0, 449890, 282731, 889, 16384⟩
    (by decide) selected_cut_17651

theorem unmarked_context_12_70682_449891 : frontier 9 ⟨449891, by decide⟩
    (prefixCache 12 70682) (prefixPartial 12 70682) = false := by
  decide +kernel

theorem node_context_12_70682_449891 : EJMOriginalGlobalDAGData.nodes 9 ⟨449891, by decide⟩ =
    .split (coordinate 12) (![⟨449836, by decide⟩,⟨449868, by decide⟩,⟨449884, by decide⟩,⟨449890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70682_449891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70682 ⟨449891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70682
    ⟨449891, by decide⟩ (by decide) (![⟨449836, by decide⟩,⟨449868, by decide⟩,⟨449884, by decide⟩,⟨449890, by decide⟩]) unmarked_context_12_70682_449891 node_context_12_70682_449891
  intro a
  fin_cases a
  · exact context_13_282728_449836
  · exact context_13_282729_449868
  · exact context_13_282730_449884
  · exact context_13_282731_449890

theorem selected_cut_17652 : selected 8 ⟨449922, by decide⟩
    (prefixPartial 13 282732) = some ⟨13, 2, 0, 449922, 282732, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_282732_449922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282732 ⟨449922, by decide⟩ :=
  accepted_of_selected 13 282732 ⟨449922, by decide⟩ ⟨13, 2, 0, 449922, 282732, 1093, 16384⟩
    (by decide) selected_cut_17652

theorem selected_cut_17653 : selected 8 ⟨449951, by decide⟩
    (prefixPartial 13 282733) = some ⟨13, 2, 0, 449951, 282733, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_282733_449951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282733 ⟨449951, by decide⟩ :=
  accepted_of_selected 13 282733 ⟨449951, by decide⟩ ⟨13, 2, 0, 449951, 282733, 2125, 16384⟩
    (by decide) selected_cut_17653

theorem selected_cut_17654 : selected 8 ⟨449969, by decide⟩
    (prefixPartial 13 282734) = some ⟨13, 2, 0, 449969, 282734, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_282734_449969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282734 ⟨449969, by decide⟩ :=
  accepted_of_selected 13 282734 ⟨449969, by decide⟩ ⟨13, 2, 0, 449969, 282734, 1681, 16384⟩
    (by decide) selected_cut_17654

theorem selected_cut_17655 : selected 8 ⟨449974, by decide⟩
    (prefixPartial 13 282735) = some ⟨13, 2, 0, 449974, 282735, 805, 16384⟩ := by
  decide +kernel

theorem context_13_282735_449974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282735 ⟨449974, by decide⟩ :=
  accepted_of_selected 13 282735 ⟨449974, by decide⟩ ⟨13, 2, 0, 449974, 282735, 805, 16384⟩
    (by decide) selected_cut_17655

theorem unmarked_context_12_70683_449975 : frontier 9 ⟨449975, by decide⟩
    (prefixCache 12 70683) (prefixPartial 12 70683) = false := by
  decide +kernel

theorem node_context_12_70683_449975 : EJMOriginalGlobalDAGData.nodes 9 ⟨449975, by decide⟩ =
    .split (coordinate 12) (![⟨449922, by decide⟩,⟨449951, by decide⟩,⟨449969, by decide⟩,⟨449974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70683_449975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70683 ⟨449975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70683
    ⟨449975, by decide⟩ (by decide) (![⟨449922, by decide⟩,⟨449951, by decide⟩,⟨449969, by decide⟩,⟨449974, by decide⟩]) unmarked_context_12_70683_449975 node_context_12_70683_449975
  intro a
  fin_cases a
  · exact context_13_282732_449922
  · exact context_13_282733_449951
  · exact context_13_282734_449969
  · exact context_13_282735_449974

theorem unmarked_context_11_17670_449976 : frontier 10 ⟨449976, by decide⟩
    (prefixCache 11 17670) (prefixPartial 11 17670) = false := by
  decide +kernel

theorem node_context_11_17670_449976 : EJMOriginalGlobalDAGData.nodes 10 ⟨449976, by decide⟩ =
    .split (coordinate 11) (![⟨449738, by decide⟩,⟨449816, by decide⟩,⟨449891, by decide⟩,⟨449975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17670_449976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17670 ⟨449976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17670
    ⟨449976, by decide⟩ (by decide) (![⟨449738, by decide⟩,⟨449816, by decide⟩,⟨449891, by decide⟩,⟨449975, by decide⟩]) unmarked_context_11_17670_449976 node_context_11_17670_449976
  intro a
  fin_cases a
  · exact context_12_70680_449738
  · exact context_12_70681_449816
  · exact context_12_70682_449891
  · exact context_12_70683_449975

theorem selected_cut_17656 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17671) = some ⟨11, 1, 0, 1736, 17671, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17671_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17671 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17671 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17671, 1, 262144⟩
    (by decide) selected_cut_17656

theorem unmarked_context_10_4417_449977 : frontier 11 ⟨449977, by decide⟩
    (prefixCache 10 4417) (prefixPartial 10 4417) = false := by
  decide +kernel

theorem node_context_10_4417_449977 : EJMOriginalGlobalDAGData.nodes 11 ⟨449977, by decide⟩ =
    .split (coordinate 10) (![⟨449504, by decide⟩,⟨449640, by decide⟩,⟨449976, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4417_449977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4417 ⟨449977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4417
    ⟨449977, by decide⟩ (by decide) (![⟨449504, by decide⟩,⟨449640, by decide⟩,⟨449976, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4417_449977 node_context_10_4417_449977
  intro a
  fin_cases a
  · exact context_11_17668_449504
  · exact context_11_17669_449640
  · exact context_11_17670_449976
  · exact context_11_17671_1736

theorem selected_cut_17657 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 70688) = some ⟨12, 1, 0, 435790, 70688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70688_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70688 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 70688 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 70688, 1, 65536⟩
    (by decide) selected_cut_17657

theorem selected_cut_17658 : selected 8 ⟨449999, by decide⟩
    (prefixPartial 13 282756) = some ⟨13, 2, 0, 449999, 282756, 885, 16384⟩ := by
  decide +kernel

theorem context_13_282756_449999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282756 ⟨449999, by decide⟩ :=
  accepted_of_selected 13 282756 ⟨449999, by decide⟩ ⟨13, 2, 0, 449999, 282756, 885, 16384⟩
    (by decide) selected_cut_17658

theorem selected_cut_17659 : selected 8 ⟨450026, by decide⟩
    (prefixPartial 13 282757) = some ⟨13, 2, 0, 450026, 282757, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_282757_450026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282757 ⟨450026, by decide⟩ :=
  accepted_of_selected 13 282757 ⟨450026, by decide⟩ ⟨13, 2, 0, 450026, 282757, 1885, 16384⟩
    (by decide) selected_cut_17659

theorem selected_cut_17660 : selected 8 ⟨450039, by decide⟩
    (prefixPartial 13 282758) = some ⟨13, 2, 0, 450039, 282758, 997, 16384⟩ := by
  decide +kernel

theorem context_13_282758_450039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282758 ⟨450039, by decide⟩ :=
  accepted_of_selected 13 282758 ⟨450039, by decide⟩ ⟨13, 2, 0, 450039, 282758, 997, 16384⟩
    (by decide) selected_cut_17660

theorem selected_cut_17661 : selected 8 ⟨450046, by decide⟩
    (prefixPartial 13 282759) = some ⟨13, 2, 0, 450046, 282759, 653, 16384⟩ := by
  decide +kernel

theorem context_13_282759_450046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282759 ⟨450046, by decide⟩ :=
  accepted_of_selected 13 282759 ⟨450046, by decide⟩ ⟨13, 2, 0, 450046, 282759, 653, 16384⟩
    (by decide) selected_cut_17661

theorem unmarked_context_12_70689_450047 : frontier 9 ⟨450047, by decide⟩
    (prefixCache 12 70689) (prefixPartial 12 70689) = false := by
  decide +kernel

theorem node_context_12_70689_450047 : EJMOriginalGlobalDAGData.nodes 9 ⟨450047, by decide⟩ =
    .split (coordinate 12) (![⟨449999, by decide⟩,⟨450026, by decide⟩,⟨450039, by decide⟩,⟨450046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70689_450047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70689 ⟨450047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70689
    ⟨450047, by decide⟩ (by decide) (![⟨449999, by decide⟩,⟨450026, by decide⟩,⟨450039, by decide⟩,⟨450046, by decide⟩]) unmarked_context_12_70689_450047 node_context_12_70689_450047
  intro a
  fin_cases a
  · exact context_13_282756_449999
  · exact context_13_282757_450026
  · exact context_13_282758_450039
  · exact context_13_282759_450046

theorem selected_cut_17662 : selected 8 ⟨450070, by decide⟩
    (prefixPartial 13 282760) = some ⟨13, 2, 0, 450070, 282760, 841, 16384⟩ := by
  decide +kernel

theorem context_13_282760_450070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282760 ⟨450070, by decide⟩ :=
  accepted_of_selected 13 282760 ⟨450070, by decide⟩ ⟨13, 2, 0, 450070, 282760, 841, 16384⟩
    (by decide) selected_cut_17662

theorem selected_cut_17663 : selected 8 ⟨450097, by decide⟩
    (prefixPartial 13 282761) = some ⟨13, 2, 0, 450097, 282761, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_282761_450097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282761 ⟨450097, by decide⟩ :=
  accepted_of_selected 13 282761 ⟨450097, by decide⟩ ⟨13, 2, 0, 450097, 282761, 2025, 16384⟩
    (by decide) selected_cut_17663

theorem selected_cut_17664 : selected 8 ⟨450117, by decide⟩
    (prefixPartial 13 282762) = some ⟨13, 2, 0, 450117, 282762, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_282762_450117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282762 ⟨450117, by decide⟩ :=
  accepted_of_selected 13 282762 ⟨450117, by decide⟩ ⟨13, 2, 0, 450117, 282762, 1129, 16384⟩
    (by decide) selected_cut_17664

theorem selected_cut_17665 : selected 8 ⟨450123, by decide⟩
    (prefixPartial 13 282763) = some ⟨13, 2, 0, 450123, 282763, 709, 16384⟩ := by
  decide +kernel

theorem context_13_282763_450123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 282763 ⟨450123, by decide⟩ :=
  accepted_of_selected 13 282763 ⟨450123, by decide⟩ ⟨13, 2, 0, 450123, 282763, 709, 16384⟩
    (by decide) selected_cut_17665

theorem unmarked_context_12_70690_450124 : frontier 9 ⟨450124, by decide⟩
    (prefixCache 12 70690) (prefixPartial 12 70690) = false := by
  decide +kernel

theorem node_context_12_70690_450124 : EJMOriginalGlobalDAGData.nodes 9 ⟨450124, by decide⟩ =
    .split (coordinate 12) (![⟨450070, by decide⟩,⟨450097, by decide⟩,⟨450117, by decide⟩,⟨450123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70690_450124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70690 ⟨450124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70690
    ⟨450124, by decide⟩ (by decide) (![⟨450070, by decide⟩,⟨450097, by decide⟩,⟨450117, by decide⟩,⟨450123, by decide⟩]) unmarked_context_12_70690_450124 node_context_12_70690_450124
  intro a
  fin_cases a
  · exact context_13_282760_450070
  · exact context_13_282761_450097
  · exact context_13_282762_450117
  · exact context_13_282763_450123

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
