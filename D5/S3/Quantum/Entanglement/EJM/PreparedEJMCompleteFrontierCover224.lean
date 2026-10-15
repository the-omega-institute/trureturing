/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover223
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21507 : selected 8 ⟨550366, by decide⟩
    (prefixPartial 13 300261) = some ⟨13, 2, 0, 550366, 300261, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_300261_550366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300261 ⟨550366, by decide⟩ :=
  accepted_of_selected 13 300261 ⟨550366, by decide⟩ ⟨13, 2, 0, 550366, 300261, 2057, 16384⟩
    (by decide) selected_cut_21507

theorem selected_cut_21508 : selected 8 ⟨550385, by decide⟩
    (prefixPartial 13 300262) = some ⟨13, 2, 0, 550385, 300262, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_300262_550385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300262 ⟨550385, by decide⟩ :=
  accepted_of_selected 13 300262 ⟨550385, by decide⟩ ⟨13, 2, 0, 550385, 300262, 1737, 16384⟩
    (by decide) selected_cut_21508

theorem selected_cut_21509 : selected 8 ⟨550393, by decide⟩
    (prefixPartial 13 300263) = some ⟨13, 2, 0, 550393, 300263, 957, 16384⟩ := by
  decide +kernel

theorem context_13_300263_550393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300263 ⟨550393, by decide⟩ :=
  accepted_of_selected 13 300263 ⟨550393, by decide⟩ ⟨13, 2, 0, 550393, 300263, 957, 16384⟩
    (by decide) selected_cut_21509

theorem unmarked_context_12_75065_550394 : frontier 9 ⟨550394, by decide⟩
    (prefixCache 12 75065) (prefixPartial 12 75065) = false := by
  decide +kernel

theorem node_context_12_75065_550394 : EJMOriginalGlobalDAGData.nodes 9 ⟨550394, by decide⟩ =
    .split (coordinate 12) (![⟨550341, by decide⟩,⟨550366, by decide⟩,⟨550385, by decide⟩,⟨550393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75065_550394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75065 ⟨550394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75065
    ⟨550394, by decide⟩ (by decide) (![⟨550341, by decide⟩,⟨550366, by decide⟩,⟨550385, by decide⟩,⟨550393, by decide⟩]) unmarked_context_12_75065_550394 node_context_12_75065_550394
  intro a
  fin_cases a
  · exact context_13_300260_550341
  · exact context_13_300261_550366
  · exact context_13_300262_550385
  · exact context_13_300263_550393

theorem selected_cut_21510 : selected 8 ⟨550400, by decide⟩
    (prefixPartial 13 300264) = some ⟨13, 2, 0, 550400, 300264, 281, 16384⟩ := by
  decide +kernel

theorem context_13_300264_550400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300264 ⟨550400, by decide⟩ :=
  accepted_of_selected 13 300264 ⟨550400, by decide⟩ ⟨13, 2, 0, 550400, 300264, 281, 16384⟩
    (by decide) selected_cut_21510

theorem selected_cut_21511 : selected 8 ⟨550425, by decide⟩
    (prefixPartial 13 300265) = some ⟨13, 2, 0, 550425, 300265, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_300265_550425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300265 ⟨550425, by decide⟩ :=
  accepted_of_selected 13 300265 ⟨550425, by decide⟩ ⟨13, 2, 0, 550425, 300265, 2313, 16384⟩
    (by decide) selected_cut_21511

theorem selected_cut_21512 : selected 8 ⟨550448, by decide⟩
    (prefixPartial 13 300266) = some ⟨13, 2, 0, 550448, 300266, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_300266_550448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300266 ⟨550448, by decide⟩ :=
  accepted_of_selected 13 300266 ⟨550448, by decide⟩ ⟨13, 2, 0, 550448, 300266, 1861, 16384⟩
    (by decide) selected_cut_21512

theorem selected_cut_21513 : selected 8 ⟨550460, by decide⟩
    (prefixPartial 13 300267) = some ⟨13, 2, 0, 550460, 300267, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_300267_550460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300267 ⟨550460, by decide⟩ :=
  accepted_of_selected 13 300267 ⟨550460, by decide⟩ ⟨13, 2, 0, 550460, 300267, 1069, 16384⟩
    (by decide) selected_cut_21513

theorem unmarked_context_12_75066_550461 : frontier 9 ⟨550461, by decide⟩
    (prefixCache 12 75066) (prefixPartial 12 75066) = false := by
  decide +kernel

theorem node_context_12_75066_550461 : EJMOriginalGlobalDAGData.nodes 9 ⟨550461, by decide⟩ =
    .split (coordinate 12) (![⟨550400, by decide⟩,⟨550425, by decide⟩,⟨550448, by decide⟩,⟨550460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75066_550461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75066 ⟨550461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75066
    ⟨550461, by decide⟩ (by decide) (![⟨550400, by decide⟩,⟨550425, by decide⟩,⟨550448, by decide⟩,⟨550460, by decide⟩]) unmarked_context_12_75066_550461 node_context_12_75066_550461
  intro a
  fin_cases a
  · exact context_13_300264_550400
  · exact context_13_300265_550425
  · exact context_13_300266_550448
  · exact context_13_300267_550460

theorem selected_cut_21514 : selected 8 ⟨550466, by decide⟩
    (prefixPartial 13 300268) = some ⟨13, 2, 0, 550466, 300268, 249, 16384⟩ := by
  decide +kernel

theorem context_13_300268_550466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300268 ⟨550466, by decide⟩ :=
  accepted_of_selected 13 300268 ⟨550466, by decide⟩ ⟨13, 2, 0, 550466, 300268, 249, 16384⟩
    (by decide) selected_cut_21514

theorem selected_cut_21515 : selected 8 ⟨550496, by decide⟩
    (prefixPartial 13 300269) = some ⟨13, 2, 0, 550496, 300269, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_300269_550496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300269 ⟨550496, by decide⟩ :=
  accepted_of_selected 13 300269 ⟨550496, by decide⟩ ⟨13, 2, 0, 550496, 300269, 2801, 16384⟩
    (by decide) selected_cut_21515

theorem selected_cut_21516 : selected 8 ⟨550526, by decide⟩
    (prefixPartial 13 300270) = some ⟨13, 2, 0, 550526, 300270, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_300270_550526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300270 ⟨550526, by decide⟩ :=
  accepted_of_selected 13 300270 ⟨550526, by decide⟩ ⟨13, 2, 0, 550526, 300270, 2085, 16384⟩
    (by decide) selected_cut_21516

theorem selected_cut_21517 : selected 8 ⟨550539, by decide⟩
    (prefixPartial 13 300271) = some ⟨13, 2, 0, 550539, 300271, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_300271_550539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300271 ⟨550539, by decide⟩ :=
  accepted_of_selected 13 300271 ⟨550539, by decide⟩ ⟨13, 2, 0, 550539, 300271, 1009, 16384⟩
    (by decide) selected_cut_21517

theorem unmarked_context_12_75067_550540 : frontier 9 ⟨550540, by decide⟩
    (prefixCache 12 75067) (prefixPartial 12 75067) = false := by
  decide +kernel

theorem node_context_12_75067_550540 : EJMOriginalGlobalDAGData.nodes 9 ⟨550540, by decide⟩ =
    .split (coordinate 12) (![⟨550466, by decide⟩,⟨550496, by decide⟩,⟨550526, by decide⟩,⟨550539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75067_550540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75067 ⟨550540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75067
    ⟨550540, by decide⟩ (by decide) (![⟨550466, by decide⟩,⟨550496, by decide⟩,⟨550526, by decide⟩,⟨550539, by decide⟩]) unmarked_context_12_75067_550540 node_context_12_75067_550540
  intro a
  fin_cases a
  · exact context_13_300268_550466
  · exact context_13_300269_550496
  · exact context_13_300270_550526
  · exact context_13_300271_550539

theorem unmarked_context_11_18766_550541 : frontier 10 ⟨550541, by decide⟩
    (prefixCache 11 18766) (prefixPartial 11 18766) = false := by
  decide +kernel

theorem node_context_11_18766_550541 : EJMOriginalGlobalDAGData.nodes 10 ⟨550541, by decide⟩ =
    .split (coordinate 11) (![⟨550332, by decide⟩,⟨550394, by decide⟩,⟨550461, by decide⟩,⟨550540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18766_550541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18766 ⟨550541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18766
    ⟨550541, by decide⟩ (by decide) (![⟨550332, by decide⟩,⟨550394, by decide⟩,⟨550461, by decide⟩,⟨550540, by decide⟩]) unmarked_context_11_18766_550541 node_context_11_18766_550541
  intro a
  fin_cases a
  · exact context_12_75064_550332
  · exact context_12_75065_550394
  · exact context_12_75066_550461
  · exact context_12_75067_550540

theorem selected_cut_21518 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75068) = some ⟨12, 1, 0, 445562, 75068, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75068_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75068 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75068 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75068, 1, 65536⟩
    (by decide) selected_cut_21518

theorem selected_cut_21519 : selected 8 ⟨550544, by decide⟩
    (prefixPartial 13 300276) = some ⟨13, 2, 0, 550544, 300276, 117, 16384⟩ := by
  decide +kernel

theorem context_13_300276_550544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300276 ⟨550544, by decide⟩ :=
  accepted_of_selected 13 300276 ⟨550544, by decide⟩ ⟨13, 2, 0, 550544, 300276, 117, 16384⟩
    (by decide) selected_cut_21519

theorem selected_cut_21520 : selected 8 ⟨550567, by decide⟩
    (prefixPartial 13 300277) = some ⟨13, 2, 0, 550567, 300277, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_300277_550567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300277 ⟨550567, by decide⟩ :=
  accepted_of_selected 13 300277 ⟨550567, by decide⟩ ⟨13, 2, 0, 550567, 300277, 2049, 16384⟩
    (by decide) selected_cut_21520

theorem selected_cut_21521 : selected 8 ⟨550588, by decide⟩
    (prefixPartial 13 300278) = some ⟨13, 2, 0, 550588, 300278, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_300278_550588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300278 ⟨550588, by decide⟩ :=
  accepted_of_selected 13 300278 ⟨550588, by decide⟩ ⟨13, 2, 0, 550588, 300278, 1593, 16384⟩
    (by decide) selected_cut_21521

theorem selected_cut_21522 : selected 8 ⟨550597, by decide⟩
    (prefixPartial 13 300279) = some ⟨13, 2, 0, 550597, 300279, 781, 16384⟩ := by
  decide +kernel

theorem context_13_300279_550597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300279 ⟨550597, by decide⟩ :=
  accepted_of_selected 13 300279 ⟨550597, by decide⟩ ⟨13, 2, 0, 550597, 300279, 781, 16384⟩
    (by decide) selected_cut_21522

theorem unmarked_context_12_75069_550598 : frontier 9 ⟨550598, by decide⟩
    (prefixCache 12 75069) (prefixPartial 12 75069) = false := by
  decide +kernel

theorem node_context_12_75069_550598 : EJMOriginalGlobalDAGData.nodes 9 ⟨550598, by decide⟩ =
    .split (coordinate 12) (![⟨550544, by decide⟩,⟨550567, by decide⟩,⟨550588, by decide⟩,⟨550597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75069_550598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75069 ⟨550598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75069
    ⟨550598, by decide⟩ (by decide) (![⟨550544, by decide⟩,⟨550567, by decide⟩,⟨550588, by decide⟩,⟨550597, by decide⟩]) unmarked_context_12_75069_550598 node_context_12_75069_550598
  intro a
  fin_cases a
  · exact context_13_300276_550544
  · exact context_13_300277_550567
  · exact context_13_300278_550588
  · exact context_13_300279_550597

theorem selected_cut_21523 : selected 8 ⟨550602, by decide⟩
    (prefixPartial 13 300280) = some ⟨13, 2, 0, 550602, 300280, 117, 16384⟩ := by
  decide +kernel

theorem context_13_300280_550602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300280 ⟨550602, by decide⟩ :=
  accepted_of_selected 13 300280 ⟨550602, by decide⟩ ⟨13, 2, 0, 550602, 300280, 117, 16384⟩
    (by decide) selected_cut_21523

theorem selected_cut_21524 : selected 8 ⟨550634, by decide⟩
    (prefixPartial 13 300281) = some ⟨13, 2, 0, 550634, 300281, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_300281_550634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300281 ⟨550634, by decide⟩ :=
  accepted_of_selected 13 300281 ⟨550634, by decide⟩ ⟨13, 2, 0, 550634, 300281, 2265, 16384⟩
    (by decide) selected_cut_21524

theorem selected_cut_21525 : selected 8 ⟨550658, by decide⟩
    (prefixPartial 13 300282) = some ⟨13, 2, 0, 550658, 300282, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_300282_550658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300282 ⟨550658, by decide⟩ :=
  accepted_of_selected 13 300282 ⟨550658, by decide⟩ ⟨13, 2, 0, 550658, 300282, 1781, 16384⟩
    (by decide) selected_cut_21525

theorem selected_cut_21526 : selected 8 ⟨550666, by decide⟩
    (prefixPartial 13 300283) = some ⟨13, 2, 0, 550666, 300283, 969, 16384⟩ := by
  decide +kernel

theorem context_13_300283_550666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300283 ⟨550666, by decide⟩ :=
  accepted_of_selected 13 300283 ⟨550666, by decide⟩ ⟨13, 2, 0, 550666, 300283, 969, 16384⟩
    (by decide) selected_cut_21526

theorem unmarked_context_12_75070_550667 : frontier 9 ⟨550667, by decide⟩
    (prefixCache 12 75070) (prefixPartial 12 75070) = false := by
  decide +kernel

theorem node_context_12_75070_550667 : EJMOriginalGlobalDAGData.nodes 9 ⟨550667, by decide⟩ =
    .split (coordinate 12) (![⟨550602, by decide⟩,⟨550634, by decide⟩,⟨550658, by decide⟩,⟨550666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75070_550667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75070 ⟨550667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75070
    ⟨550667, by decide⟩ (by decide) (![⟨550602, by decide⟩,⟨550634, by decide⟩,⟨550658, by decide⟩,⟨550666, by decide⟩]) unmarked_context_12_75070_550667 node_context_12_75070_550667
  intro a
  fin_cases a
  · exact context_13_300280_550602
  · exact context_13_300281_550634
  · exact context_13_300282_550658
  · exact context_13_300283_550666

theorem selected_cut_21527 : selected 8 ⟨550671, by decide⟩
    (prefixPartial 13 300284) = some ⟨13, 2, 0, 550671, 300284, 73, 16384⟩ := by
  decide +kernel

theorem context_13_300284_550671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300284 ⟨550671, by decide⟩ :=
  accepted_of_selected 13 300284 ⟨550671, by decide⟩ ⟨13, 2, 0, 550671, 300284, 73, 16384⟩
    (by decide) selected_cut_21527

theorem selected_cut_21528 : selected 8 ⟨550702, by decide⟩
    (prefixPartial 13 300285) = some ⟨13, 2, 0, 550702, 300285, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_300285_550702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300285 ⟨550702, by decide⟩ :=
  accepted_of_selected 13 300285 ⟨550702, by decide⟩ ⟨13, 2, 0, 550702, 300285, 2725, 16384⟩
    (by decide) selected_cut_21528

theorem selected_cut_21529 : selected 8 ⟨550722, by decide⟩
    (prefixPartial 13 300286) = some ⟨13, 2, 0, 550722, 300286, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_300286_550722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300286 ⟨550722, by decide⟩ :=
  accepted_of_selected 13 300286 ⟨550722, by decide⟩ ⟨13, 2, 0, 550722, 300286, 1965, 16384⟩
    (by decide) selected_cut_21529

theorem selected_cut_21530 : selected 8 ⟨550729, by decide⟩
    (prefixPartial 13 300287) = some ⟨13, 2, 0, 550729, 300287, 889, 16384⟩ := by
  decide +kernel

theorem context_13_300287_550729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300287 ⟨550729, by decide⟩ :=
  accepted_of_selected 13 300287 ⟨550729, by decide⟩ ⟨13, 2, 0, 550729, 300287, 889, 16384⟩
    (by decide) selected_cut_21530

theorem unmarked_context_12_75071_550730 : frontier 9 ⟨550730, by decide⟩
    (prefixCache 12 75071) (prefixPartial 12 75071) = false := by
  decide +kernel

theorem node_context_12_75071_550730 : EJMOriginalGlobalDAGData.nodes 9 ⟨550730, by decide⟩ =
    .split (coordinate 12) (![⟨550671, by decide⟩,⟨550702, by decide⟩,⟨550722, by decide⟩,⟨550729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75071_550730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75071 ⟨550730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75071
    ⟨550730, by decide⟩ (by decide) (![⟨550671, by decide⟩,⟨550702, by decide⟩,⟨550722, by decide⟩,⟨550729, by decide⟩]) unmarked_context_12_75071_550730 node_context_12_75071_550730
  intro a
  fin_cases a
  · exact context_13_300284_550671
  · exact context_13_300285_550702
  · exact context_13_300286_550722
  · exact context_13_300287_550729

theorem unmarked_context_11_18767_550731 : frontier 10 ⟨550731, by decide⟩
    (prefixCache 11 18767) (prefixPartial 11 18767) = false := by
  decide +kernel

theorem node_context_11_18767_550731 : EJMOriginalGlobalDAGData.nodes 10 ⟨550731, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨550598, by decide⟩,⟨550667, by decide⟩,⟨550730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18767_550731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18767 ⟨550731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18767
    ⟨550731, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨550598, by decide⟩,⟨550667, by decide⟩,⟨550730, by decide⟩]) unmarked_context_11_18767_550731 node_context_11_18767_550731
  intro a
  fin_cases a
  · exact context_12_75068_445562
  · exact context_12_75069_550598
  · exact context_12_75070_550667
  · exact context_12_75071_550730

theorem unmarked_context_10_4691_550732 : frontier 11 ⟨550732, by decide⟩
    (prefixCache 10 4691) (prefixPartial 10 4691) = false := by
  decide +kernel

theorem node_context_10_4691_550732 : EJMOriginalGlobalDAGData.nodes 11 ⟨550732, by decide⟩ =
    .split (coordinate 10) (![⟨549710, by decide⟩,⟨550147, by decide⟩,⟨550541, by decide⟩,⟨550731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4691_550732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4691 ⟨550732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4691
    ⟨550732, by decide⟩ (by decide) (![⟨549710, by decide⟩,⟨550147, by decide⟩,⟨550541, by decide⟩,⟨550731, by decide⟩]) unmarked_context_10_4691_550732 node_context_10_4691_550732
  intro a
  fin_cases a
  · exact context_11_18764_549710
  · exact context_11_18765_550147
  · exact context_11_18766_550541
  · exact context_11_18767_550731

theorem unmarked_context_9_1172_550733 : frontier 12 ⟨550733, by decide⟩
    (prefixCache 9 1172) (prefixPartial 9 1172) = false := by
  decide +kernel

theorem node_context_9_1172_550733 : EJMOriginalGlobalDAGData.nodes 12 ⟨550733, by decide⟩ =
    .split (coordinate 9) (![⟨546713, by decide⟩,⟨548177, by decide⟩,⟨549481, by decide⟩,⟨550732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1172_550733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1172 ⟨550733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1172
    ⟨550733, by decide⟩ (by decide) (![⟨546713, by decide⟩,⟨548177, by decide⟩,⟨549481, by decide⟩,⟨550732, by decide⟩]) unmarked_context_9_1172_550733 node_context_9_1172_550733
  intro a
  fin_cases a
  · exact context_10_4688_546713
  · exact context_10_4689_548177
  · exact context_10_4690_549481
  · exact context_10_4691_550732

theorem selected_cut_21531 : selected 9 ⟨550785, by decide⟩
    (prefixPartial 12 75072) = some ⟨12, 2, 0, 550785, 75072, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_75072_550785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75072 ⟨550785, by decide⟩ :=
  accepted_of_selected 12 75072 ⟨550785, by decide⟩ ⟨12, 2, 0, 550785, 75072, 3453, 65536⟩
    (by decide) selected_cut_21531

theorem selected_cut_21532 : selected 9 ⟨550836, by decide⟩
    (prefixPartial 12 75073) = some ⟨12, 2, 0, 550836, 75073, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_75073_550836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75073 ⟨550836, by decide⟩ :=
  accepted_of_selected 12 75073 ⟨550836, by decide⟩ ⟨12, 2, 0, 550836, 75073, 3345, 65536⟩
    (by decide) selected_cut_21532

theorem selected_cut_21533 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300296) = some ⟨13, 1, 0, 3444, 300296, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300296_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300296 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300296 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300296, 1, 16384⟩
    (by decide) selected_cut_21533

theorem selected_cut_21534 : selected 8 ⟨550859, by decide⟩
    (prefixPartial 13 300297) = some ⟨13, 2, 0, 550859, 300297, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_300297_550859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300297 ⟨550859, by decide⟩ :=
  accepted_of_selected 13 300297 ⟨550859, by decide⟩ ⟨13, 2, 0, 550859, 300297, 2041, 16384⟩
    (by decide) selected_cut_21534

theorem selected_cut_21535 : selected 8 ⟨550878, by decide⟩
    (prefixPartial 13 300298) = some ⟨13, 2, 0, 550878, 300298, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_300298_550878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300298 ⟨550878, by decide⟩ :=
  accepted_of_selected 13 300298 ⟨550878, by decide⟩ ⟨13, 2, 0, 550878, 300298, 1853, 16384⟩
    (by decide) selected_cut_21535

theorem selected_cut_21536 : selected 8 ⟨550890, by decide⟩
    (prefixPartial 13 300299) = some ⟨13, 2, 0, 550890, 300299, 957, 16384⟩ := by
  decide +kernel

theorem context_13_300299_550890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300299 ⟨550890, by decide⟩ :=
  accepted_of_selected 13 300299 ⟨550890, by decide⟩ ⟨13, 2, 0, 550890, 300299, 957, 16384⟩
    (by decide) selected_cut_21536

theorem unmarked_context_12_75074_550891 : frontier 9 ⟨550891, by decide⟩
    (prefixCache 12 75074) (prefixPartial 12 75074) = false := by
  decide +kernel

theorem node_context_12_75074_550891 : EJMOriginalGlobalDAGData.nodes 9 ⟨550891, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨550859, by decide⟩,⟨550878, by decide⟩,⟨550890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75074_550891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75074 ⟨550891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75074
    ⟨550891, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨550859, by decide⟩,⟨550878, by decide⟩,⟨550890, by decide⟩]) unmarked_context_12_75074_550891 node_context_12_75074_550891
  intro a
  fin_cases a
  · exact context_13_300296_3444
  · exact context_13_300297_550859
  · exact context_13_300298_550878
  · exact context_13_300299_550890

theorem selected_cut_21537 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300300) = some ⟨13, 1, 0, 3444, 300300, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300300_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300300 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300300 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300300, 1, 16384⟩
    (by decide) selected_cut_21537

theorem selected_cut_21538 : selected 8 ⟨550911, by decide⟩
    (prefixPartial 13 300301) = some ⟨13, 2, 0, 550911, 300301, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_300301_550911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300301 ⟨550911, by decide⟩ :=
  accepted_of_selected 13 300301 ⟨550911, by decide⟩ ⟨13, 2, 0, 550911, 300301, 1937, 16384⟩
    (by decide) selected_cut_21538

theorem selected_cut_21539 : selected 8 ⟨550929, by decide⟩
    (prefixPartial 13 300302) = some ⟨13, 2, 0, 550929, 300302, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_300302_550929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300302 ⟨550929, by decide⟩ :=
  accepted_of_selected 13 300302 ⟨550929, by decide⟩ ⟨13, 2, 0, 550929, 300302, 1889, 16384⟩
    (by decide) selected_cut_21539

theorem selected_cut_21540 : selected 8 ⟨550936, by decide⟩
    (prefixPartial 13 300303) = some ⟨13, 2, 0, 550936, 300303, 813, 16384⟩ := by
  decide +kernel

theorem context_13_300303_550936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300303 ⟨550936, by decide⟩ :=
  accepted_of_selected 13 300303 ⟨550936, by decide⟩ ⟨13, 2, 0, 550936, 300303, 813, 16384⟩
    (by decide) selected_cut_21540

theorem unmarked_context_12_75075_550937 : frontier 9 ⟨550937, by decide⟩
    (prefixCache 12 75075) (prefixPartial 12 75075) = false := by
  decide +kernel

theorem node_context_12_75075_550937 : EJMOriginalGlobalDAGData.nodes 9 ⟨550937, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨550911, by decide⟩,⟨550929, by decide⟩,⟨550936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75075_550937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75075 ⟨550937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75075
    ⟨550937, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨550911, by decide⟩,⟨550929, by decide⟩,⟨550936, by decide⟩]) unmarked_context_12_75075_550937 node_context_12_75075_550937
  intro a
  fin_cases a
  · exact context_13_300300_3444
  · exact context_13_300301_550911
  · exact context_13_300302_550929
  · exact context_13_300303_550936

theorem unmarked_context_11_18768_550938 : frontier 10 ⟨550938, by decide⟩
    (prefixCache 11 18768) (prefixPartial 11 18768) = false := by
  decide +kernel

theorem node_context_11_18768_550938 : EJMOriginalGlobalDAGData.nodes 10 ⟨550938, by decide⟩ =
    .split (coordinate 11) (![⟨550785, by decide⟩,⟨550836, by decide⟩,⟨550891, by decide⟩,⟨550937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18768_550938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18768 ⟨550938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18768
    ⟨550938, by decide⟩ (by decide) (![⟨550785, by decide⟩,⟨550836, by decide⟩,⟨550891, by decide⟩,⟨550937, by decide⟩]) unmarked_context_11_18768_550938 node_context_11_18768_550938
  intro a
  fin_cases a
  · exact context_12_75072_550785
  · exact context_12_75073_550836
  · exact context_12_75074_550891
  · exact context_12_75075_550937

theorem selected_cut_21541 : selected 9 ⟨550979, by decide⟩
    (prefixPartial 12 75076) = some ⟨12, 2, 0, 550979, 75076, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_75076_550979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75076 ⟨550979, by decide⟩ :=
  accepted_of_selected 12 75076 ⟨550979, by decide⟩ ⟨12, 2, 0, 550979, 75076, 2693, 65536⟩
    (by decide) selected_cut_21541

theorem selected_cut_21542 : selected 9 ⟨275013, by decide⟩
    (prefixPartial 12 75077) = some ⟨12, 1, 0, 275013, 75077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75077_275013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75077 ⟨275013, by decide⟩ :=
  accepted_of_selected 12 75077 ⟨275013, by decide⟩ ⟨12, 1, 0, 275013, 75077, 1, 65536⟩
    (by decide) selected_cut_21542

theorem selected_cut_21543 : selected 9 ⟨551037, by decide⟩
    (prefixPartial 12 75078) = some ⟨12, 2, 0, 551037, 75078, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_75078_551037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75078 ⟨551037, by decide⟩ :=
  accepted_of_selected 12 75078 ⟨551037, by decide⟩ ⟨12, 2, 0, 551037, 75078, 3621, 65536⟩
    (by decide) selected_cut_21543

theorem selected_cut_21544 : selected 9 ⟨551093, by decide⟩
    (prefixPartial 12 75079) = some ⟨12, 2, 0, 551093, 75079, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_75079_551093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75079 ⟨551093, by decide⟩ :=
  accepted_of_selected 12 75079 ⟨551093, by decide⟩ ⟨12, 2, 0, 551093, 75079, 3689, 65536⟩
    (by decide) selected_cut_21544

theorem unmarked_context_11_18769_551094 : frontier 10 ⟨551094, by decide⟩
    (prefixCache 11 18769) (prefixPartial 11 18769) = false := by
  decide +kernel

theorem node_context_11_18769_551094 : EJMOriginalGlobalDAGData.nodes 10 ⟨551094, by decide⟩ =
    .split (coordinate 11) (![⟨550979, by decide⟩,⟨275013, by decide⟩,⟨551037, by decide⟩,⟨551093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18769_551094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18769 ⟨551094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18769
    ⟨551094, by decide⟩ (by decide) (![⟨550979, by decide⟩,⟨275013, by decide⟩,⟨551037, by decide⟩,⟨551093, by decide⟩]) unmarked_context_11_18769_551094 node_context_11_18769_551094
  intro a
  fin_cases a
  · exact context_12_75076_550979
  · exact context_12_75077_275013
  · exact context_12_75078_551037
  · exact context_12_75079_551093

theorem selected_cut_21545 : selected 9 ⟨551145, by decide⟩
    (prefixPartial 12 75080) = some ⟨12, 2, 0, 551145, 75080, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_75080_551145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75080 ⟨551145, by decide⟩ :=
  accepted_of_selected 12 75080 ⟨551145, by decide⟩ ⟨12, 2, 0, 551145, 75080, 3905, 65536⟩
    (by decide) selected_cut_21545

theorem selected_cut_21546 : selected 9 ⟨551197, by decide⟩
    (prefixPartial 12 75081) = some ⟨12, 2, 0, 551197, 75081, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_75081_551197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75081 ⟨551197, by decide⟩ :=
  accepted_of_selected 12 75081 ⟨551197, by decide⟩ ⟨12, 2, 0, 551197, 75081, 3737, 65536⟩
    (by decide) selected_cut_21546

theorem selected_cut_21547 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300328) = some ⟨13, 1, 0, 3444, 300328, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300328_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300328 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300328 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300328, 1, 16384⟩
    (by decide) selected_cut_21547

theorem selected_cut_21548 : selected 8 ⟨551222, by decide⟩
    (prefixPartial 13 300329) = some ⟨13, 2, 0, 551222, 300329, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_300329_551222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300329 ⟨551222, by decide⟩ :=
  accepted_of_selected 13 300329 ⟨551222, by decide⟩ ⟨13, 2, 0, 551222, 300329, 1793, 16384⟩
    (by decide) selected_cut_21548

theorem selected_cut_21549 : selected 8 ⟨551244, by decide⟩
    (prefixPartial 13 300330) = some ⟨13, 2, 0, 551244, 300330, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_300330_551244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300330 ⟨551244, by decide⟩ :=
  accepted_of_selected 13 300330 ⟨551244, by decide⟩ ⟨13, 2, 0, 551244, 300330, 1805, 16384⟩
    (by decide) selected_cut_21549

theorem selected_cut_21550 : selected 8 ⟨551256, by decide⟩
    (prefixPartial 13 300331) = some ⟨13, 2, 0, 551256, 300331, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_300331_551256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300331 ⟨551256, by decide⟩ :=
  accepted_of_selected 13 300331 ⟨551256, by decide⟩ ⟨13, 2, 0, 551256, 300331, 1017, 16384⟩
    (by decide) selected_cut_21550

theorem unmarked_context_12_75082_551257 : frontier 9 ⟨551257, by decide⟩
    (prefixCache 12 75082) (prefixPartial 12 75082) = false := by
  decide +kernel

theorem node_context_12_75082_551257 : EJMOriginalGlobalDAGData.nodes 9 ⟨551257, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551222, by decide⟩,⟨551244, by decide⟩,⟨551256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75082_551257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75082 ⟨551257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75082
    ⟨551257, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551222, by decide⟩,⟨551244, by decide⟩,⟨551256, by decide⟩]) unmarked_context_12_75082_551257 node_context_12_75082_551257
  intro a
  fin_cases a
  · exact context_13_300328_3444
  · exact context_13_300329_551222
  · exact context_13_300330_551244
  · exact context_13_300331_551256

theorem selected_cut_21551 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300332) = some ⟨13, 1, 0, 3444, 300332, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300332_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300332 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300332 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300332, 1, 16384⟩
    (by decide) selected_cut_21551

theorem selected_cut_21552 : selected 8 ⟨551287, by decide⟩
    (prefixPartial 13 300333) = some ⟨13, 2, 0, 551287, 300333, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_300333_551287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300333 ⟨551287, by decide⟩ :=
  accepted_of_selected 13 300333 ⟨551287, by decide⟩ ⟨13, 2, 0, 551287, 300333, 1809, 16384⟩
    (by decide) selected_cut_21552

theorem selected_cut_21553 : selected 8 ⟨551325, by decide⟩
    (prefixPartial 13 300334) = some ⟨13, 2, 0, 551325, 300334, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_300334_551325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300334 ⟨551325, by decide⟩ :=
  accepted_of_selected 13 300334 ⟨551325, by decide⟩ ⟨13, 2, 0, 551325, 300334, 2009, 16384⟩
    (by decide) selected_cut_21553

theorem selected_cut_21554 : selected 8 ⟨551335, by decide⟩
    (prefixPartial 13 300335) = some ⟨13, 2, 0, 551335, 300335, 937, 16384⟩ := by
  decide +kernel

theorem context_13_300335_551335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300335 ⟨551335, by decide⟩ :=
  accepted_of_selected 13 300335 ⟨551335, by decide⟩ ⟨13, 2, 0, 551335, 300335, 937, 16384⟩
    (by decide) selected_cut_21554

theorem unmarked_context_12_75083_551336 : frontier 9 ⟨551336, by decide⟩
    (prefixCache 12 75083) (prefixPartial 12 75083) = false := by
  decide +kernel

theorem node_context_12_75083_551336 : EJMOriginalGlobalDAGData.nodes 9 ⟨551336, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551287, by decide⟩,⟨551325, by decide⟩,⟨551335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75083_551336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75083 ⟨551336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75083
    ⟨551336, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551287, by decide⟩,⟨551325, by decide⟩,⟨551335, by decide⟩]) unmarked_context_12_75083_551336 node_context_12_75083_551336
  intro a
  fin_cases a
  · exact context_13_300332_3444
  · exact context_13_300333_551287
  · exact context_13_300334_551325
  · exact context_13_300335_551335

theorem unmarked_context_11_18770_551337 : frontier 10 ⟨551337, by decide⟩
    (prefixCache 11 18770) (prefixPartial 11 18770) = false := by
  decide +kernel

theorem node_context_11_18770_551337 : EJMOriginalGlobalDAGData.nodes 10 ⟨551337, by decide⟩ =
    .split (coordinate 11) (![⟨551145, by decide⟩,⟨551197, by decide⟩,⟨551257, by decide⟩,⟨551336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18770_551337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18770 ⟨551337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18770
    ⟨551337, by decide⟩ (by decide) (![⟨551145, by decide⟩,⟨551197, by decide⟩,⟨551257, by decide⟩,⟨551336, by decide⟩]) unmarked_context_11_18770_551337 node_context_11_18770_551337
  intro a
  fin_cases a
  · exact context_12_75080_551145
  · exact context_12_75081_551197
  · exact context_12_75082_551257
  · exact context_12_75083_551336

theorem selected_cut_21555 : selected 9 ⟨551394, by decide⟩
    (prefixPartial 12 75084) = some ⟨12, 2, 0, 551394, 75084, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_75084_551394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75084 ⟨551394, by decide⟩ :=
  accepted_of_selected 12 75084 ⟨551394, by decide⟩ ⟨12, 2, 0, 551394, 75084, 4021, 65536⟩
    (by decide) selected_cut_21555

theorem selected_cut_21556 : selected 9 ⟨551437, by decide⟩
    (prefixPartial 12 75085) = some ⟨12, 2, 0, 551437, 75085, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_75085_551437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75085 ⟨551437, by decide⟩ :=
  accepted_of_selected 12 75085 ⟨551437, by decide⟩ ⟨12, 2, 0, 551437, 75085, 3569, 65536⟩
    (by decide) selected_cut_21556

theorem selected_cut_21557 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300344) = some ⟨13, 1, 0, 3444, 300344, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300344_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300344 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300344 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300344, 1, 16384⟩
    (by decide) selected_cut_21557

theorem selected_cut_21558 : selected 8 ⟨551464, by decide⟩
    (prefixPartial 13 300345) = some ⟨13, 2, 0, 551464, 300345, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_300345_551464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300345 ⟨551464, by decide⟩ :=
  accepted_of_selected 13 300345 ⟨551464, by decide⟩ ⟨13, 2, 0, 551464, 300345, 1797, 16384⟩
    (by decide) selected_cut_21558

theorem selected_cut_21559 : selected 8 ⟨551485, by decide⟩
    (prefixPartial 13 300346) = some ⟨13, 2, 0, 551485, 300346, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_300346_551485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300346 ⟨551485, by decide⟩ :=
  accepted_of_selected 13 300346 ⟨551485, by decide⟩ ⟨13, 2, 0, 551485, 300346, 1797, 16384⟩
    (by decide) selected_cut_21559

theorem selected_cut_21560 : selected 8 ⟨551497, by decide⟩
    (prefixPartial 13 300347) = some ⟨13, 2, 0, 551497, 300347, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_300347_551497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300347 ⟨551497, by decide⟩ :=
  accepted_of_selected 13 300347 ⟨551497, by decide⟩ ⟨13, 2, 0, 551497, 300347, 1037, 16384⟩
    (by decide) selected_cut_21560

theorem unmarked_context_12_75086_551498 : frontier 9 ⟨551498, by decide⟩
    (prefixCache 12 75086) (prefixPartial 12 75086) = false := by
  decide +kernel

theorem node_context_12_75086_551498 : EJMOriginalGlobalDAGData.nodes 9 ⟨551498, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551464, by decide⟩,⟨551485, by decide⟩,⟨551497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75086_551498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75086 ⟨551498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75086
    ⟨551498, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551464, by decide⟩,⟨551485, by decide⟩,⟨551497, by decide⟩]) unmarked_context_12_75086_551498 node_context_12_75086_551498
  intro a
  fin_cases a
  · exact context_13_300344_3444
  · exact context_13_300345_551464
  · exact context_13_300346_551485
  · exact context_13_300347_551497

theorem selected_cut_21561 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300348) = some ⟨13, 1, 0, 3444, 300348, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300348_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300348 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300348 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300348, 1, 16384⟩
    (by decide) selected_cut_21561

theorem selected_cut_21562 : selected 8 ⟨551515, by decide⟩
    (prefixPartial 13 300349) = some ⟨13, 2, 0, 551515, 300349, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_300349_551515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300349 ⟨551515, by decide⟩ :=
  accepted_of_selected 13 300349 ⟨551515, by decide⟩ ⟨13, 2, 0, 551515, 300349, 1725, 16384⟩
    (by decide) selected_cut_21562

theorem selected_cut_21563 : selected 8 ⟨551537, by decide⟩
    (prefixPartial 13 300350) = some ⟨13, 2, 0, 551537, 300350, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_300350_551537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300350 ⟨551537, by decide⟩ :=
  accepted_of_selected 13 300350 ⟨551537, by decide⟩ ⟨13, 2, 0, 551537, 300350, 1873, 16384⟩
    (by decide) selected_cut_21563

theorem selected_cut_21564 : selected 8 ⟨551545, by decide⟩
    (prefixPartial 13 300351) = some ⟨13, 2, 0, 551545, 300351, 933, 16384⟩ := by
  decide +kernel

theorem context_13_300351_551545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300351 ⟨551545, by decide⟩ :=
  accepted_of_selected 13 300351 ⟨551545, by decide⟩ ⟨13, 2, 0, 551545, 300351, 933, 16384⟩
    (by decide) selected_cut_21564

theorem unmarked_context_12_75087_551546 : frontier 9 ⟨551546, by decide⟩
    (prefixCache 12 75087) (prefixPartial 12 75087) = false := by
  decide +kernel

theorem node_context_12_75087_551546 : EJMOriginalGlobalDAGData.nodes 9 ⟨551546, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551515, by decide⟩,⟨551537, by decide⟩,⟨551545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75087_551546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75087 ⟨551546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75087
    ⟨551546, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551515, by decide⟩,⟨551537, by decide⟩,⟨551545, by decide⟩]) unmarked_context_12_75087_551546 node_context_12_75087_551546
  intro a
  fin_cases a
  · exact context_13_300348_3444
  · exact context_13_300349_551515
  · exact context_13_300350_551537
  · exact context_13_300351_551545

theorem unmarked_context_11_18771_551547 : frontier 10 ⟨551547, by decide⟩
    (prefixCache 11 18771) (prefixPartial 11 18771) = false := by
  decide +kernel

theorem node_context_11_18771_551547 : EJMOriginalGlobalDAGData.nodes 10 ⟨551547, by decide⟩ =
    .split (coordinate 11) (![⟨551394, by decide⟩,⟨551437, by decide⟩,⟨551498, by decide⟩,⟨551546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18771_551547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18771 ⟨551547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18771
    ⟨551547, by decide⟩ (by decide) (![⟨551394, by decide⟩,⟨551437, by decide⟩,⟨551498, by decide⟩,⟨551546, by decide⟩]) unmarked_context_11_18771_551547 node_context_11_18771_551547
  intro a
  fin_cases a
  · exact context_12_75084_551394
  · exact context_12_75085_551437
  · exact context_12_75086_551498
  · exact context_12_75087_551546

theorem unmarked_context_10_4692_551548 : frontier 11 ⟨551548, by decide⟩
    (prefixCache 10 4692) (prefixPartial 10 4692) = false := by
  decide +kernel

theorem node_context_10_4692_551548 : EJMOriginalGlobalDAGData.nodes 11 ⟨551548, by decide⟩ =
    .split (coordinate 10) (![⟨550938, by decide⟩,⟨551094, by decide⟩,⟨551337, by decide⟩,⟨551547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4692_551548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4692 ⟨551548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4692
    ⟨551548, by decide⟩ (by decide) (![⟨550938, by decide⟩,⟨551094, by decide⟩,⟨551337, by decide⟩,⟨551547, by decide⟩]) unmarked_context_10_4692_551548 node_context_10_4692_551548
  intro a
  fin_cases a
  · exact context_11_18768_550938
  · exact context_11_18769_551094
  · exact context_11_18770_551337
  · exact context_11_18771_551547

theorem selected_cut_21565 : selected 9 ⟨551590, by decide⟩
    (prefixPartial 12 75088) = some ⟨12, 2, 0, 551590, 75088, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_75088_551590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75088 ⟨551590, by decide⟩ :=
  accepted_of_selected 12 75088 ⟨551590, by decide⟩ ⟨12, 2, 0, 551590, 75088, 3789, 65536⟩
    (by decide) selected_cut_21565

theorem selected_cut_21566 : selected 9 ⟨551631, by decide⟩
    (prefixPartial 12 75089) = some ⟨12, 2, 0, 551631, 75089, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_75089_551631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75089 ⟨551631, by decide⟩ :=
  accepted_of_selected 12 75089 ⟨551631, by decide⟩ ⟨12, 2, 0, 551631, 75089, 3305, 65536⟩
    (by decide) selected_cut_21566

theorem selected_cut_21567 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300360) = some ⟨13, 1, 0, 3444, 300360, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300360_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300360 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300360 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300360, 1, 16384⟩
    (by decide) selected_cut_21567

theorem selected_cut_21568 : selected 8 ⟨551657, by decide⟩
    (prefixPartial 13 300361) = some ⟨13, 2, 0, 551657, 300361, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_300361_551657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300361 ⟨551657, by decide⟩ :=
  accepted_of_selected 13 300361 ⟨551657, by decide⟩ ⟨13, 2, 0, 551657, 300361, 1889, 16384⟩
    (by decide) selected_cut_21568

theorem selected_cut_21569 : selected 8 ⟨551677, by decide⟩
    (prefixPartial 13 300362) = some ⟨13, 2, 0, 551677, 300362, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_300362_551677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300362 ⟨551677, by decide⟩ :=
  accepted_of_selected 13 300362 ⟨551677, by decide⟩ ⟨13, 2, 0, 551677, 300362, 2113, 16384⟩
    (by decide) selected_cut_21569

theorem selected_cut_21570 : selected 8 ⟨551689, by decide⟩
    (prefixPartial 13 300363) = some ⟨13, 2, 0, 551689, 300363, 953, 16384⟩ := by
  decide +kernel

theorem context_13_300363_551689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300363 ⟨551689, by decide⟩ :=
  accepted_of_selected 13 300363 ⟨551689, by decide⟩ ⟨13, 2, 0, 551689, 300363, 953, 16384⟩
    (by decide) selected_cut_21570

theorem unmarked_context_12_75090_551690 : frontier 9 ⟨551690, by decide⟩
    (prefixCache 12 75090) (prefixPartial 12 75090) = false := by
  decide +kernel

theorem node_context_12_75090_551690 : EJMOriginalGlobalDAGData.nodes 9 ⟨551690, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551657, by decide⟩,⟨551677, by decide⟩,⟨551689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75090_551690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75090 ⟨551690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75090
    ⟨551690, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551657, by decide⟩,⟨551677, by decide⟩,⟨551689, by decide⟩]) unmarked_context_12_75090_551690 node_context_12_75090_551690
  intro a
  fin_cases a
  · exact context_13_300360_3444
  · exact context_13_300361_551657
  · exact context_13_300362_551677
  · exact context_13_300363_551689

theorem selected_cut_21571 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300364) = some ⟨13, 1, 0, 3444, 300364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300364, 1, 16384⟩
    (by decide) selected_cut_21571

theorem selected_cut_21572 : selected 8 ⟨551708, by decide⟩
    (prefixPartial 13 300365) = some ⟨13, 2, 0, 551708, 300365, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_300365_551708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300365 ⟨551708, by decide⟩ :=
  accepted_of_selected 13 300365 ⟨551708, by decide⟩ ⟨13, 2, 0, 551708, 300365, 1797, 16384⟩
    (by decide) selected_cut_21572

theorem selected_cut_21573 : selected 8 ⟨551727, by decide⟩
    (prefixPartial 13 300366) = some ⟨13, 2, 0, 551727, 300366, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_300366_551727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300366 ⟨551727, by decide⟩ :=
  accepted_of_selected 13 300366 ⟨551727, by decide⟩ ⟨13, 2, 0, 551727, 300366, 2065, 16384⟩
    (by decide) selected_cut_21573

theorem selected_cut_21574 : selected 8 ⟨551734, by decide⟩
    (prefixPartial 13 300367) = some ⟨13, 2, 0, 551734, 300367, 877, 16384⟩ := by
  decide +kernel

theorem context_13_300367_551734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300367 ⟨551734, by decide⟩ :=
  accepted_of_selected 13 300367 ⟨551734, by decide⟩ ⟨13, 2, 0, 551734, 300367, 877, 16384⟩
    (by decide) selected_cut_21574

theorem unmarked_context_12_75091_551735 : frontier 9 ⟨551735, by decide⟩
    (prefixCache 12 75091) (prefixPartial 12 75091) = false := by
  decide +kernel

theorem node_context_12_75091_551735 : EJMOriginalGlobalDAGData.nodes 9 ⟨551735, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551708, by decide⟩,⟨551727, by decide⟩,⟨551734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75091_551735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75091 ⟨551735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75091
    ⟨551735, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551708, by decide⟩,⟨551727, by decide⟩,⟨551734, by decide⟩]) unmarked_context_12_75091_551735 node_context_12_75091_551735
  intro a
  fin_cases a
  · exact context_13_300364_3444
  · exact context_13_300365_551708
  · exact context_13_300366_551727
  · exact context_13_300367_551734

theorem unmarked_context_11_18772_551736 : frontier 10 ⟨551736, by decide⟩
    (prefixCache 11 18772) (prefixPartial 11 18772) = false := by
  decide +kernel

theorem node_context_11_18772_551736 : EJMOriginalGlobalDAGData.nodes 10 ⟨551736, by decide⟩ =
    .split (coordinate 11) (![⟨551590, by decide⟩,⟨551631, by decide⟩,⟨551690, by decide⟩,⟨551735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18772_551736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18772 ⟨551736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18772
    ⟨551736, by decide⟩ (by decide) (![⟨551590, by decide⟩,⟨551631, by decide⟩,⟨551690, by decide⟩,⟨551735, by decide⟩]) unmarked_context_11_18772_551736 node_context_11_18772_551736
  intro a
  fin_cases a
  · exact context_12_75088_551590
  · exact context_12_75089_551631
  · exact context_12_75090_551690
  · exact context_12_75091_551735

theorem selected_cut_21575 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 18773) = some ⟨11, 1, 0, 451541, 18773, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18773_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18773 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 18773 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 18773, 1, 262144⟩
    (by decide) selected_cut_21575

theorem selected_cut_21576 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300384) = some ⟨13, 1, 0, 3444, 300384, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300384_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300384 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300384 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300384, 1, 16384⟩
    (by decide) selected_cut_21576

theorem selected_cut_21577 : selected 8 ⟨551750, by decide⟩
    (prefixPartial 13 300385) = some ⟨13, 2, 0, 551750, 300385, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_300385_551750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300385 ⟨551750, by decide⟩ :=
  accepted_of_selected 13 300385 ⟨551750, by decide⟩ ⟨13, 2, 0, 551750, 300385, 1153, 16384⟩
    (by decide) selected_cut_21577

theorem selected_cut_21578 : selected 8 ⟨551771, by decide⟩
    (prefixPartial 13 300386) = some ⟨13, 2, 0, 551771, 300386, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_300386_551771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300386 ⟨551771, by decide⟩ :=
  accepted_of_selected 13 300386 ⟨551771, by decide⟩ ⟨13, 2, 0, 551771, 300386, 1889, 16384⟩
    (by decide) selected_cut_21578

theorem selected_cut_21579 : selected 8 ⟨551786, by decide⟩
    (prefixPartial 13 300387) = some ⟨13, 2, 0, 551786, 300387, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_300387_551786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300387 ⟨551786, by decide⟩ :=
  accepted_of_selected 13 300387 ⟨551786, by decide⟩ ⟨13, 2, 0, 551786, 300387, 1073, 16384⟩
    (by decide) selected_cut_21579

theorem unmarked_context_12_75096_551787 : frontier 9 ⟨551787, by decide⟩
    (prefixCache 12 75096) (prefixPartial 12 75096) = false := by
  decide +kernel

theorem node_context_12_75096_551787 : EJMOriginalGlobalDAGData.nodes 9 ⟨551787, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551750, by decide⟩,⟨551771, by decide⟩,⟨551786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75096_551787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75096 ⟨551787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75096
    ⟨551787, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551750, by decide⟩,⟨551771, by decide⟩,⟨551786, by decide⟩]) unmarked_context_12_75096_551787 node_context_12_75096_551787
  intro a
  fin_cases a
  · exact context_13_300384_3444
  · exact context_13_300385_551750
  · exact context_13_300386_551771
  · exact context_13_300387_551786

theorem selected_cut_21580 : selected 9 ⟨551827, by decide⟩
    (prefixPartial 12 75097) = some ⟨12, 2, 0, 551827, 75097, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_75097_551827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75097 ⟨551827, by decide⟩ :=
  accepted_of_selected 12 75097 ⟨551827, by decide⟩ ⟨12, 2, 0, 551827, 75097, 3677, 65536⟩
    (by decide) selected_cut_21580

theorem selected_cut_21581 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300392) = some ⟨13, 1, 0, 3444, 300392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300392, 1, 16384⟩
    (by decide) selected_cut_21581

theorem selected_cut_21582 : selected 8 ⟨551843, by decide⟩
    (prefixPartial 13 300393) = some ⟨13, 2, 0, 551843, 300393, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_300393_551843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300393 ⟨551843, by decide⟩ :=
  accepted_of_selected 13 300393 ⟨551843, by decide⟩ ⟨13, 2, 0, 551843, 300393, 1469, 16384⟩
    (by decide) selected_cut_21582

theorem selected_cut_21583 : selected 8 ⟨551863, by decide⟩
    (prefixPartial 13 300394) = some ⟨13, 2, 0, 551863, 300394, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_300394_551863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300394 ⟨551863, by decide⟩ :=
  accepted_of_selected 13 300394 ⟨551863, by decide⟩ ⟨13, 2, 0, 551863, 300394, 2085, 16384⟩
    (by decide) selected_cut_21583

theorem selected_cut_21584 : selected 8 ⟨551876, by decide⟩
    (prefixPartial 13 300395) = some ⟨13, 2, 0, 551876, 300395, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_300395_551876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300395 ⟨551876, by decide⟩ :=
  accepted_of_selected 13 300395 ⟨551876, by decide⟩ ⟨13, 2, 0, 551876, 300395, 1181, 16384⟩
    (by decide) selected_cut_21584

theorem unmarked_context_12_75098_551877 : frontier 9 ⟨551877, by decide⟩
    (prefixCache 12 75098) (prefixPartial 12 75098) = false := by
  decide +kernel

theorem node_context_12_75098_551877 : EJMOriginalGlobalDAGData.nodes 9 ⟨551877, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551843, by decide⟩,⟨551863, by decide⟩,⟨551876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75098_551877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75098 ⟨551877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75098
    ⟨551877, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551843, by decide⟩,⟨551863, by decide⟩,⟨551876, by decide⟩]) unmarked_context_12_75098_551877 node_context_12_75098_551877
  intro a
  fin_cases a
  · exact context_13_300392_3444
  · exact context_13_300393_551843
  · exact context_13_300394_551863
  · exact context_13_300395_551876

theorem selected_cut_21585 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300396) = some ⟨13, 1, 0, 3444, 300396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300396, 1, 16384⟩
    (by decide) selected_cut_21585

theorem selected_cut_21586 : selected 8 ⟨551892, by decide⟩
    (prefixPartial 13 300397) = some ⟨13, 2, 0, 551892, 300397, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_300397_551892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300397 ⟨551892, by decide⟩ :=
  accepted_of_selected 13 300397 ⟨551892, by decide⟩ ⟨13, 2, 0, 551892, 300397, 1533, 16384⟩
    (by decide) selected_cut_21586

theorem selected_cut_21587 : selected 8 ⟨551917, by decide⟩
    (prefixPartial 13 300398) = some ⟨13, 2, 0, 551917, 300398, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_300398_551917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300398 ⟨551917, by decide⟩ :=
  accepted_of_selected 13 300398 ⟨551917, by decide⟩ ⟨13, 2, 0, 551917, 300398, 2269, 16384⟩
    (by decide) selected_cut_21587

theorem selected_cut_21588 : selected 8 ⟨551926, by decide⟩
    (prefixPartial 13 300399) = some ⟨13, 2, 0, 551926, 300399, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_300399_551926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300399 ⟨551926, by decide⟩ :=
  accepted_of_selected 13 300399 ⟨551926, by decide⟩ ⟨13, 2, 0, 551926, 300399, 1017, 16384⟩
    (by decide) selected_cut_21588

theorem unmarked_context_12_75099_551927 : frontier 9 ⟨551927, by decide⟩
    (prefixCache 12 75099) (prefixPartial 12 75099) = false := by
  decide +kernel

theorem node_context_12_75099_551927 : EJMOriginalGlobalDAGData.nodes 9 ⟨551927, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551892, by decide⟩,⟨551917, by decide⟩,⟨551926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75099_551927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75099 ⟨551927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75099
    ⟨551927, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551892, by decide⟩,⟨551917, by decide⟩,⟨551926, by decide⟩]) unmarked_context_12_75099_551927 node_context_12_75099_551927
  intro a
  fin_cases a
  · exact context_13_300396_3444
  · exact context_13_300397_551892
  · exact context_13_300398_551917
  · exact context_13_300399_551926

theorem unmarked_context_11_18774_551928 : frontier 10 ⟨551928, by decide⟩
    (prefixCache 11 18774) (prefixPartial 11 18774) = false := by
  decide +kernel

theorem node_context_11_18774_551928 : EJMOriginalGlobalDAGData.nodes 10 ⟨551928, by decide⟩ =
    .split (coordinate 11) (![⟨551787, by decide⟩,⟨551827, by decide⟩,⟨551877, by decide⟩,⟨551927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18774_551928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18774 ⟨551928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18774
    ⟨551928, by decide⟩ (by decide) (![⟨551787, by decide⟩,⟨551827, by decide⟩,⟨551877, by decide⟩,⟨551927, by decide⟩]) unmarked_context_11_18774_551928 node_context_11_18774_551928
  intro a
  fin_cases a
  · exact context_12_75096_551787
  · exact context_12_75097_551827
  · exact context_12_75098_551877
  · exact context_12_75099_551927

theorem selected_cut_21589 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300400) = some ⟨13, 1, 0, 3444, 300400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300400, 1, 16384⟩
    (by decide) selected_cut_21589

theorem selected_cut_21590 : selected 8 ⟨551941, by decide⟩
    (prefixPartial 13 300401) = some ⟨13, 2, 0, 551941, 300401, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_300401_551941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300401 ⟨551941, by decide⟩ :=
  accepted_of_selected 13 300401 ⟨551941, by decide⟩ ⟨13, 2, 0, 551941, 300401, 1385, 16384⟩
    (by decide) selected_cut_21590

theorem selected_cut_21591 : selected 8 ⟨551964, by decide⟩
    (prefixPartial 13 300402) = some ⟨13, 2, 0, 551964, 300402, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_300402_551964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300402 ⟨551964, by decide⟩ :=
  accepted_of_selected 13 300402 ⟨551964, by decide⟩ ⟨13, 2, 0, 551964, 300402, 1953, 16384⟩
    (by decide) selected_cut_21591

theorem selected_cut_21592 : selected 8 ⟨551975, by decide⟩
    (prefixPartial 13 300403) = some ⟨13, 2, 0, 551975, 300403, 937, 16384⟩ := by
  decide +kernel

theorem context_13_300403_551975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300403 ⟨551975, by decide⟩ :=
  accepted_of_selected 13 300403 ⟨551975, by decide⟩ ⟨13, 2, 0, 551975, 300403, 937, 16384⟩
    (by decide) selected_cut_21592

theorem unmarked_context_12_75100_551976 : frontier 9 ⟨551976, by decide⟩
    (prefixCache 12 75100) (prefixPartial 12 75100) = false := by
  decide +kernel

theorem node_context_12_75100_551976 : EJMOriginalGlobalDAGData.nodes 9 ⟨551976, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨551941, by decide⟩,⟨551964, by decide⟩,⟨551975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75100_551976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75100 ⟨551976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75100
    ⟨551976, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨551941, by decide⟩,⟨551964, by decide⟩,⟨551975, by decide⟩]) unmarked_context_12_75100_551976 node_context_12_75100_551976
  intro a
  fin_cases a
  · exact context_13_300400_3444
  · exact context_13_300401_551941
  · exact context_13_300402_551964
  · exact context_13_300403_551975

theorem selected_cut_21593 : selected 9 ⟨552015, by decide⟩
    (prefixPartial 12 75101) = some ⟨12, 2, 0, 552015, 75101, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_75101_552015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75101 ⟨552015, by decide⟩ :=
  accepted_of_selected 12 75101 ⟨552015, by decide⟩ ⟨12, 2, 0, 552015, 75101, 3521, 65536⟩
    (by decide) selected_cut_21593

theorem selected_cut_21594 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300408) = some ⟨13, 1, 0, 3444, 300408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300408, 1, 16384⟩
    (by decide) selected_cut_21594

theorem selected_cut_21595 : selected 8 ⟨552030, by decide⟩
    (prefixPartial 13 300409) = some ⟨13, 2, 0, 552030, 300409, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_300409_552030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300409 ⟨552030, by decide⟩ :=
  accepted_of_selected 13 300409 ⟨552030, by decide⟩ ⟨13, 2, 0, 552030, 300409, 1613, 16384⟩
    (by decide) selected_cut_21595

theorem selected_cut_21596 : selected 8 ⟨552054, by decide⟩
    (prefixPartial 13 300410) = some ⟨13, 2, 0, 552054, 300410, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_300410_552054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300410 ⟨552054, by decide⟩ :=
  accepted_of_selected 13 300410 ⟨552054, by decide⟩ ⟨13, 2, 0, 552054, 300410, 2193, 16384⟩
    (by decide) selected_cut_21596

theorem selected_cut_21597 : selected 8 ⟨552063, by decide⟩
    (prefixPartial 13 300411) = some ⟨13, 2, 0, 552063, 300411, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_300411_552063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300411 ⟨552063, by decide⟩ :=
  accepted_of_selected 13 300411 ⟨552063, by decide⟩ ⟨13, 2, 0, 552063, 300411, 1121, 16384⟩
    (by decide) selected_cut_21597

theorem unmarked_context_12_75102_552064 : frontier 9 ⟨552064, by decide⟩
    (prefixCache 12 75102) (prefixPartial 12 75102) = false := by
  decide +kernel

theorem node_context_12_75102_552064 : EJMOriginalGlobalDAGData.nodes 9 ⟨552064, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨552030, by decide⟩,⟨552054, by decide⟩,⟨552063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75102_552064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75102 ⟨552064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75102
    ⟨552064, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨552030, by decide⟩,⟨552054, by decide⟩,⟨552063, by decide⟩]) unmarked_context_12_75102_552064 node_context_12_75102_552064
  intro a
  fin_cases a
  · exact context_13_300408_3444
  · exact context_13_300409_552030
  · exact context_13_300410_552054
  · exact context_13_300411_552063

theorem selected_cut_21598 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300412) = some ⟨13, 1, 0, 3444, 300412, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300412_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300412 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300412 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300412, 1, 16384⟩
    (by decide) selected_cut_21598

theorem selected_cut_21599 : selected 8 ⟨552075, by decide⟩
    (prefixPartial 13 300413) = some ⟨13, 2, 0, 552075, 300413, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_300413_552075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300413 ⟨552075, by decide⟩ :=
  accepted_of_selected 13 300413 ⟨552075, by decide⟩ ⟨13, 2, 0, 552075, 300413, 1517, 16384⟩
    (by decide) selected_cut_21599

theorem selected_cut_21600 : selected 8 ⟨552094, by decide⟩
    (prefixPartial 13 300414) = some ⟨13, 2, 0, 552094, 300414, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_300414_552094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300414 ⟨552094, by decide⟩ :=
  accepted_of_selected 13 300414 ⟨552094, by decide⟩ ⟨13, 2, 0, 552094, 300414, 2317, 16384⟩
    (by decide) selected_cut_21600

theorem selected_cut_21601 : selected 8 ⟨552102, by decide⟩
    (prefixPartial 13 300415) = some ⟨13, 2, 0, 552102, 300415, 973, 16384⟩ := by
  decide +kernel

theorem context_13_300415_552102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300415 ⟨552102, by decide⟩ :=
  accepted_of_selected 13 300415 ⟨552102, by decide⟩ ⟨13, 2, 0, 552102, 300415, 973, 16384⟩
    (by decide) selected_cut_21601

theorem unmarked_context_12_75103_552103 : frontier 9 ⟨552103, by decide⟩
    (prefixCache 12 75103) (prefixPartial 12 75103) = false := by
  decide +kernel

theorem node_context_12_75103_552103 : EJMOriginalGlobalDAGData.nodes 9 ⟨552103, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨552075, by decide⟩,⟨552094, by decide⟩,⟨552102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75103_552103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75103 ⟨552103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75103
    ⟨552103, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨552075, by decide⟩,⟨552094, by decide⟩,⟨552102, by decide⟩]) unmarked_context_12_75103_552103 node_context_12_75103_552103
  intro a
  fin_cases a
  · exact context_13_300412_3444
  · exact context_13_300413_552075
  · exact context_13_300414_552094
  · exact context_13_300415_552102

theorem unmarked_context_11_18775_552104 : frontier 10 ⟨552104, by decide⟩
    (prefixCache 11 18775) (prefixPartial 11 18775) = false := by
  decide +kernel

theorem node_context_11_18775_552104 : EJMOriginalGlobalDAGData.nodes 10 ⟨552104, by decide⟩ =
    .split (coordinate 11) (![⟨551976, by decide⟩,⟨552015, by decide⟩,⟨552064, by decide⟩,⟨552103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18775_552104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18775 ⟨552104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18775
    ⟨552104, by decide⟩ (by decide) (![⟨551976, by decide⟩,⟨552015, by decide⟩,⟨552064, by decide⟩,⟨552103, by decide⟩]) unmarked_context_11_18775_552104 node_context_11_18775_552104
  intro a
  fin_cases a
  · exact context_12_75100_551976
  · exact context_12_75101_552015
  · exact context_12_75102_552064
  · exact context_12_75103_552103

theorem unmarked_context_10_4693_552105 : frontier 11 ⟨552105, by decide⟩
    (prefixCache 10 4693) (prefixPartial 10 4693) = false := by
  decide +kernel

theorem node_context_10_4693_552105 : EJMOriginalGlobalDAGData.nodes 11 ⟨552105, by decide⟩ =
    .split (coordinate 10) (![⟨551736, by decide⟩,⟨451541, by decide⟩,⟨551928, by decide⟩,⟨552104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4693_552105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4693 ⟨552105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4693
    ⟨552105, by decide⟩ (by decide) (![⟨551736, by decide⟩,⟨451541, by decide⟩,⟨551928, by decide⟩,⟨552104, by decide⟩]) unmarked_context_10_4693_552105 node_context_10_4693_552105
  intro a
  fin_cases a
  · exact context_11_18772_551736
  · exact context_11_18773_451541
  · exact context_11_18774_551928
  · exact context_11_18775_552104

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
