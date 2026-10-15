/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover171
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16516 : selected 9 ⟨419982, by decide⟩
    (prefixPartial 12 28279) = some ⟨12, 2, 0, 419982, 28279, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_28279_419982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28279 ⟨419982, by decide⟩ :=
  accepted_of_selected 12 28279 ⟨419982, by decide⟩ ⟨12, 2, 0, 419982, 28279, 3549, 65536⟩
    (by decide) selected_cut_16516

theorem unmarked_context_11_7069_419983 : frontier 10 ⟨419983, by decide⟩
    (prefixCache 11 7069) (prefixPartial 11 7069) = false := by
  decide +kernel

theorem node_context_11_7069_419983 : EJMOriginalGlobalDAGData.nodes 10 ⟨419983, by decide⟩ =
    .split (coordinate 11) (![⟨419797, by decide⟩,⟨419904, by decide⟩,⟨419938, by decide⟩,⟨419982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7069_419983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7069 ⟨419983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7069
    ⟨419983, by decide⟩ (by decide) (![⟨419797, by decide⟩,⟨419904, by decide⟩,⟨419938, by decide⟩,⟨419982, by decide⟩]) unmarked_context_11_7069_419983 node_context_11_7069_419983
  intro a
  fin_cases a
  · exact context_12_28276_419797
  · exact context_12_28277_419904
  · exact context_12_28278_419938
  · exact context_12_28279_419982

theorem selected_cut_16517 : selected 9 ⟨420012, by decide⟩
    (prefixPartial 12 28280) = some ⟨12, 2, 0, 420012, 28280, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_28280_420012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28280 ⟨420012, by decide⟩ :=
  accepted_of_selected 12 28280 ⟨420012, by decide⟩ ⟨12, 2, 0, 420012, 28280, 2449, 65536⟩
    (by decide) selected_cut_16517

theorem selected_cut_16518 : selected 9 ⟨420073, by decide⟩
    (prefixPartial 12 28281) = some ⟨12, 2, 0, 420073, 28281, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_28281_420073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28281 ⟨420073, by decide⟩ :=
  accepted_of_selected 12 28281 ⟨420073, by decide⟩ ⟨12, 2, 0, 420073, 28281, 3909, 65536⟩
    (by decide) selected_cut_16518

theorem selected_cut_16519 : selected 9 ⟨420145, by decide⟩
    (prefixPartial 12 28282) = some ⟨12, 2, 0, 420145, 28282, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_28282_420145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28282 ⟨420145, by decide⟩ :=
  accepted_of_selected 12 28282 ⟨420145, by decide⟩ ⟨12, 2, 0, 420145, 28282, 4069, 65536⟩
    (by decide) selected_cut_16519

theorem selected_cut_16520 : selected 9 ⟨420186, by decide⟩
    (prefixPartial 12 28283) = some ⟨12, 2, 0, 420186, 28283, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_28283_420186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28283 ⟨420186, by decide⟩ :=
  accepted_of_selected 12 28283 ⟨420186, by decide⟩ ⟨12, 2, 0, 420186, 28283, 2821, 65536⟩
    (by decide) selected_cut_16520

theorem unmarked_context_11_7070_420187 : frontier 10 ⟨420187, by decide⟩
    (prefixCache 11 7070) (prefixPartial 11 7070) = false := by
  decide +kernel

theorem node_context_11_7070_420187 : EJMOriginalGlobalDAGData.nodes 10 ⟨420187, by decide⟩ =
    .split (coordinate 11) (![⟨420012, by decide⟩,⟨420073, by decide⟩,⟨420145, by decide⟩,⟨420186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7070_420187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7070 ⟨420187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7070
    ⟨420187, by decide⟩ (by decide) (![⟨420012, by decide⟩,⟨420073, by decide⟩,⟨420145, by decide⟩,⟨420186, by decide⟩]) unmarked_context_11_7070_420187 node_context_11_7070_420187
  intro a
  fin_cases a
  · exact context_12_28280_420012
  · exact context_12_28281_420073
  · exact context_12_28282_420145
  · exact context_12_28283_420186

theorem selected_cut_16521 : selected 9 ⟨420230, by decide⟩
    (prefixPartial 12 28284) = some ⟨12, 2, 0, 420230, 28284, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_28284_420230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28284 ⟨420230, by decide⟩ :=
  accepted_of_selected 12 28284 ⟨420230, by decide⟩ ⟨12, 2, 0, 420230, 28284, 3313, 65536⟩
    (by decide) selected_cut_16521

theorem selected_cut_16522 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113140) = some ⟨13, 1, 0, 3444, 113140, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113140_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113140 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113140 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113140, 1, 16384⟩
    (by decide) selected_cut_16522

theorem selected_cut_16523 : selected 8 ⟨420238, by decide⟩
    (prefixPartial 13 113141) = some ⟨13, 2, 0, 420238, 113141, 241, 16384⟩ := by
  decide +kernel

theorem context_13_113141_420238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113141 ⟨420238, by decide⟩ :=
  accepted_of_selected 13 113141 ⟨420238, by decide⟩ ⟨13, 2, 0, 420238, 113141, 241, 16384⟩
    (by decide) selected_cut_16523

theorem selected_cut_16524 : selected 8 ⟨420325, by decide⟩
    (prefixPartial 13 113142) = some ⟨13, 2, 0, 420325, 113142, 3445, 16384⟩ := by
  decide +kernel

theorem context_13_113142_420325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113142 ⟨420325, by decide⟩ :=
  accepted_of_selected 13 113142 ⟨420325, by decide⟩ ⟨13, 2, 0, 420325, 113142, 3445, 16384⟩
    (by decide) selected_cut_16524

theorem selected_cut_16525 : selected 8 ⟨420353, by decide⟩
    (prefixPartial 13 113143) = some ⟨13, 2, 0, 420353, 113143, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_113143_420353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113143 ⟨420353, by decide⟩ :=
  accepted_of_selected 13 113143 ⟨420353, by decide⟩ ⟨13, 2, 0, 420353, 113143, 1377, 16384⟩
    (by decide) selected_cut_16525

theorem unmarked_context_12_28285_420354 : frontier 9 ⟨420354, by decide⟩
    (prefixCache 12 28285) (prefixPartial 12 28285) = false := by
  decide +kernel

theorem node_context_12_28285_420354 : EJMOriginalGlobalDAGData.nodes 9 ⟨420354, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨420238, by decide⟩,⟨420325, by decide⟩,⟨420353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28285_420354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28285 ⟨420354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28285
    ⟨420354, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨420238, by decide⟩,⟨420325, by decide⟩,⟨420353, by decide⟩]) unmarked_context_12_28285_420354 node_context_12_28285_420354
  intro a
  fin_cases a
  · exact context_13_113140_3444
  · exact context_13_113141_420238
  · exact context_13_113142_420325
  · exact context_13_113143_420353

theorem selected_cut_16526 : selected 9 ⟨420382, by decide⟩
    (prefixPartial 12 28286) = some ⟨12, 2, 0, 420382, 28286, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_28286_420382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28286 ⟨420382, by decide⟩ :=
  accepted_of_selected 12 28286 ⟨420382, by decide⟩ ⟨12, 2, 0, 420382, 28286, 3113, 65536⟩
    (by decide) selected_cut_16526

theorem selected_cut_16527 : selected 9 ⟨420445, by decide⟩
    (prefixPartial 12 28287) = some ⟨12, 2, 0, 420445, 28287, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_28287_420445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28287 ⟨420445, by decide⟩ :=
  accepted_of_selected 12 28287 ⟨420445, by decide⟩ ⟨12, 2, 0, 420445, 28287, 1145, 65536⟩
    (by decide) selected_cut_16527

theorem unmarked_context_11_7071_420446 : frontier 10 ⟨420446, by decide⟩
    (prefixCache 11 7071) (prefixPartial 11 7071) = false := by
  decide +kernel

theorem node_context_11_7071_420446 : EJMOriginalGlobalDAGData.nodes 10 ⟨420446, by decide⟩ =
    .split (coordinate 11) (![⟨420230, by decide⟩,⟨420354, by decide⟩,⟨420382, by decide⟩,⟨420445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7071_420446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7071 ⟨420446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7071
    ⟨420446, by decide⟩ (by decide) (![⟨420230, by decide⟩,⟨420354, by decide⟩,⟨420382, by decide⟩,⟨420445, by decide⟩]) unmarked_context_11_7071_420446 node_context_11_7071_420446
  intro a
  fin_cases a
  · exact context_12_28284_420230
  · exact context_12_28285_420354
  · exact context_12_28286_420382
  · exact context_12_28287_420445

theorem unmarked_context_10_1767_420447 : frontier 11 ⟨420447, by decide⟩
    (prefixCache 10 1767) (prefixPartial 10 1767) = false := by
  decide +kernel

theorem node_context_10_1767_420447 : EJMOriginalGlobalDAGData.nodes 11 ⟨420447, by decide⟩ =
    .split (coordinate 10) (![⟨419766, by decide⟩,⟨419983, by decide⟩,⟨420187, by decide⟩,⟨420446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1767_420447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1767 ⟨420447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1767
    ⟨420447, by decide⟩ (by decide) (![⟨419766, by decide⟩,⟨419983, by decide⟩,⟨420187, by decide⟩,⟨420446, by decide⟩]) unmarked_context_10_1767_420447 node_context_10_1767_420447
  intro a
  fin_cases a
  · exact context_11_7068_419766
  · exact context_11_7069_419983
  · exact context_11_7070_420187
  · exact context_11_7071_420446

theorem unmarked_context_9_441_420448 : frontier 12 ⟨420448, by decide⟩
    (prefixCache 9 441) (prefixPartial 9 441) = false := by
  decide +kernel

theorem node_context_9_441_420448 : EJMOriginalGlobalDAGData.nodes 12 ⟨420448, by decide⟩ =
    .split (coordinate 9) (![⟨417936, by decide⟩,⟨418697, by decide⟩,⟨419557, by decide⟩,⟨420447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_441_420448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 441 ⟨420448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 441
    ⟨420448, by decide⟩ (by decide) (![⟨417936, by decide⟩,⟨418697, by decide⟩,⟨419557, by decide⟩,⟨420447, by decide⟩]) unmarked_context_9_441_420448 node_context_9_441_420448
  intro a
  fin_cases a
  · exact context_10_1764_417936
  · exact context_10_1765_418697
  · exact context_10_1766_419557
  · exact context_10_1767_420447

theorem selected_cut_16528 : selected 9 ⟨420470, by decide⟩
    (prefixPartial 12 28288) = some ⟨12, 2, 0, 420470, 28288, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_28288_420470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28288 ⟨420470, by decide⟩ :=
  accepted_of_selected 12 28288 ⟨420470, by decide⟩ ⟨12, 2, 0, 420470, 28288, 2097, 65536⟩
    (by decide) selected_cut_16528

theorem selected_cut_16529 : selected 9 ⟨420498, by decide⟩
    (prefixPartial 12 28289) = some ⟨12, 2, 0, 420498, 28289, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_28289_420498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28289 ⟨420498, by decide⟩ :=
  accepted_of_selected 12 28289 ⟨420498, by decide⟩ ⟨12, 2, 0, 420498, 28289, 2421, 65536⟩
    (by decide) selected_cut_16529

theorem selected_cut_16530 : selected 9 ⟨420527, by decide⟩
    (prefixPartial 12 28290) = some ⟨12, 2, 0, 420527, 28290, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_28290_420527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28290 ⟨420527, by decide⟩ :=
  accepted_of_selected 12 28290 ⟨420527, by decide⟩ ⟨12, 2, 0, 420527, 28290, 2125, 65536⟩
    (by decide) selected_cut_16530

theorem selected_cut_16531 : selected 9 ⟨420556, by decide⟩
    (prefixPartial 12 28291) = some ⟨12, 2, 0, 420556, 28291, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_28291_420556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28291 ⟨420556, by decide⟩ :=
  accepted_of_selected 12 28291 ⟨420556, by decide⟩ ⟨12, 2, 0, 420556, 28291, 2577, 65536⟩
    (by decide) selected_cut_16531

theorem unmarked_context_11_7072_420557 : frontier 10 ⟨420557, by decide⟩
    (prefixCache 11 7072) (prefixPartial 11 7072) = false := by
  decide +kernel

theorem node_context_11_7072_420557 : EJMOriginalGlobalDAGData.nodes 10 ⟨420557, by decide⟩ =
    .split (coordinate 11) (![⟨420470, by decide⟩,⟨420498, by decide⟩,⟨420527, by decide⟩,⟨420556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7072_420557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7072 ⟨420557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7072
    ⟨420557, by decide⟩ (by decide) (![⟨420470, by decide⟩,⟨420498, by decide⟩,⟨420527, by decide⟩,⟨420556, by decide⟩]) unmarked_context_11_7072_420557 node_context_11_7072_420557
  intro a
  fin_cases a
  · exact context_12_28288_420470
  · exact context_12_28289_420498
  · exact context_12_28290_420527
  · exact context_12_28291_420556

theorem selected_cut_16532 : selected 9 ⟨420581, by decide⟩
    (prefixPartial 12 28292) = some ⟨12, 2, 0, 420581, 28292, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_28292_420581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28292 ⟨420581, by decide⟩ :=
  accepted_of_selected 12 28292 ⟨420581, by decide⟩ ⟨12, 2, 0, 420581, 28292, 2257, 65536⟩
    (by decide) selected_cut_16532

theorem selected_cut_16533 : selected 9 ⟨420607, by decide⟩
    (prefixPartial 12 28293) = some ⟨12, 2, 0, 420607, 28293, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_28293_420607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28293 ⟨420607, by decide⟩ :=
  accepted_of_selected 12 28293 ⟨420607, by decide⟩ ⟨12, 2, 0, 420607, 28293, 2329, 65536⟩
    (by decide) selected_cut_16533

theorem selected_cut_16534 : selected 9 ⟨420632, by decide⟩
    (prefixPartial 12 28294) = some ⟨12, 2, 0, 420632, 28294, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_28294_420632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28294 ⟨420632, by decide⟩ :=
  accepted_of_selected 12 28294 ⟨420632, by decide⟩ ⟨12, 2, 0, 420632, 28294, 2233, 65536⟩
    (by decide) selected_cut_16534

theorem selected_cut_16535 : selected 9 ⟨420661, by decide⟩
    (prefixPartial 12 28295) = some ⟨12, 2, 0, 420661, 28295, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_28295_420661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28295 ⟨420661, by decide⟩ :=
  accepted_of_selected 12 28295 ⟨420661, by decide⟩ ⟨12, 2, 0, 420661, 28295, 2521, 65536⟩
    (by decide) selected_cut_16535

theorem unmarked_context_11_7073_420662 : frontier 10 ⟨420662, by decide⟩
    (prefixCache 11 7073) (prefixPartial 11 7073) = false := by
  decide +kernel

theorem node_context_11_7073_420662 : EJMOriginalGlobalDAGData.nodes 10 ⟨420662, by decide⟩ =
    .split (coordinate 11) (![⟨420581, by decide⟩,⟨420607, by decide⟩,⟨420632, by decide⟩,⟨420661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7073_420662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7073 ⟨420662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7073
    ⟨420662, by decide⟩ (by decide) (![⟨420581, by decide⟩,⟨420607, by decide⟩,⟨420632, by decide⟩,⟨420661, by decide⟩]) unmarked_context_11_7073_420662 node_context_11_7073_420662
  intro a
  fin_cases a
  · exact context_12_28292_420581
  · exact context_12_28293_420607
  · exact context_12_28294_420632
  · exact context_12_28295_420661

theorem selected_cut_16536 : selected 9 ⟨420689, by decide⟩
    (prefixPartial 12 28296) = some ⟨12, 2, 0, 420689, 28296, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_28296_420689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28296 ⟨420689, by decide⟩ :=
  accepted_of_selected 12 28296 ⟨420689, by decide⟩ ⟨12, 2, 0, 420689, 28296, 2089, 65536⟩
    (by decide) selected_cut_16536

theorem selected_cut_16537 : selected 9 ⟨420713, by decide⟩
    (prefixPartial 12 28297) = some ⟨12, 2, 0, 420713, 28297, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_28297_420713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28297 ⟨420713, by decide⟩ :=
  accepted_of_selected 12 28297 ⟨420713, by decide⟩ ⟨12, 2, 0, 420713, 28297, 2429, 65536⟩
    (by decide) selected_cut_16537

theorem selected_cut_16538 : selected 9 ⟨420784, by decide⟩
    (prefixPartial 12 28298) = some ⟨12, 2, 0, 420784, 28298, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_28298_420784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28298 ⟨420784, by decide⟩ :=
  accepted_of_selected 12 28298 ⟨420784, by decide⟩ ⟨12, 2, 0, 420784, 28298, 1229, 65536⟩
    (by decide) selected_cut_16538

theorem selected_cut_16539 : selected 9 ⟨420807, by decide⟩
    (prefixPartial 12 28299) = some ⟨12, 2, 0, 420807, 28299, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_28299_420807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28299 ⟨420807, by decide⟩ :=
  accepted_of_selected 12 28299 ⟨420807, by decide⟩ ⟨12, 2, 0, 420807, 28299, 2333, 65536⟩
    (by decide) selected_cut_16539

theorem unmarked_context_11_7074_420808 : frontier 10 ⟨420808, by decide⟩
    (prefixCache 11 7074) (prefixPartial 11 7074) = false := by
  decide +kernel

theorem node_context_11_7074_420808 : EJMOriginalGlobalDAGData.nodes 10 ⟨420808, by decide⟩ =
    .split (coordinate 11) (![⟨420689, by decide⟩,⟨420713, by decide⟩,⟨420784, by decide⟩,⟨420807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7074_420808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7074 ⟨420808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7074
    ⟨420808, by decide⟩ (by decide) (![⟨420689, by decide⟩,⟨420713, by decide⟩,⟨420784, by decide⟩,⟨420807, by decide⟩]) unmarked_context_11_7074_420808 node_context_11_7074_420808
  intro a
  fin_cases a
  · exact context_12_28296_420689
  · exact context_12_28297_420713
  · exact context_12_28298_420784
  · exact context_12_28299_420807

theorem selected_cut_16540 : selected 9 ⟨420831, by decide⟩
    (prefixPartial 12 28300) = some ⟨12, 2, 0, 420831, 28300, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_28300_420831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28300 ⟨420831, by decide⟩ :=
  accepted_of_selected 12 28300 ⟨420831, by decide⟩ ⟨12, 2, 0, 420831, 28300, 2181, 65536⟩
    (by decide) selected_cut_16540

theorem selected_cut_16541 : selected 9 ⟨420854, by decide⟩
    (prefixPartial 12 28301) = some ⟨12, 2, 0, 420854, 28301, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_28301_420854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28301 ⟨420854, by decide⟩ :=
  accepted_of_selected 12 28301 ⟨420854, by decide⟩ ⟨12, 2, 0, 420854, 28301, 2269, 65536⟩
    (by decide) selected_cut_16541

theorem selected_cut_16542 : selected 9 ⟨420879, by decide⟩
    (prefixPartial 12 28302) = some ⟨12, 2, 0, 420879, 28302, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_28302_420879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28302 ⟨420879, by decide⟩ :=
  accepted_of_selected 12 28302 ⟨420879, by decide⟩ ⟨12, 2, 0, 420879, 28302, 2085, 65536⟩
    (by decide) selected_cut_16542

theorem selected_cut_16543 : selected 9 ⟨420899, by decide⟩
    (prefixPartial 12 28303) = some ⟨12, 2, 0, 420899, 28303, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_28303_420899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28303 ⟨420899, by decide⟩ :=
  accepted_of_selected 12 28303 ⟨420899, by decide⟩ ⟨12, 2, 0, 420899, 28303, 2325, 65536⟩
    (by decide) selected_cut_16543

theorem unmarked_context_11_7075_420900 : frontier 10 ⟨420900, by decide⟩
    (prefixCache 11 7075) (prefixPartial 11 7075) = false := by
  decide +kernel

theorem node_context_11_7075_420900 : EJMOriginalGlobalDAGData.nodes 10 ⟨420900, by decide⟩ =
    .split (coordinate 11) (![⟨420831, by decide⟩,⟨420854, by decide⟩,⟨420879, by decide⟩,⟨420899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7075_420900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7075 ⟨420900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7075
    ⟨420900, by decide⟩ (by decide) (![⟨420831, by decide⟩,⟨420854, by decide⟩,⟨420879, by decide⟩,⟨420899, by decide⟩]) unmarked_context_11_7075_420900 node_context_11_7075_420900
  intro a
  fin_cases a
  · exact context_12_28300_420831
  · exact context_12_28301_420854
  · exact context_12_28302_420879
  · exact context_12_28303_420899

theorem unmarked_context_10_1768_420901 : frontier 11 ⟨420901, by decide⟩
    (prefixCache 10 1768) (prefixPartial 10 1768) = false := by
  decide +kernel

theorem node_context_10_1768_420901 : EJMOriginalGlobalDAGData.nodes 11 ⟨420901, by decide⟩ =
    .split (coordinate 10) (![⟨420557, by decide⟩,⟨420662, by decide⟩,⟨420808, by decide⟩,⟨420900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1768_420901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1768 ⟨420901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1768
    ⟨420901, by decide⟩ (by decide) (![⟨420557, by decide⟩,⟨420662, by decide⟩,⟨420808, by decide⟩,⟨420900, by decide⟩]) unmarked_context_10_1768_420901 node_context_10_1768_420901
  intro a
  fin_cases a
  · exact context_11_7072_420557
  · exact context_11_7073_420662
  · exact context_11_7074_420808
  · exact context_11_7075_420900

theorem selected_cut_16544 : selected 9 ⟨420919, by decide⟩
    (prefixPartial 12 28304) = some ⟨12, 2, 0, 420919, 28304, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_28304_420919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28304 ⟨420919, by decide⟩ :=
  accepted_of_selected 12 28304 ⟨420919, by decide⟩ ⟨12, 2, 0, 420919, 28304, 2145, 65536⟩
    (by decide) selected_cut_16544

theorem selected_cut_16545 : selected 9 ⟨420947, by decide⟩
    (prefixPartial 12 28305) = some ⟨12, 2, 0, 420947, 28305, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_28305_420947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28305 ⟨420947, by decide⟩ :=
  accepted_of_selected 12 28305 ⟨420947, by decide⟩ ⟨12, 2, 0, 420947, 28305, 2601, 65536⟩
    (by decide) selected_cut_16545

theorem selected_cut_16546 : selected 9 ⟨420968, by decide⟩
    (prefixPartial 12 28306) = some ⟨12, 2, 0, 420968, 28306, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_28306_420968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28306 ⟨420968, by decide⟩ :=
  accepted_of_selected 12 28306 ⟨420968, by decide⟩ ⟨12, 2, 0, 420968, 28306, 2385, 65536⟩
    (by decide) selected_cut_16546

theorem selected_cut_16547 : selected 9 ⟨421024, by decide⟩
    (prefixPartial 12 28307) = some ⟨12, 2, 0, 421024, 28307, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_28307_421024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28307 ⟨421024, by decide⟩ :=
  accepted_of_selected 12 28307 ⟨421024, by decide⟩ ⟨12, 2, 0, 421024, 28307, 2789, 65536⟩
    (by decide) selected_cut_16547

theorem unmarked_context_11_7076_421025 : frontier 10 ⟨421025, by decide⟩
    (prefixCache 11 7076) (prefixPartial 11 7076) = false := by
  decide +kernel

theorem node_context_11_7076_421025 : EJMOriginalGlobalDAGData.nodes 10 ⟨421025, by decide⟩ =
    .split (coordinate 11) (![⟨420919, by decide⟩,⟨420947, by decide⟩,⟨420968, by decide⟩,⟨421024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7076_421025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7076 ⟨421025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7076
    ⟨421025, by decide⟩ (by decide) (![⟨420919, by decide⟩,⟨420947, by decide⟩,⟨420968, by decide⟩,⟨421024, by decide⟩]) unmarked_context_11_7076_421025 node_context_11_7076_421025
  intro a
  fin_cases a
  · exact context_12_28304_420919
  · exact context_12_28305_420947
  · exact context_12_28306_420968
  · exact context_12_28307_421024

theorem selected_cut_16548 : selected 9 ⟨421048, by decide⟩
    (prefixPartial 12 28308) = some ⟨12, 2, 0, 421048, 28308, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_28308_421048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28308 ⟨421048, by decide⟩ :=
  accepted_of_selected 12 28308 ⟨421048, by decide⟩ ⟨12, 2, 0, 421048, 28308, 2041, 65536⟩
    (by decide) selected_cut_16548

theorem selected_cut_16549 : selected 9 ⟨421068, by decide⟩
    (prefixPartial 12 28309) = some ⟨12, 2, 0, 421068, 28309, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_28309_421068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28309 ⟨421068, by decide⟩ :=
  accepted_of_selected 12 28309 ⟨421068, by decide⟩ ⟨12, 2, 0, 421068, 28309, 2329, 65536⟩
    (by decide) selected_cut_16549

theorem selected_cut_16550 : selected 9 ⟨421088, by decide⟩
    (prefixPartial 12 28310) = some ⟨12, 2, 0, 421088, 28310, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_28310_421088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28310 ⟨421088, by decide⟩ :=
  accepted_of_selected 12 28310 ⟨421088, by decide⟩ ⟨12, 2, 0, 421088, 28310, 2237, 65536⟩
    (by decide) selected_cut_16550

theorem selected_cut_16551 : selected 9 ⟨421113, by decide⟩
    (prefixPartial 12 28311) = some ⟨12, 2, 0, 421113, 28311, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_28311_421113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28311 ⟨421113, by decide⟩ :=
  accepted_of_selected 12 28311 ⟨421113, by decide⟩ ⟨12, 2, 0, 421113, 28311, 2461, 65536⟩
    (by decide) selected_cut_16551

theorem unmarked_context_11_7077_421114 : frontier 10 ⟨421114, by decide⟩
    (prefixCache 11 7077) (prefixPartial 11 7077) = false := by
  decide +kernel

theorem node_context_11_7077_421114 : EJMOriginalGlobalDAGData.nodes 10 ⟨421114, by decide⟩ =
    .split (coordinate 11) (![⟨421048, by decide⟩,⟨421068, by decide⟩,⟨421088, by decide⟩,⟨421113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7077_421114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7077 ⟨421114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7077
    ⟨421114, by decide⟩ (by decide) (![⟨421048, by decide⟩,⟨421068, by decide⟩,⟨421088, by decide⟩,⟨421113, by decide⟩]) unmarked_context_11_7077_421114 node_context_11_7077_421114
  intro a
  fin_cases a
  · exact context_12_28308_421048
  · exact context_12_28309_421068
  · exact context_12_28310_421088
  · exact context_12_28311_421113

theorem selected_cut_16552 : selected 9 ⟨421134, by decide⟩
    (prefixPartial 12 28312) = some ⟨12, 2, 0, 421134, 28312, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_28312_421134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28312 ⟨421134, by decide⟩ :=
  accepted_of_selected 12 28312 ⟨421134, by decide⟩ ⟨12, 2, 0, 421134, 28312, 1713, 65536⟩
    (by decide) selected_cut_16552

theorem selected_cut_16553 : selected 9 ⟨421153, by decide⟩
    (prefixPartial 12 28313) = some ⟨12, 2, 0, 421153, 28313, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_28313_421153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28313 ⟨421153, by decide⟩ :=
  accepted_of_selected 12 28313 ⟨421153, by decide⟩ ⟨12, 2, 0, 421153, 28313, 2157, 65536⟩
    (by decide) selected_cut_16553

theorem selected_cut_16554 : selected 9 ⟨290673, by decide⟩
    (prefixPartial 12 28314) = some ⟨12, 1, 0, 290673, 28314, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28314_290673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28314 ⟨290673, by decide⟩ :=
  accepted_of_selected 12 28314 ⟨290673, by decide⟩ ⟨12, 1, 0, 290673, 28314, 1, 65536⟩
    (by decide) selected_cut_16554

theorem selected_cut_16555 : selected 9 ⟨421174, by decide⟩
    (prefixPartial 12 28315) = some ⟨12, 2, 0, 421174, 28315, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_28315_421174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28315 ⟨421174, by decide⟩ :=
  accepted_of_selected 12 28315 ⟨421174, by decide⟩ ⟨12, 2, 0, 421174, 28315, 2153, 65536⟩
    (by decide) selected_cut_16555

theorem unmarked_context_11_7078_421175 : frontier 10 ⟨421175, by decide⟩
    (prefixCache 11 7078) (prefixPartial 11 7078) = false := by
  decide +kernel

theorem node_context_11_7078_421175 : EJMOriginalGlobalDAGData.nodes 10 ⟨421175, by decide⟩ =
    .split (coordinate 11) (![⟨421134, by decide⟩,⟨421153, by decide⟩,⟨290673, by decide⟩,⟨421174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7078_421175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7078 ⟨421175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7078
    ⟨421175, by decide⟩ (by decide) (![⟨421134, by decide⟩,⟨421153, by decide⟩,⟨290673, by decide⟩,⟨421174, by decide⟩]) unmarked_context_11_7078_421175 node_context_11_7078_421175
  intro a
  fin_cases a
  · exact context_12_28312_421134
  · exact context_12_28313_421153
  · exact context_12_28314_290673
  · exact context_12_28315_421174

theorem selected_cut_16556 : selected 9 ⟨421195, by decide⟩
    (prefixPartial 12 28316) = some ⟨12, 2, 0, 421195, 28316, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_28316_421195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28316 ⟨421195, by decide⟩ :=
  accepted_of_selected 12 28316 ⟨421195, by decide⟩ ⟨12, 2, 0, 421195, 28316, 1853, 65536⟩
    (by decide) selected_cut_16556

theorem selected_cut_16557 : selected 9 ⟨421213, by decide⟩
    (prefixPartial 12 28317) = some ⟨12, 2, 0, 421213, 28317, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_28317_421213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28317 ⟨421213, by decide⟩ :=
  accepted_of_selected 12 28317 ⟨421213, by decide⟩ ⟨12, 2, 0, 421213, 28317, 2069, 65536⟩
    (by decide) selected_cut_16557

theorem selected_cut_16558 : selected 9 ⟨421232, by decide⟩
    (prefixPartial 12 28318) = some ⟨12, 2, 0, 421232, 28318, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_28318_421232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28318 ⟨421232, by decide⟩ :=
  accepted_of_selected 12 28318 ⟨421232, by decide⟩ ⟨12, 2, 0, 421232, 28318, 1941, 65536⟩
    (by decide) selected_cut_16558

theorem selected_cut_16559 : selected 9 ⟨421247, by decide⟩
    (prefixPartial 12 28319) = some ⟨12, 2, 0, 421247, 28319, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_28319_421247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28319 ⟨421247, by decide⟩ :=
  accepted_of_selected 12 28319 ⟨421247, by decide⟩ ⟨12, 2, 0, 421247, 28319, 2161, 65536⟩
    (by decide) selected_cut_16559

theorem unmarked_context_11_7079_421248 : frontier 10 ⟨421248, by decide⟩
    (prefixCache 11 7079) (prefixPartial 11 7079) = false := by
  decide +kernel

theorem node_context_11_7079_421248 : EJMOriginalGlobalDAGData.nodes 10 ⟨421248, by decide⟩ =
    .split (coordinate 11) (![⟨421195, by decide⟩,⟨421213, by decide⟩,⟨421232, by decide⟩,⟨421247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7079_421248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7079 ⟨421248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7079
    ⟨421248, by decide⟩ (by decide) (![⟨421195, by decide⟩,⟨421213, by decide⟩,⟨421232, by decide⟩,⟨421247, by decide⟩]) unmarked_context_11_7079_421248 node_context_11_7079_421248
  intro a
  fin_cases a
  · exact context_12_28316_421195
  · exact context_12_28317_421213
  · exact context_12_28318_421232
  · exact context_12_28319_421247

theorem unmarked_context_10_1769_421249 : frontier 11 ⟨421249, by decide⟩
    (prefixCache 10 1769) (prefixPartial 10 1769) = false := by
  decide +kernel

theorem node_context_10_1769_421249 : EJMOriginalGlobalDAGData.nodes 11 ⟨421249, by decide⟩ =
    .split (coordinate 10) (![⟨421025, by decide⟩,⟨421114, by decide⟩,⟨421175, by decide⟩,⟨421248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1769_421249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1769 ⟨421249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1769
    ⟨421249, by decide⟩ (by decide) (![⟨421025, by decide⟩,⟨421114, by decide⟩,⟨421175, by decide⟩,⟨421248, by decide⟩]) unmarked_context_10_1769_421249 node_context_10_1769_421249
  intro a
  fin_cases a
  · exact context_11_7076_421025
  · exact context_11_7077_421114
  · exact context_11_7078_421175
  · exact context_11_7079_421248

theorem selected_cut_16560 : selected 9 ⟨421267, by decide⟩
    (prefixPartial 12 28320) = some ⟨12, 2, 0, 421267, 28320, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_28320_421267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28320 ⟨421267, by decide⟩ :=
  accepted_of_selected 12 28320 ⟨421267, by decide⟩ ⟨12, 2, 0, 421267, 28320, 1489, 65536⟩
    (by decide) selected_cut_16560

theorem selected_cut_16561 : selected 9 ⟨421288, by decide⟩
    (prefixPartial 12 28321) = some ⟨12, 2, 0, 421288, 28321, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_28321_421288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28321 ⟨421288, by decide⟩ :=
  accepted_of_selected 12 28321 ⟨421288, by decide⟩ ⟨12, 2, 0, 421288, 28321, 1841, 65536⟩
    (by decide) selected_cut_16561

theorem selected_cut_16562 : selected 9 ⟨421308, by decide⟩
    (prefixPartial 12 28322) = some ⟨12, 2, 0, 421308, 28322, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_28322_421308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28322 ⟨421308, by decide⟩ :=
  accepted_of_selected 12 28322 ⟨421308, by decide⟩ ⟨12, 2, 0, 421308, 28322, 1521, 65536⟩
    (by decide) selected_cut_16562

theorem selected_cut_16563 : selected 9 ⟨421330, by decide⟩
    (prefixPartial 12 28323) = some ⟨12, 2, 0, 421330, 28323, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_28323_421330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28323 ⟨421330, by decide⟩ :=
  accepted_of_selected 12 28323 ⟨421330, by decide⟩ ⟨12, 2, 0, 421330, 28323, 1881, 65536⟩
    (by decide) selected_cut_16563

theorem unmarked_context_11_7080_421331 : frontier 10 ⟨421331, by decide⟩
    (prefixCache 11 7080) (prefixPartial 11 7080) = false := by
  decide +kernel

theorem node_context_11_7080_421331 : EJMOriginalGlobalDAGData.nodes 10 ⟨421331, by decide⟩ =
    .split (coordinate 11) (![⟨421267, by decide⟩,⟨421288, by decide⟩,⟨421308, by decide⟩,⟨421330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7080_421331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7080 ⟨421331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7080
    ⟨421331, by decide⟩ (by decide) (![⟨421267, by decide⟩,⟨421288, by decide⟩,⟨421308, by decide⟩,⟨421330, by decide⟩]) unmarked_context_11_7080_421331 node_context_11_7080_421331
  intro a
  fin_cases a
  · exact context_12_28320_421267
  · exact context_12_28321_421288
  · exact context_12_28322_421308
  · exact context_12_28323_421330

theorem selected_cut_16564 : selected 9 ⟨421346, by decide⟩
    (prefixPartial 12 28324) = some ⟨12, 2, 0, 421346, 28324, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_28324_421346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28324 ⟨421346, by decide⟩ :=
  accepted_of_selected 12 28324 ⟨421346, by decide⟩ ⟨12, 2, 0, 421346, 28324, 1401, 65536⟩
    (by decide) selected_cut_16564

theorem selected_cut_16565 : selected 9 ⟨421363, by decide⟩
    (prefixPartial 12 28325) = some ⟨12, 2, 0, 421363, 28325, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_28325_421363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28325 ⟨421363, by decide⟩ :=
  accepted_of_selected 12 28325 ⟨421363, by decide⟩ ⟨12, 2, 0, 421363, 28325, 1673, 65536⟩
    (by decide) selected_cut_16565

theorem selected_cut_16566 : selected 9 ⟨421379, by decide⟩
    (prefixPartial 12 28326) = some ⟨12, 2, 0, 421379, 28326, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_28326_421379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28326 ⟨421379, by decide⟩ :=
  accepted_of_selected 12 28326 ⟨421379, by decide⟩ ⟨12, 2, 0, 421379, 28326, 1473, 65536⟩
    (by decide) selected_cut_16566

theorem selected_cut_16567 : selected 9 ⟨421397, by decide⟩
    (prefixPartial 12 28327) = some ⟨12, 2, 0, 421397, 28327, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_28327_421397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28327 ⟨421397, by decide⟩ :=
  accepted_of_selected 12 28327 ⟨421397, by decide⟩ ⟨12, 2, 0, 421397, 28327, 1745, 65536⟩
    (by decide) selected_cut_16567

theorem unmarked_context_11_7081_421398 : frontier 10 ⟨421398, by decide⟩
    (prefixCache 11 7081) (prefixPartial 11 7081) = false := by
  decide +kernel

theorem node_context_11_7081_421398 : EJMOriginalGlobalDAGData.nodes 10 ⟨421398, by decide⟩ =
    .split (coordinate 11) (![⟨421346, by decide⟩,⟨421363, by decide⟩,⟨421379, by decide⟩,⟨421397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7081_421398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7081 ⟨421398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7081
    ⟨421398, by decide⟩ (by decide) (![⟨421346, by decide⟩,⟨421363, by decide⟩,⟨421379, by decide⟩,⟨421397, by decide⟩]) unmarked_context_11_7081_421398 node_context_11_7081_421398
  intro a
  fin_cases a
  · exact context_12_28324_421346
  · exact context_12_28325_421363
  · exact context_12_28326_421379
  · exact context_12_28327_421397

theorem selected_cut_16568 : selected 9 ⟨421410, by decide⟩
    (prefixPartial 12 28328) = some ⟨12, 2, 0, 421410, 28328, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_28328_421410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28328 ⟨421410, by decide⟩ :=
  accepted_of_selected 12 28328 ⟨421410, by decide⟩ ⟨12, 2, 0, 421410, 28328, 1213, 65536⟩
    (by decide) selected_cut_16568

theorem selected_cut_16569 : selected 9 ⟨421424, by decide⟩
    (prefixPartial 12 28329) = some ⟨12, 2, 0, 421424, 28329, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_28329_421424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28329 ⟨421424, by decide⟩ :=
  accepted_of_selected 12 28329 ⟨421424, by decide⟩ ⟨12, 2, 0, 421424, 28329, 1565, 65536⟩
    (by decide) selected_cut_16569

theorem selected_cut_16570 : selected 9 ⟨421425, by decide⟩
    (prefixPartial 12 28330) = some ⟨12, 1, 0, 421425, 28330, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28330_421425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28330 ⟨421425, by decide⟩ :=
  accepted_of_selected 12 28330 ⟨421425, by decide⟩ ⟨12, 1, 0, 421425, 28330, 1, 65536⟩
    (by decide) selected_cut_16570

theorem selected_cut_16571 : selected 9 ⟨421443, by decide⟩
    (prefixPartial 12 28331) = some ⟨12, 2, 0, 421443, 28331, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_28331_421443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28331 ⟨421443, by decide⟩ :=
  accepted_of_selected 12 28331 ⟨421443, by decide⟩ ⟨12, 2, 0, 421443, 28331, 1509, 65536⟩
    (by decide) selected_cut_16571

theorem unmarked_context_11_7082_421444 : frontier 10 ⟨421444, by decide⟩
    (prefixCache 11 7082) (prefixPartial 11 7082) = false := by
  decide +kernel

theorem node_context_11_7082_421444 : EJMOriginalGlobalDAGData.nodes 10 ⟨421444, by decide⟩ =
    .split (coordinate 11) (![⟨421410, by decide⟩,⟨421424, by decide⟩,⟨421425, by decide⟩,⟨421443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7082_421444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7082 ⟨421444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7082
    ⟨421444, by decide⟩ (by decide) (![⟨421410, by decide⟩,⟨421424, by decide⟩,⟨421425, by decide⟩,⟨421443, by decide⟩]) unmarked_context_11_7082_421444 node_context_11_7082_421444
  intro a
  fin_cases a
  · exact context_12_28328_421410
  · exact context_12_28329_421424
  · exact context_12_28330_421425
  · exact context_12_28331_421443

theorem selected_cut_16572 : selected 9 ⟨421458, by decide⟩
    (prefixPartial 12 28332) = some ⟨12, 2, 0, 421458, 28332, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_28332_421458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28332 ⟨421458, by decide⟩ :=
  accepted_of_selected 12 28332 ⟨421458, by decide⟩ ⟨12, 2, 0, 421458, 28332, 1433, 65536⟩
    (by decide) selected_cut_16572

theorem selected_cut_16573 : selected 9 ⟨421473, by decide⟩
    (prefixPartial 12 28333) = some ⟨12, 2, 0, 421473, 28333, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_28333_421473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28333 ⟨421473, by decide⟩ :=
  accepted_of_selected 12 28333 ⟨421473, by decide⟩ ⟨12, 2, 0, 421473, 28333, 1565, 65536⟩
    (by decide) selected_cut_16573

theorem selected_cut_16574 : selected 9 ⟨421486, by decide⟩
    (prefixPartial 12 28334) = some ⟨12, 2, 0, 421486, 28334, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_28334_421486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28334 ⟨421486, by decide⟩ :=
  accepted_of_selected 12 28334 ⟨421486, by decide⟩ ⟨12, 2, 0, 421486, 28334, 1357, 65536⟩
    (by decide) selected_cut_16574

theorem selected_cut_16575 : selected 9 ⟨421503, by decide⟩
    (prefixPartial 12 28335) = some ⟨12, 2, 0, 421503, 28335, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_28335_421503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28335 ⟨421503, by decide⟩ :=
  accepted_of_selected 12 28335 ⟨421503, by decide⟩ ⟨12, 2, 0, 421503, 28335, 1601, 65536⟩
    (by decide) selected_cut_16575

theorem unmarked_context_11_7083_421504 : frontier 10 ⟨421504, by decide⟩
    (prefixCache 11 7083) (prefixPartial 11 7083) = false := by
  decide +kernel

theorem node_context_11_7083_421504 : EJMOriginalGlobalDAGData.nodes 10 ⟨421504, by decide⟩ =
    .split (coordinate 11) (![⟨421458, by decide⟩,⟨421473, by decide⟩,⟨421486, by decide⟩,⟨421503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7083_421504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7083 ⟨421504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7083
    ⟨421504, by decide⟩ (by decide) (![⟨421458, by decide⟩,⟨421473, by decide⟩,⟨421486, by decide⟩,⟨421503, by decide⟩]) unmarked_context_11_7083_421504 node_context_11_7083_421504
  intro a
  fin_cases a
  · exact context_12_28332_421458
  · exact context_12_28333_421473
  · exact context_12_28334_421486
  · exact context_12_28335_421503

theorem unmarked_context_10_1770_421505 : frontier 11 ⟨421505, by decide⟩
    (prefixCache 10 1770) (prefixPartial 10 1770) = false := by
  decide +kernel

theorem node_context_10_1770_421505 : EJMOriginalGlobalDAGData.nodes 11 ⟨421505, by decide⟩ =
    .split (coordinate 10) (![⟨421331, by decide⟩,⟨421398, by decide⟩,⟨421444, by decide⟩,⟨421504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1770_421505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1770 ⟨421505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1770
    ⟨421505, by decide⟩ (by decide) (![⟨421331, by decide⟩,⟨421398, by decide⟩,⟨421444, by decide⟩,⟨421504, by decide⟩]) unmarked_context_10_1770_421505 node_context_10_1770_421505
  intro a
  fin_cases a
  · exact context_11_7080_421331
  · exact context_11_7081_421398
  · exact context_11_7082_421444
  · exact context_11_7083_421504

theorem selected_cut_16576 : selected 9 ⟨421514, by decide⟩
    (prefixPartial 12 28336) = some ⟨12, 2, 0, 421514, 28336, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_28336_421514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28336 ⟨421514, by decide⟩ :=
  accepted_of_selected 12 28336 ⟨421514, by decide⟩ ⟨12, 2, 0, 421514, 28336, 1109, 65536⟩
    (by decide) selected_cut_16576

theorem selected_cut_16577 : selected 9 ⟨421525, by decide⟩
    (prefixPartial 12 28337) = some ⟨12, 2, 0, 421525, 28337, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_28337_421525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28337 ⟨421525, by decide⟩ :=
  accepted_of_selected 12 28337 ⟨421525, by decide⟩ ⟨12, 2, 0, 421525, 28337, 1181, 65536⟩
    (by decide) selected_cut_16577

theorem selected_cut_16578 : selected 9 ⟨421535, by decide⟩
    (prefixPartial 12 28338) = some ⟨12, 2, 0, 421535, 28338, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_28338_421535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28338 ⟨421535, by decide⟩ :=
  accepted_of_selected 12 28338 ⟨421535, by decide⟩ ⟨12, 2, 0, 421535, 28338, 1065, 65536⟩
    (by decide) selected_cut_16578

theorem selected_cut_16579 : selected 9 ⟨421552, by decide⟩
    (prefixPartial 12 28339) = some ⟨12, 2, 0, 421552, 28339, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_28339_421552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28339 ⟨421552, by decide⟩ :=
  accepted_of_selected 12 28339 ⟨421552, by decide⟩ ⟨12, 2, 0, 421552, 28339, 1297, 65536⟩
    (by decide) selected_cut_16579

theorem unmarked_context_11_7084_421553 : frontier 10 ⟨421553, by decide⟩
    (prefixCache 11 7084) (prefixPartial 11 7084) = false := by
  decide +kernel

theorem node_context_11_7084_421553 : EJMOriginalGlobalDAGData.nodes 10 ⟨421553, by decide⟩ =
    .split (coordinate 11) (![⟨421514, by decide⟩,⟨421525, by decide⟩,⟨421535, by decide⟩,⟨421552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7084_421553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7084 ⟨421553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7084
    ⟨421553, by decide⟩ (by decide) (![⟨421514, by decide⟩,⟨421525, by decide⟩,⟨421535, by decide⟩,⟨421552, by decide⟩]) unmarked_context_11_7084_421553 node_context_11_7084_421553
  intro a
  fin_cases a
  · exact context_12_28336_421514
  · exact context_12_28337_421525
  · exact context_12_28338_421535
  · exact context_12_28339_421552

theorem selected_cut_16580 : selected 9 ⟨421562, by decide⟩
    (prefixPartial 12 28340) = some ⟨12, 2, 0, 421562, 28340, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_28340_421562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28340 ⟨421562, by decide⟩ :=
  accepted_of_selected 12 28340 ⟨421562, by decide⟩ ⟨12, 2, 0, 421562, 28340, 1085, 65536⟩
    (by decide) selected_cut_16580

theorem selected_cut_16581 : selected 9 ⟨421573, by decide⟩
    (prefixPartial 12 28341) = some ⟨12, 2, 0, 421573, 28341, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_28341_421573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28341 ⟨421573, by decide⟩ :=
  accepted_of_selected 12 28341 ⟨421573, by decide⟩ ⟨12, 2, 0, 421573, 28341, 1145, 65536⟩
    (by decide) selected_cut_16581

theorem selected_cut_16582 : selected 9 ⟨421585, by decide⟩
    (prefixPartial 12 28342) = some ⟨12, 2, 0, 421585, 28342, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_28342_421585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28342 ⟨421585, by decide⟩ :=
  accepted_of_selected 12 28342 ⟨421585, by decide⟩ ⟨12, 2, 0, 421585, 28342, 1077, 65536⟩
    (by decide) selected_cut_16582

theorem selected_cut_16583 : selected 9 ⟨421605, by decide⟩
    (prefixPartial 12 28343) = some ⟨12, 2, 0, 421605, 28343, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_28343_421605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28343 ⟨421605, by decide⟩ :=
  accepted_of_selected 12 28343 ⟨421605, by decide⟩ ⟨12, 2, 0, 421605, 28343, 1221, 65536⟩
    (by decide) selected_cut_16583

theorem unmarked_context_11_7085_421606 : frontier 10 ⟨421606, by decide⟩
    (prefixCache 11 7085) (prefixPartial 11 7085) = false := by
  decide +kernel

theorem node_context_11_7085_421606 : EJMOriginalGlobalDAGData.nodes 10 ⟨421606, by decide⟩ =
    .split (coordinate 11) (![⟨421562, by decide⟩,⟨421573, by decide⟩,⟨421585, by decide⟩,⟨421605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7085_421606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7085 ⟨421606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7085
    ⟨421606, by decide⟩ (by decide) (![⟨421562, by decide⟩,⟨421573, by decide⟩,⟨421585, by decide⟩,⟨421605, by decide⟩]) unmarked_context_11_7085_421606 node_context_11_7085_421606
  intro a
  fin_cases a
  · exact context_12_28340_421562
  · exact context_12_28341_421573
  · exact context_12_28342_421585
  · exact context_12_28343_421605

theorem selected_cut_16584 : selected 10 ⟨421641, by decide⟩
    (prefixPartial 11 7086) = some ⟨11, 2, 0, 421641, 7086, 2889, 262144⟩ := by
  decide +kernel

theorem context_11_7086_421641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7086 ⟨421641, by decide⟩ :=
  accepted_of_selected 11 7086 ⟨421641, by decide⟩ ⟨11, 2, 0, 421641, 7086, 2889, 262144⟩
    (by decide) selected_cut_16584

theorem selected_cut_16585 : selected 10 ⟨421682, by decide⟩
    (prefixPartial 11 7087) = some ⟨11, 2, 0, 421682, 7087, 3397, 262144⟩ := by
  decide +kernel

theorem context_11_7087_421682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7087 ⟨421682, by decide⟩ :=
  accepted_of_selected 11 7087 ⟨421682, by decide⟩ ⟨11, 2, 0, 421682, 7087, 3397, 262144⟩
    (by decide) selected_cut_16585

theorem unmarked_context_10_1771_421683 : frontier 11 ⟨421683, by decide⟩
    (prefixCache 10 1771) (prefixPartial 10 1771) = false := by
  decide +kernel

theorem node_context_10_1771_421683 : EJMOriginalGlobalDAGData.nodes 11 ⟨421683, by decide⟩ =
    .split (coordinate 10) (![⟨421553, by decide⟩,⟨421606, by decide⟩,⟨421641, by decide⟩,⟨421682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1771_421683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1771 ⟨421683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1771
    ⟨421683, by decide⟩ (by decide) (![⟨421553, by decide⟩,⟨421606, by decide⟩,⟨421641, by decide⟩,⟨421682, by decide⟩]) unmarked_context_10_1771_421683 node_context_10_1771_421683
  intro a
  fin_cases a
  · exact context_11_7084_421553
  · exact context_11_7085_421606
  · exact context_11_7086_421641
  · exact context_11_7087_421682

theorem unmarked_context_9_442_421684 : frontier 12 ⟨421684, by decide⟩
    (prefixCache 9 442) (prefixPartial 9 442) = false := by
  decide +kernel

theorem node_context_9_442_421684 : EJMOriginalGlobalDAGData.nodes 12 ⟨421684, by decide⟩ =
    .split (coordinate 9) (![⟨420901, by decide⟩,⟨421249, by decide⟩,⟨421505, by decide⟩,⟨421683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_442_421684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 442 ⟨421684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 442
    ⟨421684, by decide⟩ (by decide) (![⟨420901, by decide⟩,⟨421249, by decide⟩,⟨421505, by decide⟩,⟨421683, by decide⟩]) unmarked_context_9_442_421684 node_context_9_442_421684
  intro a
  fin_cases a
  · exact context_10_1768_420901
  · exact context_10_1769_421249
  · exact context_10_1770_421505
  · exact context_10_1771_421683

theorem selected_cut_16586 : selected 10 ⟨421717, by decide⟩
    (prefixPartial 11 7088) = some ⟨11, 2, 0, 421717, 7088, 3761, 262144⟩ := by
  decide +kernel

theorem context_11_7088_421717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7088 ⟨421717, by decide⟩ :=
  accepted_of_selected 11 7088 ⟨421717, by decide⟩ ⟨11, 2, 0, 421717, 7088, 3761, 262144⟩
    (by decide) selected_cut_16586

theorem selected_cut_16587 : selected 10 ⟨421749, by decide⟩
    (prefixPartial 11 7089) = some ⟨11, 2, 0, 421749, 7089, 3333, 262144⟩ := by
  decide +kernel

theorem context_11_7089_421749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7089 ⟨421749, by decide⟩ :=
  accepted_of_selected 11 7089 ⟨421749, by decide⟩ ⟨11, 2, 0, 421749, 7089, 3333, 262144⟩
    (by decide) selected_cut_16587

theorem selected_cut_16588 : selected 10 ⟨421781, by decide⟩
    (prefixPartial 11 7090) = some ⟨11, 2, 0, 421781, 7090, 3381, 262144⟩ := by
  decide +kernel

theorem context_11_7090_421781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7090 ⟨421781, by decide⟩ :=
  accepted_of_selected 11 7090 ⟨421781, by decide⟩ ⟨11, 2, 0, 421781, 7090, 3381, 262144⟩
    (by decide) selected_cut_16588

theorem selected_cut_16589 : selected 10 ⟨421806, by decide⟩
    (prefixPartial 11 7091) = some ⟨11, 2, 0, 421806, 7091, 3029, 262144⟩ := by
  decide +kernel

theorem context_11_7091_421806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7091 ⟨421806, by decide⟩ :=
  accepted_of_selected 11 7091 ⟨421806, by decide⟩ ⟨11, 2, 0, 421806, 7091, 3029, 262144⟩
    (by decide) selected_cut_16589

theorem unmarked_context_10_1772_421807 : frontier 11 ⟨421807, by decide⟩
    (prefixCache 10 1772) (prefixPartial 10 1772) = false := by
  decide +kernel

theorem node_context_10_1772_421807 : EJMOriginalGlobalDAGData.nodes 11 ⟨421807, by decide⟩ =
    .split (coordinate 10) (![⟨421717, by decide⟩,⟨421749, by decide⟩,⟨421781, by decide⟩,⟨421806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1772_421807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1772 ⟨421807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1772
    ⟨421807, by decide⟩ (by decide) (![⟨421717, by decide⟩,⟨421749, by decide⟩,⟨421781, by decide⟩,⟨421806, by decide⟩]) unmarked_context_10_1772_421807 node_context_10_1772_421807
  intro a
  fin_cases a
  · exact context_11_7088_421717
  · exact context_11_7089_421749
  · exact context_11_7090_421781
  · exact context_11_7091_421806

theorem selected_cut_16590 : selected 10 ⟨421834, by decide⟩
    (prefixPartial 11 7092) = some ⟨11, 2, 0, 421834, 7092, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_7092_421834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7092 ⟨421834, by decide⟩ :=
  accepted_of_selected 11 7092 ⟨421834, by decide⟩ ⟨11, 2, 0, 421834, 7092, 2885, 262144⟩
    (by decide) selected_cut_16590

theorem selected_cut_16591 : selected 10 ⟨421857, by decide⟩
    (prefixPartial 11 7093) = some ⟨11, 2, 0, 421857, 7093, 2261, 262144⟩ := by
  decide +kernel

theorem context_11_7093_421857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7093 ⟨421857, by decide⟩ :=
  accepted_of_selected 11 7093 ⟨421857, by decide⟩ ⟨11, 2, 0, 421857, 7093, 2261, 262144⟩
    (by decide) selected_cut_16591

theorem selected_cut_16592 : selected 10 ⟨421878, by decide⟩
    (prefixPartial 11 7094) = some ⟨11, 2, 0, 421878, 7094, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_7094_421878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7094 ⟨421878, by decide⟩ :=
  accepted_of_selected 11 7094 ⟨421878, by decide⟩ ⟨11, 2, 0, 421878, 7094, 2069, 262144⟩
    (by decide) selected_cut_16592

theorem selected_cut_16593 : selected 10 ⟨421892, by decide⟩
    (prefixPartial 11 7095) = some ⟨11, 2, 0, 421892, 7095, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_7095_421892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7095 ⟨421892, by decide⟩ :=
  accepted_of_selected 11 7095 ⟨421892, by decide⟩ ⟨11, 2, 0, 421892, 7095, 1805, 262144⟩
    (by decide) selected_cut_16593

theorem unmarked_context_10_1773_421893 : frontier 11 ⟨421893, by decide⟩
    (prefixCache 10 1773) (prefixPartial 10 1773) = false := by
  decide +kernel

theorem node_context_10_1773_421893 : EJMOriginalGlobalDAGData.nodes 11 ⟨421893, by decide⟩ =
    .split (coordinate 10) (![⟨421834, by decide⟩,⟨421857, by decide⟩,⟨421878, by decide⟩,⟨421892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1773_421893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1773 ⟨421893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1773
    ⟨421893, by decide⟩ (by decide) (![⟨421834, by decide⟩,⟨421857, by decide⟩,⟨421878, by decide⟩,⟨421892, by decide⟩]) unmarked_context_10_1773_421893 node_context_10_1773_421893
  intro a
  fin_cases a
  · exact context_11_7092_421834
  · exact context_11_7093_421857
  · exact context_11_7094_421878
  · exact context_11_7095_421892

theorem selected_cut_16594 : selected 11 ⟨421955, by decide⟩
    (prefixPartial 10 1774) = some ⟨10, 2, 0, 421955, 1774, 3913, 1048576⟩ := by
  decide +kernel

theorem context_10_1774_421955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1774 ⟨421955, by decide⟩ :=
  accepted_of_selected 10 1774 ⟨421955, by decide⟩ ⟨10, 2, 0, 421955, 1774, 3913, 1048576⟩
    (by decide) selected_cut_16594

theorem selected_cut_16595 : selected 11 ⟨421997, by decide⟩
    (prefixPartial 10 1775) = some ⟨10, 2, 0, 421997, 1775, 1229, 1048576⟩ := by
  decide +kernel

theorem context_10_1775_421997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1775 ⟨421997, by decide⟩ :=
  accepted_of_selected 10 1775 ⟨421997, by decide⟩ ⟨10, 2, 0, 421997, 1775, 1229, 1048576⟩
    (by decide) selected_cut_16595

theorem unmarked_context_9_443_421998 : frontier 12 ⟨421998, by decide⟩
    (prefixCache 9 443) (prefixPartial 9 443) = false := by
  decide +kernel

theorem node_context_9_443_421998 : EJMOriginalGlobalDAGData.nodes 12 ⟨421998, by decide⟩ =
    .split (coordinate 9) (![⟨421807, by decide⟩,⟨421893, by decide⟩,⟨421955, by decide⟩,⟨421997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_443_421998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 443 ⟨421998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 443
    ⟨421998, by decide⟩ (by decide) (![⟨421807, by decide⟩,⟨421893, by decide⟩,⟨421955, by decide⟩,⟨421997, by decide⟩]) unmarked_context_9_443_421998 node_context_9_443_421998
  intro a
  fin_cases a
  · exact context_10_1772_421807
  · exact context_10_1773_421893
  · exact context_10_1774_421955
  · exact context_10_1775_421997

theorem unmarked_context_8_110_421999 : frontier 13 ⟨421999, by decide⟩
    (prefixCache 8 110) (prefixPartial 8 110) = false := by
  decide +kernel

theorem node_context_8_110_421999 : EJMOriginalGlobalDAGData.nodes 13 ⟨421999, by decide⟩ =
    .split (coordinate 8) (![⟨416577, by decide⟩,⟨420448, by decide⟩,⟨421684, by decide⟩,⟨421998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_110_421999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 110 ⟨421999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 110
    ⟨421999, by decide⟩ (by decide) (![⟨416577, by decide⟩,⟨420448, by decide⟩,⟨421684, by decide⟩,⟨421998, by decide⟩]) unmarked_context_8_110_421999 node_context_8_110_421999
  intro a
  fin_cases a
  · exact context_9_440_416577
  · exact context_9_441_420448
  · exact context_9_442_421684
  · exact context_9_443_421998

theorem selected_cut_16596 : selected 10 ⟨422001, by decide⟩
    (prefixPartial 11 7104) = some ⟨11, 2, 0, 422001, 7104, 5, 262144⟩ := by
  decide +kernel

theorem context_11_7104_422001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7104 ⟨422001, by decide⟩ :=
  accepted_of_selected 11 7104 ⟨422001, by decide⟩ ⟨11, 2, 0, 422001, 7104, 5, 262144⟩
    (by decide) selected_cut_16596

theorem selected_cut_16597 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 28420) = some ⟨12, 1, 0, 34034, 28420, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28420_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28420 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 28420 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 28420, 1, 65536⟩
    (by decide) selected_cut_16597

theorem selected_cut_16598 : selected 7 ⟨422052, by decide⟩
    (prefixPartial 14 454736) = some ⟨14, 2, 0, 422052, 454736, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_454736_422052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454736 ⟨422052, by decide⟩ :=
  accepted_of_selected 14 454736 ⟨422052, by decide⟩ ⟨14, 2, 0, 422052, 454736, 1289, 4096⟩
    (by decide) selected_cut_16598

theorem selected_cut_16599 : selected 7 ⟨422084, by decide⟩
    (prefixPartial 14 454737) = some ⟨14, 2, 0, 422084, 454737, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_454737_422084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454737 ⟨422084, by decide⟩ :=
  accepted_of_selected 14 454737 ⟨422084, by decide⟩ ⟨14, 2, 0, 422084, 454737, 1357, 4096⟩
    (by decide) selected_cut_16599

theorem selected_cut_16600 : selected 7 ⟨422110, by decide⟩
    (prefixPartial 14 454738) = some ⟨14, 2, 0, 422110, 454738, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_454738_422110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454738 ⟨422110, by decide⟩ :=
  accepted_of_selected 14 454738 ⟨422110, by decide⟩ ⟨14, 2, 0, 422110, 454738, 1189, 4096⟩
    (by decide) selected_cut_16600

theorem selected_cut_16601 : selected 7 ⟨422128, by decide⟩
    (prefixPartial 14 454739) = some ⟨14, 2, 0, 422128, 454739, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_454739_422128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454739 ⟨422128, by decide⟩ :=
  accepted_of_selected 14 454739 ⟨422128, by decide⟩ ⟨14, 2, 0, 422128, 454739, 1021, 4096⟩
    (by decide) selected_cut_16601

theorem unmarked_context_13_113684_422129 : frontier 8 ⟨422129, by decide⟩
    (prefixCache 13 113684) (prefixPartial 13 113684) = false := by
  decide +kernel

theorem node_context_13_113684_422129 : EJMOriginalGlobalDAGData.nodes 8 ⟨422129, by decide⟩ =
    .split (coordinate 13) (![⟨422052, by decide⟩,⟨422084, by decide⟩,⟨422110, by decide⟩,⟨422128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113684_422129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113684 ⟨422129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113684
    ⟨422129, by decide⟩ (by decide) (![⟨422052, by decide⟩,⟨422084, by decide⟩,⟨422110, by decide⟩,⟨422128, by decide⟩]) unmarked_context_13_113684_422129 node_context_13_113684_422129
  intro a
  fin_cases a
  · exact context_14_454736_422052
  · exact context_14_454737_422084
  · exact context_14_454738_422110
  · exact context_14_454739_422128

theorem selected_cut_16602 : selected 7 ⟨422163, by decide⟩
    (prefixPartial 14 454740) = some ⟨14, 2, 0, 422163, 454740, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_454740_422163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454740 ⟨422163, by decide⟩ :=
  accepted_of_selected 14 454740 ⟨422163, by decide⟩ ⟨14, 2, 0, 422163, 454740, 1133, 4096⟩
    (by decide) selected_cut_16602

theorem selected_cut_16603 : selected 7 ⟨422202, by decide⟩
    (prefixPartial 14 454741) = some ⟨14, 2, 0, 422202, 454741, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_454741_422202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454741 ⟨422202, by decide⟩ :=
  accepted_of_selected 14 454741 ⟨422202, by decide⟩ ⟨14, 2, 0, 422202, 454741, 1053, 4096⟩
    (by decide) selected_cut_16603

theorem selected_cut_16604 : selected 7 ⟨422235, by decide⟩
    (prefixPartial 14 454742) = some ⟨14, 2, 0, 422235, 454742, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_454742_422235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454742 ⟨422235, by decide⟩ :=
  accepted_of_selected 14 454742 ⟨422235, by decide⟩ ⟨14, 2, 0, 422235, 454742, 1041, 4096⟩
    (by decide) selected_cut_16604

theorem selected_cut_16605 : selected 7 ⟨422267, by decide⟩
    (prefixPartial 14 454743) = some ⟨14, 2, 0, 422267, 454743, 877, 4096⟩ := by
  decide +kernel

theorem context_14_454743_422267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454743 ⟨422267, by decide⟩ :=
  accepted_of_selected 14 454743 ⟨422267, by decide⟩ ⟨14, 2, 0, 422267, 454743, 877, 4096⟩
    (by decide) selected_cut_16605

theorem unmarked_context_13_113685_422268 : frontier 8 ⟨422268, by decide⟩
    (prefixCache 13 113685) (prefixPartial 13 113685) = false := by
  decide +kernel

theorem node_context_13_113685_422268 : EJMOriginalGlobalDAGData.nodes 8 ⟨422268, by decide⟩ =
    .split (coordinate 13) (![⟨422163, by decide⟩,⟨422202, by decide⟩,⟨422235, by decide⟩,⟨422267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113685_422268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113685 ⟨422268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113685
    ⟨422268, by decide⟩ (by decide) (![⟨422163, by decide⟩,⟨422202, by decide⟩,⟨422235, by decide⟩,⟨422267, by decide⟩]) unmarked_context_13_113685_422268 node_context_13_113685_422268
  intro a
  fin_cases a
  · exact context_14_454740_422163
  · exact context_14_454741_422202
  · exact context_14_454742_422235
  · exact context_14_454743_422267

theorem selected_cut_16606 : selected 8 ⟨422336, by decide⟩
    (prefixPartial 13 113686) = some ⟨13, 2, 0, 422336, 113686, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_113686_422336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113686 ⟨422336, by decide⟩ :=
  accepted_of_selected 13 113686 ⟨422336, by decide⟩ ⟨13, 2, 0, 422336, 113686, 2777, 16384⟩
    (by decide) selected_cut_16606

theorem selected_cut_16607 : selected 8 ⟨422348, by decide⟩
    (prefixPartial 13 113687) = some ⟨13, 2, 0, 422348, 113687, 861, 16384⟩ := by
  decide +kernel

theorem context_13_113687_422348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113687 ⟨422348, by decide⟩ :=
  accepted_of_selected 13 113687 ⟨422348, by decide⟩ ⟨13, 2, 0, 422348, 113687, 861, 16384⟩
    (by decide) selected_cut_16607

theorem unmarked_context_12_28421_422349 : frontier 9 ⟨422349, by decide⟩
    (prefixCache 12 28421) (prefixPartial 12 28421) = false := by
  decide +kernel

theorem node_context_12_28421_422349 : EJMOriginalGlobalDAGData.nodes 9 ⟨422349, by decide⟩ =
    .split (coordinate 12) (![⟨422129, by decide⟩,⟨422268, by decide⟩,⟨422336, by decide⟩,⟨422348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28421_422349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28421 ⟨422349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28421
    ⟨422349, by decide⟩ (by decide) (![⟨422129, by decide⟩,⟨422268, by decide⟩,⟨422336, by decide⟩,⟨422348, by decide⟩]) unmarked_context_12_28421_422349 node_context_12_28421_422349
  intro a
  fin_cases a
  · exact context_13_113684_422129
  · exact context_13_113685_422268
  · exact context_13_113686_422336
  · exact context_13_113687_422348

theorem selected_cut_16608 : selected 7 ⟨422383, by decide⟩
    (prefixPartial 14 454752) = some ⟨14, 2, 0, 422383, 454752, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_454752_422383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454752 ⟨422383, by decide⟩ :=
  accepted_of_selected 14 454752 ⟨422383, by decide⟩ ⟨14, 2, 0, 422383, 454752, 1161, 4096⟩
    (by decide) selected_cut_16608

theorem selected_cut_16609 : selected 7 ⟨422417, by decide⟩
    (prefixPartial 14 454753) = some ⟨14, 2, 0, 422417, 454753, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_454753_422417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454753 ⟨422417, by decide⟩ :=
  accepted_of_selected 14 454753 ⟨422417, by decide⟩ ⟨14, 2, 0, 422417, 454753, 1433, 4096⟩
    (by decide) selected_cut_16609

theorem selected_cut_16610 : selected 7 ⟨422445, by decide⟩
    (prefixPartial 14 454754) = some ⟨14, 2, 0, 422445, 454754, 1325, 4096⟩ := by
  decide +kernel

theorem context_14_454754_422445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454754 ⟨422445, by decide⟩ :=
  accepted_of_selected 14 454754 ⟨422445, by decide⟩ ⟨14, 2, 0, 422445, 454754, 1325, 4096⟩
    (by decide) selected_cut_16610

theorem selected_cut_16611 : selected 7 ⟨422465, by decide⟩
    (prefixPartial 14 454755) = some ⟨14, 2, 0, 422465, 454755, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_454755_422465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 454755 ⟨422465, by decide⟩ :=
  accepted_of_selected 14 454755 ⟨422465, by decide⟩ ⟨14, 2, 0, 422465, 454755, 1113, 4096⟩
    (by decide) selected_cut_16611

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
