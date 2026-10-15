/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover379
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36483 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289308) = some ⟨12, 1, 0, 1738, 289308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289308_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289308 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289308 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289308, 1, 65536⟩
    (by decide) selected_cut_36483

theorem selected_cut_36484 : selected 9 ⟨966943, by decide⟩
    (prefixPartial 12 289309) = some ⟨12, 2, 0, 966943, 289309, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_289309_966943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289309 ⟨966943, by decide⟩ :=
  accepted_of_selected 12 289309 ⟨966943, by decide⟩ ⟨12, 2, 0, 966943, 289309, 2069, 65536⟩
    (by decide) selected_cut_36484

theorem selected_cut_36485 : selected 9 ⟨966996, by decide⟩
    (prefixPartial 12 289310) = some ⟨12, 2, 0, 966996, 289310, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_289310_966996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289310 ⟨966996, by decide⟩ :=
  accepted_of_selected 12 289310 ⟨966996, by decide⟩ ⟨12, 2, 0, 966996, 289310, 2969, 65536⟩
    (by decide) selected_cut_36485

theorem selected_cut_36486 : selected 9 ⟨967055, by decide⟩
    (prefixPartial 12 289311) = some ⟨12, 2, 0, 967055, 289311, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_289311_967055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289311 ⟨967055, by decide⟩ :=
  accepted_of_selected 12 289311 ⟨967055, by decide⟩ ⟨12, 2, 0, 967055, 289311, 3189, 65536⟩
    (by decide) selected_cut_36486

theorem unmarked_context_11_72327_967056 : frontier 10 ⟨967056, by decide⟩
    (prefixCache 11 72327) (prefixPartial 11 72327) = false := by
  decide +kernel

theorem node_context_11_72327_967056 : EJMOriginalGlobalDAGData.nodes 10 ⟨967056, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨966943, by decide⟩,⟨966996, by decide⟩,⟨967055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72327_967056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72327 ⟨967056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72327
    ⟨967056, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨966943, by decide⟩,⟨966996, by decide⟩,⟨967055, by decide⟩]) unmarked_context_11_72327_967056 node_context_11_72327_967056
  intro a
  fin_cases a
  · exact context_12_289308_1738
  · exact context_12_289309_966943
  · exact context_12_289310_966996
  · exact context_12_289311_967055

theorem unmarked_context_10_18081_967057 : frontier 11 ⟨967057, by decide⟩
    (prefixCache 10 18081) (prefixPartial 10 18081) = false := by
  decide +kernel

theorem node_context_10_18081_967057 : EJMOriginalGlobalDAGData.nodes 11 ⟨967057, by decide⟩ =
    .split (coordinate 10) (![⟨966644, by decide⟩,⟨966769, by decide⟩,⟨966888, by decide⟩,⟨967056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18081_967057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18081 ⟨967057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18081
    ⟨967057, by decide⟩ (by decide) (![⟨966644, by decide⟩,⟨966769, by decide⟩,⟨966888, by decide⟩,⟨967056, by decide⟩]) unmarked_context_10_18081_967057 node_context_10_18081_967057
  intro a
  fin_cases a
  · exact context_11_72324_966644
  · exact context_11_72325_966769
  · exact context_11_72326_966888
  · exact context_11_72327_967056

theorem selected_cut_36487 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289312) = some ⟨12, 1, 0, 1738, 289312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289312_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289312 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289312 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289312, 1, 65536⟩
    (by decide) selected_cut_36487

theorem selected_cut_36488 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289313) = some ⟨12, 1, 0, 1738, 289313, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289313_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289313 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289313 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289313, 1, 65536⟩
    (by decide) selected_cut_36488

theorem selected_cut_36489 : selected 9 ⟨967110, by decide⟩
    (prefixPartial 12 289314) = some ⟨12, 2, 0, 967110, 289314, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_289314_967110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289314 ⟨967110, by decide⟩ :=
  accepted_of_selected 12 289314 ⟨967110, by decide⟩ ⟨12, 2, 0, 967110, 289314, 1833, 65536⟩
    (by decide) selected_cut_36489

theorem selected_cut_36490 : selected 9 ⟨967173, by decide⟩
    (prefixPartial 12 289315) = some ⟨12, 2, 0, 967173, 289315, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_289315_967173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289315 ⟨967173, by decide⟩ :=
  accepted_of_selected 12 289315 ⟨967173, by decide⟩ ⟨12, 2, 0, 967173, 289315, 3097, 65536⟩
    (by decide) selected_cut_36490

theorem unmarked_context_11_72328_967174 : frontier 10 ⟨967174, by decide⟩
    (prefixCache 11 72328) (prefixPartial 11 72328) = false := by
  decide +kernel

theorem node_context_11_72328_967174 : EJMOriginalGlobalDAGData.nodes 10 ⟨967174, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨967110, by decide⟩,⟨967173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72328_967174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72328 ⟨967174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72328
    ⟨967174, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨967110, by decide⟩,⟨967173, by decide⟩]) unmarked_context_11_72328_967174 node_context_11_72328_967174
  intro a
  fin_cases a
  · exact context_12_289312_1738
  · exact context_12_289313_1738
  · exact context_12_289314_967110
  · exact context_12_289315_967173

theorem selected_cut_36491 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289316) = some ⟨12, 1, 0, 1738, 289316, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289316_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289316 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289316 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289316, 1, 65536⟩
    (by decide) selected_cut_36491

theorem selected_cut_36492 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289317) = some ⟨12, 1, 0, 1738, 289317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289317_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289317 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289317 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289317, 1, 65536⟩
    (by decide) selected_cut_36492

theorem selected_cut_36493 : selected 9 ⟨967225, by decide⟩
    (prefixPartial 12 289318) = some ⟨12, 2, 0, 967225, 289318, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_289318_967225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289318 ⟨967225, by decide⟩ :=
  accepted_of_selected 12 289318 ⟨967225, by decide⟩ ⟨12, 2, 0, 967225, 289318, 1825, 65536⟩
    (by decide) selected_cut_36493

theorem selected_cut_36494 : selected 9 ⟨967281, by decide⟩
    (prefixPartial 12 289319) = some ⟨12, 2, 0, 967281, 289319, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_289319_967281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289319 ⟨967281, by decide⟩ :=
  accepted_of_selected 12 289319 ⟨967281, by decide⟩ ⟨12, 2, 0, 967281, 289319, 2745, 65536⟩
    (by decide) selected_cut_36494

theorem unmarked_context_11_72329_967282 : frontier 10 ⟨967282, by decide⟩
    (prefixCache 11 72329) (prefixPartial 11 72329) = false := by
  decide +kernel

theorem node_context_11_72329_967282 : EJMOriginalGlobalDAGData.nodes 10 ⟨967282, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨967225, by decide⟩,⟨967281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72329_967282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72329 ⟨967282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72329
    ⟨967282, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨967225, by decide⟩,⟨967281, by decide⟩]) unmarked_context_11_72329_967282 node_context_11_72329_967282
  intro a
  fin_cases a
  · exact context_12_289316_1738
  · exact context_12_289317_1738
  · exact context_12_289318_967225
  · exact context_12_289319_967281

theorem selected_cut_36495 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 72330) = some ⟨11, 1, 0, 900587, 72330, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72330_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72330 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 72330 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 72330, 1, 262144⟩
    (by decide) selected_cut_36495

theorem selected_cut_36496 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289324) = some ⟨12, 1, 0, 1738, 289324, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289324_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289324 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289324 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289324, 1, 65536⟩
    (by decide) selected_cut_36496

theorem selected_cut_36497 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289325) = some ⟨12, 1, 0, 1738, 289325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289325_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289325 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289325 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289325, 1, 65536⟩
    (by decide) selected_cut_36497

theorem selected_cut_36498 : selected 9 ⟨967327, by decide⟩
    (prefixPartial 12 289326) = some ⟨12, 2, 0, 967327, 289326, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_289326_967327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289326 ⟨967327, by decide⟩ :=
  accepted_of_selected 12 289326 ⟨967327, by decide⟩ ⟨12, 2, 0, 967327, 289326, 1933, 65536⟩
    (by decide) selected_cut_36498

theorem selected_cut_36499 : selected 9 ⟨967380, by decide⟩
    (prefixPartial 12 289327) = some ⟨12, 2, 0, 967380, 289327, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_289327_967380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289327 ⟨967380, by decide⟩ :=
  accepted_of_selected 12 289327 ⟨967380, by decide⟩ ⟨12, 2, 0, 967380, 289327, 2917, 65536⟩
    (by decide) selected_cut_36499

theorem unmarked_context_11_72331_967381 : frontier 10 ⟨967381, by decide⟩
    (prefixCache 11 72331) (prefixPartial 11 72331) = false := by
  decide +kernel

theorem node_context_11_72331_967381 : EJMOriginalGlobalDAGData.nodes 10 ⟨967381, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨967327, by decide⟩,⟨967380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72331_967381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72331 ⟨967381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72331
    ⟨967381, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨967327, by decide⟩,⟨967380, by decide⟩]) unmarked_context_11_72331_967381 node_context_11_72331_967381
  intro a
  fin_cases a
  · exact context_12_289324_1738
  · exact context_12_289325_1738
  · exact context_12_289326_967327
  · exact context_12_289327_967380

theorem unmarked_context_10_18082_967382 : frontier 11 ⟨967382, by decide⟩
    (prefixCache 10 18082) (prefixPartial 10 18082) = false := by
  decide +kernel

theorem node_context_10_18082_967382 : EJMOriginalGlobalDAGData.nodes 11 ⟨967382, by decide⟩ =
    .split (coordinate 10) (![⟨967174, by decide⟩,⟨967282, by decide⟩,⟨900587, by decide⟩,⟨967381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18082_967382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18082 ⟨967382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18082
    ⟨967382, by decide⟩ (by decide) (![⟨967174, by decide⟩,⟨967282, by decide⟩,⟨900587, by decide⟩,⟨967381, by decide⟩]) unmarked_context_10_18082_967382 node_context_10_18082_967382
  intro a
  fin_cases a
  · exact context_11_72328_967174
  · exact context_11_72329_967282
  · exact context_11_72330_900587
  · exact context_11_72331_967381

theorem selected_cut_36500 : selected 10 ⟨967460, by decide⟩
    (prefixPartial 11 72332) = some ⟨11, 2, 0, 967460, 72332, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_72332_967460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72332 ⟨967460, by decide⟩ :=
  accepted_of_selected 11 72332 ⟨967460, by decide⟩ ⟨11, 2, 0, 967460, 72332, 2377, 262144⟩
    (by decide) selected_cut_36500

theorem selected_cut_36501 : selected 10 ⟨967514, by decide⟩
    (prefixPartial 11 72333) = some ⟨11, 2, 0, 967514, 72333, 2005, 262144⟩ := by
  decide +kernel

theorem context_11_72333_967514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72333 ⟨967514, by decide⟩ :=
  accepted_of_selected 11 72333 ⟨967514, by decide⟩ ⟨11, 2, 0, 967514, 72333, 2005, 262144⟩
    (by decide) selected_cut_36501

theorem selected_cut_36502 : selected 10 ⟨967582, by decide⟩
    (prefixPartial 11 72334) = some ⟨11, 2, 0, 967582, 72334, 2317, 262144⟩ := by
  decide +kernel

theorem context_11_72334_967582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72334 ⟨967582, by decide⟩ :=
  accepted_of_selected 11 72334 ⟨967582, by decide⟩ ⟨11, 2, 0, 967582, 72334, 2317, 262144⟩
    (by decide) selected_cut_36502

theorem selected_cut_36503 : selected 10 ⟨967626, by decide⟩
    (prefixPartial 11 72335) = some ⟨11, 2, 0, 967626, 72335, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_72335_967626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72335 ⟨967626, by decide⟩ :=
  accepted_of_selected 11 72335 ⟨967626, by decide⟩ ⟨11, 2, 0, 967626, 72335, 1925, 262144⟩
    (by decide) selected_cut_36503

theorem unmarked_context_10_18083_967627 : frontier 11 ⟨967627, by decide⟩
    (prefixCache 10 18083) (prefixPartial 10 18083) = false := by
  decide +kernel

theorem node_context_10_18083_967627 : EJMOriginalGlobalDAGData.nodes 11 ⟨967627, by decide⟩ =
    .split (coordinate 10) (![⟨967460, by decide⟩,⟨967514, by decide⟩,⟨967582, by decide⟩,⟨967626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18083_967627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18083 ⟨967627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18083
    ⟨967627, by decide⟩ (by decide) (![⟨967460, by decide⟩,⟨967514, by decide⟩,⟨967582, by decide⟩,⟨967626, by decide⟩]) unmarked_context_10_18083_967627 node_context_10_18083_967627
  intro a
  fin_cases a
  · exact context_11_72332_967460
  · exact context_11_72333_967514
  · exact context_11_72334_967582
  · exact context_11_72335_967626

theorem unmarked_context_9_4520_967628 : frontier 12 ⟨967628, by decide⟩
    (prefixCache 9 4520) (prefixPartial 9 4520) = false := by
  decide +kernel

theorem node_context_9_4520_967628 : EJMOriginalGlobalDAGData.nodes 12 ⟨967628, by decide⟩ =
    .split (coordinate 9) (![⟨966450, by decide⟩,⟨967057, by decide⟩,⟨967382, by decide⟩,⟨967627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4520_967628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4520 ⟨967628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4520
    ⟨967628, by decide⟩ (by decide) (![⟨966450, by decide⟩,⟨967057, by decide⟩,⟨967382, by decide⟩,⟨967627, by decide⟩]) unmarked_context_9_4520_967628 node_context_9_4520_967628
  intro a
  fin_cases a
  · exact context_10_18080_966450
  · exact context_10_18081_967057
  · exact context_10_18082_967382
  · exact context_10_18083_967627

theorem selected_cut_36504 : selected 9 ⟨967703, by decide⟩
    (prefixPartial 12 289344) = some ⟨12, 2, 0, 967703, 289344, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_289344_967703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289344 ⟨967703, by decide⟩ :=
  accepted_of_selected 12 289344 ⟨967703, by decide⟩ ⟨12, 2, 0, 967703, 289344, 1077, 65536⟩
    (by decide) selected_cut_36504

theorem selected_cut_36505 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289345) = some ⟨12, 1, 0, 896706, 289345, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289345_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289345 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289345 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289345, 1, 65536⟩
    (by decide) selected_cut_36505

theorem selected_cut_36506 : selected 9 ⟨967749, by decide⟩
    (prefixPartial 12 289346) = some ⟨12, 2, 0, 967749, 289346, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_289346_967749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289346 ⟨967749, by decide⟩ :=
  accepted_of_selected 12 289346 ⟨967749, by decide⟩ ⟨12, 2, 0, 967749, 289346, 2329, 65536⟩
    (by decide) selected_cut_36506

theorem selected_cut_36507 : selected 9 ⟨967795, by decide⟩
    (prefixPartial 12 289347) = some ⟨12, 2, 0, 967795, 289347, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_289347_967795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289347 ⟨967795, by decide⟩ :=
  accepted_of_selected 12 289347 ⟨967795, by decide⟩ ⟨12, 2, 0, 967795, 289347, 2677, 65536⟩
    (by decide) selected_cut_36507

theorem unmarked_context_11_72336_967796 : frontier 10 ⟨967796, by decide⟩
    (prefixCache 11 72336) (prefixPartial 11 72336) = false := by
  decide +kernel

theorem node_context_11_72336_967796 : EJMOriginalGlobalDAGData.nodes 10 ⟨967796, by decide⟩ =
    .split (coordinate 11) (![⟨967703, by decide⟩,⟨896706, by decide⟩,⟨967749, by decide⟩,⟨967795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72336_967796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72336 ⟨967796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72336
    ⟨967796, by decide⟩ (by decide) (![⟨967703, by decide⟩,⟨896706, by decide⟩,⟨967749, by decide⟩,⟨967795, by decide⟩]) unmarked_context_11_72336_967796 node_context_11_72336_967796
  intro a
  fin_cases a
  · exact context_12_289344_967703
  · exact context_12_289345_896706
  · exact context_12_289346_967749
  · exact context_12_289347_967795

theorem selected_cut_36508 : selected 9 ⟨967846, by decide⟩
    (prefixPartial 12 289348) = some ⟨12, 2, 0, 967846, 289348, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_289348_967846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289348 ⟨967846, by decide⟩ :=
  accepted_of_selected 12 289348 ⟨967846, by decide⟩ ⟨12, 2, 0, 967846, 289348, 2021, 65536⟩
    (by decide) selected_cut_36508

theorem selected_cut_36509 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289349) = some ⟨12, 1, 0, 896706, 289349, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289349_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289349 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289349 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289349, 1, 65536⟩
    (by decide) selected_cut_36509

theorem selected_cut_36510 : selected 9 ⟨967895, by decide⟩
    (prefixPartial 12 289350) = some ⟨12, 2, 0, 967895, 289350, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_289350_967895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289350 ⟨967895, by decide⟩ :=
  accepted_of_selected 12 289350 ⟨967895, by decide⟩ ⟨12, 2, 0, 967895, 289350, 2313, 65536⟩
    (by decide) selected_cut_36510

theorem selected_cut_36511 : selected 9 ⟨967939, by decide⟩
    (prefixPartial 12 289351) = some ⟨12, 2, 0, 967939, 289351, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_289351_967939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289351 ⟨967939, by decide⟩ :=
  accepted_of_selected 12 289351 ⟨967939, by decide⟩ ⟨12, 2, 0, 967939, 289351, 2509, 65536⟩
    (by decide) selected_cut_36511

theorem unmarked_context_11_72337_967940 : frontier 10 ⟨967940, by decide⟩
    (prefixCache 11 72337) (prefixPartial 11 72337) = false := by
  decide +kernel

theorem node_context_11_72337_967940 : EJMOriginalGlobalDAGData.nodes 10 ⟨967940, by decide⟩ =
    .split (coordinate 11) (![⟨967846, by decide⟩,⟨896706, by decide⟩,⟨967895, by decide⟩,⟨967939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72337_967940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72337 ⟨967940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72337
    ⟨967940, by decide⟩ (by decide) (![⟨967846, by decide⟩,⟨896706, by decide⟩,⟨967895, by decide⟩,⟨967939, by decide⟩]) unmarked_context_11_72337_967940 node_context_11_72337_967940
  intro a
  fin_cases a
  · exact context_12_289348_967846
  · exact context_12_289349_896706
  · exact context_12_289350_967895
  · exact context_12_289351_967939

theorem selected_cut_36512 : selected 9 ⟨967986, by decide⟩
    (prefixPartial 12 289352) = some ⟨12, 2, 0, 967986, 289352, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_289352_967986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289352 ⟨967986, by decide⟩ :=
  accepted_of_selected 12 289352 ⟨967986, by decide⟩ ⟨12, 2, 0, 967986, 289352, 1917, 65536⟩
    (by decide) selected_cut_36512

theorem selected_cut_36513 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289353) = some ⟨12, 1, 0, 896706, 289353, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289353_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289353 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289353 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289353, 1, 65536⟩
    (by decide) selected_cut_36513

theorem selected_cut_36514 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 289354) = some ⟨12, 1, 0, 893903, 289354, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289354_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289354 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 289354 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 289354, 1, 65536⟩
    (by decide) selected_cut_36514

theorem selected_cut_36515 : selected 9 ⟨968027, by decide⟩
    (prefixPartial 12 289355) = some ⟨12, 2, 0, 968027, 289355, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_289355_968027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289355 ⟨968027, by decide⟩ :=
  accepted_of_selected 12 289355 ⟨968027, by decide⟩ ⟨12, 2, 0, 968027, 289355, 2369, 65536⟩
    (by decide) selected_cut_36515

theorem unmarked_context_11_72338_968028 : frontier 10 ⟨968028, by decide⟩
    (prefixCache 11 72338) (prefixPartial 11 72338) = false := by
  decide +kernel

theorem node_context_11_72338_968028 : EJMOriginalGlobalDAGData.nodes 10 ⟨968028, by decide⟩ =
    .split (coordinate 11) (![⟨967986, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨968027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72338_968028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72338 ⟨968028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72338
    ⟨968028, by decide⟩ (by decide) (![⟨967986, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨968027, by decide⟩]) unmarked_context_11_72338_968028 node_context_11_72338_968028
  intro a
  fin_cases a
  · exact context_12_289352_967986
  · exact context_12_289353_896706
  · exact context_12_289354_893903
  · exact context_12_289355_968027

theorem selected_cut_36516 : selected 9 ⟨968076, by decide⟩
    (prefixPartial 12 289356) = some ⟨12, 2, 0, 968076, 289356, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_289356_968076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289356 ⟨968076, by decide⟩ :=
  accepted_of_selected 12 289356 ⟨968076, by decide⟩ ⟨12, 2, 0, 968076, 289356, 1805, 65536⟩
    (by decide) selected_cut_36516

theorem selected_cut_36517 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289357) = some ⟨12, 1, 0, 896706, 289357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289357_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289357 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289357 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289357, 1, 65536⟩
    (by decide) selected_cut_36517

theorem selected_cut_36518 : selected 9 ⟨968118, by decide⟩
    (prefixPartial 12 289358) = some ⟨12, 2, 0, 968118, 289358, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_289358_968118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289358 ⟨968118, by decide⟩ :=
  accepted_of_selected 12 289358 ⟨968118, by decide⟩ ⟨12, 2, 0, 968118, 289358, 2221, 65536⟩
    (by decide) selected_cut_36518

theorem selected_cut_36519 : selected 9 ⟨968165, by decide⟩
    (prefixPartial 12 289359) = some ⟨12, 2, 0, 968165, 289359, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_289359_968165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289359 ⟨968165, by decide⟩ :=
  accepted_of_selected 12 289359 ⟨968165, by decide⟩ ⟨12, 2, 0, 968165, 289359, 2413, 65536⟩
    (by decide) selected_cut_36519

theorem unmarked_context_11_72339_968166 : frontier 10 ⟨968166, by decide⟩
    (prefixCache 11 72339) (prefixPartial 11 72339) = false := by
  decide +kernel

theorem node_context_11_72339_968166 : EJMOriginalGlobalDAGData.nodes 10 ⟨968166, by decide⟩ =
    .split (coordinate 11) (![⟨968076, by decide⟩,⟨896706, by decide⟩,⟨968118, by decide⟩,⟨968165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72339_968166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72339 ⟨968166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72339
    ⟨968166, by decide⟩ (by decide) (![⟨968076, by decide⟩,⟨896706, by decide⟩,⟨968118, by decide⟩,⟨968165, by decide⟩]) unmarked_context_11_72339_968166 node_context_11_72339_968166
  intro a
  fin_cases a
  · exact context_12_289356_968076
  · exact context_12_289357_896706
  · exact context_12_289358_968118
  · exact context_12_289359_968165

theorem unmarked_context_10_18084_968167 : frontier 11 ⟨968167, by decide⟩
    (prefixCache 10 18084) (prefixPartial 10 18084) = false := by
  decide +kernel

theorem node_context_10_18084_968167 : EJMOriginalGlobalDAGData.nodes 11 ⟨968167, by decide⟩ =
    .split (coordinate 10) (![⟨967796, by decide⟩,⟨967940, by decide⟩,⟨968028, by decide⟩,⟨968166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18084_968167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18084 ⟨968167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18084
    ⟨968167, by decide⟩ (by decide) (![⟨967796, by decide⟩,⟨967940, by decide⟩,⟨968028, by decide⟩,⟨968166, by decide⟩]) unmarked_context_10_18084_968167 node_context_10_18084_968167
  intro a
  fin_cases a
  · exact context_11_72336_967796
  · exact context_11_72337_967940
  · exact context_11_72338_968028
  · exact context_11_72339_968166

theorem selected_cut_36520 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18085) = some ⟨10, 1, 0, 893098, 18085, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18085_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18085 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18085 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18085, 1, 1048576⟩
    (by decide) selected_cut_36520

theorem selected_cut_36521 : selected 10 ⟨968239, by decide⟩
    (prefixPartial 11 72344) = some ⟨11, 2, 0, 968239, 72344, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_72344_968239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72344 ⟨968239, by decide⟩ :=
  accepted_of_selected 11 72344 ⟨968239, by decide⟩ ⟨11, 2, 0, 968239, 72344, 2989, 262144⟩
    (by decide) selected_cut_36521

theorem selected_cut_36522 : selected 10 ⟨968301, by decide⟩
    (prefixPartial 11 72345) = some ⟨11, 2, 0, 968301, 72345, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_72345_968301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72345 ⟨968301, by decide⟩ :=
  accepted_of_selected 11 72345 ⟨968301, by decide⟩ ⟨11, 2, 0, 968301, 72345, 2845, 262144⟩
    (by decide) selected_cut_36522

theorem selected_cut_36523 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 72346) = some ⟨11, 1, 0, 900587, 72346, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72346_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72346 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 72346 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 72346, 1, 262144⟩
    (by decide) selected_cut_36523

theorem selected_cut_36524 : selected 10 ⟨968367, by decide⟩
    (prefixPartial 11 72347) = some ⟨11, 2, 0, 968367, 72347, 2945, 262144⟩ := by
  decide +kernel

theorem context_11_72347_968367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72347 ⟨968367, by decide⟩ :=
  accepted_of_selected 11 72347 ⟨968367, by decide⟩ ⟨11, 2, 0, 968367, 72347, 2945, 262144⟩
    (by decide) selected_cut_36524

theorem unmarked_context_10_18086_968368 : frontier 11 ⟨968368, by decide⟩
    (prefixCache 10 18086) (prefixPartial 10 18086) = false := by
  decide +kernel

theorem node_context_10_18086_968368 : EJMOriginalGlobalDAGData.nodes 11 ⟨968368, by decide⟩ =
    .split (coordinate 10) (![⟨968239, by decide⟩,⟨968301, by decide⟩,⟨900587, by decide⟩,⟨968367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18086_968368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18086 ⟨968368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18086
    ⟨968368, by decide⟩ (by decide) (![⟨968239, by decide⟩,⟨968301, by decide⟩,⟨900587, by decide⟩,⟨968367, by decide⟩]) unmarked_context_10_18086_968368 node_context_10_18086_968368
  intro a
  fin_cases a
  · exact context_11_72344_968239
  · exact context_11_72345_968301
  · exact context_11_72346_900587
  · exact context_11_72347_968367

theorem selected_cut_36525 : selected 10 ⟨968409, by decide⟩
    (prefixPartial 11 72348) = some ⟨11, 2, 0, 968409, 72348, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_72348_968409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72348 ⟨968409, by decide⟩ :=
  accepted_of_selected 11 72348 ⟨968409, by decide⟩ ⟨11, 2, 0, 968409, 72348, 1425, 262144⟩
    (by decide) selected_cut_36525

theorem selected_cut_36526 : selected 10 ⟨968440, by decide⟩
    (prefixPartial 11 72349) = some ⟨11, 2, 0, 968440, 72349, 1265, 262144⟩ := by
  decide +kernel

theorem context_11_72349_968440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72349 ⟨968440, by decide⟩ :=
  accepted_of_selected 11 72349 ⟨968440, by decide⟩ ⟨11, 2, 0, 968440, 72349, 1265, 262144⟩
    (by decide) selected_cut_36526

theorem selected_cut_36527 : selected 10 ⟨968470, by decide⟩
    (prefixPartial 11 72350) = some ⟨11, 2, 0, 968470, 72350, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_72350_968470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72350 ⟨968470, by decide⟩ :=
  accepted_of_selected 11 72350 ⟨968470, by decide⟩ ⟨11, 2, 0, 968470, 72350, 1293, 262144⟩
    (by decide) selected_cut_36527

theorem selected_cut_36528 : selected 10 ⟨968512, by decide⟩
    (prefixPartial 11 72351) = some ⟨11, 2, 0, 968512, 72351, 537, 262144⟩ := by
  decide +kernel

theorem context_11_72351_968512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72351 ⟨968512, by decide⟩ :=
  accepted_of_selected 11 72351 ⟨968512, by decide⟩ ⟨11, 2, 0, 968512, 72351, 537, 262144⟩
    (by decide) selected_cut_36528

theorem unmarked_context_10_18087_968513 : frontier 11 ⟨968513, by decide⟩
    (prefixCache 10 18087) (prefixPartial 10 18087) = false := by
  decide +kernel

theorem node_context_10_18087_968513 : EJMOriginalGlobalDAGData.nodes 11 ⟨968513, by decide⟩ =
    .split (coordinate 10) (![⟨968409, by decide⟩,⟨968440, by decide⟩,⟨968470, by decide⟩,⟨968512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18087_968513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18087 ⟨968513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18087
    ⟨968513, by decide⟩ (by decide) (![⟨968409, by decide⟩,⟨968440, by decide⟩,⟨968470, by decide⟩,⟨968512, by decide⟩]) unmarked_context_10_18087_968513 node_context_10_18087_968513
  intro a
  fin_cases a
  · exact context_11_72348_968409
  · exact context_11_72349_968440
  · exact context_11_72350_968470
  · exact context_11_72351_968512

theorem unmarked_context_9_4521_968514 : frontier 12 ⟨968514, by decide⟩
    (prefixCache 9 4521) (prefixPartial 9 4521) = false := by
  decide +kernel

theorem node_context_9_4521_968514 : EJMOriginalGlobalDAGData.nodes 12 ⟨968514, by decide⟩ =
    .split (coordinate 9) (![⟨968167, by decide⟩,⟨893098, by decide⟩,⟨968368, by decide⟩,⟨968513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4521_968514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4521 ⟨968514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4521
    ⟨968514, by decide⟩ (by decide) (![⟨968167, by decide⟩,⟨893098, by decide⟩,⟨968368, by decide⟩,⟨968513, by decide⟩]) unmarked_context_9_4521_968514 node_context_9_4521_968514
  intro a
  fin_cases a
  · exact context_10_18084_968167
  · exact context_10_18085_893098
  · exact context_10_18086_968368
  · exact context_10_18087_968513

theorem selected_cut_36529 : selected 9 ⟨290056, by decide⟩
    (prefixPartial 12 289408) = some ⟨12, 1, 0, 290056, 289408, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289408_290056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289408 ⟨290056, by decide⟩ :=
  accepted_of_selected 12 289408 ⟨290056, by decide⟩ ⟨12, 1, 0, 290056, 289408, 1, 65536⟩
    (by decide) selected_cut_36529

theorem selected_cut_36530 : selected 9 ⟨968544, by decide⟩
    (prefixPartial 12 289409) = some ⟨12, 2, 0, 968544, 289409, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_289409_968544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289409 ⟨968544, by decide⟩ :=
  accepted_of_selected 12 289409 ⟨968544, by decide⟩ ⟨12, 2, 0, 968544, 289409, 1573, 65536⟩
    (by decide) selected_cut_36530

theorem selected_cut_36531 : selected 9 ⟨968569, by decide⟩
    (prefixPartial 12 289410) = some ⟨12, 2, 0, 968569, 289410, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_289410_968569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289410 ⟨968569, by decide⟩ :=
  accepted_of_selected 12 289410 ⟨968569, by decide⟩ ⟨12, 2, 0, 968569, 289410, 1445, 65536⟩
    (by decide) selected_cut_36531

theorem selected_cut_36532 : selected 9 ⟨968598, by decide⟩
    (prefixPartial 12 289411) = some ⟨12, 2, 0, 968598, 289411, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_289411_968598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289411 ⟨968598, by decide⟩ :=
  accepted_of_selected 12 289411 ⟨968598, by decide⟩ ⟨12, 2, 0, 968598, 289411, 1685, 65536⟩
    (by decide) selected_cut_36532

theorem unmarked_context_11_72352_968599 : frontier 10 ⟨968599, by decide⟩
    (prefixCache 11 72352) (prefixPartial 11 72352) = false := by
  decide +kernel

theorem node_context_11_72352_968599 : EJMOriginalGlobalDAGData.nodes 10 ⟨968599, by decide⟩ =
    .split (coordinate 11) (![⟨290056, by decide⟩,⟨968544, by decide⟩,⟨968569, by decide⟩,⟨968598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72352_968599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72352 ⟨968599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72352
    ⟨968599, by decide⟩ (by decide) (![⟨290056, by decide⟩,⟨968544, by decide⟩,⟨968569, by decide⟩,⟨968598, by decide⟩]) unmarked_context_11_72352_968599 node_context_11_72352_968599
  intro a
  fin_cases a
  · exact context_12_289408_290056
  · exact context_12_289409_968544
  · exact context_12_289410_968569
  · exact context_12_289411_968598

theorem selected_cut_36533 : selected 9 ⟨968625, by decide⟩
    (prefixPartial 12 289412) = some ⟨12, 2, 0, 968625, 289412, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_289412_968625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289412 ⟨968625, by decide⟩ :=
  accepted_of_selected 12 289412 ⟨968625, by decide⟩ ⟨12, 2, 0, 968625, 289412, 1389, 65536⟩
    (by decide) selected_cut_36533

theorem selected_cut_36534 : selected 9 ⟨968660, by decide⟩
    (prefixPartial 12 289413) = some ⟨12, 2, 0, 968660, 289413, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_289413_968660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289413 ⟨968660, by decide⟩ :=
  accepted_of_selected 12 289413 ⟨968660, by decide⟩ ⟨12, 2, 0, 968660, 289413, 1577, 65536⟩
    (by decide) selected_cut_36534

theorem selected_cut_36535 : selected 9 ⟨968690, by decide⟩
    (prefixPartial 12 289414) = some ⟨12, 2, 0, 968690, 289414, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_289414_968690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289414 ⟨968690, by decide⟩ :=
  accepted_of_selected 12 289414 ⟨968690, by decide⟩ ⟨12, 2, 0, 968690, 289414, 1561, 65536⟩
    (by decide) selected_cut_36535

theorem selected_cut_36536 : selected 9 ⟨968721, by decide⟩
    (prefixPartial 12 289415) = some ⟨12, 2, 0, 968721, 289415, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_289415_968721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289415 ⟨968721, by decide⟩ :=
  accepted_of_selected 12 289415 ⟨968721, by decide⟩ ⟨12, 2, 0, 968721, 289415, 1585, 65536⟩
    (by decide) selected_cut_36536

theorem unmarked_context_11_72353_968722 : frontier 10 ⟨968722, by decide⟩
    (prefixCache 11 72353) (prefixPartial 11 72353) = false := by
  decide +kernel

theorem node_context_11_72353_968722 : EJMOriginalGlobalDAGData.nodes 10 ⟨968722, by decide⟩ =
    .split (coordinate 11) (![⟨968625, by decide⟩,⟨968660, by decide⟩,⟨968690, by decide⟩,⟨968721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72353_968722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72353 ⟨968722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72353
    ⟨968722, by decide⟩ (by decide) (![⟨968625, by decide⟩,⟨968660, by decide⟩,⟨968690, by decide⟩,⟨968721, by decide⟩]) unmarked_context_11_72353_968722 node_context_11_72353_968722
  intro a
  fin_cases a
  · exact context_12_289412_968625
  · exact context_12_289413_968660
  · exact context_12_289414_968690
  · exact context_12_289415_968721

theorem selected_cut_36537 : selected 9 ⟨968749, by decide⟩
    (prefixPartial 12 289416) = some ⟨12, 2, 0, 968749, 289416, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_289416_968749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289416 ⟨968749, by decide⟩ :=
  accepted_of_selected 12 289416 ⟨968749, by decide⟩ ⟨12, 2, 0, 968749, 289416, 1301, 65536⟩
    (by decide) selected_cut_36537

theorem selected_cut_36538 : selected 9 ⟨968778, by decide⟩
    (prefixPartial 12 289417) = some ⟨12, 2, 0, 968778, 289417, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_289417_968778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289417 ⟨968778, by decide⟩ :=
  accepted_of_selected 12 289417 ⟨968778, by decide⟩ ⟨12, 2, 0, 968778, 289417, 1437, 65536⟩
    (by decide) selected_cut_36538

theorem selected_cut_36539 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 289418) = some ⟨12, 1, 0, 893903, 289418, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289418_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289418 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 289418 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 289418, 1, 65536⟩
    (by decide) selected_cut_36539

theorem selected_cut_36540 : selected 9 ⟨968805, by decide⟩
    (prefixPartial 12 289419) = some ⟨12, 2, 0, 968805, 289419, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_289419_968805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289419 ⟨968805, by decide⟩ :=
  accepted_of_selected 12 289419 ⟨968805, by decide⟩ ⟨12, 2, 0, 968805, 289419, 1501, 65536⟩
    (by decide) selected_cut_36540

theorem unmarked_context_11_72354_968806 : frontier 10 ⟨968806, by decide⟩
    (prefixCache 11 72354) (prefixPartial 11 72354) = false := by
  decide +kernel

theorem node_context_11_72354_968806 : EJMOriginalGlobalDAGData.nodes 10 ⟨968806, by decide⟩ =
    .split (coordinate 11) (![⟨968749, by decide⟩,⟨968778, by decide⟩,⟨893903, by decide⟩,⟨968805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72354_968806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72354 ⟨968806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72354
    ⟨968806, by decide⟩ (by decide) (![⟨968749, by decide⟩,⟨968778, by decide⟩,⟨893903, by decide⟩,⟨968805, by decide⟩]) unmarked_context_11_72354_968806 node_context_11_72354_968806
  intro a
  fin_cases a
  · exact context_12_289416_968749
  · exact context_12_289417_968778
  · exact context_12_289418_893903
  · exact context_12_289419_968805

theorem selected_cut_36541 : selected 9 ⟨968840, by decide⟩
    (prefixPartial 12 289420) = some ⟨12, 2, 0, 968840, 289420, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_289420_968840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289420 ⟨968840, by decide⟩ :=
  accepted_of_selected 12 289420 ⟨968840, by decide⟩ ⟨12, 2, 0, 968840, 289420, 1321, 65536⟩
    (by decide) selected_cut_36541

theorem selected_cut_36542 : selected 9 ⟨968871, by decide⟩
    (prefixPartial 12 289421) = some ⟨12, 2, 0, 968871, 289421, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_289421_968871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289421 ⟨968871, by decide⟩ :=
  accepted_of_selected 12 289421 ⟨968871, by decide⟩ ⟨12, 2, 0, 968871, 289421, 1517, 65536⟩
    (by decide) selected_cut_36542

theorem selected_cut_36543 : selected 9 ⟨968901, by decide⟩
    (prefixPartial 12 289422) = some ⟨12, 2, 0, 968901, 289422, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_289422_968901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289422 ⟨968901, by decide⟩ :=
  accepted_of_selected 12 289422 ⟨968901, by decide⟩ ⟨12, 2, 0, 968901, 289422, 1461, 65536⟩
    (by decide) selected_cut_36543

theorem selected_cut_36544 : selected 9 ⟨968931, by decide⟩
    (prefixPartial 12 289423) = some ⟨12, 2, 0, 968931, 289423, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_289423_968931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289423 ⟨968931, by decide⟩ :=
  accepted_of_selected 12 289423 ⟨968931, by decide⟩ ⟨12, 2, 0, 968931, 289423, 1493, 65536⟩
    (by decide) selected_cut_36544

theorem unmarked_context_11_72355_968932 : frontier 10 ⟨968932, by decide⟩
    (prefixCache 11 72355) (prefixPartial 11 72355) = false := by
  decide +kernel

theorem node_context_11_72355_968932 : EJMOriginalGlobalDAGData.nodes 10 ⟨968932, by decide⟩ =
    .split (coordinate 11) (![⟨968840, by decide⟩,⟨968871, by decide⟩,⟨968901, by decide⟩,⟨968931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72355_968932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72355 ⟨968932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72355
    ⟨968932, by decide⟩ (by decide) (![⟨968840, by decide⟩,⟨968871, by decide⟩,⟨968901, by decide⟩,⟨968931, by decide⟩]) unmarked_context_11_72355_968932 node_context_11_72355_968932
  intro a
  fin_cases a
  · exact context_12_289420_968840
  · exact context_12_289421_968871
  · exact context_12_289422_968901
  · exact context_12_289423_968931

theorem unmarked_context_10_18088_968933 : frontier 11 ⟨968933, by decide⟩
    (prefixCache 10 18088) (prefixPartial 10 18088) = false := by
  decide +kernel

theorem node_context_10_18088_968933 : EJMOriginalGlobalDAGData.nodes 11 ⟨968933, by decide⟩ =
    .split (coordinate 10) (![⟨968599, by decide⟩,⟨968722, by decide⟩,⟨968806, by decide⟩,⟨968932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18088_968933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18088 ⟨968933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18088
    ⟨968933, by decide⟩ (by decide) (![⟨968599, by decide⟩,⟨968722, by decide⟩,⟨968806, by decide⟩,⟨968932, by decide⟩]) unmarked_context_10_18088_968933 node_context_10_18088_968933
  intro a
  fin_cases a
  · exact context_11_72352_968599
  · exact context_11_72353_968722
  · exact context_11_72354_968806
  · exact context_11_72355_968932

theorem selected_cut_36545 : selected 10 ⟨969004, by decide⟩
    (prefixPartial 11 72356) = some ⟨11, 2, 0, 969004, 72356, 3061, 262144⟩ := by
  decide +kernel

theorem context_11_72356_969004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72356 ⟨969004, by decide⟩ :=
  accepted_of_selected 11 72356 ⟨969004, by decide⟩ ⟨11, 2, 0, 969004, 72356, 3061, 262144⟩
    (by decide) selected_cut_36545

theorem selected_cut_36546 : selected 10 ⟨969057, by decide⟩
    (prefixPartial 11 72357) = some ⟨11, 2, 0, 969057, 72357, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_72357_969057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72357 ⟨969057, by decide⟩ :=
  accepted_of_selected 11 72357 ⟨969057, by decide⟩ ⟨11, 2, 0, 969057, 72357, 2193, 262144⟩
    (by decide) selected_cut_36546

theorem selected_cut_36547 : selected 10 ⟨969088, by decide⟩
    (prefixPartial 11 72358) = some ⟨11, 2, 0, 969088, 72358, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_72358_969088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72358 ⟨969088, by decide⟩ :=
  accepted_of_selected 11 72358 ⟨969088, by decide⟩ ⟨11, 2, 0, 969088, 72358, 1661, 262144⟩
    (by decide) selected_cut_36547

theorem selected_cut_36548 : selected 10 ⟨969148, by decide⟩
    (prefixPartial 11 72359) = some ⟨11, 2, 0, 969148, 72359, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_72359_969148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72359 ⟨969148, by decide⟩ :=
  accepted_of_selected 11 72359 ⟨969148, by decide⟩ ⟨11, 2, 0, 969148, 72359, 2725, 262144⟩
    (by decide) selected_cut_36548

theorem unmarked_context_10_18089_969149 : frontier 11 ⟨969149, by decide⟩
    (prefixCache 10 18089) (prefixPartial 10 18089) = false := by
  decide +kernel

theorem node_context_10_18089_969149 : EJMOriginalGlobalDAGData.nodes 11 ⟨969149, by decide⟩ =
    .split (coordinate 10) (![⟨969004, by decide⟩,⟨969057, by decide⟩,⟨969088, by decide⟩,⟨969148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18089_969149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18089 ⟨969149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18089
    ⟨969149, by decide⟩ (by decide) (![⟨969004, by decide⟩,⟨969057, by decide⟩,⟨969088, by decide⟩,⟨969148, by decide⟩]) unmarked_context_10_18089_969149 node_context_10_18089_969149
  intro a
  fin_cases a
  · exact context_11_72356_969004
  · exact context_11_72357_969057
  · exact context_11_72358_969088
  · exact context_11_72359_969148

theorem selected_cut_36549 : selected 11 ⟨969204, by decide⟩
    (prefixPartial 10 18090) = some ⟨10, 2, 0, 969204, 18090, 2497, 1048576⟩ := by
  decide +kernel

theorem context_10_18090_969204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18090 ⟨969204, by decide⟩ :=
  accepted_of_selected 10 18090 ⟨969204, by decide⟩ ⟨10, 2, 0, 969204, 18090, 2497, 1048576⟩
    (by decide) selected_cut_36549

theorem selected_cut_36550 : selected 11 ⟨969243, by decide⟩
    (prefixPartial 10 18091) = some ⟨10, 2, 0, 969243, 18091, 1713, 1048576⟩ := by
  decide +kernel

theorem context_10_18091_969243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18091 ⟨969243, by decide⟩ :=
  accepted_of_selected 10 18091 ⟨969243, by decide⟩ ⟨10, 2, 0, 969243, 18091, 1713, 1048576⟩
    (by decide) selected_cut_36550

theorem unmarked_context_9_4522_969244 : frontier 12 ⟨969244, by decide⟩
    (prefixCache 9 4522) (prefixPartial 9 4522) = false := by
  decide +kernel

theorem node_context_9_4522_969244 : EJMOriginalGlobalDAGData.nodes 12 ⟨969244, by decide⟩ =
    .split (coordinate 9) (![⟨968933, by decide⟩,⟨969149, by decide⟩,⟨969204, by decide⟩,⟨969243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4522_969244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4522 ⟨969244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4522
    ⟨969244, by decide⟩ (by decide) (![⟨968933, by decide⟩,⟨969149, by decide⟩,⟨969204, by decide⟩,⟨969243, by decide⟩]) unmarked_context_9_4522_969244 node_context_9_4522_969244
  intro a
  fin_cases a
  · exact context_10_18088_968933
  · exact context_10_18089_969149
  · exact context_10_18090_969204
  · exact context_10_18091_969243

theorem selected_cut_36551 : selected 10 ⟨969297, by decide⟩
    (prefixPartial 11 72368) = some ⟨11, 2, 0, 969297, 72368, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_72368_969297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72368 ⟨969297, by decide⟩ :=
  accepted_of_selected 11 72368 ⟨969297, by decide⟩ ⟨11, 2, 0, 969297, 72368, 3169, 262144⟩
    (by decide) selected_cut_36551

theorem selected_cut_36552 : selected 10 ⟨969346, by decide⟩
    (prefixPartial 11 72369) = some ⟨11, 2, 0, 969346, 72369, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_72369_969346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72369 ⟨969346, by decide⟩ :=
  accepted_of_selected 11 72369 ⟨969346, by decide⟩ ⟨11, 2, 0, 969346, 72369, 2413, 262144⟩
    (by decide) selected_cut_36552

theorem selected_cut_36553 : selected 10 ⟨969377, by decide⟩
    (prefixPartial 11 72370) = some ⟨11, 2, 0, 969377, 72370, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_72370_969377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72370 ⟨969377, by decide⟩ :=
  accepted_of_selected 11 72370 ⟨969377, by decide⟩ ⟨11, 2, 0, 969377, 72370, 1669, 262144⟩
    (by decide) selected_cut_36553

theorem selected_cut_36554 : selected 10 ⟨969435, by decide⟩
    (prefixPartial 11 72371) = some ⟨11, 2, 0, 969435, 72371, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_72371_969435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72371 ⟨969435, by decide⟩ :=
  accepted_of_selected 11 72371 ⟨969435, by decide⟩ ⟨11, 2, 0, 969435, 72371, 2073, 262144⟩
    (by decide) selected_cut_36554

theorem unmarked_context_10_18092_969436 : frontier 11 ⟨969436, by decide⟩
    (prefixCache 10 18092) (prefixPartial 10 18092) = false := by
  decide +kernel

theorem node_context_10_18092_969436 : EJMOriginalGlobalDAGData.nodes 11 ⟨969436, by decide⟩ =
    .split (coordinate 10) (![⟨969297, by decide⟩,⟨969346, by decide⟩,⟨969377, by decide⟩,⟨969435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18092_969436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18092 ⟨969436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18092
    ⟨969436, by decide⟩ (by decide) (![⟨969297, by decide⟩,⟨969346, by decide⟩,⟨969377, by decide⟩,⟨969435, by decide⟩]) unmarked_context_10_18092_969436 node_context_10_18092_969436
  intro a
  fin_cases a
  · exact context_11_72368_969297
  · exact context_11_72369_969346
  · exact context_11_72370_969377
  · exact context_11_72371_969435

theorem selected_cut_36555 : selected 11 ⟨969525, by decide⟩
    (prefixPartial 10 18093) = some ⟨10, 2, 0, 969525, 18093, 2569, 1048576⟩ := by
  decide +kernel

theorem context_10_18093_969525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18093 ⟨969525, by decide⟩ :=
  accepted_of_selected 10 18093 ⟨969525, by decide⟩ ⟨10, 2, 0, 969525, 18093, 2569, 1048576⟩
    (by decide) selected_cut_36555

theorem selected_cut_36556 : selected 11 ⟨969552, by decide⟩
    (prefixPartial 10 18094) = some ⟨10, 2, 0, 969552, 18094, 653, 1048576⟩ := by
  decide +kernel

theorem context_10_18094_969552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18094 ⟨969552, by decide⟩ :=
  accepted_of_selected 10 18094 ⟨969552, by decide⟩ ⟨10, 2, 0, 969552, 18094, 653, 1048576⟩
    (by decide) selected_cut_36556

theorem selected_cut_36557 : selected 11 ⟨969557, by decide⟩
    (prefixPartial 10 18095) = some ⟨10, 2, 0, 969557, 18095, 65, 1048576⟩ := by
  decide +kernel

theorem context_10_18095_969557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18095 ⟨969557, by decide⟩ :=
  accepted_of_selected 10 18095 ⟨969557, by decide⟩ ⟨10, 2, 0, 969557, 18095, 65, 1048576⟩
    (by decide) selected_cut_36557

theorem unmarked_context_9_4523_969558 : frontier 12 ⟨969558, by decide⟩
    (prefixCache 9 4523) (prefixPartial 9 4523) = false := by
  decide +kernel

theorem node_context_9_4523_969558 : EJMOriginalGlobalDAGData.nodes 12 ⟨969558, by decide⟩ =
    .split (coordinate 9) (![⟨969436, by decide⟩,⟨969525, by decide⟩,⟨969552, by decide⟩,⟨969557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4523_969558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4523 ⟨969558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4523
    ⟨969558, by decide⟩ (by decide) (![⟨969436, by decide⟩,⟨969525, by decide⟩,⟨969552, by decide⟩,⟨969557, by decide⟩]) unmarked_context_9_4523_969558 node_context_9_4523_969558
  intro a
  fin_cases a
  · exact context_10_18092_969436
  · exact context_10_18093_969525
  · exact context_10_18094_969552
  · exact context_10_18095_969557

theorem unmarked_context_8_1130_969559 : frontier 13 ⟨969559, by decide⟩
    (prefixCache 8 1130) (prefixPartial 8 1130) = false := by
  decide +kernel

theorem node_context_8_1130_969559 : EJMOriginalGlobalDAGData.nodes 13 ⟨969559, by decide⟩ =
    .split (coordinate 8) (![⟨967628, by decide⟩,⟨968514, by decide⟩,⟨969244, by decide⟩,⟨969558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1130_969559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1130 ⟨969559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1130
    ⟨969559, by decide⟩ (by decide) (![⟨967628, by decide⟩,⟨968514, by decide⟩,⟨969244, by decide⟩,⟨969558, by decide⟩]) unmarked_context_8_1130_969559 node_context_8_1130_969559
  intro a
  fin_cases a
  · exact context_9_4520_967628
  · exact context_9_4521_968514
  · exact context_9_4522_969244
  · exact context_9_4523_969558

theorem selected_cut_36558 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 289536) = some ⟨12, 1, 0, 34034, 289536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289536_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289536 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 289536 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 289536, 1, 65536⟩
    (by decide) selected_cut_36558

theorem selected_cut_36559 : selected 9 ⟨969606, by decide⟩
    (prefixPartial 12 289537) = some ⟨12, 2, 0, 969606, 289537, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_289537_969606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289537 ⟨969606, by decide⟩ :=
  accepted_of_selected 12 289537 ⟨969606, by decide⟩ ⟨12, 2, 0, 969606, 289537, 3525, 65536⟩
    (by decide) selected_cut_36559

theorem selected_cut_36560 : selected 9 ⟨969653, by decide⟩
    (prefixPartial 12 289538) = some ⟨12, 2, 0, 969653, 289538, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_289538_969653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289538 ⟨969653, by decide⟩ :=
  accepted_of_selected 12 289538 ⟨969653, by decide⟩ ⟨12, 2, 0, 969653, 289538, 3549, 65536⟩
    (by decide) selected_cut_36560

theorem selected_cut_36561 : selected 9 ⟨969706, by decide⟩
    (prefixPartial 12 289539) = some ⟨12, 2, 0, 969706, 289539, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_289539_969706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289539 ⟨969706, by decide⟩ :=
  accepted_of_selected 12 289539 ⟨969706, by decide⟩ ⟨12, 2, 0, 969706, 289539, 3753, 65536⟩
    (by decide) selected_cut_36561

theorem unmarked_context_11_72384_969707 : frontier 10 ⟨969707, by decide⟩
    (prefixCache 11 72384) (prefixPartial 11 72384) = false := by
  decide +kernel

theorem node_context_11_72384_969707 : EJMOriginalGlobalDAGData.nodes 10 ⟨969707, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨969606, by decide⟩,⟨969653, by decide⟩,⟨969706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72384_969707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72384 ⟨969707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72384
    ⟨969707, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨969606, by decide⟩,⟨969653, by decide⟩,⟨969706, by decide⟩]) unmarked_context_11_72384_969707 node_context_11_72384_969707
  intro a
  fin_cases a
  · exact context_12_289536_34034
  · exact context_12_289537_969606
  · exact context_12_289538_969653
  · exact context_12_289539_969706

theorem selected_cut_36562 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 289540) = some ⟨12, 1, 0, 34034, 289540, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289540_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289540 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 289540 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 289540, 1, 65536⟩
    (by decide) selected_cut_36562

theorem selected_cut_36563 : selected 9 ⟨969767, by decide⟩
    (prefixPartial 12 289541) = some ⟨12, 2, 0, 969767, 289541, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_289541_969767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289541 ⟨969767, by decide⟩ :=
  accepted_of_selected 12 289541 ⟨969767, by decide⟩ ⟨12, 2, 0, 969767, 289541, 3909, 65536⟩
    (by decide) selected_cut_36563

theorem selected_cut_36564 : selected 9 ⟨969819, by decide⟩
    (prefixPartial 12 289542) = some ⟨12, 2, 0, 969819, 289542, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_289542_969819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289542 ⟨969819, by decide⟩ :=
  accepted_of_selected 12 289542 ⟨969819, by decide⟩ ⟨12, 2, 0, 969819, 289542, 3593, 65536⟩
    (by decide) selected_cut_36564

theorem selected_cut_36565 : selected 9 ⟨969879, by decide⟩
    (prefixPartial 12 289543) = some ⟨12, 2, 0, 969879, 289543, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_289543_969879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289543 ⟨969879, by decide⟩ :=
  accepted_of_selected 12 289543 ⟨969879, by decide⟩ ⟨12, 2, 0, 969879, 289543, 3829, 65536⟩
    (by decide) selected_cut_36565

theorem unmarked_context_11_72385_969880 : frontier 10 ⟨969880, by decide⟩
    (prefixCache 11 72385) (prefixPartial 11 72385) = false := by
  decide +kernel

theorem node_context_11_72385_969880 : EJMOriginalGlobalDAGData.nodes 10 ⟨969880, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨969767, by decide⟩,⟨969819, by decide⟩,⟨969879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72385_969880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72385 ⟨969880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72385
    ⟨969880, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨969767, by decide⟩,⟨969819, by decide⟩,⟨969879, by decide⟩]) unmarked_context_11_72385_969880 node_context_11_72385_969880
  intro a
  fin_cases a
  · exact context_12_289540_34034
  · exact context_12_289541_969767
  · exact context_12_289542_969819
  · exact context_12_289543_969879

theorem selected_cut_36566 : selected 8 ⟨969913, by decide⟩
    (prefixPartial 13 1158176) = some ⟨13, 2, 0, 969913, 1158176, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_1158176_969913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1158176 ⟨969913, by decide⟩ :=
  accepted_of_selected 13 1158176 ⟨969913, by decide⟩ ⟨13, 2, 0, 969913, 1158176, 1341, 16384⟩
    (by decide) selected_cut_36566

theorem selected_cut_36567 : selected 8 ⟨969948, by decide⟩
    (prefixPartial 13 1158177) = some ⟨13, 2, 0, 969948, 1158177, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_1158177_969948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1158177 ⟨969948, by decide⟩ :=
  accepted_of_selected 13 1158177 ⟨969948, by decide⟩ ⟨13, 2, 0, 969948, 1158177, 1117, 16384⟩
    (by decide) selected_cut_36567

theorem selected_cut_36568 : selected 8 ⟨969976, by decide⟩
    (prefixPartial 13 1158178) = some ⟨13, 2, 0, 969976, 1158178, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_1158178_969976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1158178 ⟨969976, by decide⟩ :=
  accepted_of_selected 13 1158178 ⟨969976, by decide⟩ ⟨13, 2, 0, 969976, 1158178, 1261, 16384⟩
    (by decide) selected_cut_36568

theorem selected_cut_36569 : selected 8 ⟨969994, by decide⟩
    (prefixPartial 13 1158179) = some ⟨13, 2, 0, 969994, 1158179, 765, 16384⟩ := by
  decide +kernel

theorem context_13_1158179_969994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1158179 ⟨969994, by decide⟩ :=
  accepted_of_selected 13 1158179 ⟨969994, by decide⟩ ⟨13, 2, 0, 969994, 1158179, 765, 16384⟩
    (by decide) selected_cut_36569

theorem unmarked_context_12_289544_969995 : frontier 9 ⟨969995, by decide⟩
    (prefixCache 12 289544) (prefixPartial 12 289544) = false := by
  decide +kernel

theorem node_context_12_289544_969995 : EJMOriginalGlobalDAGData.nodes 9 ⟨969995, by decide⟩ =
    .split (coordinate 12) (![⟨969913, by decide⟩,⟨969948, by decide⟩,⟨969976, by decide⟩,⟨969994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_289544_969995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289544 ⟨969995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 289544
    ⟨969995, by decide⟩ (by decide) (![⟨969913, by decide⟩,⟨969948, by decide⟩,⟨969976, by decide⟩,⟨969994, by decide⟩]) unmarked_context_12_289544_969995 node_context_12_289544_969995
  intro a
  fin_cases a
  · exact context_13_1158176_969913
  · exact context_13_1158177_969948
  · exact context_13_1158178_969976
  · exact context_13_1158179_969994

theorem selected_cut_36570 : selected 9 ⟨970068, by decide⟩
    (prefixPartial 12 289545) = some ⟨12, 2, 0, 970068, 289545, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_289545_970068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289545 ⟨970068, by decide⟩ :=
  accepted_of_selected 12 289545 ⟨970068, by decide⟩ ⟨12, 2, 0, 970068, 289545, 3993, 65536⟩
    (by decide) selected_cut_36570

theorem selected_cut_36571 : selected 9 ⟨970134, by decide⟩
    (prefixPartial 12 289546) = some ⟨12, 2, 0, 970134, 289546, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_289546_970134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289546 ⟨970134, by decide⟩ :=
  accepted_of_selected 12 289546 ⟨970134, by decide⟩ ⟨12, 2, 0, 970134, 289546, 3649, 65536⟩
    (by decide) selected_cut_36571

theorem selected_cut_36572 : selected 9 ⟨970202, by decide⟩
    (prefixPartial 12 289547) = some ⟨12, 2, 0, 970202, 289547, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_289547_970202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289547 ⟨970202, by decide⟩ :=
  accepted_of_selected 12 289547 ⟨970202, by decide⟩ ⟨12, 2, 0, 970202, 289547, 4009, 65536⟩
    (by decide) selected_cut_36572

theorem unmarked_context_11_72386_970203 : frontier 10 ⟨970203, by decide⟩
    (prefixCache 11 72386) (prefixPartial 11 72386) = false := by
  decide +kernel

theorem node_context_11_72386_970203 : EJMOriginalGlobalDAGData.nodes 10 ⟨970203, by decide⟩ =
    .split (coordinate 11) (![⟨969995, by decide⟩,⟨970068, by decide⟩,⟨970134, by decide⟩,⟨970202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72386_970203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72386 ⟨970203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72386
    ⟨970203, by decide⟩ (by decide) (![⟨969995, by decide⟩,⟨970068, by decide⟩,⟨970134, by decide⟩,⟨970202, by decide⟩]) unmarked_context_11_72386_970203 node_context_11_72386_970203
  intro a
  fin_cases a
  · exact context_12_289544_969995
  · exact context_12_289545_970068
  · exact context_12_289546_970134
  · exact context_12_289547_970202

theorem selected_cut_36573 : selected 9 ⟨970269, by decide⟩
    (prefixPartial 12 289548) = some ⟨12, 2, 0, 970269, 289548, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_289548_970269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289548 ⟨970269, by decide⟩ :=
  accepted_of_selected 12 289548 ⟨970269, by decide⟩ ⟨12, 2, 0, 970269, 289548, 2169, 65536⟩
    (by decide) selected_cut_36573

theorem selected_cut_36574 : selected 9 ⟨970318, by decide⟩
    (prefixPartial 12 289549) = some ⟨12, 2, 0, 970318, 289549, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_289549_970318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289549 ⟨970318, by decide⟩ :=
  accepted_of_selected 12 289549 ⟨970318, by decide⟩ ⟨12, 2, 0, 970318, 289549, 3493, 65536⟩
    (by decide) selected_cut_36574

theorem selected_cut_36575 : selected 9 ⟨970376, by decide⟩
    (prefixPartial 12 289550) = some ⟨12, 2, 0, 970376, 289550, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_289550_970376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289550 ⟨970376, by decide⟩ :=
  accepted_of_selected 12 289550 ⟨970376, by decide⟩ ⟨12, 2, 0, 970376, 289550, 3641, 65536⟩
    (by decide) selected_cut_36575

theorem selected_cut_36576 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 289551) = some ⟨12, 1, 0, 903806, 289551, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289551_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289551 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 289551 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 289551, 1, 65536⟩
    (by decide) selected_cut_36576

theorem unmarked_context_11_72387_970377 : frontier 10 ⟨970377, by decide⟩
    (prefixCache 11 72387) (prefixPartial 11 72387) = false := by
  decide +kernel

theorem node_context_11_72387_970377 : EJMOriginalGlobalDAGData.nodes 10 ⟨970377, by decide⟩ =
    .split (coordinate 11) (![⟨970269, by decide⟩,⟨970318, by decide⟩,⟨970376, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72387_970377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72387 ⟨970377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72387
    ⟨970377, by decide⟩ (by decide) (![⟨970269, by decide⟩,⟨970318, by decide⟩,⟨970376, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72387_970377 node_context_11_72387_970377
  intro a
  fin_cases a
  · exact context_12_289548_970269
  · exact context_12_289549_970318
  · exact context_12_289550_970376
  · exact context_12_289551_903806

theorem unmarked_context_10_18096_970378 : frontier 11 ⟨970378, by decide⟩
    (prefixCache 10 18096) (prefixPartial 10 18096) = false := by
  decide +kernel

theorem node_context_10_18096_970378 : EJMOriginalGlobalDAGData.nodes 11 ⟨970378, by decide⟩ =
    .split (coordinate 10) (![⟨969707, by decide⟩,⟨969880, by decide⟩,⟨970203, by decide⟩,⟨970377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18096_970378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18096 ⟨970378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18096
    ⟨970378, by decide⟩ (by decide) (![⟨969707, by decide⟩,⟨969880, by decide⟩,⟨970203, by decide⟩,⟨970377, by decide⟩]) unmarked_context_10_18096_970378 node_context_10_18096_970378
  intro a
  fin_cases a
  · exact context_11_72384_969707
  · exact context_11_72385_969880
  · exact context_11_72386_970203
  · exact context_11_72387_970377

theorem selected_cut_36577 : selected 9 ⟨970432, by decide⟩
    (prefixPartial 12 289552) = some ⟨12, 2, 0, 970432, 289552, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_289552_970432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289552 ⟨970432, by decide⟩ :=
  accepted_of_selected 12 289552 ⟨970432, by decide⟩ ⟨12, 2, 0, 970432, 289552, 3409, 65536⟩
    (by decide) selected_cut_36577

theorem selected_cut_36578 : selected 9 ⟨970492, by decide⟩
    (prefixPartial 12 289553) = some ⟨12, 2, 0, 970492, 289553, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_289553_970492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289553 ⟨970492, by decide⟩ :=
  accepted_of_selected 12 289553 ⟨970492, by decide⟩ ⟨12, 2, 0, 970492, 289553, 3569, 65536⟩
    (by decide) selected_cut_36578

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
