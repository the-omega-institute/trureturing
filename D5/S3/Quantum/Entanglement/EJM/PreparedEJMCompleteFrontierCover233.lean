/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover232
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22372 : selected 8 ⟨569264, by decide⟩
    (prefixPartial 13 302398) = some ⟨13, 2, 0, 569264, 302398, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_302398_569264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302398 ⟨569264, by decide⟩ :=
  accepted_of_selected 13 302398 ⟨569264, by decide⟩ ⟨13, 2, 0, 569264, 302398, 2677, 16384⟩
    (by decide) selected_cut_22372

theorem selected_cut_22373 : selected 8 ⟨569274, by decide⟩
    (prefixPartial 13 302399) = some ⟨13, 2, 0, 569274, 302399, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_302399_569274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302399 ⟨569274, by decide⟩ :=
  accepted_of_selected 13 302399 ⟨569274, by decide⟩ ⟨13, 2, 0, 569274, 302399, 1073, 16384⟩
    (by decide) selected_cut_22373

theorem unmarked_context_12_75599_569275 : frontier 9 ⟨569275, by decide⟩
    (prefixCache 12 75599) (prefixPartial 12 75599) = false := by
  decide +kernel

theorem node_context_12_75599_569275 : EJMOriginalGlobalDAGData.nodes 9 ⟨569275, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569214, by decide⟩,⟨569264, by decide⟩,⟨569274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75599_569275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75599 ⟨569275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75599
    ⟨569275, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569214, by decide⟩,⟨569264, by decide⟩,⟨569274, by decide⟩]) unmarked_context_12_75599_569275 node_context_12_75599_569275
  intro a
  fin_cases a
  · exact context_13_302396_3444
  · exact context_13_302397_569214
  · exact context_13_302398_569264
  · exact context_13_302399_569274

theorem unmarked_context_11_18899_569276 : frontier 10 ⟨569276, by decide⟩
    (prefixCache 11 18899) (prefixPartial 11 18899) = false := by
  decide +kernel

theorem node_context_11_18899_569276 : EJMOriginalGlobalDAGData.nodes 10 ⟨569276, by decide⟩ =
    .split (coordinate 11) (![⟨569014, by decide⟩,⟨569080, by decide⟩,⟨569148, by decide⟩,⟨569275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18899_569276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18899 ⟨569276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18899
    ⟨569276, by decide⟩ (by decide) (![⟨569014, by decide⟩,⟨569080, by decide⟩,⟨569148, by decide⟩,⟨569275, by decide⟩]) unmarked_context_11_18899_569276 node_context_11_18899_569276
  intro a
  fin_cases a
  · exact context_12_75596_569014
  · exact context_12_75597_569080
  · exact context_12_75598_569148
  · exact context_12_75599_569275

theorem unmarked_context_10_4724_569277 : frontier 11 ⟨569277, by decide⟩
    (prefixCache 10 4724) (prefixPartial 10 4724) = false := by
  decide +kernel

theorem node_context_10_4724_569277 : EJMOriginalGlobalDAGData.nodes 11 ⟨569277, by decide⟩ =
    .split (coordinate 10) (![⟨568440, by decide⟩,⟨568684, by decide⟩,⟨568969, by decide⟩,⟨569276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4724_569277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4724 ⟨569277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4724
    ⟨569277, by decide⟩ (by decide) (![⟨568440, by decide⟩,⟨568684, by decide⟩,⟨568969, by decide⟩,⟨569276, by decide⟩]) unmarked_context_10_4724_569277 node_context_10_4724_569277
  intro a
  fin_cases a
  · exact context_11_18896_568440
  · exact context_11_18897_568684
  · exact context_11_18898_568969
  · exact context_11_18899_569276

theorem selected_cut_22374 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302400) = some ⟨13, 1, 0, 3444, 302400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302400, 1, 16384⟩
    (by decide) selected_cut_22374

theorem selected_cut_22375 : selected 8 ⟨569305, by decide⟩
    (prefixPartial 13 302401) = some ⟨13, 2, 0, 569305, 302401, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_302401_569305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302401 ⟨569305, by decide⟩ :=
  accepted_of_selected 13 302401 ⟨569305, by decide⟩ ⟨13, 2, 0, 569305, 302401, 1877, 16384⟩
    (by decide) selected_cut_22375

theorem selected_cut_22376 : selected 8 ⟨569332, by decide⟩
    (prefixPartial 13 302402) = some ⟨13, 2, 0, 569332, 302402, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_302402_569332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302402 ⟨569332, by decide⟩ :=
  accepted_of_selected 13 302402 ⟨569332, by decide⟩ ⟨13, 2, 0, 569332, 302402, 1733, 16384⟩
    (by decide) selected_cut_22376

theorem selected_cut_22377 : selected 8 ⟨569339, by decide⟩
    (prefixPartial 13 302403) = some ⟨13, 2, 0, 569339, 302403, 721, 16384⟩ := by
  decide +kernel

theorem context_13_302403_569339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302403 ⟨569339, by decide⟩ :=
  accepted_of_selected 13 302403 ⟨569339, by decide⟩ ⟨13, 2, 0, 569339, 302403, 721, 16384⟩
    (by decide) selected_cut_22377

theorem unmarked_context_12_75600_569340 : frontier 9 ⟨569340, by decide⟩
    (prefixCache 12 75600) (prefixPartial 12 75600) = false := by
  decide +kernel

theorem node_context_12_75600_569340 : EJMOriginalGlobalDAGData.nodes 9 ⟨569340, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569305, by decide⟩,⟨569332, by decide⟩,⟨569339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75600_569340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75600 ⟨569340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75600
    ⟨569340, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569305, by decide⟩,⟨569332, by decide⟩,⟨569339, by decide⟩]) unmarked_context_12_75600_569340 node_context_12_75600_569340
  intro a
  fin_cases a
  · exact context_13_302400_3444
  · exact context_13_302401_569305
  · exact context_13_302402_569332
  · exact context_13_302403_569339

theorem selected_cut_22378 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302404) = some ⟨13, 1, 0, 3444, 302404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302404, 1, 16384⟩
    (by decide) selected_cut_22378

theorem selected_cut_22379 : selected 8 ⟨569380, by decide⟩
    (prefixPartial 13 302405) = some ⟨13, 2, 0, 569380, 302405, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_302405_569380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302405 ⟨569380, by decide⟩ :=
  accepted_of_selected 13 302405 ⟨569380, by decide⟩ ⟨13, 2, 0, 569380, 302405, 2405, 16384⟩
    (by decide) selected_cut_22379

theorem selected_cut_22380 : selected 8 ⟨569403, by decide⟩
    (prefixPartial 13 302406) = some ⟨13, 2, 0, 569403, 302406, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_302406_569403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302406 ⟨569403, by decide⟩ :=
  accepted_of_selected 13 302406 ⟨569403, by decide⟩ ⟨13, 2, 0, 569403, 302406, 1669, 16384⟩
    (by decide) selected_cut_22380

theorem selected_cut_22381 : selected 8 ⟨569408, by decide⟩
    (prefixPartial 13 302407) = some ⟨13, 2, 0, 569408, 302407, 617, 16384⟩ := by
  decide +kernel

theorem context_13_302407_569408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302407 ⟨569408, by decide⟩ :=
  accepted_of_selected 13 302407 ⟨569408, by decide⟩ ⟨13, 2, 0, 569408, 302407, 617, 16384⟩
    (by decide) selected_cut_22381

theorem unmarked_context_12_75601_569409 : frontier 9 ⟨569409, by decide⟩
    (prefixCache 12 75601) (prefixPartial 12 75601) = false := by
  decide +kernel

theorem node_context_12_75601_569409 : EJMOriginalGlobalDAGData.nodes 9 ⟨569409, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569380, by decide⟩,⟨569403, by decide⟩,⟨569408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75601_569409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75601 ⟨569409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75601
    ⟨569409, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569380, by decide⟩,⟨569403, by decide⟩,⟨569408, by decide⟩]) unmarked_context_12_75601_569409 node_context_12_75601_569409
  intro a
  fin_cases a
  · exact context_13_302404_3444
  · exact context_13_302405_569380
  · exact context_13_302406_569403
  · exact context_13_302407_569408

theorem selected_cut_22382 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302408) = some ⟨13, 1, 0, 3444, 302408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302408, 1, 16384⟩
    (by decide) selected_cut_22382

theorem selected_cut_22383 : selected 8 ⟨569456, by decide⟩
    (prefixPartial 13 302409) = some ⟨13, 2, 0, 569456, 302409, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_302409_569456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302409 ⟨569456, by decide⟩ :=
  accepted_of_selected 13 302409 ⟨569456, by decide⟩ ⟨13, 2, 0, 569456, 302409, 2713, 16384⟩
    (by decide) selected_cut_22383

theorem selected_cut_22384 : selected 8 ⟨569485, by decide⟩
    (prefixPartial 13 302410) = some ⟨13, 2, 0, 569485, 302410, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_302410_569485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302410 ⟨569485, by decide⟩ :=
  accepted_of_selected 13 302410 ⟨569485, by decide⟩ ⟨13, 2, 0, 569485, 302410, 2113, 16384⟩
    (by decide) selected_cut_22384

theorem selected_cut_22385 : selected 8 ⟨569497, by decide⟩
    (prefixPartial 13 302411) = some ⟨13, 2, 0, 569497, 302411, 825, 16384⟩ := by
  decide +kernel

theorem context_13_302411_569497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302411 ⟨569497, by decide⟩ :=
  accepted_of_selected 13 302411 ⟨569497, by decide⟩ ⟨13, 2, 0, 569497, 302411, 825, 16384⟩
    (by decide) selected_cut_22385

theorem unmarked_context_12_75602_569498 : frontier 9 ⟨569498, by decide⟩
    (prefixCache 12 75602) (prefixPartial 12 75602) = false := by
  decide +kernel

theorem node_context_12_75602_569498 : EJMOriginalGlobalDAGData.nodes 9 ⟨569498, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569456, by decide⟩,⟨569485, by decide⟩,⟨569497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75602_569498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75602 ⟨569498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75602
    ⟨569498, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569456, by decide⟩,⟨569485, by decide⟩,⟨569497, by decide⟩]) unmarked_context_12_75602_569498 node_context_12_75602_569498
  intro a
  fin_cases a
  · exact context_13_302408_3444
  · exact context_13_302409_569456
  · exact context_13_302410_569485
  · exact context_13_302411_569497

theorem selected_cut_22386 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302412) = some ⟨13, 1, 0, 3444, 302412, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302412_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302412 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302412 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302412, 1, 16384⟩
    (by decide) selected_cut_22386

theorem selected_cut_22387 : selected 8 ⟨569523, by decide⟩
    (prefixPartial 13 302413) = some ⟨13, 2, 0, 569523, 302413, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_302413_569523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302413 ⟨569523, by decide⟩ :=
  accepted_of_selected 13 302413 ⟨569523, by decide⟩ ⟨13, 2, 0, 569523, 302413, 2189, 16384⟩
    (by decide) selected_cut_22387

theorem selected_cut_22388 : selected 8 ⟨569546, by decide⟩
    (prefixPartial 13 302414) = some ⟨13, 2, 0, 569546, 302414, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_302414_569546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302414 ⟨569546, by decide⟩ :=
  accepted_of_selected 13 302414 ⟨569546, by decide⟩ ⟨13, 2, 0, 569546, 302414, 1937, 16384⟩
    (by decide) selected_cut_22388

theorem selected_cut_22389 : selected 8 ⟨569551, by decide⟩
    (prefixPartial 13 302415) = some ⟨13, 2, 0, 569551, 302415, 609, 16384⟩ := by
  decide +kernel

theorem context_13_302415_569551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302415 ⟨569551, by decide⟩ :=
  accepted_of_selected 13 302415 ⟨569551, by decide⟩ ⟨13, 2, 0, 569551, 302415, 609, 16384⟩
    (by decide) selected_cut_22389

theorem unmarked_context_12_75603_569552 : frontier 9 ⟨569552, by decide⟩
    (prefixCache 12 75603) (prefixPartial 12 75603) = false := by
  decide +kernel

theorem node_context_12_75603_569552 : EJMOriginalGlobalDAGData.nodes 9 ⟨569552, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569523, by decide⟩,⟨569546, by decide⟩,⟨569551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75603_569552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75603 ⟨569552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75603
    ⟨569552, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569523, by decide⟩,⟨569546, by decide⟩,⟨569551, by decide⟩]) unmarked_context_12_75603_569552 node_context_12_75603_569552
  intro a
  fin_cases a
  · exact context_13_302412_3444
  · exact context_13_302413_569523
  · exact context_13_302414_569546
  · exact context_13_302415_569551

theorem unmarked_context_11_18900_569553 : frontier 10 ⟨569553, by decide⟩
    (prefixCache 11 18900) (prefixPartial 11 18900) = false := by
  decide +kernel

theorem node_context_11_18900_569553 : EJMOriginalGlobalDAGData.nodes 10 ⟨569553, by decide⟩ =
    .split (coordinate 11) (![⟨569340, by decide⟩,⟨569409, by decide⟩,⟨569498, by decide⟩,⟨569552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18900_569553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18900 ⟨569553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18900
    ⟨569553, by decide⟩ (by decide) (![⟨569340, by decide⟩,⟨569409, by decide⟩,⟨569498, by decide⟩,⟨569552, by decide⟩]) unmarked_context_11_18900_569553 node_context_11_18900_569553
  intro a
  fin_cases a
  · exact context_12_75600_569340
  · exact context_12_75601_569409
  · exact context_12_75602_569498
  · exact context_12_75603_569552

theorem selected_cut_22390 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 18901) = some ⟨11, 1, 0, 451541, 18901, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18901_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18901 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 18901 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 18901, 1, 262144⟩
    (by decide) selected_cut_22390

theorem selected_cut_22391 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302432) = some ⟨13, 1, 0, 3444, 302432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302432, 1, 16384⟩
    (by decide) selected_cut_22391

theorem selected_cut_22392 : selected 8 ⟨569574, by decide⟩
    (prefixPartial 13 302433) = some ⟨13, 2, 0, 569574, 302433, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_302433_569574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302433 ⟨569574, by decide⟩ :=
  accepted_of_selected 13 302433 ⟨569574, by decide⟩ ⟨13, 2, 0, 569574, 302433, 1533, 16384⟩
    (by decide) selected_cut_22392

theorem selected_cut_22393 : selected 8 ⟨569596, by decide⟩
    (prefixPartial 13 302434) = some ⟨13, 2, 0, 569596, 302434, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_302434_569596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302434 ⟨569596, by decide⟩ :=
  accepted_of_selected 13 302434 ⟨569596, by decide⟩ ⟨13, 2, 0, 569596, 302434, 1833, 16384⟩
    (by decide) selected_cut_22393

theorem selected_cut_22394 : selected 8 ⟨569606, by decide⟩
    (prefixPartial 13 302435) = some ⟨13, 2, 0, 569606, 302435, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_302435_569606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302435 ⟨569606, by decide⟩ :=
  accepted_of_selected 13 302435 ⟨569606, by decide⟩ ⟨13, 2, 0, 569606, 302435, 1033, 16384⟩
    (by decide) selected_cut_22394

theorem unmarked_context_12_75608_569607 : frontier 9 ⟨569607, by decide⟩
    (prefixCache 12 75608) (prefixPartial 12 75608) = false := by
  decide +kernel

theorem node_context_12_75608_569607 : EJMOriginalGlobalDAGData.nodes 9 ⟨569607, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569574, by decide⟩,⟨569596, by decide⟩,⟨569606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75608_569607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75608 ⟨569607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75608
    ⟨569607, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569574, by decide⟩,⟨569596, by decide⟩,⟨569606, by decide⟩]) unmarked_context_12_75608_569607 node_context_12_75608_569607
  intro a
  fin_cases a
  · exact context_13_302432_3444
  · exact context_13_302433_569574
  · exact context_13_302434_569596
  · exact context_13_302435_569606

theorem selected_cut_22395 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302436) = some ⟨13, 1, 0, 3444, 302436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302436, 1, 16384⟩
    (by decide) selected_cut_22395

theorem selected_cut_22396 : selected 8 ⟨569631, by decide⟩
    (prefixPartial 13 302437) = some ⟨13, 2, 0, 569631, 302437, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_302437_569631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302437 ⟨569631, by decide⟩ :=
  accepted_of_selected 13 302437 ⟨569631, by decide⟩ ⟨13, 2, 0, 569631, 302437, 1633, 16384⟩
    (by decide) selected_cut_22396

theorem selected_cut_22397 : selected 8 ⟨569662, by decide⟩
    (prefixPartial 13 302438) = some ⟨13, 2, 0, 569662, 302438, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_302438_569662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302438 ⟨569662, by decide⟩ :=
  accepted_of_selected 13 302438 ⟨569662, by decide⟩ ⟨13, 2, 0, 569662, 302438, 1817, 16384⟩
    (by decide) selected_cut_22397

theorem selected_cut_22398 : selected 8 ⟨569669, by decide⟩
    (prefixPartial 13 302439) = some ⟨13, 2, 0, 569669, 302439, 901, 16384⟩ := by
  decide +kernel

theorem context_13_302439_569669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302439 ⟨569669, by decide⟩ :=
  accepted_of_selected 13 302439 ⟨569669, by decide⟩ ⟨13, 2, 0, 569669, 302439, 901, 16384⟩
    (by decide) selected_cut_22398

theorem unmarked_context_12_75609_569670 : frontier 9 ⟨569670, by decide⟩
    (prefixCache 12 75609) (prefixPartial 12 75609) = false := by
  decide +kernel

theorem node_context_12_75609_569670 : EJMOriginalGlobalDAGData.nodes 9 ⟨569670, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569631, by decide⟩,⟨569662, by decide⟩,⟨569669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75609_569670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75609 ⟨569670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75609
    ⟨569670, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569631, by decide⟩,⟨569662, by decide⟩,⟨569669, by decide⟩]) unmarked_context_12_75609_569670 node_context_12_75609_569670
  intro a
  fin_cases a
  · exact context_13_302436_3444
  · exact context_13_302437_569631
  · exact context_13_302438_569662
  · exact context_13_302439_569669

theorem selected_cut_22399 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302440) = some ⟨13, 1, 0, 3444, 302440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302440, 1, 16384⟩
    (by decide) selected_cut_22399

theorem selected_cut_22400 : selected 8 ⟨569701, by decide⟩
    (prefixPartial 13 302441) = some ⟨13, 2, 0, 569701, 302441, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_302441_569701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302441 ⟨569701, by decide⟩ :=
  accepted_of_selected 13 302441 ⟨569701, by decide⟩ ⟨13, 2, 0, 569701, 302441, 1909, 16384⟩
    (by decide) selected_cut_22400

theorem selected_cut_22401 : selected 8 ⟨569727, by decide⟩
    (prefixPartial 13 302442) = some ⟨13, 2, 0, 569727, 302442, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_302442_569727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302442 ⟨569727, by decide⟩ :=
  accepted_of_selected 13 302442 ⟨569727, by decide⟩ ⟨13, 2, 0, 569727, 302442, 2137, 16384⟩
    (by decide) selected_cut_22401

theorem selected_cut_22402 : selected 8 ⟨569744, by decide⟩
    (prefixPartial 13 302443) = some ⟨13, 2, 0, 569744, 302443, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_302443_569744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302443 ⟨569744, by decide⟩ :=
  accepted_of_selected 13 302443 ⟨569744, by decide⟩ ⟨13, 2, 0, 569744, 302443, 1145, 16384⟩
    (by decide) selected_cut_22402

theorem unmarked_context_12_75610_569745 : frontier 9 ⟨569745, by decide⟩
    (prefixCache 12 75610) (prefixPartial 12 75610) = false := by
  decide +kernel

theorem node_context_12_75610_569745 : EJMOriginalGlobalDAGData.nodes 9 ⟨569745, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569701, by decide⟩,⟨569727, by decide⟩,⟨569744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75610_569745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75610 ⟨569745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75610
    ⟨569745, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569701, by decide⟩,⟨569727, by decide⟩,⟨569744, by decide⟩]) unmarked_context_12_75610_569745 node_context_12_75610_569745
  intro a
  fin_cases a
  · exact context_13_302440_3444
  · exact context_13_302441_569701
  · exact context_13_302442_569727
  · exact context_13_302443_569744

theorem selected_cut_22403 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302444) = some ⟨13, 1, 0, 3444, 302444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302444, 1, 16384⟩
    (by decide) selected_cut_22403

theorem selected_cut_22404 : selected 8 ⟨569763, by decide⟩
    (prefixPartial 13 302445) = some ⟨13, 2, 0, 569763, 302445, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_302445_569763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302445 ⟨569763, by decide⟩ :=
  accepted_of_selected 13 302445 ⟨569763, by decide⟩ ⟨13, 2, 0, 569763, 302445, 1725, 16384⟩
    (by decide) selected_cut_22404

theorem selected_cut_22405 : selected 8 ⟨569794, by decide⟩
    (prefixPartial 13 302446) = some ⟨13, 2, 0, 569794, 302446, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_302446_569794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302446 ⟨569794, by decide⟩ :=
  accepted_of_selected 13 302446 ⟨569794, by decide⟩ ⟨13, 2, 0, 569794, 302446, 2053, 16384⟩
    (by decide) selected_cut_22405

theorem selected_cut_22406 : selected 8 ⟨569805, by decide⟩
    (prefixPartial 13 302447) = some ⟨13, 2, 0, 569805, 302447, 913, 16384⟩ := by
  decide +kernel

theorem context_13_302447_569805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302447 ⟨569805, by decide⟩ :=
  accepted_of_selected 13 302447 ⟨569805, by decide⟩ ⟨13, 2, 0, 569805, 302447, 913, 16384⟩
    (by decide) selected_cut_22406

theorem unmarked_context_12_75611_569806 : frontier 9 ⟨569806, by decide⟩
    (prefixCache 12 75611) (prefixPartial 12 75611) = false := by
  decide +kernel

theorem node_context_12_75611_569806 : EJMOriginalGlobalDAGData.nodes 9 ⟨569806, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569763, by decide⟩,⟨569794, by decide⟩,⟨569805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75611_569806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75611 ⟨569806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75611
    ⟨569806, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569763, by decide⟩,⟨569794, by decide⟩,⟨569805, by decide⟩]) unmarked_context_12_75611_569806 node_context_12_75611_569806
  intro a
  fin_cases a
  · exact context_13_302444_3444
  · exact context_13_302445_569763
  · exact context_13_302446_569794
  · exact context_13_302447_569805

theorem unmarked_context_11_18902_569807 : frontier 10 ⟨569807, by decide⟩
    (prefixCache 11 18902) (prefixPartial 11 18902) = false := by
  decide +kernel

theorem node_context_11_18902_569807 : EJMOriginalGlobalDAGData.nodes 10 ⟨569807, by decide⟩ =
    .split (coordinate 11) (![⟨569607, by decide⟩,⟨569670, by decide⟩,⟨569745, by decide⟩,⟨569806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18902_569807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18902 ⟨569807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18902
    ⟨569807, by decide⟩ (by decide) (![⟨569607, by decide⟩,⟨569670, by decide⟩,⟨569745, by decide⟩,⟨569806, by decide⟩]) unmarked_context_11_18902_569807 node_context_11_18902_569807
  intro a
  fin_cases a
  · exact context_12_75608_569607
  · exact context_12_75609_569670
  · exact context_12_75610_569745
  · exact context_12_75611_569806

theorem selected_cut_22407 : selected 9 ⟨569853, by decide⟩
    (prefixPartial 12 75612) = some ⟨12, 2, 0, 569853, 75612, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_75612_569853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75612 ⟨569853, by decide⟩ :=
  accepted_of_selected 12 75612 ⟨569853, by decide⟩ ⟨12, 2, 0, 569853, 75612, 4001, 65536⟩
    (by decide) selected_cut_22407

theorem selected_cut_22408 : selected 9 ⟨569903, by decide⟩
    (prefixPartial 12 75613) = some ⟨12, 2, 0, 569903, 75613, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_75613_569903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75613 ⟨569903, by decide⟩ :=
  accepted_of_selected 12 75613 ⟨569903, by decide⟩ ⟨12, 2, 0, 569903, 75613, 3989, 65536⟩
    (by decide) selected_cut_22408

theorem selected_cut_22409 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302456) = some ⟨13, 1, 0, 3444, 302456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302456, 1, 16384⟩
    (by decide) selected_cut_22409

theorem selected_cut_22410 : selected 8 ⟨569932, by decide⟩
    (prefixPartial 13 302457) = some ⟨13, 2, 0, 569932, 302457, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_302457_569932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302457 ⟨569932, by decide⟩ :=
  accepted_of_selected 13 302457 ⟨569932, by decide⟩ ⟨13, 2, 0, 569932, 302457, 1757, 16384⟩
    (by decide) selected_cut_22410

theorem selected_cut_22411 : selected 8 ⟨569955, by decide⟩
    (prefixPartial 13 302458) = some ⟨13, 2, 0, 569955, 302458, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_302458_569955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302458 ⟨569955, by decide⟩ :=
  accepted_of_selected 13 302458 ⟨569955, by decide⟩ ⟨13, 2, 0, 569955, 302458, 1937, 16384⟩
    (by decide) selected_cut_22411

theorem selected_cut_22412 : selected 8 ⟨569961, by decide⟩
    (prefixPartial 13 302459) = some ⟨13, 2, 0, 569961, 302459, 993, 16384⟩ := by
  decide +kernel

theorem context_13_302459_569961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302459 ⟨569961, by decide⟩ :=
  accepted_of_selected 13 302459 ⟨569961, by decide⟩ ⟨13, 2, 0, 569961, 302459, 993, 16384⟩
    (by decide) selected_cut_22412

theorem unmarked_context_12_75614_569962 : frontier 9 ⟨569962, by decide⟩
    (prefixCache 12 75614) (prefixPartial 12 75614) = false := by
  decide +kernel

theorem node_context_12_75614_569962 : EJMOriginalGlobalDAGData.nodes 9 ⟨569962, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569932, by decide⟩,⟨569955, by decide⟩,⟨569961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75614_569962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75614 ⟨569962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75614
    ⟨569962, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569932, by decide⟩,⟨569955, by decide⟩,⟨569961, by decide⟩]) unmarked_context_12_75614_569962 node_context_12_75614_569962
  intro a
  fin_cases a
  · exact context_13_302456_3444
  · exact context_13_302457_569932
  · exact context_13_302458_569955
  · exact context_13_302459_569961

theorem selected_cut_22413 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302460) = some ⟨13, 1, 0, 3444, 302460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302460, 1, 16384⟩
    (by decide) selected_cut_22413

theorem selected_cut_22414 : selected 8 ⟨570000, by decide⟩
    (prefixPartial 13 302461) = some ⟨13, 2, 0, 570000, 302461, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_302461_570000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302461 ⟨570000, by decide⟩ :=
  accepted_of_selected 13 302461 ⟨570000, by decide⟩ ⟨13, 2, 0, 570000, 302461, 2309, 16384⟩
    (by decide) selected_cut_22414

theorem selected_cut_22415 : selected 8 ⟨570077, by decide⟩
    (prefixPartial 13 302462) = some ⟨13, 2, 0, 570077, 302462, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_302462_570077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302462 ⟨570077, by decide⟩ :=
  accepted_of_selected 13 302462 ⟨570077, by decide⟩ ⟨13, 2, 0, 570077, 302462, 3313, 16384⟩
    (by decide) selected_cut_22415

theorem selected_cut_22416 : selected 8 ⟨570090, by decide⟩
    (prefixPartial 13 302463) = some ⟨13, 2, 0, 570090, 302463, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_302463_570090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302463 ⟨570090, by decide⟩ :=
  accepted_of_selected 13 302463 ⟨570090, by decide⟩ ⟨13, 2, 0, 570090, 302463, 1181, 16384⟩
    (by decide) selected_cut_22416

theorem unmarked_context_12_75615_570091 : frontier 9 ⟨570091, by decide⟩
    (prefixCache 12 75615) (prefixPartial 12 75615) = false := by
  decide +kernel

theorem node_context_12_75615_570091 : EJMOriginalGlobalDAGData.nodes 9 ⟨570091, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨570000, by decide⟩,⟨570077, by decide⟩,⟨570090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75615_570091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75615 ⟨570091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75615
    ⟨570091, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨570000, by decide⟩,⟨570077, by decide⟩,⟨570090, by decide⟩]) unmarked_context_12_75615_570091 node_context_12_75615_570091
  intro a
  fin_cases a
  · exact context_13_302460_3444
  · exact context_13_302461_570000
  · exact context_13_302462_570077
  · exact context_13_302463_570090

theorem unmarked_context_11_18903_570092 : frontier 10 ⟨570092, by decide⟩
    (prefixCache 11 18903) (prefixPartial 11 18903) = false := by
  decide +kernel

theorem node_context_11_18903_570092 : EJMOriginalGlobalDAGData.nodes 10 ⟨570092, by decide⟩ =
    .split (coordinate 11) (![⟨569853, by decide⟩,⟨569903, by decide⟩,⟨569962, by decide⟩,⟨570091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18903_570092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18903 ⟨570092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18903
    ⟨570092, by decide⟩ (by decide) (![⟨569853, by decide⟩,⟨569903, by decide⟩,⟨569962, by decide⟩,⟨570091, by decide⟩]) unmarked_context_11_18903_570092 node_context_11_18903_570092
  intro a
  fin_cases a
  · exact context_12_75612_569853
  · exact context_12_75613_569903
  · exact context_12_75614_569962
  · exact context_12_75615_570091

theorem unmarked_context_10_4725_570093 : frontier 11 ⟨570093, by decide⟩
    (prefixCache 10 4725) (prefixPartial 10 4725) = false := by
  decide +kernel

theorem node_context_10_4725_570093 : EJMOriginalGlobalDAGData.nodes 11 ⟨570093, by decide⟩ =
    .split (coordinate 10) (![⟨569553, by decide⟩,⟨451541, by decide⟩,⟨569807, by decide⟩,⟨570092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4725_570093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4725 ⟨570093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4725
    ⟨570093, by decide⟩ (by decide) (![⟨569553, by decide⟩,⟨451541, by decide⟩,⟨569807, by decide⟩,⟨570092, by decide⟩]) unmarked_context_10_4725_570093 node_context_10_4725_570093
  intro a
  fin_cases a
  · exact context_11_18900_569553
  · exact context_11_18901_451541
  · exact context_11_18902_569807
  · exact context_11_18903_570092

theorem selected_cut_22417 : selected 9 ⟨570139, by decide⟩
    (prefixPartial 12 75616) = some ⟨12, 2, 0, 570139, 75616, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_75616_570139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75616 ⟨570139, by decide⟩ :=
  accepted_of_selected 12 75616 ⟨570139, by decide⟩ ⟨12, 2, 0, 570139, 75616, 3753, 65536⟩
    (by decide) selected_cut_22417

theorem selected_cut_22418 : selected 9 ⟨570191, by decide⟩
    (prefixPartial 12 75617) = some ⟨12, 2, 0, 570191, 75617, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_75617_570191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75617 ⟨570191, by decide⟩ :=
  accepted_of_selected 12 75617 ⟨570191, by decide⟩ ⟨12, 2, 0, 570191, 75617, 3949, 65536⟩
    (by decide) selected_cut_22418

theorem selected_cut_22419 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302472) = some ⟨13, 1, 0, 3444, 302472, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302472_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302472 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302472 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302472, 1, 16384⟩
    (by decide) selected_cut_22419

theorem selected_cut_22420 : selected 8 ⟨570216, by decide⟩
    (prefixPartial 13 302473) = some ⟨13, 2, 0, 570216, 302473, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_302473_570216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302473 ⟨570216, by decide⟩ :=
  accepted_of_selected 13 302473 ⟨570216, by decide⟩ ⟨13, 2, 0, 570216, 302473, 1729, 16384⟩
    (by decide) selected_cut_22420

theorem selected_cut_22421 : selected 8 ⟨570239, by decide⟩
    (prefixPartial 13 302474) = some ⟨13, 2, 0, 570239, 302474, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_302474_570239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302474 ⟨570239, by decide⟩ :=
  accepted_of_selected 13 302474 ⟨570239, by decide⟩ ⟨13, 2, 0, 570239, 302474, 1861, 16384⟩
    (by decide) selected_cut_22421

theorem selected_cut_22422 : selected 8 ⟨570248, by decide⟩
    (prefixPartial 13 302475) = some ⟨13, 2, 0, 570248, 302475, 829, 16384⟩ := by
  decide +kernel

theorem context_13_302475_570248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302475 ⟨570248, by decide⟩ :=
  accepted_of_selected 13 302475 ⟨570248, by decide⟩ ⟨13, 2, 0, 570248, 302475, 829, 16384⟩
    (by decide) selected_cut_22422

theorem unmarked_context_12_75618_570249 : frontier 9 ⟨570249, by decide⟩
    (prefixCache 12 75618) (prefixPartial 12 75618) = false := by
  decide +kernel

theorem node_context_12_75618_570249 : EJMOriginalGlobalDAGData.nodes 9 ⟨570249, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨570216, by decide⟩,⟨570239, by decide⟩,⟨570248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75618_570249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75618 ⟨570249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75618
    ⟨570249, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨570216, by decide⟩,⟨570239, by decide⟩,⟨570248, by decide⟩]) unmarked_context_12_75618_570249 node_context_12_75618_570249
  intro a
  fin_cases a
  · exact context_13_302472_3444
  · exact context_13_302473_570216
  · exact context_13_302474_570239
  · exact context_13_302475_570248

theorem selected_cut_22423 : selected 9 ⟨570296, by decide⟩
    (prefixPartial 12 75619) = some ⟨12, 2, 0, 570296, 75619, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_75619_570296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75619 ⟨570296, by decide⟩ :=
  accepted_of_selected 12 75619 ⟨570296, by decide⟩ ⟨12, 2, 0, 570296, 75619, 3997, 65536⟩
    (by decide) selected_cut_22423

theorem unmarked_context_11_18904_570297 : frontier 10 ⟨570297, by decide⟩
    (prefixCache 11 18904) (prefixPartial 11 18904) = false := by
  decide +kernel

theorem node_context_11_18904_570297 : EJMOriginalGlobalDAGData.nodes 10 ⟨570297, by decide⟩ =
    .split (coordinate 11) (![⟨570139, by decide⟩,⟨570191, by decide⟩,⟨570249, by decide⟩,⟨570296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18904_570297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18904 ⟨570297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18904
    ⟨570297, by decide⟩ (by decide) (![⟨570139, by decide⟩,⟨570191, by decide⟩,⟨570249, by decide⟩,⟨570296, by decide⟩]) unmarked_context_11_18904_570297 node_context_11_18904_570297
  intro a
  fin_cases a
  · exact context_12_75616_570139
  · exact context_12_75617_570191
  · exact context_12_75618_570249
  · exact context_12_75619_570296

theorem selected_cut_22424 : selected 9 ⟨570347, by decide⟩
    (prefixPartial 12 75620) = some ⟨12, 2, 0, 570347, 75620, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_75620_570347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75620 ⟨570347, by decide⟩ :=
  accepted_of_selected 12 75620 ⟨570347, by decide⟩ ⟨12, 2, 0, 570347, 75620, 3797, 65536⟩
    (by decide) selected_cut_22424

theorem selected_cut_22425 : selected 9 ⟨570392, by decide⟩
    (prefixPartial 12 75621) = some ⟨12, 2, 0, 570392, 75621, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_75621_570392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75621 ⟨570392, by decide⟩ :=
  accepted_of_selected 12 75621 ⟨570392, by decide⟩ ⟨12, 2, 0, 570392, 75621, 3653, 65536⟩
    (by decide) selected_cut_22425

theorem selected_cut_22426 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302488) = some ⟨13, 1, 0, 3444, 302488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302488, 1, 16384⟩
    (by decide) selected_cut_22426

theorem selected_cut_22427 : selected 8 ⟨570415, by decide⟩
    (prefixPartial 13 302489) = some ⟨13, 2, 0, 570415, 302489, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_302489_570415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302489 ⟨570415, by decide⟩ :=
  accepted_of_selected 13 302489 ⟨570415, by decide⟩ ⟨13, 2, 0, 570415, 302489, 1341, 16384⟩
    (by decide) selected_cut_22427

theorem selected_cut_22428 : selected 8 ⟨570438, by decide⟩
    (prefixPartial 13 302490) = some ⟨13, 2, 0, 570438, 302490, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_302490_570438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302490 ⟨570438, by decide⟩ :=
  accepted_of_selected 13 302490 ⟨570438, by decide⟩ ⟨13, 2, 0, 570438, 302490, 1917, 16384⟩
    (by decide) selected_cut_22428

theorem selected_cut_22429 : selected 8 ⟨570446, by decide⟩
    (prefixPartial 13 302491) = some ⟨13, 2, 0, 570446, 302491, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_302491_570446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302491 ⟨570446, by decide⟩ :=
  accepted_of_selected 13 302491 ⟨570446, by decide⟩ ⟨13, 2, 0, 570446, 302491, 1105, 16384⟩
    (by decide) selected_cut_22429

theorem unmarked_context_12_75622_570447 : frontier 9 ⟨570447, by decide⟩
    (prefixCache 12 75622) (prefixPartial 12 75622) = false := by
  decide +kernel

theorem node_context_12_75622_570447 : EJMOriginalGlobalDAGData.nodes 9 ⟨570447, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨570415, by decide⟩,⟨570438, by decide⟩,⟨570446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75622_570447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75622 ⟨570447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75622
    ⟨570447, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨570415, by decide⟩,⟨570438, by decide⟩,⟨570446, by decide⟩]) unmarked_context_12_75622_570447 node_context_12_75622_570447
  intro a
  fin_cases a
  · exact context_13_302488_3444
  · exact context_13_302489_570415
  · exact context_13_302490_570438
  · exact context_13_302491_570446

theorem selected_cut_22430 : selected 9 ⟨570490, by decide⟩
    (prefixPartial 12 75623) = some ⟨12, 2, 0, 570490, 75623, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_75623_570490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75623 ⟨570490, by decide⟩ :=
  accepted_of_selected 12 75623 ⟨570490, by decide⟩ ⟨12, 2, 0, 570490, 75623, 4061, 65536⟩
    (by decide) selected_cut_22430

theorem unmarked_context_11_18905_570491 : frontier 10 ⟨570491, by decide⟩
    (prefixCache 11 18905) (prefixPartial 11 18905) = false := by
  decide +kernel

theorem node_context_11_18905_570491 : EJMOriginalGlobalDAGData.nodes 10 ⟨570491, by decide⟩ =
    .split (coordinate 11) (![⟨570347, by decide⟩,⟨570392, by decide⟩,⟨570447, by decide⟩,⟨570490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18905_570491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18905 ⟨570491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18905
    ⟨570491, by decide⟩ (by decide) (![⟨570347, by decide⟩,⟨570392, by decide⟩,⟨570447, by decide⟩,⟨570490, by decide⟩]) unmarked_context_11_18905_570491 node_context_11_18905_570491
  intro a
  fin_cases a
  · exact context_12_75620_570347
  · exact context_12_75621_570392
  · exact context_12_75622_570447
  · exact context_12_75623_570490

theorem selected_cut_22431 : selected 9 ⟨570542, by decide⟩
    (prefixPartial 12 75624) = some ⟨12, 2, 0, 570542, 75624, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_75624_570542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75624 ⟨570542, by decide⟩ :=
  accepted_of_selected 12 75624 ⟨570542, by decide⟩ ⟨12, 2, 0, 570542, 75624, 3697, 65536⟩
    (by decide) selected_cut_22431

theorem selected_cut_22432 : selected 9 ⟨570595, by decide⟩
    (prefixPartial 12 75625) = some ⟨12, 2, 0, 570595, 75625, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_75625_570595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75625 ⟨570595, by decide⟩ :=
  accepted_of_selected 12 75625 ⟨570595, by decide⟩ ⟨12, 2, 0, 570595, 75625, 3805, 65536⟩
    (by decide) selected_cut_22432

theorem selected_cut_22433 : selected 9 ⟨570651, by decide⟩
    (prefixPartial 12 75626) = some ⟨12, 2, 0, 570651, 75626, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_75626_570651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75626 ⟨570651, by decide⟩ :=
  accepted_of_selected 12 75626 ⟨570651, by decide⟩ ⟨12, 2, 0, 570651, 75626, 4033, 65536⟩
    (by decide) selected_cut_22433

theorem selected_cut_22434 : selected 9 ⟨570694, by decide⟩
    (prefixPartial 12 75627) = some ⟨12, 2, 0, 570694, 75627, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_75627_570694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75627 ⟨570694, by decide⟩ :=
  accepted_of_selected 12 75627 ⟨570694, by decide⟩ ⟨12, 2, 0, 570694, 75627, 3685, 65536⟩
    (by decide) selected_cut_22434

theorem unmarked_context_11_18906_570695 : frontier 10 ⟨570695, by decide⟩
    (prefixCache 11 18906) (prefixPartial 11 18906) = false := by
  decide +kernel

theorem node_context_11_18906_570695 : EJMOriginalGlobalDAGData.nodes 10 ⟨570695, by decide⟩ =
    .split (coordinate 11) (![⟨570542, by decide⟩,⟨570595, by decide⟩,⟨570651, by decide⟩,⟨570694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18906_570695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18906 ⟨570695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18906
    ⟨570695, by decide⟩ (by decide) (![⟨570542, by decide⟩,⟨570595, by decide⟩,⟨570651, by decide⟩,⟨570694, by decide⟩]) unmarked_context_11_18906_570695 node_context_11_18906_570695
  intro a
  fin_cases a
  · exact context_12_75624_570542
  · exact context_12_75625_570595
  · exact context_12_75626_570651
  · exact context_12_75627_570694

theorem selected_cut_22435 : selected 9 ⟨570733, by decide⟩
    (prefixPartial 12 75628) = some ⟨12, 2, 0, 570733, 75628, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_75628_570733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75628 ⟨570733, by decide⟩ :=
  accepted_of_selected 12 75628 ⟨570733, by decide⟩ ⟨12, 2, 0, 570733, 75628, 3417, 65536⟩
    (by decide) selected_cut_22435

theorem selected_cut_22436 : selected 9 ⟨570776, by decide⟩
    (prefixPartial 12 75629) = some ⟨12, 2, 0, 570776, 75629, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_75629_570776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75629 ⟨570776, by decide⟩ :=
  accepted_of_selected 12 75629 ⟨570776, by decide⟩ ⟨12, 2, 0, 570776, 75629, 3589, 65536⟩
    (by decide) selected_cut_22436

theorem selected_cut_22437 : selected 9 ⟨570826, by decide⟩
    (prefixPartial 12 75630) = some ⟨12, 2, 0, 570826, 75630, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_75630_570826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75630 ⟨570826, by decide⟩ :=
  accepted_of_selected 12 75630 ⟨570826, by decide⟩ ⟨12, 2, 0, 570826, 75630, 3785, 65536⟩
    (by decide) selected_cut_22437

theorem selected_cut_22438 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302524) = some ⟨13, 1, 0, 3444, 302524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302524, 1, 16384⟩
    (by decide) selected_cut_22438

theorem selected_cut_22439 : selected 8 ⟨570863, by decide⟩
    (prefixPartial 13 302525) = some ⟨13, 2, 0, 570863, 302525, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_302525_570863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302525 ⟨570863, by decide⟩ :=
  accepted_of_selected 13 302525 ⟨570863, by decide⟩ ⟨13, 2, 0, 570863, 302525, 1433, 16384⟩
    (by decide) selected_cut_22439

theorem selected_cut_22440 : selected 8 ⟨570921, by decide⟩
    (prefixPartial 13 302526) = some ⟨13, 2, 0, 570921, 302526, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_302526_570921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302526 ⟨570921, by decide⟩ :=
  accepted_of_selected 13 302526 ⟨570921, by decide⟩ ⟨13, 2, 0, 570921, 302526, 2977, 16384⟩
    (by decide) selected_cut_22440

theorem selected_cut_22441 : selected 8 ⟨570933, by decide⟩
    (prefixPartial 13 302527) = some ⟨13, 2, 0, 570933, 302527, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_302527_570933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302527 ⟨570933, by decide⟩ :=
  accepted_of_selected 13 302527 ⟨570933, by decide⟩ ⟨13, 2, 0, 570933, 302527, 1117, 16384⟩
    (by decide) selected_cut_22441

theorem unmarked_context_12_75631_570934 : frontier 9 ⟨570934, by decide⟩
    (prefixCache 12 75631) (prefixPartial 12 75631) = false := by
  decide +kernel

theorem node_context_12_75631_570934 : EJMOriginalGlobalDAGData.nodes 9 ⟨570934, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨570863, by decide⟩,⟨570921, by decide⟩,⟨570933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75631_570934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75631 ⟨570934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75631
    ⟨570934, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨570863, by decide⟩,⟨570921, by decide⟩,⟨570933, by decide⟩]) unmarked_context_12_75631_570934 node_context_12_75631_570934
  intro a
  fin_cases a
  · exact context_13_302524_3444
  · exact context_13_302525_570863
  · exact context_13_302526_570921
  · exact context_13_302527_570933

theorem unmarked_context_11_18907_570935 : frontier 10 ⟨570935, by decide⟩
    (prefixCache 11 18907) (prefixPartial 11 18907) = false := by
  decide +kernel

theorem node_context_11_18907_570935 : EJMOriginalGlobalDAGData.nodes 10 ⟨570935, by decide⟩ =
    .split (coordinate 11) (![⟨570733, by decide⟩,⟨570776, by decide⟩,⟨570826, by decide⟩,⟨570934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18907_570935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18907 ⟨570935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18907
    ⟨570935, by decide⟩ (by decide) (![⟨570733, by decide⟩,⟨570776, by decide⟩,⟨570826, by decide⟩,⟨570934, by decide⟩]) unmarked_context_11_18907_570935 node_context_11_18907_570935
  intro a
  fin_cases a
  · exact context_12_75628_570733
  · exact context_12_75629_570776
  · exact context_12_75630_570826
  · exact context_12_75631_570934

theorem unmarked_context_10_4726_570936 : frontier 11 ⟨570936, by decide⟩
    (prefixCache 10 4726) (prefixPartial 10 4726) = false := by
  decide +kernel

theorem node_context_10_4726_570936 : EJMOriginalGlobalDAGData.nodes 11 ⟨570936, by decide⟩ =
    .split (coordinate 10) (![⟨570297, by decide⟩,⟨570491, by decide⟩,⟨570695, by decide⟩,⟨570935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4726_570936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4726 ⟨570936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4726
    ⟨570936, by decide⟩ (by decide) (![⟨570297, by decide⟩,⟨570491, by decide⟩,⟨570695, by decide⟩,⟨570935, by decide⟩]) unmarked_context_10_4726_570936 node_context_10_4726_570936
  intro a
  fin_cases a
  · exact context_11_18904_570297
  · exact context_11_18905_570491
  · exact context_11_18906_570695
  · exact context_11_18907_570935

theorem selected_cut_22442 : selected 9 ⟨570975, by decide⟩
    (prefixPartial 12 75632) = some ⟨12, 2, 0, 570975, 75632, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_75632_570975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75632 ⟨570975, by decide⟩ :=
  accepted_of_selected 12 75632 ⟨570975, by decide⟩ ⟨12, 2, 0, 570975, 75632, 3549, 65536⟩
    (by decide) selected_cut_22442

theorem selected_cut_22443 : selected 9 ⟨571022, by decide⟩
    (prefixPartial 12 75633) = some ⟨12, 2, 0, 571022, 75633, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_75633_571022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75633 ⟨571022, by decide⟩ :=
  accepted_of_selected 12 75633 ⟨571022, by decide⟩ ⟨12, 2, 0, 571022, 75633, 3613, 65536⟩
    (by decide) selected_cut_22443

theorem selected_cut_22444 : selected 9 ⟨571071, by decide⟩
    (prefixPartial 12 75634) = some ⟨12, 2, 0, 571071, 75634, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_75634_571071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75634 ⟨571071, by decide⟩ :=
  accepted_of_selected 12 75634 ⟨571071, by decide⟩ ⟨12, 2, 0, 571071, 75634, 3973, 65536⟩
    (by decide) selected_cut_22444

theorem selected_cut_22445 : selected 9 ⟨571114, by decide⟩
    (prefixPartial 12 75635) = some ⟨12, 2, 0, 571114, 75635, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_75635_571114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75635 ⟨571114, by decide⟩ :=
  accepted_of_selected 12 75635 ⟨571114, by decide⟩ ⟨12, 2, 0, 571114, 75635, 3457, 65536⟩
    (by decide) selected_cut_22445

theorem unmarked_context_11_18908_571115 : frontier 10 ⟨571115, by decide⟩
    (prefixCache 11 18908) (prefixPartial 11 18908) = false := by
  decide +kernel

theorem node_context_11_18908_571115 : EJMOriginalGlobalDAGData.nodes 10 ⟨571115, by decide⟩ =
    .split (coordinate 11) (![⟨570975, by decide⟩,⟨571022, by decide⟩,⟨571071, by decide⟩,⟨571114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18908_571115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18908 ⟨571115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18908
    ⟨571115, by decide⟩ (by decide) (![⟨570975, by decide⟩,⟨571022, by decide⟩,⟨571071, by decide⟩,⟨571114, by decide⟩]) unmarked_context_11_18908_571115 node_context_11_18908_571115
  intro a
  fin_cases a
  · exact context_12_75632_570975
  · exact context_12_75633_571022
  · exact context_12_75634_571071
  · exact context_12_75635_571114

theorem selected_cut_22446 : selected 9 ⟨571158, by decide⟩
    (prefixPartial 12 75636) = some ⟨12, 2, 0, 571158, 75636, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_75636_571158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75636 ⟨571158, by decide⟩ :=
  accepted_of_selected 12 75636 ⟨571158, by decide⟩ ⟨12, 2, 0, 571158, 75636, 3617, 65536⟩
    (by decide) selected_cut_22446

theorem selected_cut_22447 : selected 9 ⟨571208, by decide⟩
    (prefixPartial 12 75637) = some ⟨12, 2, 0, 571208, 75637, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_75637_571208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75637 ⟨571208, by decide⟩ :=
  accepted_of_selected 12 75637 ⟨571208, by decide⟩ ⟨12, 2, 0, 571208, 75637, 3417, 65536⟩
    (by decide) selected_cut_22447

theorem selected_cut_22448 : selected 9 ⟨571262, by decide⟩
    (prefixPartial 12 75638) = some ⟨12, 2, 0, 571262, 75638, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_75638_571262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75638 ⟨571262, by decide⟩ :=
  accepted_of_selected 12 75638 ⟨571262, by decide⟩ ⟨12, 2, 0, 571262, 75638, 3885, 65536⟩
    (by decide) selected_cut_22448

theorem selected_cut_22449 : selected 9 ⟨571301, by decide⟩
    (prefixPartial 12 75639) = some ⟨12, 2, 0, 571301, 75639, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_75639_571301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75639 ⟨571301, by decide⟩ :=
  accepted_of_selected 12 75639 ⟨571301, by decide⟩ ⟨12, 2, 0, 571301, 75639, 3673, 65536⟩
    (by decide) selected_cut_22449

theorem unmarked_context_11_18909_571302 : frontier 10 ⟨571302, by decide⟩
    (prefixCache 11 18909) (prefixPartial 11 18909) = false := by
  decide +kernel

theorem node_context_11_18909_571302 : EJMOriginalGlobalDAGData.nodes 10 ⟨571302, by decide⟩ =
    .split (coordinate 11) (![⟨571158, by decide⟩,⟨571208, by decide⟩,⟨571262, by decide⟩,⟨571301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18909_571302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18909 ⟨571302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18909
    ⟨571302, by decide⟩ (by decide) (![⟨571158, by decide⟩,⟨571208, by decide⟩,⟨571262, by decide⟩,⟨571301, by decide⟩]) unmarked_context_11_18909_571302 node_context_11_18909_571302
  intro a
  fin_cases a
  · exact context_12_75636_571158
  · exact context_12_75637_571208
  · exact context_12_75638_571262
  · exact context_12_75639_571301

theorem selected_cut_22450 : selected 9 ⟨571366, by decide⟩
    (prefixPartial 12 75640) = some ⟨12, 2, 0, 571366, 75640, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_75640_571366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75640 ⟨571366, by decide⟩ :=
  accepted_of_selected 12 75640 ⟨571366, by decide⟩ ⟨12, 2, 0, 571366, 75640, 3577, 65536⟩
    (by decide) selected_cut_22450

theorem selected_cut_22451 : selected 9 ⟨571427, by decide⟩
    (prefixPartial 12 75641) = some ⟨12, 2, 0, 571427, 75641, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_75641_571427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75641 ⟨571427, by decide⟩ :=
  accepted_of_selected 12 75641 ⟨571427, by decide⟩ ⟨12, 2, 0, 571427, 75641, 3581, 65536⟩
    (by decide) selected_cut_22451

theorem selected_cut_22452 : selected 9 ⟨571495, by decide⟩
    (prefixPartial 12 75642) = some ⟨12, 2, 0, 571495, 75642, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_75642_571495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75642 ⟨571495, by decide⟩ :=
  accepted_of_selected 12 75642 ⟨571495, by decide⟩ ⟨12, 2, 0, 571495, 75642, 3805, 65536⟩
    (by decide) selected_cut_22452

theorem selected_cut_22453 : selected 9 ⟨571540, by decide⟩
    (prefixPartial 12 75643) = some ⟨12, 2, 0, 571540, 75643, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_75643_571540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75643 ⟨571540, by decide⟩ :=
  accepted_of_selected 12 75643 ⟨571540, by decide⟩ ⟨12, 2, 0, 571540, 75643, 3393, 65536⟩
    (by decide) selected_cut_22453

theorem unmarked_context_11_18910_571541 : frontier 10 ⟨571541, by decide⟩
    (prefixCache 11 18910) (prefixPartial 11 18910) = false := by
  decide +kernel

theorem node_context_11_18910_571541 : EJMOriginalGlobalDAGData.nodes 10 ⟨571541, by decide⟩ =
    .split (coordinate 11) (![⟨571366, by decide⟩,⟨571427, by decide⟩,⟨571495, by decide⟩,⟨571540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18910_571541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18910 ⟨571541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18910
    ⟨571541, by decide⟩ (by decide) (![⟨571366, by decide⟩,⟨571427, by decide⟩,⟨571495, by decide⟩,⟨571540, by decide⟩]) unmarked_context_11_18910_571541 node_context_11_18910_571541
  intro a
  fin_cases a
  · exact context_12_75640_571366
  · exact context_12_75641_571427
  · exact context_12_75642_571495
  · exact context_12_75643_571540

theorem selected_cut_22454 : selected 9 ⟨571568, by decide⟩
    (prefixPartial 12 75644) = some ⟨12, 2, 0, 571568, 75644, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_75644_571568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75644 ⟨571568, by decide⟩ :=
  accepted_of_selected 12 75644 ⟨571568, by decide⟩ ⟨12, 2, 0, 571568, 75644, 2889, 65536⟩
    (by decide) selected_cut_22454

theorem selected_cut_22455 : selected 9 ⟨571603, by decide⟩
    (prefixPartial 12 75645) = some ⟨12, 2, 0, 571603, 75645, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_75645_571603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75645 ⟨571603, by decide⟩ :=
  accepted_of_selected 12 75645 ⟨571603, by decide⟩ ⟨12, 2, 0, 571603, 75645, 2881, 65536⟩
    (by decide) selected_cut_22455

theorem selected_cut_22456 : selected 9 ⟨571632, by decide⟩
    (prefixPartial 12 75646) = some ⟨12, 2, 0, 571632, 75646, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_75646_571632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75646 ⟨571632, by decide⟩ :=
  accepted_of_selected 12 75646 ⟨571632, by decide⟩ ⟨12, 2, 0, 571632, 75646, 3053, 65536⟩
    (by decide) selected_cut_22456

theorem selected_cut_22457 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 75647) = some ⟨12, 1, 0, 512556, 75647, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75647_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75647 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 75647 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 75647, 1, 65536⟩
    (by decide) selected_cut_22457

theorem unmarked_context_11_18911_571633 : frontier 10 ⟨571633, by decide⟩
    (prefixCache 11 18911) (prefixPartial 11 18911) = false := by
  decide +kernel

theorem node_context_11_18911_571633 : EJMOriginalGlobalDAGData.nodes 10 ⟨571633, by decide⟩ =
    .split (coordinate 11) (![⟨571568, by decide⟩,⟨571603, by decide⟩,⟨571632, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18911_571633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18911 ⟨571633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18911
    ⟨571633, by decide⟩ (by decide) (![⟨571568, by decide⟩,⟨571603, by decide⟩,⟨571632, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_18911_571633 node_context_11_18911_571633
  intro a
  fin_cases a
  · exact context_12_75644_571568
  · exact context_12_75645_571603
  · exact context_12_75646_571632
  · exact context_12_75647_512556

theorem unmarked_context_10_4727_571634 : frontier 11 ⟨571634, by decide⟩
    (prefixCache 10 4727) (prefixPartial 10 4727) = false := by
  decide +kernel

theorem node_context_10_4727_571634 : EJMOriginalGlobalDAGData.nodes 11 ⟨571634, by decide⟩ =
    .split (coordinate 10) (![⟨571115, by decide⟩,⟨571302, by decide⟩,⟨571541, by decide⟩,⟨571633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4727_571634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4727 ⟨571634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4727
    ⟨571634, by decide⟩ (by decide) (![⟨571115, by decide⟩,⟨571302, by decide⟩,⟨571541, by decide⟩,⟨571633, by decide⟩]) unmarked_context_10_4727_571634 node_context_10_4727_571634
  intro a
  fin_cases a
  · exact context_11_18908_571115
  · exact context_11_18909_571302
  · exact context_11_18910_571541
  · exact context_11_18911_571633

theorem unmarked_context_9_1181_571635 : frontier 12 ⟨571635, by decide⟩
    (prefixCache 9 1181) (prefixPartial 9 1181) = false := by
  decide +kernel

theorem node_context_9_1181_571635 : EJMOriginalGlobalDAGData.nodes 12 ⟨571635, by decide⟩ =
    .split (coordinate 9) (![⟨569277, by decide⟩,⟨570093, by decide⟩,⟨570936, by decide⟩,⟨571634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1181_571635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1181 ⟨571635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1181
    ⟨571635, by decide⟩ (by decide) (![⟨569277, by decide⟩,⟨570093, by decide⟩,⟨570936, by decide⟩,⟨571634, by decide⟩]) unmarked_context_9_1181_571635 node_context_9_1181_571635
  intro a
  fin_cases a
  · exact context_10_4724_569277
  · exact context_10_4725_570093
  · exact context_10_4726_570936
  · exact context_10_4727_571634

theorem selected_cut_22458 : selected 9 ⟨571657, by decide⟩
    (prefixPartial 12 75648) = some ⟨12, 2, 0, 571657, 75648, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_75648_571657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75648 ⟨571657, by decide⟩ :=
  accepted_of_selected 12 75648 ⟨571657, by decide⟩ ⟨12, 2, 0, 571657, 75648, 2109, 65536⟩
    (by decide) selected_cut_22458

theorem selected_cut_22459 : selected 9 ⟨571682, by decide⟩
    (prefixPartial 12 75649) = some ⟨12, 2, 0, 571682, 75649, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_75649_571682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75649 ⟨571682, by decide⟩ :=
  accepted_of_selected 12 75649 ⟨571682, by decide⟩ ⟨12, 2, 0, 571682, 75649, 2101, 65536⟩
    (by decide) selected_cut_22459

theorem selected_cut_22460 : selected 9 ⟨571709, by decide⟩
    (prefixPartial 12 75650) = some ⟨12, 2, 0, 571709, 75650, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_75650_571709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75650 ⟨571709, by decide⟩ :=
  accepted_of_selected 12 75650 ⟨571709, by decide⟩ ⟨12, 2, 0, 571709, 75650, 2141, 65536⟩
    (by decide) selected_cut_22460

theorem selected_cut_22461 : selected 9 ⟨571735, by decide⟩
    (prefixPartial 12 75651) = some ⟨12, 2, 0, 571735, 75651, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_75651_571735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75651 ⟨571735, by decide⟩ :=
  accepted_of_selected 12 75651 ⟨571735, by decide⟩ ⟨12, 2, 0, 571735, 75651, 2193, 65536⟩
    (by decide) selected_cut_22461

theorem unmarked_context_11_18912_571736 : frontier 10 ⟨571736, by decide⟩
    (prefixCache 11 18912) (prefixPartial 11 18912) = false := by
  decide +kernel

theorem node_context_11_18912_571736 : EJMOriginalGlobalDAGData.nodes 10 ⟨571736, by decide⟩ =
    .split (coordinate 11) (![⟨571657, by decide⟩,⟨571682, by decide⟩,⟨571709, by decide⟩,⟨571735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18912_571736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18912 ⟨571736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18912
    ⟨571736, by decide⟩ (by decide) (![⟨571657, by decide⟩,⟨571682, by decide⟩,⟨571709, by decide⟩,⟨571735, by decide⟩]) unmarked_context_11_18912_571736 node_context_11_18912_571736
  intro a
  fin_cases a
  · exact context_12_75648_571657
  · exact context_12_75649_571682
  · exact context_12_75650_571709
  · exact context_12_75651_571735

theorem selected_cut_22462 : selected 9 ⟨571760, by decide⟩
    (prefixPartial 12 75652) = some ⟨12, 2, 0, 571760, 75652, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_75652_571760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75652 ⟨571760, by decide⟩ :=
  accepted_of_selected 12 75652 ⟨571760, by decide⟩ ⟨12, 2, 0, 571760, 75652, 2201, 65536⟩
    (by decide) selected_cut_22462

theorem selected_cut_22463 : selected 9 ⟨571784, by decide⟩
    (prefixPartial 12 75653) = some ⟨12, 2, 0, 571784, 75653, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_75653_571784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75653 ⟨571784, by decide⟩ :=
  accepted_of_selected 12 75653 ⟨571784, by decide⟩ ⟨12, 2, 0, 571784, 75653, 2109, 65536⟩
    (by decide) selected_cut_22463

theorem selected_cut_22464 : selected 9 ⟨571812, by decide⟩
    (prefixPartial 12 75654) = some ⟨12, 2, 0, 571812, 75654, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_75654_571812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75654 ⟨571812, by decide⟩ :=
  accepted_of_selected 12 75654 ⟨571812, by decide⟩ ⟨12, 2, 0, 571812, 75654, 2253, 65536⟩
    (by decide) selected_cut_22464

theorem selected_cut_22465 : selected 9 ⟨571838, by decide⟩
    (prefixPartial 12 75655) = some ⟨12, 2, 0, 571838, 75655, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_75655_571838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75655 ⟨571838, by decide⟩ :=
  accepted_of_selected 12 75655 ⟨571838, by decide⟩ ⟨12, 2, 0, 571838, 75655, 2337, 65536⟩
    (by decide) selected_cut_22465

theorem unmarked_context_11_18913_571839 : frontier 10 ⟨571839, by decide⟩
    (prefixCache 11 18913) (prefixPartial 11 18913) = false := by
  decide +kernel

theorem node_context_11_18913_571839 : EJMOriginalGlobalDAGData.nodes 10 ⟨571839, by decide⟩ =
    .split (coordinate 11) (![⟨571760, by decide⟩,⟨571784, by decide⟩,⟨571812, by decide⟩,⟨571838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18913_571839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18913 ⟨571839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18913
    ⟨571839, by decide⟩ (by decide) (![⟨571760, by decide⟩,⟨571784, by decide⟩,⟨571812, by decide⟩,⟨571838, by decide⟩]) unmarked_context_11_18913_571839 node_context_11_18913_571839
  intro a
  fin_cases a
  · exact context_12_75652_571760
  · exact context_12_75653_571784
  · exact context_12_75654_571812
  · exact context_12_75655_571838

theorem selected_cut_22466 : selected 9 ⟨571868, by decide⟩
    (prefixPartial 12 75656) = some ⟨12, 2, 0, 571868, 75656, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_75656_571868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75656 ⟨571868, by decide⟩ :=
  accepted_of_selected 12 75656 ⟨571868, by decide⟩ ⟨12, 2, 0, 571868, 75656, 2373, 65536⟩
    (by decide) selected_cut_22466

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
