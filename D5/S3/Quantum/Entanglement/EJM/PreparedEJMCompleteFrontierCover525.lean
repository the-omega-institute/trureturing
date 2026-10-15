/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover524
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50404 : selected 10 ⟨1439347, by decide⟩
    (prefixPartial 11 106195) = some ⟨11, 2, 0, 1439347, 106195, 2593, 262144⟩ := by
  decide +kernel

theorem context_11_106195_1439347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106195 ⟨1439347, by decide⟩ :=
  accepted_of_selected 11 106195 ⟨1439347, by decide⟩ ⟨11, 2, 0, 1439347, 106195, 2593, 262144⟩
    (by decide) selected_cut_50404

theorem unmarked_context_10_26548_1439348 : frontier 11 ⟨1439348, by decide⟩
    (prefixCache 10 26548) (prefixPartial 10 26548) = false := by
  decide +kernel

theorem node_context_10_26548_1439348 : EJMOriginalGlobalDAGData.nodes 11 ⟨1439348, by decide⟩ =
    .split (coordinate 10) (![⟨1439148, by decide⟩,⟨1439225, by decide⟩,⟨1439290, by decide⟩,⟨1439347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26548_1439348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26548 ⟨1439348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26548
    ⟨1439348, by decide⟩ (by decide) (![⟨1439148, by decide⟩,⟨1439225, by decide⟩,⟨1439290, by decide⟩,⟨1439347, by decide⟩]) unmarked_context_10_26548_1439348 node_context_10_26548_1439348
  intro a
  fin_cases a
  · exact context_11_106192_1439148
  · exact context_11_106193_1439225
  · exact context_11_106194_1439290
  · exact context_11_106195_1439347

theorem selected_cut_50405 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26549) = some ⟨10, 1, 0, 893098, 26549, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26549_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26549 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26549 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26549, 1, 1048576⟩
    (by decide) selected_cut_50405

theorem selected_cut_50406 : selected 10 ⟨1439409, by decide⟩
    (prefixPartial 11 106200) = some ⟨11, 2, 0, 1439409, 106200, 3293, 262144⟩ := by
  decide +kernel

theorem context_11_106200_1439409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106200 ⟨1439409, by decide⟩ :=
  accepted_of_selected 11 106200 ⟨1439409, by decide⟩ ⟨11, 2, 0, 1439409, 106200, 3293, 262144⟩
    (by decide) selected_cut_50406

theorem selected_cut_50407 : selected 10 ⟨1439454, by decide⟩
    (prefixPartial 11 106201) = some ⟨11, 2, 0, 1439454, 106201, 2561, 262144⟩ := by
  decide +kernel

theorem context_11_106201_1439454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106201 ⟨1439454, by decide⟩ :=
  accepted_of_selected 11 106201 ⟨1439454, by decide⟩ ⟨11, 2, 0, 1439454, 106201, 2561, 262144⟩
    (by decide) selected_cut_50407

theorem selected_cut_50408 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 106202) = some ⟨11, 1, 0, 900587, 106202, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106202_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106202 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 106202 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 106202, 1, 262144⟩
    (by decide) selected_cut_50408

theorem selected_cut_50409 : selected 10 ⟨1439484, by decide⟩
    (prefixPartial 11 106203) = some ⟨11, 2, 0, 1439484, 106203, 1761, 262144⟩ := by
  decide +kernel

theorem context_11_106203_1439484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106203 ⟨1439484, by decide⟩ :=
  accepted_of_selected 11 106203 ⟨1439484, by decide⟩ ⟨11, 2, 0, 1439484, 106203, 1761, 262144⟩
    (by decide) selected_cut_50409

theorem unmarked_context_10_26550_1439485 : frontier 11 ⟨1439485, by decide⟩
    (prefixCache 10 26550) (prefixPartial 10 26550) = false := by
  decide +kernel

theorem node_context_10_26550_1439485 : EJMOriginalGlobalDAGData.nodes 11 ⟨1439485, by decide⟩ =
    .split (coordinate 10) (![⟨1439409, by decide⟩,⟨1439454, by decide⟩,⟨900587, by decide⟩,⟨1439484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26550_1439485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26550 ⟨1439485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26550
    ⟨1439485, by decide⟩ (by decide) (![⟨1439409, by decide⟩,⟨1439454, by decide⟩,⟨900587, by decide⟩,⟨1439484, by decide⟩]) unmarked_context_10_26550_1439485 node_context_10_26550_1439485
  intro a
  fin_cases a
  · exact context_11_106200_1439409
  · exact context_11_106201_1439454
  · exact context_11_106202_900587
  · exact context_11_106203_1439484

theorem selected_cut_50410 : selected 10 ⟨1439527, by decide⟩
    (prefixPartial 11 106204) = some ⟨11, 2, 0, 1439527, 106204, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_106204_1439527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106204 ⟨1439527, by decide⟩ :=
  accepted_of_selected 11 106204 ⟨1439527, by decide⟩ ⟨11, 2, 0, 1439527, 106204, 1889, 262144⟩
    (by decide) selected_cut_50410

theorem selected_cut_50411 : selected 10 ⟨1439578, by decide⟩
    (prefixPartial 11 106205) = some ⟨11, 2, 0, 1439578, 106205, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_106205_1439578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106205 ⟨1439578, by decide⟩ :=
  accepted_of_selected 11 106205 ⟨1439578, by decide⟩ ⟨11, 2, 0, 1439578, 106205, 2445, 262144⟩
    (by decide) selected_cut_50411

theorem selected_cut_50412 : selected 10 ⟨1439607, by decide⟩
    (prefixPartial 11 106206) = some ⟨11, 2, 0, 1439607, 106206, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_106206_1439607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106206 ⟨1439607, by decide⟩ :=
  accepted_of_selected 11 106206 ⟨1439607, by decide⟩ ⟨11, 2, 0, 1439607, 106206, 1417, 262144⟩
    (by decide) selected_cut_50412

theorem selected_cut_50413 : selected 10 ⟨1439608, by decide⟩
    (prefixPartial 11 106207) = some ⟨11, 2, 0, 1439608, 106207, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106207_1439608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106207 ⟨1439608, by decide⟩ :=
  accepted_of_selected 11 106207 ⟨1439608, by decide⟩ ⟨11, 2, 0, 1439608, 106207, 5, 262144⟩
    (by decide) selected_cut_50413

theorem unmarked_context_10_26551_1439609 : frontier 11 ⟨1439609, by decide⟩
    (prefixCache 10 26551) (prefixPartial 10 26551) = false := by
  decide +kernel

theorem node_context_10_26551_1439609 : EJMOriginalGlobalDAGData.nodes 11 ⟨1439609, by decide⟩ =
    .split (coordinate 10) (![⟨1439527, by decide⟩,⟨1439578, by decide⟩,⟨1439607, by decide⟩,⟨1439608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26551_1439609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26551 ⟨1439609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26551
    ⟨1439609, by decide⟩ (by decide) (![⟨1439527, by decide⟩,⟨1439578, by decide⟩,⟨1439607, by decide⟩,⟨1439608, by decide⟩]) unmarked_context_10_26551_1439609 node_context_10_26551_1439609
  intro a
  fin_cases a
  · exact context_11_106204_1439527
  · exact context_11_106205_1439578
  · exact context_11_106206_1439607
  · exact context_11_106207_1439608

theorem unmarked_context_9_6637_1439610 : frontier 12 ⟨1439610, by decide⟩
    (prefixCache 9 6637) (prefixPartial 9 6637) = false := by
  decide +kernel

theorem node_context_9_6637_1439610 : EJMOriginalGlobalDAGData.nodes 12 ⟨1439610, by decide⟩ =
    .split (coordinate 9) (![⟨1439348, by decide⟩,⟨893098, by decide⟩,⟨1439485, by decide⟩,⟨1439609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6637_1439610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6637 ⟨1439610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6637
    ⟨1439610, by decide⟩ (by decide) (![⟨1439348, by decide⟩,⟨893098, by decide⟩,⟨1439485, by decide⟩,⟨1439609, by decide⟩]) unmarked_context_9_6637_1439610 node_context_9_6637_1439610
  intro a
  fin_cases a
  · exact context_10_26548_1439348
  · exact context_10_26549_893098
  · exact context_10_26550_1439485
  · exact context_10_26551_1439609

theorem selected_cut_50414 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 106208) = some ⟨11, 1, 0, 1375697, 106208, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106208_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106208 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 106208 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 106208, 1, 262144⟩
    (by decide) selected_cut_50414

theorem selected_cut_50415 : selected 10 ⟨1439648, by decide⟩
    (prefixPartial 11 106209) = some ⟨11, 2, 0, 1439648, 106209, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_106209_1439648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106209 ⟨1439648, by decide⟩ :=
  accepted_of_selected 11 106209 ⟨1439648, by decide⟩ ⟨11, 2, 0, 1439648, 106209, 1805, 262144⟩
    (by decide) selected_cut_50415

theorem selected_cut_50416 : selected 10 ⟨1439707, by decide⟩
    (prefixPartial 11 106210) = some ⟨11, 2, 0, 1439707, 106210, 2533, 262144⟩ := by
  decide +kernel

theorem context_11_106210_1439707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106210 ⟨1439707, by decide⟩ :=
  accepted_of_selected 11 106210 ⟨1439707, by decide⟩ ⟨11, 2, 0, 1439707, 106210, 2533, 262144⟩
    (by decide) selected_cut_50416

theorem selected_cut_50417 : selected 10 ⟨1439756, by decide⟩
    (prefixPartial 11 106211) = some ⟨11, 2, 0, 1439756, 106211, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_106211_1439756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106211 ⟨1439756, by decide⟩ :=
  accepted_of_selected 11 106211 ⟨1439756, by decide⟩ ⟨11, 2, 0, 1439756, 106211, 2265, 262144⟩
    (by decide) selected_cut_50417

theorem unmarked_context_10_26552_1439757 : frontier 11 ⟨1439757, by decide⟩
    (prefixCache 10 26552) (prefixPartial 10 26552) = false := by
  decide +kernel

theorem node_context_10_26552_1439757 : EJMOriginalGlobalDAGData.nodes 11 ⟨1439757, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1439648, by decide⟩,⟨1439707, by decide⟩,⟨1439756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26552_1439757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26552 ⟨1439757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26552
    ⟨1439757, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1439648, by decide⟩,⟨1439707, by decide⟩,⟨1439756, by decide⟩]) unmarked_context_10_26552_1439757 node_context_10_26552_1439757
  intro a
  fin_cases a
  · exact context_11_106208_1375697
  · exact context_11_106209_1439648
  · exact context_11_106210_1439707
  · exact context_11_106211_1439756

theorem selected_cut_50418 : selected 10 ⟨1439808, by decide⟩
    (prefixPartial 11 106212) = some ⟨11, 2, 0, 1439808, 106212, 2033, 262144⟩ := by
  decide +kernel

theorem context_11_106212_1439808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106212 ⟨1439808, by decide⟩ :=
  accepted_of_selected 11 106212 ⟨1439808, by decide⟩ ⟨11, 2, 0, 1439808, 106212, 2033, 262144⟩
    (by decide) selected_cut_50418

theorem selected_cut_50419 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 106213) = some ⟨11, 1, 0, 1378525, 106213, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106213_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106213 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 106213 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 106213, 1, 262144⟩
    (by decide) selected_cut_50419

theorem selected_cut_50420 : selected 10 ⟨1439848, by decide⟩
    (prefixPartial 11 106214) = some ⟨11, 2, 0, 1439848, 106214, 1761, 262144⟩ := by
  decide +kernel

theorem context_11_106214_1439848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106214 ⟨1439848, by decide⟩ :=
  accepted_of_selected 11 106214 ⟨1439848, by decide⟩ ⟨11, 2, 0, 1439848, 106214, 1761, 262144⟩
    (by decide) selected_cut_50420

theorem selected_cut_50421 : selected 10 ⟨1439874, by decide⟩
    (prefixPartial 11 106215) = some ⟨11, 2, 0, 1439874, 106215, 1057, 262144⟩ := by
  decide +kernel

theorem context_11_106215_1439874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106215 ⟨1439874, by decide⟩ :=
  accepted_of_selected 11 106215 ⟨1439874, by decide⟩ ⟨11, 2, 0, 1439874, 106215, 1057, 262144⟩
    (by decide) selected_cut_50421

theorem unmarked_context_10_26553_1439875 : frontier 11 ⟨1439875, by decide⟩
    (prefixCache 10 26553) (prefixPartial 10 26553) = false := by
  decide +kernel

theorem node_context_10_26553_1439875 : EJMOriginalGlobalDAGData.nodes 11 ⟨1439875, by decide⟩ =
    .split (coordinate 10) (![⟨1439808, by decide⟩,⟨1378525, by decide⟩,⟨1439848, by decide⟩,⟨1439874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26553_1439875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26553 ⟨1439875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26553
    ⟨1439875, by decide⟩ (by decide) (![⟨1439808, by decide⟩,⟨1378525, by decide⟩,⟨1439848, by decide⟩,⟨1439874, by decide⟩]) unmarked_context_10_26553_1439875 node_context_10_26553_1439875
  intro a
  fin_cases a
  · exact context_11_106212_1439808
  · exact context_11_106213_1378525
  · exact context_11_106214_1439848
  · exact context_11_106215_1439874

theorem selected_cut_50422 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 26554) = some ⟨10, 2, 0, 1432895, 26554, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_26554_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26554 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 26554 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 26554, 5, 1048576⟩
    (by decide) selected_cut_50422

theorem selected_cut_50423 : selected 11 ⟨1439968, by decide⟩
    (prefixPartial 10 26555) = some ⟨10, 2, 0, 1439968, 26555, 3449, 1048576⟩ := by
  decide +kernel

theorem context_10_26555_1439968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26555 ⟨1439968, by decide⟩ :=
  accepted_of_selected 10 26555 ⟨1439968, by decide⟩ ⟨10, 2, 0, 1439968, 26555, 3449, 1048576⟩
    (by decide) selected_cut_50423

theorem unmarked_context_9_6638_1439969 : frontier 12 ⟨1439969, by decide⟩
    (prefixCache 9 6638) (prefixPartial 9 6638) = false := by
  decide +kernel

theorem node_context_9_6638_1439969 : EJMOriginalGlobalDAGData.nodes 12 ⟨1439969, by decide⟩ =
    .split (coordinate 9) (![⟨1439757, by decide⟩,⟨1439875, by decide⟩,⟨1432895, by decide⟩,⟨1439968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6638_1439969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6638 ⟨1439969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6638
    ⟨1439969, by decide⟩ (by decide) (![⟨1439757, by decide⟩,⟨1439875, by decide⟩,⟨1432895, by decide⟩,⟨1439968, by decide⟩]) unmarked_context_9_6638_1439969 node_context_9_6638_1439969
  intro a
  fin_cases a
  · exact context_10_26552_1439757
  · exact context_10_26553_1439875
  · exact context_10_26554_1432895
  · exact context_10_26555_1439968

theorem selected_cut_50424 : selected 12 ⟨1440090, by decide⟩
    (prefixPartial 9 6639) = some ⟨9, 2, 0, 1440090, 6639, 3965, 4194304⟩ := by
  decide +kernel

theorem context_9_6639_1440090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6639 ⟨1440090, by decide⟩ :=
  accepted_of_selected 9 6639 ⟨1440090, by decide⟩ ⟨9, 2, 0, 1440090, 6639, 3965, 4194304⟩
    (by decide) selected_cut_50424

theorem unmarked_context_8_1659_1440091 : frontier 13 ⟨1440091, by decide⟩
    (prefixCache 8 1659) (prefixPartial 8 1659) = false := by
  decide +kernel

theorem node_context_8_1659_1440091 : EJMOriginalGlobalDAGData.nodes 13 ⟨1440091, by decide⟩ =
    .split (coordinate 8) (![⟨1439112, by decide⟩,⟨1439610, by decide⟩,⟨1439969, by decide⟩,⟨1440090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1659_1440091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1659 ⟨1440091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1659
    ⟨1440091, by decide⟩ (by decide) (![⟨1439112, by decide⟩,⟨1439610, by decide⟩,⟨1439969, by decide⟩,⟨1440090, by decide⟩]) unmarked_context_8_1659_1440091 node_context_8_1659_1440091
  intro a
  fin_cases a
  · exact context_9_6636_1439112
  · exact context_9_6637_1439610
  · exact context_9_6638_1439969
  · exact context_9_6639_1440090

theorem unmarked_context_7_414_1440092 : frontier 14 ⟨1440092, by decide⟩
    (prefixCache 7 414) (prefixPartial 7 414) = false := by
  decide +kernel

theorem node_context_7_414_1440092 : EJMOriginalGlobalDAGData.nodes 14 ⟨1440092, by decide⟩ =
    .split (coordinate 7) (![⟨1433108, by decide⟩,⟨1435280, by decide⟩,⟨1437986, by decide⟩,⟨1440091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_414_1440092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 414 ⟨1440092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 414
    ⟨1440092, by decide⟩ (by decide) (![⟨1433108, by decide⟩,⟨1435280, by decide⟩,⟨1437986, by decide⟩,⟨1440091, by decide⟩]) unmarked_context_7_414_1440092 node_context_7_414_1440092
  intro a
  fin_cases a
  · exact context_8_1656_1433108
  · exact context_8_1657_1435280
  · exact context_8_1658_1437986
  · exact context_8_1659_1440091

theorem selected_cut_50425 : selected 11 ⟨1440211, by decide⟩
    (prefixPartial 10 26560) = some ⟨10, 2, 0, 1440211, 26560, 2809, 1048576⟩ := by
  decide +kernel

theorem context_10_26560_1440211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26560 ⟨1440211, by decide⟩ :=
  accepted_of_selected 10 26560 ⟨1440211, by decide⟩ ⟨10, 2, 0, 1440211, 26560, 2809, 1048576⟩
    (by decide) selected_cut_50425

theorem selected_cut_50426 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424976) = some ⟨12, 1, 0, 1415033, 424976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424976_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424976 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424976 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424976, 1, 65536⟩
    (by decide) selected_cut_50426

theorem selected_cut_50427 : selected 9 ⟨1440267, by decide⟩
    (prefixPartial 12 424977) = some ⟨12, 2, 0, 1440267, 424977, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_424977_1440267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424977 ⟨1440267, by decide⟩ :=
  accepted_of_selected 12 424977 ⟨1440267, by decide⟩ ⟨12, 2, 0, 1440267, 424977, 2201, 65536⟩
    (by decide) selected_cut_50427

theorem selected_cut_50428 : selected 9 ⟨1440335, by decide⟩
    (prefixPartial 12 424978) = some ⟨12, 2, 0, 1440335, 424978, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_424978_1440335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424978 ⟨1440335, by decide⟩ :=
  accepted_of_selected 12 424978 ⟨1440335, by decide⟩ ⟨12, 2, 0, 1440335, 424978, 2249, 65536⟩
    (by decide) selected_cut_50428

theorem selected_cut_50429 : selected 9 ⟨1440398, by decide⟩
    (prefixPartial 12 424979) = some ⟨12, 2, 0, 1440398, 424979, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_424979_1440398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424979 ⟨1440398, by decide⟩ :=
  accepted_of_selected 12 424979 ⟨1440398, by decide⟩ ⟨12, 2, 0, 1440398, 424979, 2201, 65536⟩
    (by decide) selected_cut_50429

theorem unmarked_context_11_106244_1440399 : frontier 10 ⟨1440399, by decide⟩
    (prefixCache 11 106244) (prefixPartial 11 106244) = false := by
  decide +kernel

theorem node_context_11_106244_1440399 : EJMOriginalGlobalDAGData.nodes 10 ⟨1440399, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1440267, by decide⟩,⟨1440335, by decide⟩,⟨1440398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106244_1440399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106244 ⟨1440399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106244
    ⟨1440399, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1440267, by decide⟩,⟨1440335, by decide⟩,⟨1440398, by decide⟩]) unmarked_context_11_106244_1440399 node_context_11_106244_1440399
  intro a
  fin_cases a
  · exact context_12_424976_1415033
  · exact context_12_424977_1440267
  · exact context_12_424978_1440335
  · exact context_12_424979_1440398

theorem selected_cut_50430 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 106245) = some ⟨11, 1, 0, 1241271, 106245, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106245_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106245 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 106245 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 106245, 1, 262144⟩
    (by decide) selected_cut_50430

theorem selected_cut_50431 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424984) = some ⟨12, 1, 0, 1415033, 424984, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424984_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424984 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424984 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424984, 1, 65536⟩
    (by decide) selected_cut_50431

theorem selected_cut_50432 : selected 9 ⟨1440458, by decide⟩
    (prefixPartial 12 424985) = some ⟨12, 2, 0, 1440458, 424985, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_424985_1440458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424985 ⟨1440458, by decide⟩ :=
  accepted_of_selected 12 424985 ⟨1440458, by decide⟩ ⟨12, 2, 0, 1440458, 424985, 2129, 65536⟩
    (by decide) selected_cut_50432

theorem selected_cut_50433 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 424986) = some ⟨12, 1, 0, 448662, 424986, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424986_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424986 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 424986 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 424986, 1, 65536⟩
    (by decide) selected_cut_50433

theorem selected_cut_50434 : selected 9 ⟨1440524, by decide⟩
    (prefixPartial 12 424987) = some ⟨12, 2, 0, 1440524, 424987, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_424987_1440524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424987 ⟨1440524, by decide⟩ :=
  accepted_of_selected 12 424987 ⟨1440524, by decide⟩ ⟨12, 2, 0, 1440524, 424987, 2485, 65536⟩
    (by decide) selected_cut_50434

theorem unmarked_context_11_106246_1440525 : frontier 10 ⟨1440525, by decide⟩
    (prefixCache 11 106246) (prefixPartial 11 106246) = false := by
  decide +kernel

theorem node_context_11_106246_1440525 : EJMOriginalGlobalDAGData.nodes 10 ⟨1440525, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1440458, by decide⟩,⟨448662, by decide⟩,⟨1440524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106246_1440525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106246 ⟨1440525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106246
    ⟨1440525, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1440458, by decide⟩,⟨448662, by decide⟩,⟨1440524, by decide⟩]) unmarked_context_11_106246_1440525 node_context_11_106246_1440525
  intro a
  fin_cases a
  · exact context_12_424984_1415033
  · exact context_12_424985_1440458
  · exact context_12_424986_448662
  · exact context_12_424987_1440524

theorem selected_cut_50435 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424988) = some ⟨12, 1, 0, 1415033, 424988, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424988_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424988 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424988 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424988, 1, 65536⟩
    (by decide) selected_cut_50435

theorem selected_cut_50436 : selected 9 ⟨1440573, by decide⟩
    (prefixPartial 12 424989) = some ⟨12, 2, 0, 1440573, 424989, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_424989_1440573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424989 ⟨1440573, by decide⟩ :=
  accepted_of_selected 12 424989 ⟨1440573, by decide⟩ ⟨12, 2, 0, 1440573, 424989, 1981, 65536⟩
    (by decide) selected_cut_50436

theorem selected_cut_50437 : selected 9 ⟨1440635, by decide⟩
    (prefixPartial 12 424990) = some ⟨12, 2, 0, 1440635, 424990, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_424990_1440635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424990 ⟨1440635, by decide⟩ :=
  accepted_of_selected 12 424990 ⟨1440635, by decide⟩ ⟨12, 2, 0, 1440635, 424990, 2353, 65536⟩
    (by decide) selected_cut_50437

theorem selected_cut_50438 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 424991) = some ⟨12, 1, 0, 760511, 424991, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424991_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424991 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 424991 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 424991, 1, 65536⟩
    (by decide) selected_cut_50438

theorem unmarked_context_11_106247_1440636 : frontier 10 ⟨1440636, by decide⟩
    (prefixCache 11 106247) (prefixPartial 11 106247) = false := by
  decide +kernel

theorem node_context_11_106247_1440636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1440636, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1440573, by decide⟩,⟨1440635, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106247_1440636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106247 ⟨1440636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106247
    ⟨1440636, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1440573, by decide⟩,⟨1440635, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_106247_1440636 node_context_11_106247_1440636
  intro a
  fin_cases a
  · exact context_12_424988_1415033
  · exact context_12_424989_1440573
  · exact context_12_424990_1440635
  · exact context_12_424991_760511

theorem unmarked_context_10_26561_1440637 : frontier 11 ⟨1440637, by decide⟩
    (prefixCache 10 26561) (prefixPartial 10 26561) = false := by
  decide +kernel

theorem node_context_10_26561_1440637 : EJMOriginalGlobalDAGData.nodes 11 ⟨1440637, by decide⟩ =
    .split (coordinate 10) (![⟨1440399, by decide⟩,⟨1241271, by decide⟩,⟨1440525, by decide⟩,⟨1440636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26561_1440637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26561 ⟨1440637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26561
    ⟨1440637, by decide⟩ (by decide) (![⟨1440399, by decide⟩,⟨1241271, by decide⟩,⟨1440525, by decide⟩,⟨1440636, by decide⟩]) unmarked_context_10_26561_1440637 node_context_10_26561_1440637
  intro a
  fin_cases a
  · exact context_11_106244_1440399
  · exact context_11_106245_1241271
  · exact context_11_106246_1440525
  · exact context_11_106247_1440636

theorem selected_cut_50439 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 424992) = some ⟨12, 1, 0, 435160, 424992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424992_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424992 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 424992 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 424992, 1, 65536⟩
    (by decide) selected_cut_50439

theorem selected_cut_50440 : selected 9 ⟨1440693, by decide⟩
    (prefixPartial 12 424993) = some ⟨12, 2, 0, 1440693, 424993, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_424993_1440693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424993 ⟨1440693, by decide⟩ :=
  accepted_of_selected 12 424993 ⟨1440693, by decide⟩ ⟨12, 2, 0, 1440693, 424993, 2189, 65536⟩
    (by decide) selected_cut_50440

theorem selected_cut_50441 : selected 9 ⟨1440747, by decide⟩
    (prefixPartial 12 424994) = some ⟨12, 2, 0, 1440747, 424994, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_424994_1440747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424994 ⟨1440747, by decide⟩ :=
  accepted_of_selected 12 424994 ⟨1440747, by decide⟩ ⟨12, 2, 0, 1440747, 424994, 2293, 65536⟩
    (by decide) selected_cut_50441

theorem selected_cut_50442 : selected 9 ⟨1440808, by decide⟩
    (prefixPartial 12 424995) = some ⟨12, 2, 0, 1440808, 424995, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_424995_1440808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424995 ⟨1440808, by decide⟩ :=
  accepted_of_selected 12 424995 ⟨1440808, by decide⟩ ⟨12, 2, 0, 1440808, 424995, 2057, 65536⟩
    (by decide) selected_cut_50442

theorem unmarked_context_11_106248_1440809 : frontier 10 ⟨1440809, by decide⟩
    (prefixCache 11 106248) (prefixPartial 11 106248) = false := by
  decide +kernel

theorem node_context_11_106248_1440809 : EJMOriginalGlobalDAGData.nodes 10 ⟨1440809, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1440693, by decide⟩,⟨1440747, by decide⟩,⟨1440808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106248_1440809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106248 ⟨1440809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106248
    ⟨1440809, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1440693, by decide⟩,⟨1440747, by decide⟩,⟨1440808, by decide⟩]) unmarked_context_11_106248_1440809 node_context_11_106248_1440809
  intro a
  fin_cases a
  · exact context_12_424992_435160
  · exact context_12_424993_1440693
  · exact context_12_424994_1440747
  · exact context_12_424995_1440808

theorem selected_cut_50443 : selected 10 ⟨1440906, by decide⟩
    (prefixPartial 11 106249) = some ⟨11, 2, 0, 1440906, 106249, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_106249_1440906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106249 ⟨1440906, by decide⟩ :=
  accepted_of_selected 11 106249 ⟨1440906, by decide⟩ ⟨11, 2, 0, 1440906, 106249, 3785, 262144⟩
    (by decide) selected_cut_50443

theorem selected_cut_50444 : selected 10 ⟨1440957, by decide⟩
    (prefixPartial 11 106250) = some ⟨11, 2, 0, 1440957, 106250, 1913, 262144⟩ := by
  decide +kernel

theorem context_11_106250_1440957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106250 ⟨1440957, by decide⟩ :=
  accepted_of_selected 11 106250 ⟨1440957, by decide⟩ ⟨11, 2, 0, 1440957, 106250, 1913, 262144⟩
    (by decide) selected_cut_50444

theorem selected_cut_50445 : selected 10 ⟨1441054, by decide⟩
    (prefixPartial 11 106251) = some ⟨11, 2, 0, 1441054, 106251, 3773, 262144⟩ := by
  decide +kernel

theorem context_11_106251_1441054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106251 ⟨1441054, by decide⟩ :=
  accepted_of_selected 11 106251 ⟨1441054, by decide⟩ ⟨11, 2, 0, 1441054, 106251, 3773, 262144⟩
    (by decide) selected_cut_50445

theorem unmarked_context_10_26562_1441055 : frontier 11 ⟨1441055, by decide⟩
    (prefixCache 10 26562) (prefixPartial 10 26562) = false := by
  decide +kernel

theorem node_context_10_26562_1441055 : EJMOriginalGlobalDAGData.nodes 11 ⟨1441055, by decide⟩ =
    .split (coordinate 10) (![⟨1440809, by decide⟩,⟨1440906, by decide⟩,⟨1440957, by decide⟩,⟨1441054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26562_1441055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26562 ⟨1441055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26562
    ⟨1441055, by decide⟩ (by decide) (![⟨1440809, by decide⟩,⟨1440906, by decide⟩,⟨1440957, by decide⟩,⟨1441054, by decide⟩]) unmarked_context_10_26562_1441055 node_context_10_26562_1441055
  intro a
  fin_cases a
  · exact context_11_106248_1440809
  · exact context_11_106249_1440906
  · exact context_11_106250_1440957
  · exact context_11_106251_1441054

theorem selected_cut_50446 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 425008) = some ⟨12, 1, 0, 1416143, 425008, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425008_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425008 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 425008 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 425008, 1, 65536⟩
    (by decide) selected_cut_50446

theorem selected_cut_50447 : selected 9 ⟨1441097, by decide⟩
    (prefixPartial 12 425009) = some ⟨12, 2, 0, 1441097, 425009, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_425009_1441097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425009 ⟨1441097, by decide⟩ :=
  accepted_of_selected 12 425009 ⟨1441097, by decide⟩ ⟨12, 2, 0, 1441097, 425009, 1681, 65536⟩
    (by decide) selected_cut_50447

theorem selected_cut_50448 : selected 9 ⟨1441138, by decide⟩
    (prefixPartial 12 425010) = some ⟨12, 2, 0, 1441138, 425010, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_425010_1441138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425010 ⟨1441138, by decide⟩ :=
  accepted_of_selected 12 425010 ⟨1441138, by decide⟩ ⟨12, 2, 0, 1441138, 425010, 1601, 65536⟩
    (by decide) selected_cut_50448

theorem selected_cut_50449 : selected 9 ⟨1441176, by decide⟩
    (prefixPartial 12 425011) = some ⟨12, 2, 0, 1441176, 425011, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_425011_1441176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425011 ⟨1441176, by decide⟩ :=
  accepted_of_selected 12 425011 ⟨1441176, by decide⟩ ⟨12, 2, 0, 1441176, 425011, 1557, 65536⟩
    (by decide) selected_cut_50449

theorem unmarked_context_11_106252_1441177 : frontier 10 ⟨1441177, by decide⟩
    (prefixCache 11 106252) (prefixPartial 11 106252) = false := by
  decide +kernel

theorem node_context_11_106252_1441177 : EJMOriginalGlobalDAGData.nodes 10 ⟨1441177, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1441097, by decide⟩,⟨1441138, by decide⟩,⟨1441176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106252_1441177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106252 ⟨1441177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106252
    ⟨1441177, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1441097, by decide⟩,⟨1441138, by decide⟩,⟨1441176, by decide⟩]) unmarked_context_11_106252_1441177 node_context_11_106252_1441177
  intro a
  fin_cases a
  · exact context_12_425008_1416143
  · exact context_12_425009_1441097
  · exact context_12_425010_1441138
  · exact context_12_425011_1441176

theorem selected_cut_50450 : selected 10 ⟨1441265, by decide⟩
    (prefixPartial 11 106253) = some ⟨11, 2, 0, 1441265, 106253, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_106253_1441265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106253 ⟨1441265, by decide⟩ :=
  accepted_of_selected 11 106253 ⟨1441265, by decide⟩ ⟨11, 2, 0, 1441265, 106253, 2985, 262144⟩
    (by decide) selected_cut_50450

theorem selected_cut_50451 : selected 10 ⟨1441330, by decide⟩
    (prefixPartial 11 106254) = some ⟨11, 2, 0, 1441330, 106254, 2889, 262144⟩ := by
  decide +kernel

theorem context_11_106254_1441330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106254 ⟨1441330, by decide⟩ :=
  accepted_of_selected 11 106254 ⟨1441330, by decide⟩ ⟨11, 2, 0, 1441330, 106254, 2889, 262144⟩
    (by decide) selected_cut_50451

theorem selected_cut_50452 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106255) = some ⟨11, 1, 0, 977886, 106255, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106255_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106255 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106255 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106255, 1, 262144⟩
    (by decide) selected_cut_50452

theorem unmarked_context_10_26563_1441331 : frontier 11 ⟨1441331, by decide⟩
    (prefixCache 10 26563) (prefixPartial 10 26563) = false := by
  decide +kernel

theorem node_context_10_26563_1441331 : EJMOriginalGlobalDAGData.nodes 11 ⟨1441331, by decide⟩ =
    .split (coordinate 10) (![⟨1441177, by decide⟩,⟨1441265, by decide⟩,⟨1441330, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26563_1441331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26563 ⟨1441331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26563
    ⟨1441331, by decide⟩ (by decide) (![⟨1441177, by decide⟩,⟨1441265, by decide⟩,⟨1441330, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26563_1441331 node_context_10_26563_1441331
  intro a
  fin_cases a
  · exact context_11_106252_1441177
  · exact context_11_106253_1441265
  · exact context_11_106254_1441330
  · exact context_11_106255_977886

theorem unmarked_context_9_6640_1441332 : frontier 12 ⟨1441332, by decide⟩
    (prefixCache 9 6640) (prefixPartial 9 6640) = false := by
  decide +kernel

theorem node_context_9_6640_1441332 : EJMOriginalGlobalDAGData.nodes 12 ⟨1441332, by decide⟩ =
    .split (coordinate 9) (![⟨1440211, by decide⟩,⟨1440637, by decide⟩,⟨1441055, by decide⟩,⟨1441331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6640_1441332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6640 ⟨1441332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6640
    ⟨1441332, by decide⟩ (by decide) (![⟨1440211, by decide⟩,⟨1440637, by decide⟩,⟨1441055, by decide⟩,⟨1441331, by decide⟩]) unmarked_context_9_6640_1441332 node_context_9_6640_1441332
  intro a
  fin_cases a
  · exact context_10_26560_1440211
  · exact context_10_26561_1440637
  · exact context_10_26562_1441055
  · exact context_10_26563_1441331

theorem selected_cut_50453 : selected 10 ⟨1441334, by decide⟩
    (prefixPartial 11 106256) = some ⟨11, 2, 0, 1441334, 106256, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106256_1441334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106256 ⟨1441334, by decide⟩ :=
  accepted_of_selected 11 106256 ⟨1441334, by decide⟩ ⟨11, 2, 0, 1441334, 106256, 5, 262144⟩
    (by decide) selected_cut_50453

theorem selected_cut_50454 : selected 10 ⟨1441436, by decide⟩
    (prefixPartial 11 106257) = some ⟨11, 2, 0, 1441436, 106257, 3965, 262144⟩ := by
  decide +kernel

theorem context_11_106257_1441436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106257 ⟨1441436, by decide⟩ :=
  accepted_of_selected 11 106257 ⟨1441436, by decide⟩ ⟨11, 2, 0, 1441436, 106257, 3965, 262144⟩
    (by decide) selected_cut_50454

theorem selected_cut_50455 : selected 10 ⟨1441508, by decide⟩
    (prefixPartial 11 106258) = some ⟨11, 2, 0, 1441508, 106258, 2697, 262144⟩ := by
  decide +kernel

theorem context_11_106258_1441508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106258 ⟨1441508, by decide⟩ :=
  accepted_of_selected 11 106258 ⟨1441508, by decide⟩ ⟨11, 2, 0, 1441508, 106258, 2697, 262144⟩
    (by decide) selected_cut_50455

theorem selected_cut_50456 : selected 10 ⟨1441563, by decide⟩
    (prefixPartial 11 106259) = some ⟨11, 2, 0, 1441563, 106259, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_106259_1441563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106259 ⟨1441563, by decide⟩ :=
  accepted_of_selected 11 106259 ⟨1441563, by decide⟩ ⟨11, 2, 0, 1441563, 106259, 2449, 262144⟩
    (by decide) selected_cut_50456

theorem unmarked_context_10_26564_1441564 : frontier 11 ⟨1441564, by decide⟩
    (prefixCache 10 26564) (prefixPartial 10 26564) = false := by
  decide +kernel

theorem node_context_10_26564_1441564 : EJMOriginalGlobalDAGData.nodes 11 ⟨1441564, by decide⟩ =
    .split (coordinate 10) (![⟨1441334, by decide⟩,⟨1441436, by decide⟩,⟨1441508, by decide⟩,⟨1441563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26564_1441564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26564 ⟨1441564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26564
    ⟨1441564, by decide⟩ (by decide) (![⟨1441334, by decide⟩,⟨1441436, by decide⟩,⟨1441508, by decide⟩,⟨1441563, by decide⟩]) unmarked_context_10_26564_1441564 node_context_10_26564_1441564
  intro a
  fin_cases a
  · exact context_11_106256_1441334
  · exact context_11_106257_1441436
  · exact context_11_106258_1441508
  · exact context_11_106259_1441563

theorem selected_cut_50457 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26565) = some ⟨10, 1, 0, 893098, 26565, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26565_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26565 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26565 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26565, 1, 1048576⟩
    (by decide) selected_cut_50457

theorem selected_cut_50458 : selected 10 ⟨1441631, by decide⟩
    (prefixPartial 11 106264) = some ⟨11, 2, 0, 1441631, 106264, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_106264_1441631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106264 ⟨1441631, by decide⟩ :=
  accepted_of_selected 11 106264 ⟨1441631, by decide⟩ ⟨11, 2, 0, 1441631, 106264, 2393, 262144⟩
    (by decide) selected_cut_50458

theorem selected_cut_50459 : selected 10 ⟨1441702, by decide⟩
    (prefixPartial 11 106265) = some ⟨11, 2, 0, 1441702, 106265, 3073, 262144⟩ := by
  decide +kernel

theorem context_11_106265_1441702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106265 ⟨1441702, by decide⟩ :=
  accepted_of_selected 11 106265 ⟨1441702, by decide⟩ ⟨11, 2, 0, 1441702, 106265, 3073, 262144⟩
    (by decide) selected_cut_50459

theorem selected_cut_50460 : selected 10 ⟨1441725, by decide⟩
    (prefixPartial 11 106266) = some ⟨11, 2, 0, 1441725, 106266, 1009, 262144⟩ := by
  decide +kernel

theorem context_11_106266_1441725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106266 ⟨1441725, by decide⟩ :=
  accepted_of_selected 11 106266 ⟨1441725, by decide⟩ ⟨11, 2, 0, 1441725, 106266, 1009, 262144⟩
    (by decide) selected_cut_50460

theorem selected_cut_50461 : selected 10 ⟨1441761, by decide⟩
    (prefixPartial 11 106267) = some ⟨11, 2, 0, 1441761, 106267, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_106267_1441761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106267 ⟨1441761, by decide⟩ :=
  accepted_of_selected 11 106267 ⟨1441761, by decide⟩ ⟨11, 2, 0, 1441761, 106267, 1801, 262144⟩
    (by decide) selected_cut_50461

theorem unmarked_context_10_26566_1441762 : frontier 11 ⟨1441762, by decide⟩
    (prefixCache 10 26566) (prefixPartial 10 26566) = false := by
  decide +kernel

theorem node_context_10_26566_1441762 : EJMOriginalGlobalDAGData.nodes 11 ⟨1441762, by decide⟩ =
    .split (coordinate 10) (![⟨1441631, by decide⟩,⟨1441702, by decide⟩,⟨1441725, by decide⟩,⟨1441761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26566_1441762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26566 ⟨1441762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26566
    ⟨1441762, by decide⟩ (by decide) (![⟨1441631, by decide⟩,⟨1441702, by decide⟩,⟨1441725, by decide⟩,⟨1441761, by decide⟩]) unmarked_context_10_26566_1441762 node_context_10_26566_1441762
  intro a
  fin_cases a
  · exact context_11_106264_1441631
  · exact context_11_106265_1441702
  · exact context_11_106266_1441725
  · exact context_11_106267_1441761

theorem selected_cut_50462 : selected 10 ⟨1441790, by decide⟩
    (prefixPartial 11 106268) = some ⟨11, 2, 0, 1441790, 106268, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_106268_1441790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106268 ⟨1441790, by decide⟩ :=
  accepted_of_selected 11 106268 ⟨1441790, by decide⟩ ⟨11, 2, 0, 1441790, 106268, 1537, 262144⟩
    (by decide) selected_cut_50462

theorem selected_cut_50463 : selected 10 ⟨1441843, by decide⟩
    (prefixPartial 11 106269) = some ⟨11, 2, 0, 1441843, 106269, 2289, 262144⟩ := by
  decide +kernel

theorem context_11_106269_1441843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106269 ⟨1441843, by decide⟩ :=
  accepted_of_selected 11 106269 ⟨1441843, by decide⟩ ⟨11, 2, 0, 1441843, 106269, 2289, 262144⟩
    (by decide) selected_cut_50463

theorem selected_cut_50464 : selected 10 ⟨1441888, by decide⟩
    (prefixPartial 11 106270) = some ⟨11, 2, 0, 1441888, 106270, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_106270_1441888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106270 ⟨1441888, by decide⟩ :=
  accepted_of_selected 11 106270 ⟨1441888, by decide⟩ ⟨11, 2, 0, 1441888, 106270, 2193, 262144⟩
    (by decide) selected_cut_50464

theorem selected_cut_50465 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106271) = some ⟨11, 1, 0, 977886, 106271, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106271_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106271 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106271 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106271, 1, 262144⟩
    (by decide) selected_cut_50465

theorem unmarked_context_10_26567_1441889 : frontier 11 ⟨1441889, by decide⟩
    (prefixCache 10 26567) (prefixPartial 10 26567) = false := by
  decide +kernel

theorem node_context_10_26567_1441889 : EJMOriginalGlobalDAGData.nodes 11 ⟨1441889, by decide⟩ =
    .split (coordinate 10) (![⟨1441790, by decide⟩,⟨1441843, by decide⟩,⟨1441888, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26567_1441889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26567 ⟨1441889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26567
    ⟨1441889, by decide⟩ (by decide) (![⟨1441790, by decide⟩,⟨1441843, by decide⟩,⟨1441888, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26567_1441889 node_context_10_26567_1441889
  intro a
  fin_cases a
  · exact context_11_106268_1441790
  · exact context_11_106269_1441843
  · exact context_11_106270_1441888
  · exact context_11_106271_977886

theorem unmarked_context_9_6641_1441890 : frontier 12 ⟨1441890, by decide⟩
    (prefixCache 9 6641) (prefixPartial 9 6641) = false := by
  decide +kernel

theorem node_context_9_6641_1441890 : EJMOriginalGlobalDAGData.nodes 12 ⟨1441890, by decide⟩ =
    .split (coordinate 9) (![⟨1441564, by decide⟩,⟨893098, by decide⟩,⟨1441762, by decide⟩,⟨1441889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6641_1441890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6641 ⟨1441890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6641
    ⟨1441890, by decide⟩ (by decide) (![⟨1441564, by decide⟩,⟨893098, by decide⟩,⟨1441762, by decide⟩,⟨1441889, by decide⟩]) unmarked_context_9_6641_1441890 node_context_9_6641_1441890
  intro a
  fin_cases a
  · exact context_10_26564_1441564
  · exact context_10_26565_893098
  · exact context_10_26566_1441762
  · exact context_10_26567_1441889

theorem selected_cut_50466 : selected 10 ⟨1441891, by decide⟩
    (prefixPartial 11 106272) = some ⟨11, 2, 0, 1441891, 106272, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106272_1441891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106272 ⟨1441891, by decide⟩ :=
  accepted_of_selected 11 106272 ⟨1441891, by decide⟩ ⟨11, 2, 0, 1441891, 106272, 5, 262144⟩
    (by decide) selected_cut_50466

theorem selected_cut_50467 : selected 10 ⟨1441938, by decide⟩
    (prefixPartial 11 106273) = some ⟨11, 2, 0, 1441938, 106273, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_106273_1441938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106273 ⟨1441938, by decide⟩ :=
  accepted_of_selected 11 106273 ⟨1441938, by decide⟩ ⟨11, 2, 0, 1441938, 106273, 1673, 262144⟩
    (by decide) selected_cut_50467

theorem selected_cut_50468 : selected 10 ⟨1442010, by decide⟩
    (prefixPartial 11 106274) = some ⟨11, 2, 0, 1442010, 106274, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_106274_1442010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106274 ⟨1442010, by decide⟩ :=
  accepted_of_selected 11 106274 ⟨1442010, by decide⟩ ⟨11, 2, 0, 1442010, 106274, 2397, 262144⟩
    (by decide) selected_cut_50468

theorem selected_cut_50469 : selected 10 ⟨1442039, by decide⟩
    (prefixPartial 11 106275) = some ⟨11, 2, 0, 1442039, 106275, 1297, 262144⟩ := by
  decide +kernel

theorem context_11_106275_1442039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106275 ⟨1442039, by decide⟩ :=
  accepted_of_selected 11 106275 ⟨1442039, by decide⟩ ⟨11, 2, 0, 1442039, 106275, 1297, 262144⟩
    (by decide) selected_cut_50469

theorem unmarked_context_10_26568_1442040 : frontier 11 ⟨1442040, by decide⟩
    (prefixCache 10 26568) (prefixPartial 10 26568) = false := by
  decide +kernel

theorem node_context_10_26568_1442040 : EJMOriginalGlobalDAGData.nodes 11 ⟨1442040, by decide⟩ =
    .split (coordinate 10) (![⟨1441891, by decide⟩,⟨1441938, by decide⟩,⟨1442010, by decide⟩,⟨1442039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26568_1442040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26568 ⟨1442040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26568
    ⟨1442040, by decide⟩ (by decide) (![⟨1441891, by decide⟩,⟨1441938, by decide⟩,⟨1442010, by decide⟩,⟨1442039, by decide⟩]) unmarked_context_10_26568_1442040 node_context_10_26568_1442040
  intro a
  fin_cases a
  · exact context_11_106272_1441891
  · exact context_11_106273_1441938
  · exact context_11_106274_1442010
  · exact context_11_106275_1442039

theorem selected_cut_50470 : selected 10 ⟨1442072, by decide⟩
    (prefixPartial 11 106276) = some ⟨11, 2, 0, 1442072, 106276, 1245, 262144⟩ := by
  decide +kernel

theorem context_11_106276_1442072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106276 ⟨1442072, by decide⟩ :=
  accepted_of_selected 11 106276 ⟨1442072, by decide⟩ ⟨11, 2, 0, 1442072, 106276, 1245, 262144⟩
    (by decide) selected_cut_50470

theorem selected_cut_50471 : selected 10 ⟨1420880, by decide⟩
    (prefixPartial 11 106277) = some ⟨11, 1, 0, 1420880, 106277, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106277_1420880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106277 ⟨1420880, by decide⟩ :=
  accepted_of_selected 11 106277 ⟨1420880, by decide⟩ ⟨11, 1, 0, 1420880, 106277, 1, 262144⟩
    (by decide) selected_cut_50471

theorem selected_cut_50472 : selected 10 ⟨1442121, by decide⟩
    (prefixPartial 11 106278) = some ⟨11, 2, 0, 1442121, 106278, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_106278_1442121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106278 ⟨1442121, by decide⟩ :=
  accepted_of_selected 11 106278 ⟨1442121, by decide⟩ ⟨11, 2, 0, 1442121, 106278, 1897, 262144⟩
    (by decide) selected_cut_50472

theorem selected_cut_50473 : selected 10 ⟨1442145, by decide⟩
    (prefixPartial 11 106279) = some ⟨11, 2, 0, 1442145, 106279, 957, 262144⟩ := by
  decide +kernel

theorem context_11_106279_1442145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106279 ⟨1442145, by decide⟩ :=
  accepted_of_selected 11 106279 ⟨1442145, by decide⟩ ⟨11, 2, 0, 1442145, 106279, 957, 262144⟩
    (by decide) selected_cut_50473

theorem unmarked_context_10_26569_1442146 : frontier 11 ⟨1442146, by decide⟩
    (prefixCache 10 26569) (prefixPartial 10 26569) = false := by
  decide +kernel

theorem node_context_10_26569_1442146 : EJMOriginalGlobalDAGData.nodes 11 ⟨1442146, by decide⟩ =
    .split (coordinate 10) (![⟨1442072, by decide⟩,⟨1420880, by decide⟩,⟨1442121, by decide⟩,⟨1442145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26569_1442146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26569 ⟨1442146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26569
    ⟨1442146, by decide⟩ (by decide) (![⟨1442072, by decide⟩,⟨1420880, by decide⟩,⟨1442121, by decide⟩,⟨1442145, by decide⟩]) unmarked_context_10_26569_1442146 node_context_10_26569_1442146
  intro a
  fin_cases a
  · exact context_11_106276_1442072
  · exact context_11_106277_1420880
  · exact context_11_106278_1442121
  · exact context_11_106279_1442145

theorem selected_cut_50474 : selected 11 ⟨1442154, by decide⟩
    (prefixPartial 10 26570) = some ⟨10, 2, 0, 1442154, 26570, 417, 1048576⟩ := by
  decide +kernel

theorem context_10_26570_1442154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26570 ⟨1442154, by decide⟩ :=
  accepted_of_selected 10 26570 ⟨1442154, by decide⟩ ⟨10, 2, 0, 1442154, 26570, 417, 1048576⟩
    (by decide) selected_cut_50474

theorem selected_cut_50475 : selected 11 ⟨1442221, by decide⟩
    (prefixPartial 10 26571) = some ⟨10, 2, 0, 1442221, 26571, 2709, 1048576⟩ := by
  decide +kernel

theorem context_10_26571_1442221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26571 ⟨1442221, by decide⟩ :=
  accepted_of_selected 10 26571 ⟨1442221, by decide⟩ ⟨10, 2, 0, 1442221, 26571, 2709, 1048576⟩
    (by decide) selected_cut_50475

theorem unmarked_context_9_6642_1442222 : frontier 12 ⟨1442222, by decide⟩
    (prefixCache 9 6642) (prefixPartial 9 6642) = false := by
  decide +kernel

theorem node_context_9_6642_1442222 : EJMOriginalGlobalDAGData.nodes 12 ⟨1442222, by decide⟩ =
    .split (coordinate 9) (![⟨1442040, by decide⟩,⟨1442146, by decide⟩,⟨1442154, by decide⟩,⟨1442221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6642_1442222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6642 ⟨1442222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6642
    ⟨1442222, by decide⟩ (by decide) (![⟨1442040, by decide⟩,⟨1442146, by decide⟩,⟨1442154, by decide⟩,⟨1442221, by decide⟩]) unmarked_context_9_6642_1442222 node_context_9_6642_1442222
  intro a
  fin_cases a
  · exact context_10_26568_1442040
  · exact context_10_26569_1442146
  · exact context_10_26570_1442154
  · exact context_10_26571_1442221

theorem selected_cut_50476 : selected 12 ⟨1442328, by decide⟩
    (prefixPartial 9 6643) = some ⟨9, 2, 0, 1442328, 6643, 3097, 4194304⟩ := by
  decide +kernel

theorem context_9_6643_1442328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6643 ⟨1442328, by decide⟩ :=
  accepted_of_selected 9 6643 ⟨1442328, by decide⟩ ⟨9, 2, 0, 1442328, 6643, 3097, 4194304⟩
    (by decide) selected_cut_50476

theorem unmarked_context_8_1660_1442329 : frontier 13 ⟨1442329, by decide⟩
    (prefixCache 8 1660) (prefixPartial 8 1660) = false := by
  decide +kernel

theorem node_context_8_1660_1442329 : EJMOriginalGlobalDAGData.nodes 13 ⟨1442329, by decide⟩ =
    .split (coordinate 8) (![⟨1441332, by decide⟩,⟨1441890, by decide⟩,⟨1442222, by decide⟩,⟨1442328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1660_1442329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1660 ⟨1442329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1660
    ⟨1442329, by decide⟩ (by decide) (![⟨1441332, by decide⟩,⟨1441890, by decide⟩,⟨1442222, by decide⟩,⟨1442328, by decide⟩]) unmarked_context_8_1660_1442329 node_context_8_1660_1442329
  intro a
  fin_cases a
  · exact context_9_6640_1441332
  · exact context_9_6641_1441890
  · exact context_9_6642_1442222
  · exact context_9_6643_1442328

theorem selected_cut_50477 : selected 11 ⟨1442392, by decide⟩
    (prefixPartial 10 26576) = some ⟨10, 2, 0, 1442392, 26576, 2385, 1048576⟩ := by
  decide +kernel

theorem context_10_26576_1442392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26576 ⟨1442392, by decide⟩ :=
  accepted_of_selected 10 26576 ⟨1442392, by decide⟩ ⟨10, 2, 0, 1442392, 26576, 2385, 1048576⟩
    (by decide) selected_cut_50477

theorem selected_cut_50478 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425232) = some ⟨12, 1, 0, 1415033, 425232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425232_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425232 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425232 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425232, 1, 65536⟩
    (by decide) selected_cut_50478

theorem selected_cut_50479 : selected 9 ⟨1442442, by decide⟩
    (prefixPartial 12 425233) = some ⟨12, 2, 0, 1442442, 425233, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_425233_1442442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425233 ⟨1442442, by decide⟩ :=
  accepted_of_selected 12 425233 ⟨1442442, by decide⟩ ⟨12, 2, 0, 1442442, 425233, 1813, 65536⟩
    (by decide) selected_cut_50479

theorem selected_cut_50480 : selected 9 ⟨1442491, by decide⟩
    (prefixPartial 12 425234) = some ⟨12, 2, 0, 1442491, 425234, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_425234_1442491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425234 ⟨1442491, by decide⟩ :=
  accepted_of_selected 12 425234 ⟨1442491, by decide⟩ ⟨12, 2, 0, 1442491, 425234, 2009, 65536⟩
    (by decide) selected_cut_50480

theorem selected_cut_50481 : selected 9 ⟨1442531, by decide⟩
    (prefixPartial 12 425235) = some ⟨12, 2, 0, 1442531, 425235, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_425235_1442531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425235 ⟨1442531, by decide⟩ :=
  accepted_of_selected 12 425235 ⟨1442531, by decide⟩ ⟨12, 2, 0, 1442531, 425235, 1985, 65536⟩
    (by decide) selected_cut_50481

theorem unmarked_context_11_106308_1442532 : frontier 10 ⟨1442532, by decide⟩
    (prefixCache 11 106308) (prefixPartial 11 106308) = false := by
  decide +kernel

theorem node_context_11_106308_1442532 : EJMOriginalGlobalDAGData.nodes 10 ⟨1442532, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1442442, by decide⟩,⟨1442491, by decide⟩,⟨1442531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106308_1442532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106308 ⟨1442532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106308
    ⟨1442532, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1442442, by decide⟩,⟨1442491, by decide⟩,⟨1442531, by decide⟩]) unmarked_context_11_106308_1442532 node_context_11_106308_1442532
  intro a
  fin_cases a
  · exact context_12_425232_1415033
  · exact context_12_425233_1442442
  · exact context_12_425234_1442491
  · exact context_12_425235_1442531

theorem selected_cut_50482 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 106309) = some ⟨11, 1, 0, 1241271, 106309, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106309_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106309 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 106309 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 106309, 1, 262144⟩
    (by decide) selected_cut_50482

theorem selected_cut_50483 : selected 10 ⟨1442615, by decide⟩
    (prefixPartial 11 106310) = some ⟨11, 2, 0, 1442615, 106310, 3633, 262144⟩ := by
  decide +kernel

theorem context_11_106310_1442615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106310 ⟨1442615, by decide⟩ :=
  accepted_of_selected 11 106310 ⟨1442615, by decide⟩ ⟨11, 2, 0, 1442615, 106310, 3633, 262144⟩
    (by decide) selected_cut_50483

theorem selected_cut_50484 : selected 10 ⟨1442691, by decide⟩
    (prefixPartial 11 106311) = some ⟨11, 2, 0, 1442691, 106311, 3529, 262144⟩ := by
  decide +kernel

theorem context_11_106311_1442691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106311 ⟨1442691, by decide⟩ :=
  accepted_of_selected 11 106311 ⟨1442691, by decide⟩ ⟨11, 2, 0, 1442691, 106311, 3529, 262144⟩
    (by decide) selected_cut_50484

theorem unmarked_context_10_26577_1442692 : frontier 11 ⟨1442692, by decide⟩
    (prefixCache 10 26577) (prefixPartial 10 26577) = false := by
  decide +kernel

theorem node_context_10_26577_1442692 : EJMOriginalGlobalDAGData.nodes 11 ⟨1442692, by decide⟩ =
    .split (coordinate 10) (![⟨1442532, by decide⟩,⟨1241271, by decide⟩,⟨1442615, by decide⟩,⟨1442691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26577_1442692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26577 ⟨1442692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26577
    ⟨1442692, by decide⟩ (by decide) (![⟨1442532, by decide⟩,⟨1241271, by decide⟩,⟨1442615, by decide⟩,⟨1442691, by decide⟩]) unmarked_context_10_26577_1442692 node_context_10_26577_1442692
  intro a
  fin_cases a
  · exact context_11_106308_1442532
  · exact context_11_106309_1241271
  · exact context_11_106310_1442615
  · exact context_11_106311_1442691

theorem selected_cut_50485 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 425248) = some ⟨12, 1, 0, 435160, 425248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425248_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425248 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 425248 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 425248, 1, 65536⟩
    (by decide) selected_cut_50485

theorem selected_cut_50486 : selected 9 ⟨1442747, by decide⟩
    (prefixPartial 12 425249) = some ⟨12, 2, 0, 1442747, 425249, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_425249_1442747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425249 ⟨1442747, by decide⟩ :=
  accepted_of_selected 12 425249 ⟨1442747, by decide⟩ ⟨12, 2, 0, 1442747, 425249, 2193, 65536⟩
    (by decide) selected_cut_50486

theorem selected_cut_50487 : selected 9 ⟨1442808, by decide⟩
    (prefixPartial 12 425250) = some ⟨12, 2, 0, 1442808, 425250, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_425250_1442808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425250 ⟨1442808, by decide⟩ :=
  accepted_of_selected 12 425250 ⟨1442808, by decide⟩ ⟨12, 2, 0, 1442808, 425250, 2281, 65536⟩
    (by decide) selected_cut_50487

theorem selected_cut_50488 : selected 9 ⟨1442853, by decide⟩
    (prefixPartial 12 425251) = some ⟨12, 2, 0, 1442853, 425251, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_425251_1442853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425251 ⟨1442853, by decide⟩ :=
  accepted_of_selected 12 425251 ⟨1442853, by decide⟩ ⟨12, 2, 0, 1442853, 425251, 2033, 65536⟩
    (by decide) selected_cut_50488

theorem unmarked_context_11_106312_1442854 : frontier 10 ⟨1442854, by decide⟩
    (prefixCache 11 106312) (prefixPartial 11 106312) = false := by
  decide +kernel

theorem node_context_11_106312_1442854 : EJMOriginalGlobalDAGData.nodes 10 ⟨1442854, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1442747, by decide⟩,⟨1442808, by decide⟩,⟨1442853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106312_1442854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106312 ⟨1442854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106312
    ⟨1442854, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1442747, by decide⟩,⟨1442808, by decide⟩,⟨1442853, by decide⟩]) unmarked_context_11_106312_1442854 node_context_11_106312_1442854
  intro a
  fin_cases a
  · exact context_12_425248_435160
  · exact context_12_425249_1442747
  · exact context_12_425250_1442808
  · exact context_12_425251_1442853

theorem selected_cut_50489 : selected 10 ⟨1442936, by decide⟩
    (prefixPartial 11 106313) = some ⟨11, 2, 0, 1442936, 106313, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_106313_1442936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106313 ⟨1442936, by decide⟩ :=
  accepted_of_selected 11 106313 ⟨1442936, by decide⟩ ⟨11, 2, 0, 1442936, 106313, 3717, 262144⟩
    (by decide) selected_cut_50489

theorem selected_cut_50490 : selected 10 ⟨1442982, by decide⟩
    (prefixPartial 11 106314) = some ⟨11, 2, 0, 1442982, 106314, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_106314_1442982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106314 ⟨1442982, by decide⟩ :=
  accepted_of_selected 11 106314 ⟨1442982, by decide⟩ ⟨11, 2, 0, 1442982, 106314, 1749, 262144⟩
    (by decide) selected_cut_50490

theorem selected_cut_50491 : selected 10 ⟨1443065, by decide⟩
    (prefixPartial 11 106315) = some ⟨11, 2, 0, 1443065, 106315, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_106315_1443065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106315 ⟨1443065, by decide⟩ :=
  accepted_of_selected 11 106315 ⟨1443065, by decide⟩ ⟨11, 2, 0, 1443065, 106315, 3653, 262144⟩
    (by decide) selected_cut_50491

theorem unmarked_context_10_26578_1443066 : frontier 11 ⟨1443066, by decide⟩
    (prefixCache 10 26578) (prefixPartial 10 26578) = false := by
  decide +kernel

theorem node_context_10_26578_1443066 : EJMOriginalGlobalDAGData.nodes 11 ⟨1443066, by decide⟩ =
    .split (coordinate 10) (![⟨1442854, by decide⟩,⟨1442936, by decide⟩,⟨1442982, by decide⟩,⟨1443065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26578_1443066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26578 ⟨1443066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26578
    ⟨1443066, by decide⟩ (by decide) (![⟨1442854, by decide⟩,⟨1442936, by decide⟩,⟨1442982, by decide⟩,⟨1443065, by decide⟩]) unmarked_context_10_26578_1443066 node_context_10_26578_1443066
  intro a
  fin_cases a
  · exact context_11_106312_1442854
  · exact context_11_106313_1442936
  · exact context_11_106314_1442982
  · exact context_11_106315_1443065

theorem selected_cut_50492 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 425264) = some ⟨12, 1, 0, 1416143, 425264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425264_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425264 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 425264 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 425264, 1, 65536⟩
    (by decide) selected_cut_50492

theorem selected_cut_50493 : selected 9 ⟨1443100, by decide⟩
    (prefixPartial 12 425265) = some ⟨12, 2, 0, 1443100, 425265, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_425265_1443100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425265 ⟨1443100, by decide⟩ :=
  accepted_of_selected 12 425265 ⟨1443100, by decide⟩ ⟨12, 2, 0, 1443100, 425265, 1573, 65536⟩
    (by decide) selected_cut_50493

theorem selected_cut_50494 : selected 9 ⟨1443135, by decide⟩
    (prefixPartial 12 425266) = some ⟨12, 2, 0, 1443135, 425266, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_425266_1443135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425266 ⟨1443135, by decide⟩ :=
  accepted_of_selected 12 425266 ⟨1443135, by decide⟩ ⟨12, 2, 0, 1443135, 425266, 1493, 65536⟩
    (by decide) selected_cut_50494

theorem selected_cut_50495 : selected 9 ⟨1443174, by decide⟩
    (prefixPartial 12 425267) = some ⟨12, 2, 0, 1443174, 425267, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_425267_1443174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425267 ⟨1443174, by decide⟩ :=
  accepted_of_selected 12 425267 ⟨1443174, by decide⟩ ⟨12, 2, 0, 1443174, 425267, 1537, 65536⟩
    (by decide) selected_cut_50495

theorem unmarked_context_11_106316_1443175 : frontier 10 ⟨1443175, by decide⟩
    (prefixCache 11 106316) (prefixPartial 11 106316) = false := by
  decide +kernel

theorem node_context_11_106316_1443175 : EJMOriginalGlobalDAGData.nodes 10 ⟨1443175, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1443100, by decide⟩,⟨1443135, by decide⟩,⟨1443174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106316_1443175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106316 ⟨1443175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106316
    ⟨1443175, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1443100, by decide⟩,⟨1443135, by decide⟩,⟨1443174, by decide⟩]) unmarked_context_11_106316_1443175 node_context_11_106316_1443175
  intro a
  fin_cases a
  · exact context_12_425264_1416143
  · exact context_12_425265_1443100
  · exact context_12_425266_1443135
  · exact context_12_425267_1443174

theorem selected_cut_50496 : selected 10 ⟨1443237, by decide⟩
    (prefixPartial 11 106317) = some ⟨11, 2, 0, 1443237, 106317, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_106317_1443237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106317 ⟨1443237, by decide⟩ :=
  accepted_of_selected 11 106317 ⟨1443237, by decide⟩ ⟨11, 2, 0, 1443237, 106317, 2737, 262144⟩
    (by decide) selected_cut_50496

theorem selected_cut_50497 : selected 10 ⟨1443330, by decide⟩
    (prefixPartial 11 106318) = some ⟨11, 2, 0, 1443330, 106318, 3265, 262144⟩ := by
  decide +kernel

theorem context_11_106318_1443330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106318 ⟨1443330, by decide⟩ :=
  accepted_of_selected 11 106318 ⟨1443330, by decide⟩ ⟨11, 2, 0, 1443330, 106318, 3265, 262144⟩
    (by decide) selected_cut_50497

theorem selected_cut_50498 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106319) = some ⟨11, 1, 0, 977886, 106319, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106319_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106319 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106319 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106319, 1, 262144⟩
    (by decide) selected_cut_50498

theorem unmarked_context_10_26579_1443331 : frontier 11 ⟨1443331, by decide⟩
    (prefixCache 10 26579) (prefixPartial 10 26579) = false := by
  decide +kernel

theorem node_context_10_26579_1443331 : EJMOriginalGlobalDAGData.nodes 11 ⟨1443331, by decide⟩ =
    .split (coordinate 10) (![⟨1443175, by decide⟩,⟨1443237, by decide⟩,⟨1443330, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26579_1443331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26579 ⟨1443331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26579
    ⟨1443331, by decide⟩ (by decide) (![⟨1443175, by decide⟩,⟨1443237, by decide⟩,⟨1443330, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26579_1443331 node_context_10_26579_1443331
  intro a
  fin_cases a
  · exact context_11_106316_1443175
  · exact context_11_106317_1443237
  · exact context_11_106318_1443330
  · exact context_11_106319_977886

theorem unmarked_context_9_6644_1443332 : frontier 12 ⟨1443332, by decide⟩
    (prefixCache 9 6644) (prefixPartial 9 6644) = false := by
  decide +kernel

theorem node_context_9_6644_1443332 : EJMOriginalGlobalDAGData.nodes 12 ⟨1443332, by decide⟩ =
    .split (coordinate 9) (![⟨1442392, by decide⟩,⟨1442692, by decide⟩,⟨1443066, by decide⟩,⟨1443331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6644_1443332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6644 ⟨1443332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6644
    ⟨1443332, by decide⟩ (by decide) (![⟨1442392, by decide⟩,⟨1442692, by decide⟩,⟨1443066, by decide⟩,⟨1443331, by decide⟩]) unmarked_context_9_6644_1443332 node_context_9_6644_1443332
  intro a
  fin_cases a
  · exact context_10_26576_1442392
  · exact context_10_26577_1442692
  · exact context_10_26578_1443066
  · exact context_10_26579_1443331

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
