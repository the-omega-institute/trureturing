/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover004
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00482 : selected 10 ⟨22732, by decide⟩
    (prefixPartial 11 359) = some ⟨11, 2, 0, 22732, 359, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_359_22732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 359 ⟨22732, by decide⟩ :=
  accepted_of_selected 11 359 ⟨22732, by decide⟩ ⟨11, 2, 0, 22732, 359, 2897, 262144⟩
    (by decide) selected_cut_00482

theorem unmarked_context_10_89_22733 : frontier 11 ⟨22733, by decide⟩
    (prefixCache 10 89) (prefixPartial 10 89) = false := by
  decide +kernel

theorem node_context_10_89_22733 : EJMOriginalGlobalDAGData.nodes 11 ⟨22733, by decide⟩ =
    .split (coordinate 10) (![⟨22078, by decide⟩,⟨22469, by decide⟩,⟨22610, by decide⟩,⟨22732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_89_22733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 89 ⟨22733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 89
    ⟨22733, by decide⟩ (by decide) (![⟨22078, by decide⟩,⟨22469, by decide⟩,⟨22610, by decide⟩,⟨22732, by decide⟩]) unmarked_context_10_89_22733 node_context_10_89_22733
  intro a
  fin_cases a
  · exact context_11_356_22078
  · exact context_11_357_22469
  · exact context_11_358_22610
  · exact context_11_359_22732

theorem selected_cut_00483 : selected 11 ⟨22975, by decide⟩
    (prefixPartial 10 90) = some ⟨10, 2, 0, 22975, 90, 3949, 1048576⟩ := by
  decide +kernel

theorem context_10_90_22975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 90 ⟨22975, by decide⟩ :=
  accepted_of_selected 10 90 ⟨22975, by decide⟩ ⟨10, 2, 0, 22975, 90, 3949, 1048576⟩
    (by decide) selected_cut_00483

theorem selected_cut_00484 : selected 11 ⟨23020, by decide⟩
    (prefixPartial 10 91) = some ⟨10, 2, 0, 23020, 91, 501, 1048576⟩ := by
  decide +kernel

theorem context_10_91_23020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 91 ⟨23020, by decide⟩ :=
  accepted_of_selected 10 91 ⟨23020, by decide⟩ ⟨10, 2, 0, 23020, 91, 501, 1048576⟩
    (by decide) selected_cut_00484

theorem unmarked_context_9_22_23021 : frontier 12 ⟨23021, by decide⟩
    (prefixCache 9 22) (prefixPartial 9 22) = false := by
  decide +kernel

theorem node_context_9_22_23021 : EJMOriginalGlobalDAGData.nodes 12 ⟨23021, by decide⟩ =
    .split (coordinate 9) (![⟨21885, by decide⟩,⟨22733, by decide⟩,⟨22975, by decide⟩,⟨23020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_22_23021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 22 ⟨23021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 22
    ⟨23021, by decide⟩ (by decide) (![⟨21885, by decide⟩,⟨22733, by decide⟩,⟨22975, by decide⟩,⟨23020, by decide⟩]) unmarked_context_9_22_23021 node_context_9_22_23021
  intro a
  fin_cases a
  · exact context_10_88_21885
  · exact context_10_89_22733
  · exact context_10_90_22975
  · exact context_10_91_23020

theorem selected_cut_00485 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 23) = some ⟨9, 1, 0, 4601, 23, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_23_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 23 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 23 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 23, 1, 4194304⟩
    (by decide) selected_cut_00485

theorem unmarked_context_8_5_23022 : frontier 13 ⟨23022, by decide⟩
    (prefixCache 8 5) (prefixPartial 8 5) = false := by
  decide +kernel

theorem node_context_8_5_23022 : EJMOriginalGlobalDAGData.nodes 13 ⟨23022, by decide⟩ =
    .split (coordinate 8) (![⟨18952, by decide⟩,⟨20846, by decide⟩,⟨23021, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_5_23022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 5 ⟨23022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 5
    ⟨23022, by decide⟩ (by decide) (![⟨18952, by decide⟩,⟨20846, by decide⟩,⟨23021, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_5_23022 node_context_8_5_23022
  intro a
  fin_cases a
  · exact context_9_20_18952
  · exact context_9_21_20846
  · exact context_9_22_23021
  · exact context_9_23_4601

theorem selected_cut_00486 : selected 8 ⟨23159, by decide⟩
    (prefixPartial 13 6144) = some ⟨13, 2, 0, 23159, 6144, 3581, 16384⟩ := by
  decide +kernel

theorem context_13_6144_23159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6144 ⟨23159, by decide⟩ :=
  accepted_of_selected 13 6144 ⟨23159, by decide⟩ ⟨13, 2, 0, 23159, 6144, 3581, 16384⟩
    (by decide) selected_cut_00486

theorem selected_cut_00487 : selected 7 ⟨23183, by decide⟩
    (prefixPartial 14 24580) = some ⟨14, 2, 0, 23183, 24580, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_24580_23183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24580 ⟨23183, by decide⟩ :=
  accepted_of_selected 14 24580 ⟨23183, by decide⟩ ⟨14, 2, 0, 23183, 24580, 1097, 4096⟩
    (by decide) selected_cut_00487

theorem selected_cut_00488 : selected 7 ⟨23208, by decide⟩
    (prefixPartial 14 24581) = some ⟨14, 2, 0, 23208, 24581, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_24581_23208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24581 ⟨23208, by decide⟩ :=
  accepted_of_selected 14 24581 ⟨23208, by decide⟩ ⟨14, 2, 0, 23208, 24581, 1081, 4096⟩
    (by decide) selected_cut_00488

theorem selected_cut_00489 : selected 7 ⟨23242, by decide⟩
    (prefixPartial 14 24582) = some ⟨14, 2, 0, 23242, 24582, 1149, 4096⟩ := by
  decide +kernel

theorem context_14_24582_23242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24582 ⟨23242, by decide⟩ :=
  accepted_of_selected 14 24582 ⟨23242, by decide⟩ ⟨14, 2, 0, 23242, 24582, 1149, 4096⟩
    (by decide) selected_cut_00489

theorem selected_cut_00490 : selected 7 ⟨23285, by decide⟩
    (prefixPartial 14 24583) = some ⟨14, 2, 0, 23285, 24583, 965, 4096⟩ := by
  decide +kernel

theorem context_14_24583_23285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24583 ⟨23285, by decide⟩ :=
  accepted_of_selected 14 24583 ⟨23285, by decide⟩ ⟨14, 2, 0, 23285, 24583, 965, 4096⟩
    (by decide) selected_cut_00490

theorem unmarked_context_13_6145_23286 : frontier 8 ⟨23286, by decide⟩
    (prefixCache 13 6145) (prefixPartial 13 6145) = false := by
  decide +kernel

theorem node_context_13_6145_23286 : EJMOriginalGlobalDAGData.nodes 8 ⟨23286, by decide⟩ =
    .split (coordinate 13) (![⟨23183, by decide⟩,⟨23208, by decide⟩,⟨23242, by decide⟩,⟨23285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6145_23286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6145 ⟨23286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6145
    ⟨23286, by decide⟩ (by decide) (![⟨23183, by decide⟩,⟨23208, by decide⟩,⟨23242, by decide⟩,⟨23285, by decide⟩]) unmarked_context_13_6145_23286 node_context_13_6145_23286
  intro a
  fin_cases a
  · exact context_14_24580_23183
  · exact context_14_24581_23208
  · exact context_14_24582_23242
  · exact context_14_24583_23285

theorem selected_cut_00491 : selected 8 ⟨1982, by decide⟩
    (prefixPartial 13 6146) = some ⟨13, 1, 0, 1982, 6146, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6146_1982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6146 ⟨1982, by decide⟩ :=
  accepted_of_selected 13 6146 ⟨1982, by decide⟩ ⟨13, 1, 0, 1982, 6146, 1, 16384⟩
    (by decide) selected_cut_00491

theorem selected_cut_00492 : selected 8 ⟨23319, by decide⟩
    (prefixPartial 13 6147) = some ⟨13, 2, 0, 23319, 6147, 861, 16384⟩ := by
  decide +kernel

theorem context_13_6147_23319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6147 ⟨23319, by decide⟩ :=
  accepted_of_selected 13 6147 ⟨23319, by decide⟩ ⟨13, 2, 0, 23319, 6147, 861, 16384⟩
    (by decide) selected_cut_00492

theorem unmarked_context_12_1536_23320 : frontier 9 ⟨23320, by decide⟩
    (prefixCache 12 1536) (prefixPartial 12 1536) = false := by
  decide +kernel

theorem node_context_12_1536_23320 : EJMOriginalGlobalDAGData.nodes 9 ⟨23320, by decide⟩ =
    .split (coordinate 12) (![⟨23159, by decide⟩,⟨23286, by decide⟩,⟨1982, by decide⟩,⟨23319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1536_23320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1536 ⟨23320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1536
    ⟨23320, by decide⟩ (by decide) (![⟨23159, by decide⟩,⟨23286, by decide⟩,⟨1982, by decide⟩,⟨23319, by decide⟩]) unmarked_context_12_1536_23320 node_context_12_1536_23320
  intro a
  fin_cases a
  · exact context_13_6144_23159
  · exact context_13_6145_23286
  · exact context_13_6146_1982
  · exact context_13_6147_23319

theorem selected_cut_00493 : selected 7 ⟨23360, by decide⟩
    (prefixPartial 14 24592) = some ⟨14, 2, 0, 23360, 24592, 1577, 4096⟩ := by
  decide +kernel

theorem context_14_24592_23360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24592 ⟨23360, by decide⟩ :=
  accepted_of_selected 14 24592 ⟨23360, by decide⟩ ⟨14, 2, 0, 23360, 24592, 1577, 4096⟩
    (by decide) selected_cut_00493

theorem selected_cut_00494 : selected 7 ⟨23390, by decide⟩
    (prefixPartial 14 24593) = some ⟨14, 2, 0, 23390, 24593, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_24593_23390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24593 ⟨23390, by decide⟩ :=
  accepted_of_selected 14 24593 ⟨23390, by decide⟩ ⟨14, 2, 0, 23390, 24593, 1241, 4096⟩
    (by decide) selected_cut_00494

theorem selected_cut_00495 : selected 7 ⟨23413, by decide⟩
    (prefixPartial 14 24594) = some ⟨14, 2, 0, 23413, 24594, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_24594_23413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24594 ⟨23413, by decide⟩ :=
  accepted_of_selected 14 24594 ⟨23413, by decide⟩ ⟨14, 2, 0, 23413, 24594, 1113, 4096⟩
    (by decide) selected_cut_00495

theorem selected_cut_00496 : selected 7 ⟨23429, by decide⟩
    (prefixPartial 14 24595) = some ⟨14, 2, 0, 23429, 24595, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_24595_23429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24595 ⟨23429, by decide⟩ :=
  accepted_of_selected 14 24595 ⟨23429, by decide⟩ ⟨14, 2, 0, 23429, 24595, 1161, 4096⟩
    (by decide) selected_cut_00496

theorem unmarked_context_13_6148_23430 : frontier 8 ⟨23430, by decide⟩
    (prefixCache 13 6148) (prefixPartial 13 6148) = false := by
  decide +kernel

theorem node_context_13_6148_23430 : EJMOriginalGlobalDAGData.nodes 8 ⟨23430, by decide⟩ =
    .split (coordinate 13) (![⟨23360, by decide⟩,⟨23390, by decide⟩,⟨23413, by decide⟩,⟨23429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6148_23430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6148 ⟨23430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6148
    ⟨23430, by decide⟩ (by decide) (![⟨23360, by decide⟩,⟨23390, by decide⟩,⟨23413, by decide⟩,⟨23429, by decide⟩]) unmarked_context_13_6148_23430 node_context_13_6148_23430
  intro a
  fin_cases a
  · exact context_14_24592_23360
  · exact context_14_24593_23390
  · exact context_14_24594_23413
  · exact context_14_24595_23429

theorem selected_cut_00497 : selected 8 ⟨23503, by decide⟩
    (prefixPartial 13 6149) = some ⟨13, 2, 0, 23503, 6149, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_6149_23503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6149 ⟨23503, by decide⟩ :=
  accepted_of_selected 13 6149 ⟨23503, by decide⟩ ⟨13, 2, 0, 23503, 6149, 3165, 16384⟩
    (by decide) selected_cut_00497

theorem selected_cut_00498 : selected 8 ⟨23542, by decide⟩
    (prefixPartial 13 6150) = some ⟨13, 2, 0, 23542, 6150, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_6150_23542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6150 ⟨23542, by decide⟩ :=
  accepted_of_selected 13 6150 ⟨23542, by decide⟩ ⟨13, 2, 0, 23542, 6150, 2053, 16384⟩
    (by decide) selected_cut_00498

theorem selected_cut_00499 : selected 8 ⟨23570, by decide⟩
    (prefixPartial 13 6151) = some ⟨13, 2, 0, 23570, 6151, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_6151_23570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6151 ⟨23570, by decide⟩ :=
  accepted_of_selected 13 6151 ⟨23570, by decide⟩ ⟨13, 2, 0, 23570, 6151, 1253, 16384⟩
    (by decide) selected_cut_00499

theorem unmarked_context_12_1537_23571 : frontier 9 ⟨23571, by decide⟩
    (prefixCache 12 1537) (prefixPartial 12 1537) = false := by
  decide +kernel

theorem node_context_12_1537_23571 : EJMOriginalGlobalDAGData.nodes 9 ⟨23571, by decide⟩ =
    .split (coordinate 12) (![⟨23430, by decide⟩,⟨23503, by decide⟩,⟨23542, by decide⟩,⟨23570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1537_23571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1537 ⟨23571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1537
    ⟨23571, by decide⟩ (by decide) (![⟨23430, by decide⟩,⟨23503, by decide⟩,⟨23542, by decide⟩,⟨23570, by decide⟩]) unmarked_context_12_1537_23571 node_context_12_1537_23571
  intro a
  fin_cases a
  · exact context_13_6148_23430
  · exact context_13_6149_23503
  · exact context_13_6150_23542
  · exact context_13_6151_23570

theorem selected_cut_00500 : selected 7 ⟨23595, by decide⟩
    (prefixPartial 14 24608) = some ⟨14, 2, 0, 23595, 24608, 1309, 4096⟩ := by
  decide +kernel

theorem context_14_24608_23595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24608 ⟨23595, by decide⟩ :=
  accepted_of_selected 14 24608 ⟨23595, by decide⟩ ⟨14, 2, 0, 23595, 24608, 1309, 4096⟩
    (by decide) selected_cut_00500

theorem selected_cut_00501 : selected 7 ⟨23614, by decide⟩
    (prefixPartial 14 24609) = some ⟨14, 2, 0, 23614, 24609, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_24609_23614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24609 ⟨23614, by decide⟩ :=
  accepted_of_selected 14 24609 ⟨23614, by decide⟩ ⟨14, 2, 0, 23614, 24609, 1077, 4096⟩
    (by decide) selected_cut_00501

theorem selected_cut_00502 : selected 7 ⟨23630, by decide⟩
    (prefixPartial 14 24610) = some ⟨14, 2, 0, 23630, 24610, 909, 4096⟩ := by
  decide +kernel

theorem context_14_24610_23630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24610 ⟨23630, by decide⟩ :=
  accepted_of_selected 14 24610 ⟨23630, by decide⟩ ⟨14, 2, 0, 23630, 24610, 909, 4096⟩
    (by decide) selected_cut_00502

theorem selected_cut_00503 : selected 7 ⟨23644, by decide⟩
    (prefixPartial 14 24611) = some ⟨14, 2, 0, 23644, 24611, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_24611_23644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24611 ⟨23644, by decide⟩ :=
  accepted_of_selected 14 24611 ⟨23644, by decide⟩ ⟨14, 2, 0, 23644, 24611, 1037, 4096⟩
    (by decide) selected_cut_00503

theorem unmarked_context_13_6152_23645 : frontier 8 ⟨23645, by decide⟩
    (prefixCache 13 6152) (prefixPartial 13 6152) = false := by
  decide +kernel

theorem node_context_13_6152_23645 : EJMOriginalGlobalDAGData.nodes 8 ⟨23645, by decide⟩ =
    .split (coordinate 13) (![⟨23595, by decide⟩,⟨23614, by decide⟩,⟨23630, by decide⟩,⟨23644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6152_23645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6152 ⟨23645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6152
    ⟨23645, by decide⟩ (by decide) (![⟨23595, by decide⟩,⟨23614, by decide⟩,⟨23630, by decide⟩,⟨23644, by decide⟩]) unmarked_context_13_6152_23645 node_context_13_6152_23645
  intro a
  fin_cases a
  · exact context_14_24608_23595
  · exact context_14_24609_23614
  · exact context_14_24610_23630
  · exact context_14_24611_23644

theorem selected_cut_00504 : selected 8 ⟨23693, by decide⟩
    (prefixPartial 13 6153) = some ⟨13, 2, 0, 23693, 6153, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_6153_23693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6153 ⟨23693, by decide⟩ :=
  accepted_of_selected 13 6153 ⟨23693, by decide⟩ ⟨13, 2, 0, 23693, 6153, 3141, 16384⟩
    (by decide) selected_cut_00504

theorem selected_cut_00505 : selected 8 ⟨23721, by decide⟩
    (prefixPartial 13 6154) = some ⟨13, 2, 0, 23721, 6154, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_6154_23721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6154 ⟨23721, by decide⟩ :=
  accepted_of_selected 13 6154 ⟨23721, by decide⟩ ⟨13, 2, 0, 23721, 6154, 1841, 16384⟩
    (by decide) selected_cut_00505

theorem selected_cut_00506 : selected 8 ⟨23734, by decide⟩
    (prefixPartial 13 6155) = some ⟨13, 2, 0, 23734, 6155, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_6155_23734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6155 ⟨23734, by decide⟩ :=
  accepted_of_selected 13 6155 ⟨23734, by decide⟩ ⟨13, 2, 0, 23734, 6155, 1189, 16384⟩
    (by decide) selected_cut_00506

theorem unmarked_context_12_1538_23735 : frontier 9 ⟨23735, by decide⟩
    (prefixCache 12 1538) (prefixPartial 12 1538) = false := by
  decide +kernel

theorem node_context_12_1538_23735 : EJMOriginalGlobalDAGData.nodes 9 ⟨23735, by decide⟩ =
    .split (coordinate 12) (![⟨23645, by decide⟩,⟨23693, by decide⟩,⟨23721, by decide⟩,⟨23734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1538_23735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1538 ⟨23735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1538
    ⟨23735, by decide⟩ (by decide) (![⟨23645, by decide⟩,⟨23693, by decide⟩,⟨23721, by decide⟩,⟨23734, by decide⟩]) unmarked_context_12_1538_23735 node_context_12_1538_23735
  intro a
  fin_cases a
  · exact context_13_6152_23645
  · exact context_13_6153_23693
  · exact context_13_6154_23721
  · exact context_13_6155_23734

theorem selected_cut_00507 : selected 7 ⟨23767, by decide⟩
    (prefixPartial 14 24624) = some ⟨14, 2, 0, 23767, 24624, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_24624_23767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24624 ⟨23767, by decide⟩ :=
  accepted_of_selected 14 24624 ⟨23767, by decide⟩ ⟨14, 2, 0, 23767, 24624, 1433, 4096⟩
    (by decide) selected_cut_00507

theorem selected_cut_00508 : selected 7 ⟨23783, by decide⟩
    (prefixPartial 14 24625) = some ⟨14, 2, 0, 23783, 24625, 1261, 4096⟩ := by
  decide +kernel

theorem context_14_24625_23783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24625 ⟨23783, by decide⟩ :=
  accepted_of_selected 14 24625 ⟨23783, by decide⟩ ⟨14, 2, 0, 23783, 24625, 1261, 4096⟩
    (by decide) selected_cut_00508

theorem selected_cut_00509 : selected 7 ⟨23802, by decide⟩
    (prefixPartial 14 24626) = some ⟨14, 2, 0, 23802, 24626, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_24626_23802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24626 ⟨23802, by decide⟩ :=
  accepted_of_selected 14 24626 ⟨23802, by decide⟩ ⟨14, 2, 0, 23802, 24626, 1161, 4096⟩
    (by decide) selected_cut_00509

theorem selected_cut_00510 : selected 7 ⟨23817, by decide⟩
    (prefixPartial 14 24627) = some ⟨14, 2, 0, 23817, 24627, 1141, 4096⟩ := by
  decide +kernel

theorem context_14_24627_23817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24627 ⟨23817, by decide⟩ :=
  accepted_of_selected 14 24627 ⟨23817, by decide⟩ ⟨14, 2, 0, 23817, 24627, 1141, 4096⟩
    (by decide) selected_cut_00510

theorem unmarked_context_13_6156_23818 : frontier 8 ⟨23818, by decide⟩
    (prefixCache 13 6156) (prefixPartial 13 6156) = false := by
  decide +kernel

theorem node_context_13_6156_23818 : EJMOriginalGlobalDAGData.nodes 8 ⟨23818, by decide⟩ =
    .split (coordinate 13) (![⟨23767, by decide⟩,⟨23783, by decide⟩,⟨23802, by decide⟩,⟨23817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6156_23818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6156 ⟨23818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6156
    ⟨23818, by decide⟩ (by decide) (![⟨23767, by decide⟩,⟨23783, by decide⟩,⟨23802, by decide⟩,⟨23817, by decide⟩]) unmarked_context_13_6156_23818 node_context_13_6156_23818
  intro a
  fin_cases a
  · exact context_14_24624_23767
  · exact context_14_24625_23783
  · exact context_14_24626_23802
  · exact context_14_24627_23817

theorem selected_cut_00511 : selected 8 ⟨23881, by decide⟩
    (prefixPartial 13 6157) = some ⟨13, 2, 0, 23881, 6157, 3401, 16384⟩ := by
  decide +kernel

theorem context_13_6157_23881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6157 ⟨23881, by decide⟩ :=
  accepted_of_selected 13 6157 ⟨23881, by decide⟩ ⟨13, 2, 0, 23881, 6157, 3401, 16384⟩
    (by decide) selected_cut_00511

theorem selected_cut_00512 : selected 8 ⟨23929, by decide⟩
    (prefixPartial 13 6158) = some ⟨13, 2, 0, 23929, 6158, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_6158_23929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6158 ⟨23929, by decide⟩ :=
  accepted_of_selected 13 6158 ⟨23929, by decide⟩ ⟨13, 2, 0, 23929, 6158, 2201, 16384⟩
    (by decide) selected_cut_00512

theorem selected_cut_00513 : selected 8 ⟨23951, by decide⟩
    (prefixPartial 13 6159) = some ⟨13, 2, 0, 23951, 6159, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_6159_23951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6159 ⟨23951, by decide⟩ :=
  accepted_of_selected 13 6159 ⟨23951, by decide⟩ ⟨13, 2, 0, 23951, 6159, 1049, 16384⟩
    (by decide) selected_cut_00513

theorem unmarked_context_12_1539_23952 : frontier 9 ⟨23952, by decide⟩
    (prefixCache 12 1539) (prefixPartial 12 1539) = false := by
  decide +kernel

theorem node_context_12_1539_23952 : EJMOriginalGlobalDAGData.nodes 9 ⟨23952, by decide⟩ =
    .split (coordinate 12) (![⟨23818, by decide⟩,⟨23881, by decide⟩,⟨23929, by decide⟩,⟨23951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1539_23952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1539 ⟨23952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1539
    ⟨23952, by decide⟩ (by decide) (![⟨23818, by decide⟩,⟨23881, by decide⟩,⟨23929, by decide⟩,⟨23951, by decide⟩]) unmarked_context_12_1539_23952 node_context_12_1539_23952
  intro a
  fin_cases a
  · exact context_13_6156_23818
  · exact context_13_6157_23881
  · exact context_13_6158_23929
  · exact context_13_6159_23951

theorem unmarked_context_11_384_23953 : frontier 10 ⟨23953, by decide⟩
    (prefixCache 11 384) (prefixPartial 11 384) = false := by
  decide +kernel

theorem node_context_11_384_23953 : EJMOriginalGlobalDAGData.nodes 10 ⟨23953, by decide⟩ =
    .split (coordinate 11) (![⟨23320, by decide⟩,⟨23571, by decide⟩,⟨23735, by decide⟩,⟨23952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_384_23953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 384 ⟨23953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 384
    ⟨23953, by decide⟩ (by decide) (![⟨23320, by decide⟩,⟨23571, by decide⟩,⟨23735, by decide⟩,⟨23952, by decide⟩]) unmarked_context_11_384_23953 node_context_11_384_23953
  intro a
  fin_cases a
  · exact context_12_1536_23320
  · exact context_12_1537_23571
  · exact context_12_1538_23735
  · exact context_12_1539_23952

theorem selected_cut_00514 : selected 7 ⟨24007, by decide⟩
    (prefixPartial 14 24640) = some ⟨14, 2, 0, 24007, 24640, 2169, 4096⟩ := by
  decide +kernel

theorem context_14_24640_24007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24640 ⟨24007, by decide⟩ :=
  accepted_of_selected 14 24640 ⟨24007, by decide⟩ ⟨14, 2, 0, 24007, 24640, 2169, 4096⟩
    (by decide) selected_cut_00514

theorem selected_cut_00515 : selected 7 ⟨24031, by decide⟩
    (prefixPartial 14 24641) = some ⟨14, 2, 0, 24031, 24641, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_24641_24031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24641 ⟨24031, by decide⟩ :=
  accepted_of_selected 14 24641 ⟨24031, by decide⟩ ⟨14, 2, 0, 24031, 24641, 1161, 4096⟩
    (by decide) selected_cut_00515

theorem selected_cut_00516 : selected 7 ⟨24054, by decide⟩
    (prefixPartial 14 24642) = some ⟨14, 2, 0, 24054, 24642, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_24642_24054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24642 ⟨24054, by decide⟩ :=
  accepted_of_selected 14 24642 ⟨24054, by decide⟩ ⟨14, 2, 0, 24054, 24642, 1229, 4096⟩
    (by decide) selected_cut_00516

theorem selected_cut_00517 : selected 7 ⟨24075, by decide⟩
    (prefixPartial 14 24643) = some ⟨14, 2, 0, 24075, 24643, 1225, 4096⟩ := by
  decide +kernel

theorem context_14_24643_24075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24643 ⟨24075, by decide⟩ :=
  accepted_of_selected 14 24643 ⟨24075, by decide⟩ ⟨14, 2, 0, 24075, 24643, 1225, 4096⟩
    (by decide) selected_cut_00517

theorem unmarked_context_13_6160_24076 : frontier 8 ⟨24076, by decide⟩
    (prefixCache 13 6160) (prefixPartial 13 6160) = false := by
  decide +kernel

theorem node_context_13_6160_24076 : EJMOriginalGlobalDAGData.nodes 8 ⟨24076, by decide⟩ =
    .split (coordinate 13) (![⟨24007, by decide⟩,⟨24031, by decide⟩,⟨24054, by decide⟩,⟨24075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6160_24076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6160 ⟨24076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6160
    ⟨24076, by decide⟩ (by decide) (![⟨24007, by decide⟩,⟨24031, by decide⟩,⟨24054, by decide⟩,⟨24075, by decide⟩]) unmarked_context_13_6160_24076 node_context_13_6160_24076
  intro a
  fin_cases a
  · exact context_14_24640_24007
  · exact context_14_24641_24031
  · exact context_14_24642_24054
  · exact context_14_24643_24075

theorem selected_cut_00518 : selected 7 ⟨24100, by decide⟩
    (prefixPartial 14 24644) = some ⟨14, 2, 0, 24100, 24644, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_24644_24100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24644 ⟨24100, by decide⟩ :=
  accepted_of_selected 14 24644 ⟨24100, by decide⟩ ⟨14, 2, 0, 24100, 24644, 1297, 4096⟩
    (by decide) selected_cut_00518

theorem selected_cut_00519 : selected 7 ⟨24131, by decide⟩
    (prefixPartial 14 24645) = some ⟨14, 2, 0, 24131, 24645, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_24645_24131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24645 ⟨24131, by decide⟩ :=
  accepted_of_selected 14 24645 ⟨24131, by decide⟩ ⟨14, 2, 0, 24131, 24645, 1417, 4096⟩
    (by decide) selected_cut_00519

theorem selected_cut_00520 : selected 7 ⟨24149, by decide⟩
    (prefixPartial 14 24646) = some ⟨14, 2, 0, 24149, 24646, 981, 4096⟩ := by
  decide +kernel

theorem context_14_24646_24149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24646 ⟨24149, by decide⟩ :=
  accepted_of_selected 14 24646 ⟨24149, by decide⟩ ⟨14, 2, 0, 24149, 24646, 981, 4096⟩
    (by decide) selected_cut_00520

theorem selected_cut_00521 : selected 7 ⟨24175, by decide⟩
    (prefixPartial 14 24647) = some ⟨14, 2, 0, 24175, 24647, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_24647_24175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24647 ⟨24175, by decide⟩ :=
  accepted_of_selected 14 24647 ⟨24175, by decide⟩ ⟨14, 2, 0, 24175, 24647, 1117, 4096⟩
    (by decide) selected_cut_00521

theorem unmarked_context_13_6161_24176 : frontier 8 ⟨24176, by decide⟩
    (prefixCache 13 6161) (prefixPartial 13 6161) = false := by
  decide +kernel

theorem node_context_13_6161_24176 : EJMOriginalGlobalDAGData.nodes 8 ⟨24176, by decide⟩ =
    .split (coordinate 13) (![⟨24100, by decide⟩,⟨24131, by decide⟩,⟨24149, by decide⟩,⟨24175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6161_24176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6161 ⟨24176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6161
    ⟨24176, by decide⟩ (by decide) (![⟨24100, by decide⟩,⟨24131, by decide⟩,⟨24149, by decide⟩,⟨24175, by decide⟩]) unmarked_context_13_6161_24176 node_context_13_6161_24176
  intro a
  fin_cases a
  · exact context_14_24644_24100
  · exact context_14_24645_24131
  · exact context_14_24646_24149
  · exact context_14_24647_24175

theorem selected_cut_00522 : selected 8 ⟨24267, by decide⟩
    (prefixPartial 13 6162) = some ⟨13, 2, 0, 24267, 6162, 3277, 16384⟩ := by
  decide +kernel

theorem context_13_6162_24267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6162 ⟨24267, by decide⟩ :=
  accepted_of_selected 13 6162 ⟨24267, by decide⟩ ⟨13, 2, 0, 24267, 6162, 3277, 16384⟩
    (by decide) selected_cut_00522

theorem selected_cut_00523 : selected 8 ⟨24314, by decide⟩
    (prefixPartial 13 6163) = some ⟨13, 2, 0, 24314, 6163, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_6163_24314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6163 ⟨24314, by decide⟩ :=
  accepted_of_selected 13 6163 ⟨24314, by decide⟩ ⟨13, 2, 0, 24314, 6163, 1457, 16384⟩
    (by decide) selected_cut_00523

theorem unmarked_context_12_1540_24315 : frontier 9 ⟨24315, by decide⟩
    (prefixCache 12 1540) (prefixPartial 12 1540) = false := by
  decide +kernel

theorem node_context_12_1540_24315 : EJMOriginalGlobalDAGData.nodes 9 ⟨24315, by decide⟩ =
    .split (coordinate 12) (![⟨24076, by decide⟩,⟨24176, by decide⟩,⟨24267, by decide⟩,⟨24314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1540_24315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1540 ⟨24315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1540
    ⟨24315, by decide⟩ (by decide) (![⟨24076, by decide⟩,⟨24176, by decide⟩,⟨24267, by decide⟩,⟨24314, by decide⟩]) unmarked_context_12_1540_24315 node_context_12_1540_24315
  intro a
  fin_cases a
  · exact context_13_6160_24076
  · exact context_13_6161_24176
  · exact context_13_6162_24267
  · exact context_13_6163_24314

theorem selected_cut_00524 : selected 7 ⟨24343, by decide⟩
    (prefixPartial 14 24656) = some ⟨14, 2, 0, 24343, 24656, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_24656_24343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24656 ⟨24343, by decide⟩ :=
  accepted_of_selected 14 24656 ⟨24343, by decide⟩ ⟨14, 2, 0, 24343, 24656, 1249, 4096⟩
    (by decide) selected_cut_00524

theorem selected_cut_00525 : selected 7 ⟨24371, by decide⟩
    (prefixPartial 14 24657) = some ⟨14, 2, 0, 24371, 24657, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_24657_24371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24657 ⟨24371, by decide⟩ :=
  accepted_of_selected 14 24657 ⟨24371, by decide⟩ ⟨14, 2, 0, 24371, 24657, 1153, 4096⟩
    (by decide) selected_cut_00525

theorem selected_cut_00526 : selected 7 ⟨24393, by decide⟩
    (prefixPartial 14 24658) = some ⟨14, 2, 0, 24393, 24658, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_24658_24393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24658 ⟨24393, by decide⟩ :=
  accepted_of_selected 14 24658 ⟨24393, by decide⟩ ⟨14, 2, 0, 24393, 24658, 1073, 4096⟩
    (by decide) selected_cut_00526

theorem selected_cut_00527 : selected 7 ⟨24414, by decide⟩
    (prefixPartial 14 24659) = some ⟨14, 2, 0, 24414, 24659, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_24659_24414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24659 ⟨24414, by decide⟩ :=
  accepted_of_selected 14 24659 ⟨24414, by decide⟩ ⟨14, 2, 0, 24414, 24659, 1189, 4096⟩
    (by decide) selected_cut_00527

theorem unmarked_context_13_6164_24415 : frontier 8 ⟨24415, by decide⟩
    (prefixCache 13 6164) (prefixPartial 13 6164) = false := by
  decide +kernel

theorem node_context_13_6164_24415 : EJMOriginalGlobalDAGData.nodes 8 ⟨24415, by decide⟩ =
    .split (coordinate 13) (![⟨24343, by decide⟩,⟨24371, by decide⟩,⟨24393, by decide⟩,⟨24414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6164_24415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6164 ⟨24415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6164
    ⟨24415, by decide⟩ (by decide) (![⟨24343, by decide⟩,⟨24371, by decide⟩,⟨24393, by decide⟩,⟨24414, by decide⟩]) unmarked_context_13_6164_24415 node_context_13_6164_24415
  intro a
  fin_cases a
  · exact context_14_24656_24343
  · exact context_14_24657_24371
  · exact context_14_24658_24393
  · exact context_14_24659_24414

theorem selected_cut_00528 : selected 8 ⟨24469, by decide⟩
    (prefixPartial 13 6165) = some ⟨13, 2, 0, 24469, 6165, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_6165_24469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6165 ⟨24469, by decide⟩ :=
  accepted_of_selected 13 6165 ⟨24469, by decide⟩ ⟨13, 2, 0, 24469, 6165, 3457, 16384⟩
    (by decide) selected_cut_00528

theorem selected_cut_00529 : selected 8 ⟨24507, by decide⟩
    (prefixPartial 13 6166) = some ⟨13, 2, 0, 24507, 6166, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_6166_24507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6166 ⟨24507, by decide⟩ :=
  accepted_of_selected 13 6166 ⟨24507, by decide⟩ ⟨13, 2, 0, 24507, 6166, 2325, 16384⟩
    (by decide) selected_cut_00529

theorem selected_cut_00530 : selected 8 ⟨24534, by decide⟩
    (prefixPartial 13 6167) = some ⟨13, 2, 0, 24534, 6167, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_6167_24534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6167 ⟨24534, by decide⟩ :=
  accepted_of_selected 13 6167 ⟨24534, by decide⟩ ⟨13, 2, 0, 24534, 6167, 1317, 16384⟩
    (by decide) selected_cut_00530

theorem unmarked_context_12_1541_24535 : frontier 9 ⟨24535, by decide⟩
    (prefixCache 12 1541) (prefixPartial 12 1541) = false := by
  decide +kernel

theorem node_context_12_1541_24535 : EJMOriginalGlobalDAGData.nodes 9 ⟨24535, by decide⟩ =
    .split (coordinate 12) (![⟨24415, by decide⟩,⟨24469, by decide⟩,⟨24507, by decide⟩,⟨24534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1541_24535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1541 ⟨24535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1541
    ⟨24535, by decide⟩ (by decide) (![⟨24415, by decide⟩,⟨24469, by decide⟩,⟨24507, by decide⟩,⟨24534, by decide⟩]) unmarked_context_12_1541_24535 node_context_12_1541_24535
  intro a
  fin_cases a
  · exact context_13_6164_24415
  · exact context_13_6165_24469
  · exact context_13_6166_24507
  · exact context_13_6167_24534

theorem selected_cut_00531 : selected 7 ⟨24559, by decide⟩
    (prefixPartial 14 24672) = some ⟨14, 2, 0, 24559, 24672, 997, 4096⟩ := by
  decide +kernel

theorem context_14_24672_24559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24672 ⟨24559, by decide⟩ :=
  accepted_of_selected 14 24672 ⟨24559, by decide⟩ ⟨14, 2, 0, 24559, 24672, 997, 4096⟩
    (by decide) selected_cut_00531

theorem selected_cut_00532 : selected 7 ⟨24589, by decide⟩
    (prefixPartial 14 24673) = some ⟨14, 2, 0, 24589, 24673, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_24673_24589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24673 ⟨24589, by decide⟩ :=
  accepted_of_selected 14 24673 ⟨24589, by decide⟩ ⟨14, 2, 0, 24589, 24673, 1189, 4096⟩
    (by decide) selected_cut_00532

theorem selected_cut_00533 : selected 7 ⟨24608, by decide⟩
    (prefixPartial 14 24674) = some ⟨14, 2, 0, 24608, 24674, 909, 4096⟩ := by
  decide +kernel

theorem context_14_24674_24608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24674 ⟨24608, by decide⟩ :=
  accepted_of_selected 14 24674 ⟨24608, by decide⟩ ⟨14, 2, 0, 24608, 24674, 909, 4096⟩
    (by decide) selected_cut_00533

theorem selected_cut_00534 : selected 7 ⟨24627, by decide⟩
    (prefixPartial 14 24675) = some ⟨14, 2, 0, 24627, 24675, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_24675_24627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24675 ⟨24627, by decide⟩ :=
  accepted_of_selected 14 24675 ⟨24627, by decide⟩ ⟨14, 2, 0, 24627, 24675, 1137, 4096⟩
    (by decide) selected_cut_00534

theorem unmarked_context_13_6168_24628 : frontier 8 ⟨24628, by decide⟩
    (prefixCache 13 6168) (prefixPartial 13 6168) = false := by
  decide +kernel

theorem node_context_13_6168_24628 : EJMOriginalGlobalDAGData.nodes 8 ⟨24628, by decide⟩ =
    .split (coordinate 13) (![⟨24559, by decide⟩,⟨24589, by decide⟩,⟨24608, by decide⟩,⟨24627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6168_24628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6168 ⟨24628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6168
    ⟨24628, by decide⟩ (by decide) (![⟨24559, by decide⟩,⟨24589, by decide⟩,⟨24608, by decide⟩,⟨24627, by decide⟩]) unmarked_context_13_6168_24628 node_context_13_6168_24628
  intro a
  fin_cases a
  · exact context_14_24672_24559
  · exact context_14_24673_24589
  · exact context_14_24674_24608
  · exact context_14_24675_24627

theorem selected_cut_00535 : selected 8 ⟨24672, by decide⟩
    (prefixPartial 13 6169) = some ⟨13, 2, 0, 24672, 6169, 3461, 16384⟩ := by
  decide +kernel

theorem context_13_6169_24672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6169 ⟨24672, by decide⟩ :=
  accepted_of_selected 13 6169 ⟨24672, by decide⟩ ⟨13, 2, 0, 24672, 6169, 3461, 16384⟩
    (by decide) selected_cut_00535

theorem selected_cut_00536 : selected 8 ⟨24710, by decide⟩
    (prefixPartial 13 6170) = some ⟨13, 2, 0, 24710, 6170, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_6170_24710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6170 ⟨24710, by decide⟩ :=
  accepted_of_selected 13 6170 ⟨24710, by decide⟩ ⟨13, 2, 0, 24710, 6170, 2317, 16384⟩
    (by decide) selected_cut_00536

theorem selected_cut_00537 : selected 8 ⟨24739, by decide⟩
    (prefixPartial 13 6171) = some ⟨13, 2, 0, 24739, 6171, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_6171_24739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6171 ⟨24739, by decide⟩ :=
  accepted_of_selected 13 6171 ⟨24739, by decide⟩ ⟨13, 2, 0, 24739, 6171, 1405, 16384⟩
    (by decide) selected_cut_00537

theorem unmarked_context_12_1542_24740 : frontier 9 ⟨24740, by decide⟩
    (prefixCache 12 1542) (prefixPartial 12 1542) = false := by
  decide +kernel

theorem node_context_12_1542_24740 : EJMOriginalGlobalDAGData.nodes 9 ⟨24740, by decide⟩ =
    .split (coordinate 12) (![⟨24628, by decide⟩,⟨24672, by decide⟩,⟨24710, by decide⟩,⟨24739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1542_24740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1542 ⟨24740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1542
    ⟨24740, by decide⟩ (by decide) (![⟨24628, by decide⟩,⟨24672, by decide⟩,⟨24710, by decide⟩,⟨24739, by decide⟩]) unmarked_context_12_1542_24740 node_context_12_1542_24740
  intro a
  fin_cases a
  · exact context_13_6168_24628
  · exact context_13_6169_24672
  · exact context_13_6170_24710
  · exact context_13_6171_24739

theorem selected_cut_00538 : selected 7 ⟨24762, by decide⟩
    (prefixPartial 14 24688) = some ⟨14, 2, 0, 24762, 24688, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_24688_24762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24688 ⟨24762, by decide⟩ :=
  accepted_of_selected 14 24688 ⟨24762, by decide⟩ ⟨14, 2, 0, 24762, 24688, 1137, 4096⟩
    (by decide) selected_cut_00538

theorem selected_cut_00539 : selected 7 ⟨24785, by decide⟩
    (prefixPartial 14 24689) = some ⟨14, 2, 0, 24785, 24689, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_24689_24785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24689 ⟨24785, by decide⟩ :=
  accepted_of_selected 14 24689 ⟨24785, by decide⟩ ⟨14, 2, 0, 24785, 24689, 1273, 4096⟩
    (by decide) selected_cut_00539

theorem selected_cut_00540 : selected 7 ⟨24805, by decide⟩
    (prefixPartial 14 24690) = some ⟨14, 2, 0, 24805, 24690, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_24690_24805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24690 ⟨24805, by decide⟩ :=
  accepted_of_selected 14 24690 ⟨24805, by decide⟩ ⟨14, 2, 0, 24805, 24690, 1209, 4096⟩
    (by decide) selected_cut_00540

theorem selected_cut_00541 : selected 7 ⟨24832, by decide⟩
    (prefixPartial 14 24691) = some ⟨14, 2, 0, 24832, 24691, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_24691_24832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24691 ⟨24832, by decide⟩ :=
  accepted_of_selected 14 24691 ⟨24832, by decide⟩ ⟨14, 2, 0, 24832, 24691, 1237, 4096⟩
    (by decide) selected_cut_00541

theorem unmarked_context_13_6172_24833 : frontier 8 ⟨24833, by decide⟩
    (prefixCache 13 6172) (prefixPartial 13 6172) = false := by
  decide +kernel

theorem node_context_13_6172_24833 : EJMOriginalGlobalDAGData.nodes 8 ⟨24833, by decide⟩ =
    .split (coordinate 13) (![⟨24762, by decide⟩,⟨24785, by decide⟩,⟨24805, by decide⟩,⟨24832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6172_24833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6172 ⟨24833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6172
    ⟨24833, by decide⟩ (by decide) (![⟨24762, by decide⟩,⟨24785, by decide⟩,⟨24805, by decide⟩,⟨24832, by decide⟩]) unmarked_context_13_6172_24833 node_context_13_6172_24833
  intro a
  fin_cases a
  · exact context_14_24688_24762
  · exact context_14_24689_24785
  · exact context_14_24690_24805
  · exact context_14_24691_24832

theorem selected_cut_00542 : selected 8 ⟨24900, by decide⟩
    (prefixPartial 13 6173) = some ⟨13, 2, 0, 24900, 6173, 3937, 16384⟩ := by
  decide +kernel

theorem context_13_6173_24900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6173 ⟨24900, by decide⟩ :=
  accepted_of_selected 13 6173 ⟨24900, by decide⟩ ⟨13, 2, 0, 24900, 6173, 3937, 16384⟩
    (by decide) selected_cut_00542

theorem selected_cut_00543 : selected 8 ⟨24958, by decide⟩
    (prefixPartial 13 6174) = some ⟨13, 2, 0, 24958, 6174, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_6174_24958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6174 ⟨24958, by decide⟩ :=
  accepted_of_selected 13 6174 ⟨24958, by decide⟩ ⟨13, 2, 0, 24958, 6174, 2829, 16384⟩
    (by decide) selected_cut_00543

theorem selected_cut_00544 : selected 8 ⟨24975, by decide⟩
    (prefixPartial 13 6175) = some ⟨13, 2, 0, 24975, 6175, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_6175_24975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6175 ⟨24975, by decide⟩ :=
  accepted_of_selected 13 6175 ⟨24975, by decide⟩ ⟨13, 2, 0, 24975, 6175, 1293, 16384⟩
    (by decide) selected_cut_00544

theorem unmarked_context_12_1543_24976 : frontier 9 ⟨24976, by decide⟩
    (prefixCache 12 1543) (prefixPartial 12 1543) = false := by
  decide +kernel

theorem node_context_12_1543_24976 : EJMOriginalGlobalDAGData.nodes 9 ⟨24976, by decide⟩ =
    .split (coordinate 12) (![⟨24833, by decide⟩,⟨24900, by decide⟩,⟨24958, by decide⟩,⟨24975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1543_24976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1543 ⟨24976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1543
    ⟨24976, by decide⟩ (by decide) (![⟨24833, by decide⟩,⟨24900, by decide⟩,⟨24958, by decide⟩,⟨24975, by decide⟩]) unmarked_context_12_1543_24976 node_context_12_1543_24976
  intro a
  fin_cases a
  · exact context_13_6172_24833
  · exact context_13_6173_24900
  · exact context_13_6174_24958
  · exact context_13_6175_24975

theorem unmarked_context_11_385_24977 : frontier 10 ⟨24977, by decide⟩
    (prefixCache 11 385) (prefixPartial 11 385) = false := by
  decide +kernel

theorem node_context_11_385_24977 : EJMOriginalGlobalDAGData.nodes 10 ⟨24977, by decide⟩ =
    .split (coordinate 11) (![⟨24315, by decide⟩,⟨24535, by decide⟩,⟨24740, by decide⟩,⟨24976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_385_24977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 385 ⟨24977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 385
    ⟨24977, by decide⟩ (by decide) (![⟨24315, by decide⟩,⟨24535, by decide⟩,⟨24740, by decide⟩,⟨24976, by decide⟩]) unmarked_context_11_385_24977 node_context_11_385_24977
  intro a
  fin_cases a
  · exact context_12_1540_24315
  · exact context_12_1541_24535
  · exact context_12_1542_24740
  · exact context_12_1543_24976

theorem selected_cut_00545 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 1544) = some ⟨12, 1, 0, 3161, 1544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1544_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1544 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 1544 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 1544, 1, 65536⟩
    (by decide) selected_cut_00545

theorem selected_cut_00546 : selected 7 ⟨25005, by decide⟩
    (prefixPartial 14 24720) = some ⟨14, 2, 0, 25005, 24720, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_24720_25005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24720 ⟨25005, by decide⟩ :=
  accepted_of_selected 14 24720 ⟨25005, by decide⟩ ⟨14, 2, 0, 25005, 24720, 1137, 4096⟩
    (by decide) selected_cut_00546

theorem selected_cut_00547 : selected 7 ⟨25037, by decide⟩
    (prefixPartial 14 24721) = some ⟨14, 2, 0, 25037, 24721, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_24721_25037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24721 ⟨25037, by decide⟩ :=
  accepted_of_selected 14 24721 ⟨25037, by decide⟩ ⟨14, 2, 0, 25037, 24721, 1269, 4096⟩
    (by decide) selected_cut_00547

theorem selected_cut_00548 : selected 7 ⟨25065, by decide⟩
    (prefixPartial 14 24722) = some ⟨14, 2, 0, 25065, 24722, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_24722_25065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24722 ⟨25065, by decide⟩ :=
  accepted_of_selected 14 24722 ⟨25065, by decide⟩ ⟨14, 2, 0, 25065, 24722, 1125, 4096⟩
    (by decide) selected_cut_00548

theorem selected_cut_00549 : selected 7 ⟨25092, by decide⟩
    (prefixPartial 14 24723) = some ⟨14, 2, 0, 25092, 24723, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_24723_25092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24723 ⟨25092, by decide⟩ :=
  accepted_of_selected 14 24723 ⟨25092, by decide⟩ ⟨14, 2, 0, 25092, 24723, 1161, 4096⟩
    (by decide) selected_cut_00549

theorem unmarked_context_13_6180_25093 : frontier 8 ⟨25093, by decide⟩
    (prefixCache 13 6180) (prefixPartial 13 6180) = false := by
  decide +kernel

theorem node_context_13_6180_25093 : EJMOriginalGlobalDAGData.nodes 8 ⟨25093, by decide⟩ =
    .split (coordinate 13) (![⟨25005, by decide⟩,⟨25037, by decide⟩,⟨25065, by decide⟩,⟨25092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6180_25093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6180 ⟨25093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6180
    ⟨25093, by decide⟩ (by decide) (![⟨25005, by decide⟩,⟨25037, by decide⟩,⟨25065, by decide⟩,⟨25092, by decide⟩]) unmarked_context_13_6180_25093 node_context_13_6180_25093
  intro a
  fin_cases a
  · exact context_14_24720_25005
  · exact context_14_24721_25037
  · exact context_14_24722_25065
  · exact context_14_24723_25092

theorem selected_cut_00550 : selected 7 ⟨25108, by decide⟩
    (prefixPartial 14 24724) = some ⟨14, 2, 0, 25108, 24724, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_24724_25108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24724 ⟨25108, by decide⟩ :=
  accepted_of_selected 14 24724 ⟨25108, by decide⟩ ⟨14, 2, 0, 25108, 24724, 1053, 4096⟩
    (by decide) selected_cut_00550

theorem selected_cut_00551 : selected 7 ⟨25129, by decide⟩
    (prefixPartial 14 24725) = some ⟨14, 2, 0, 25129, 24725, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_24725_25129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24725 ⟨25129, by decide⟩ :=
  accepted_of_selected 14 24725 ⟨25129, by decide⟩ ⟨14, 2, 0, 25129, 24725, 1069, 4096⟩
    (by decide) selected_cut_00551

theorem selected_cut_00552 : selected 7 ⟨25149, by decide⟩
    (prefixPartial 14 24726) = some ⟨14, 2, 0, 25149, 24726, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_24726_25149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24726 ⟨25149, by decide⟩ :=
  accepted_of_selected 14 24726 ⟨25149, by decide⟩ ⟨14, 2, 0, 25149, 24726, 1129, 4096⟩
    (by decide) selected_cut_00552

theorem selected_cut_00553 : selected 7 ⟨25165, by decide⟩
    (prefixPartial 14 24727) = some ⟨14, 2, 0, 25165, 24727, 901, 4096⟩ := by
  decide +kernel

theorem context_14_24727_25165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24727 ⟨25165, by decide⟩ :=
  accepted_of_selected 14 24727 ⟨25165, by decide⟩ ⟨14, 2, 0, 25165, 24727, 901, 4096⟩
    (by decide) selected_cut_00553

theorem unmarked_context_13_6181_25166 : frontier 8 ⟨25166, by decide⟩
    (prefixCache 13 6181) (prefixPartial 13 6181) = false := by
  decide +kernel

theorem node_context_13_6181_25166 : EJMOriginalGlobalDAGData.nodes 8 ⟨25166, by decide⟩ =
    .split (coordinate 13) (![⟨25108, by decide⟩,⟨25129, by decide⟩,⟨25149, by decide⟩,⟨25165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6181_25166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6181 ⟨25166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6181
    ⟨25166, by decide⟩ (by decide) (![⟨25108, by decide⟩,⟨25129, by decide⟩,⟨25149, by decide⟩,⟨25165, by decide⟩]) unmarked_context_13_6181_25166 node_context_13_6181_25166
  intro a
  fin_cases a
  · exact context_14_24724_25108
  · exact context_14_24725_25129
  · exact context_14_24726_25149
  · exact context_14_24727_25165

theorem selected_cut_00554 : selected 8 ⟨25210, by decide⟩
    (prefixPartial 13 6182) = some ⟨13, 2, 0, 25210, 6182, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_6182_25210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6182 ⟨25210, by decide⟩ :=
  accepted_of_selected 13 6182 ⟨25210, by decide⟩ ⟨13, 2, 0, 25210, 6182, 2577, 16384⟩
    (by decide) selected_cut_00554

theorem selected_cut_00555 : selected 8 ⟨25229, by decide⟩
    (prefixPartial 13 6183) = some ⟨13, 2, 0, 25229, 6183, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_6183_25229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6183 ⟨25229, by decide⟩ :=
  accepted_of_selected 13 6183 ⟨25229, by decide⟩ ⟨13, 2, 0, 25229, 6183, 1377, 16384⟩
    (by decide) selected_cut_00555

theorem unmarked_context_12_1545_25230 : frontier 9 ⟨25230, by decide⟩
    (prefixCache 12 1545) (prefixPartial 12 1545) = false := by
  decide +kernel

theorem node_context_12_1545_25230 : EJMOriginalGlobalDAGData.nodes 9 ⟨25230, by decide⟩ =
    .split (coordinate 12) (![⟨25093, by decide⟩,⟨25166, by decide⟩,⟨25210, by decide⟩,⟨25229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1545_25230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1545 ⟨25230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1545
    ⟨25230, by decide⟩ (by decide) (![⟨25093, by decide⟩,⟨25166, by decide⟩,⟨25210, by decide⟩,⟨25229, by decide⟩]) unmarked_context_12_1545_25230 node_context_12_1545_25230
  intro a
  fin_cases a
  · exact context_13_6180_25093
  · exact context_13_6181_25166
  · exact context_13_6182_25210
  · exact context_13_6183_25229

theorem selected_cut_00556 : selected 7 ⟨25256, by decide⟩
    (prefixPartial 14 24736) = some ⟨14, 2, 0, 25256, 24736, 1745, 4096⟩ := by
  decide +kernel

theorem context_14_24736_25256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24736 ⟨25256, by decide⟩ :=
  accepted_of_selected 14 24736 ⟨25256, by decide⟩ ⟨14, 2, 0, 25256, 24736, 1745, 4096⟩
    (by decide) selected_cut_00556

theorem selected_cut_00557 : selected 7 ⟨25299, by decide⟩
    (prefixPartial 14 24737) = some ⟨14, 2, 0, 25299, 24737, 1765, 4096⟩ := by
  decide +kernel

theorem context_14_24737_25299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24737 ⟨25299, by decide⟩ :=
  accepted_of_selected 14 24737 ⟨25299, by decide⟩ ⟨14, 2, 0, 25299, 24737, 1765, 4096⟩
    (by decide) selected_cut_00557

theorem selected_cut_00558 : selected 7 ⟨25326, by decide⟩
    (prefixPartial 14 24738) = some ⟨14, 2, 0, 25326, 24738, 1381, 4096⟩ := by
  decide +kernel

theorem context_14_24738_25326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24738 ⟨25326, by decide⟩ :=
  accepted_of_selected 14 24738 ⟨25326, by decide⟩ ⟨14, 2, 0, 25326, 24738, 1381, 4096⟩
    (by decide) selected_cut_00558

theorem selected_cut_00559 : selected 7 ⟨25352, by decide⟩
    (prefixPartial 14 24739) = some ⟨14, 2, 0, 25352, 24739, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_24739_25352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24739 ⟨25352, by decide⟩ :=
  accepted_of_selected 14 24739 ⟨25352, by decide⟩ ⟨14, 2, 0, 25352, 24739, 1553, 4096⟩
    (by decide) selected_cut_00559

theorem unmarked_context_13_6184_25353 : frontier 8 ⟨25353, by decide⟩
    (prefixCache 13 6184) (prefixPartial 13 6184) = false := by
  decide +kernel

theorem node_context_13_6184_25353 : EJMOriginalGlobalDAGData.nodes 8 ⟨25353, by decide⟩ =
    .split (coordinate 13) (![⟨25256, by decide⟩,⟨25299, by decide⟩,⟨25326, by decide⟩,⟨25352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6184_25353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6184 ⟨25353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6184
    ⟨25353, by decide⟩ (by decide) (![⟨25256, by decide⟩,⟨25299, by decide⟩,⟨25326, by decide⟩,⟨25352, by decide⟩]) unmarked_context_13_6184_25353 node_context_13_6184_25353
  intro a
  fin_cases a
  · exact context_14_24736_25256
  · exact context_14_24737_25299
  · exact context_14_24738_25326
  · exact context_14_24739_25352

theorem selected_cut_00560 : selected 7 ⟨25372, by decide⟩
    (prefixPartial 14 24740) = some ⟨14, 2, 0, 25372, 24740, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_24740_25372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24740 ⟨25372, by decide⟩ :=
  accepted_of_selected 14 24740 ⟨25372, by decide⟩ ⟨14, 2, 0, 25372, 24740, 1341, 4096⟩
    (by decide) selected_cut_00560

theorem selected_cut_00561 : selected 7 ⟨25400, by decide⟩
    (prefixPartial 14 24741) = some ⟨14, 2, 0, 25400, 24741, 1521, 4096⟩ := by
  decide +kernel

theorem context_14_24741_25400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24741 ⟨25400, by decide⟩ :=
  accepted_of_selected 14 24741 ⟨25400, by decide⟩ ⟨14, 2, 0, 25400, 24741, 1521, 4096⟩
    (by decide) selected_cut_00561

theorem selected_cut_00562 : selected 7 ⟨25430, by decide⟩
    (prefixPartial 14 24742) = some ⟨14, 2, 0, 25430, 24742, 1673, 4096⟩ := by
  decide +kernel

theorem context_14_24742_25430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24742 ⟨25430, by decide⟩ :=
  accepted_of_selected 14 24742 ⟨25430, by decide⟩ ⟨14, 2, 0, 25430, 24742, 1673, 4096⟩
    (by decide) selected_cut_00562

theorem selected_cut_00563 : selected 7 ⟨25452, by decide⟩
    (prefixPartial 14 24743) = some ⟨14, 2, 0, 25452, 24743, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_24743_25452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24743 ⟨25452, by decide⟩ :=
  accepted_of_selected 14 24743 ⟨25452, by decide⟩ ⟨14, 2, 0, 25452, 24743, 1193, 4096⟩
    (by decide) selected_cut_00563

theorem unmarked_context_13_6185_25453 : frontier 8 ⟨25453, by decide⟩
    (prefixCache 13 6185) (prefixPartial 13 6185) = false := by
  decide +kernel

theorem node_context_13_6185_25453 : EJMOriginalGlobalDAGData.nodes 8 ⟨25453, by decide⟩ =
    .split (coordinate 13) (![⟨25372, by decide⟩,⟨25400, by decide⟩,⟨25430, by decide⟩,⟨25452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6185_25453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6185 ⟨25453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6185
    ⟨25453, by decide⟩ (by decide) (![⟨25372, by decide⟩,⟨25400, by decide⟩,⟨25430, by decide⟩,⟨25452, by decide⟩]) unmarked_context_13_6185_25453 node_context_13_6185_25453
  intro a
  fin_cases a
  · exact context_14_24740_25372
  · exact context_14_24741_25400
  · exact context_14_24742_25430
  · exact context_14_24743_25452

theorem selected_cut_00564 : selected 8 ⟨25533, by decide⟩
    (prefixPartial 13 6186) = some ⟨13, 2, 0, 25533, 6186, 3489, 16384⟩ := by
  decide +kernel

theorem context_13_6186_25533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6186 ⟨25533, by decide⟩ :=
  accepted_of_selected 13 6186 ⟨25533, by decide⟩ ⟨13, 2, 0, 25533, 6186, 3489, 16384⟩
    (by decide) selected_cut_00564

theorem selected_cut_00565 : selected 8 ⟨25600, by decide⟩
    (prefixPartial 13 6187) = some ⟨13, 2, 0, 25600, 6187, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_6187_25600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6187 ⟨25600, by decide⟩ :=
  accepted_of_selected 13 6187 ⟨25600, by decide⟩ ⟨13, 2, 0, 25600, 6187, 1849, 16384⟩
    (by decide) selected_cut_00565

theorem unmarked_context_12_1546_25601 : frontier 9 ⟨25601, by decide⟩
    (prefixCache 12 1546) (prefixPartial 12 1546) = false := by
  decide +kernel

theorem node_context_12_1546_25601 : EJMOriginalGlobalDAGData.nodes 9 ⟨25601, by decide⟩ =
    .split (coordinate 12) (![⟨25353, by decide⟩,⟨25453, by decide⟩,⟨25533, by decide⟩,⟨25600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1546_25601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1546 ⟨25601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1546
    ⟨25601, by decide⟩ (by decide) (![⟨25353, by decide⟩,⟨25453, by decide⟩,⟨25533, by decide⟩,⟨25600, by decide⟩]) unmarked_context_12_1546_25601 node_context_12_1546_25601
  intro a
  fin_cases a
  · exact context_13_6184_25353
  · exact context_13_6185_25453
  · exact context_13_6186_25533
  · exact context_13_6187_25600

theorem selected_cut_00566 : selected 7 ⟨25617, by decide⟩
    (prefixPartial 14 24752) = some ⟨14, 2, 0, 25617, 24752, 701, 4096⟩ := by
  decide +kernel

theorem context_14_24752_25617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24752 ⟨25617, by decide⟩ :=
  accepted_of_selected 14 24752 ⟨25617, by decide⟩ ⟨14, 2, 0, 25617, 24752, 701, 4096⟩
    (by decide) selected_cut_00566

theorem selected_cut_00567 : selected 7 ⟨25638, by decide⟩
    (prefixPartial 14 24753) = some ⟨14, 2, 0, 25638, 24753, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_24753_25638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24753 ⟨25638, by decide⟩ :=
  accepted_of_selected 14 24753 ⟨25638, by decide⟩ ⟨14, 2, 0, 25638, 24753, 1281, 4096⟩
    (by decide) selected_cut_00567

theorem selected_cut_00568 : selected 7 ⟨25659, by decide⟩
    (prefixPartial 14 24754) = some ⟨14, 2, 0, 25659, 24754, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_24754_25659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24754 ⟨25659, by decide⟩ :=
  accepted_of_selected 14 24754 ⟨25659, by decide⟩ ⟨14, 2, 0, 25659, 24754, 1117, 4096⟩
    (by decide) selected_cut_00568

theorem selected_cut_00569 : selected 7 ⟨25679, by decide⟩
    (prefixPartial 14 24755) = some ⟨14, 2, 0, 25679, 24755, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_24755_25679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24755 ⟨25679, by decide⟩ :=
  accepted_of_selected 14 24755 ⟨25679, by decide⟩ ⟨14, 2, 0, 25679, 24755, 1113, 4096⟩
    (by decide) selected_cut_00569

theorem unmarked_context_13_6188_25680 : frontier 8 ⟨25680, by decide⟩
    (prefixCache 13 6188) (prefixPartial 13 6188) = false := by
  decide +kernel

theorem node_context_13_6188_25680 : EJMOriginalGlobalDAGData.nodes 8 ⟨25680, by decide⟩ =
    .split (coordinate 13) (![⟨25617, by decide⟩,⟨25638, by decide⟩,⟨25659, by decide⟩,⟨25679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6188_25680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6188 ⟨25680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6188
    ⟨25680, by decide⟩ (by decide) (![⟨25617, by decide⟩,⟨25638, by decide⟩,⟨25659, by decide⟩,⟨25679, by decide⟩]) unmarked_context_13_6188_25680 node_context_13_6188_25680
  intro a
  fin_cases a
  · exact context_14_24752_25617
  · exact context_14_24753_25638
  · exact context_14_24754_25659
  · exact context_14_24755_25679

theorem selected_cut_00570 : selected 7 ⟨25696, by decide⟩
    (prefixPartial 14 24756) = some ⟨14, 2, 0, 25696, 24756, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_24756_25696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24756 ⟨25696, by decide⟩ :=
  accepted_of_selected 14 24756 ⟨25696, by decide⟩ ⟨14, 2, 0, 25696, 24756, 1097, 4096⟩
    (by decide) selected_cut_00570

theorem selected_cut_00571 : selected 7 ⟨25715, by decide⟩
    (prefixPartial 14 24757) = some ⟨14, 2, 0, 25715, 24757, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_24757_25715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24757 ⟨25715, by decide⟩ :=
  accepted_of_selected 14 24757 ⟨25715, by decide⟩ ⟨14, 2, 0, 25715, 24757, 1201, 4096⟩
    (by decide) selected_cut_00571

theorem selected_cut_00572 : selected 7 ⟨25734, by decide⟩
    (prefixPartial 14 24758) = some ⟨14, 2, 0, 25734, 24758, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_24758_25734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24758 ⟨25734, by decide⟩ :=
  accepted_of_selected 14 24758 ⟨25734, by decide⟩ ⟨14, 2, 0, 25734, 24758, 1213, 4096⟩
    (by decide) selected_cut_00572

theorem selected_cut_00573 : selected 7 ⟨25748, by decide⟩
    (prefixPartial 14 24759) = some ⟨14, 2, 0, 25748, 24759, 933, 4096⟩ := by
  decide +kernel

theorem context_14_24759_25748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24759 ⟨25748, by decide⟩ :=
  accepted_of_selected 14 24759 ⟨25748, by decide⟩ ⟨14, 2, 0, 25748, 24759, 933, 4096⟩
    (by decide) selected_cut_00573

theorem unmarked_context_13_6189_25749 : frontier 8 ⟨25749, by decide⟩
    (prefixCache 13 6189) (prefixPartial 13 6189) = false := by
  decide +kernel

theorem node_context_13_6189_25749 : EJMOriginalGlobalDAGData.nodes 8 ⟨25749, by decide⟩ =
    .split (coordinate 13) (![⟨25696, by decide⟩,⟨25715, by decide⟩,⟨25734, by decide⟩,⟨25748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6189_25749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6189 ⟨25749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6189
    ⟨25749, by decide⟩ (by decide) (![⟨25696, by decide⟩,⟨25715, by decide⟩,⟨25734, by decide⟩,⟨25748, by decide⟩]) unmarked_context_13_6189_25749 node_context_13_6189_25749
  intro a
  fin_cases a
  · exact context_14_24756_25696
  · exact context_14_24757_25715
  · exact context_14_24758_25734
  · exact context_14_24759_25748

theorem selected_cut_00574 : selected 8 ⟨25799, by decide⟩
    (prefixPartial 13 6190) = some ⟨13, 2, 0, 25799, 6190, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_6190_25799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6190 ⟨25799, by decide⟩ :=
  accepted_of_selected 13 6190 ⟨25799, by decide⟩ ⟨13, 2, 0, 25799, 6190, 2709, 16384⟩
    (by decide) selected_cut_00574

theorem selected_cut_00575 : selected 8 ⟨25816, by decide⟩
    (prefixPartial 13 6191) = some ⟨13, 2, 0, 25816, 6191, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_6191_25816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6191 ⟨25816, by decide⟩ :=
  accepted_of_selected 13 6191 ⟨25816, by decide⟩ ⟨13, 2, 0, 25816, 6191, 1205, 16384⟩
    (by decide) selected_cut_00575

theorem unmarked_context_12_1547_25817 : frontier 9 ⟨25817, by decide⟩
    (prefixCache 12 1547) (prefixPartial 12 1547) = false := by
  decide +kernel

theorem node_context_12_1547_25817 : EJMOriginalGlobalDAGData.nodes 9 ⟨25817, by decide⟩ =
    .split (coordinate 12) (![⟨25680, by decide⟩,⟨25749, by decide⟩,⟨25799, by decide⟩,⟨25816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1547_25817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1547 ⟨25817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1547
    ⟨25817, by decide⟩ (by decide) (![⟨25680, by decide⟩,⟨25749, by decide⟩,⟨25799, by decide⟩,⟨25816, by decide⟩]) unmarked_context_12_1547_25817 node_context_12_1547_25817
  intro a
  fin_cases a
  · exact context_13_6188_25680
  · exact context_13_6189_25749
  · exact context_13_6190_25799
  · exact context_13_6191_25816

theorem unmarked_context_11_386_25818 : frontier 10 ⟨25818, by decide⟩
    (prefixCache 11 386) (prefixPartial 11 386) = false := by
  decide +kernel

theorem node_context_11_386_25818 : EJMOriginalGlobalDAGData.nodes 10 ⟨25818, by decide⟩ =
    .split (coordinate 11) (![⟨3161, by decide⟩,⟨25230, by decide⟩,⟨25601, by decide⟩,⟨25817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_386_25818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 386 ⟨25818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 386
    ⟨25818, by decide⟩ (by decide) (![⟨3161, by decide⟩,⟨25230, by decide⟩,⟨25601, by decide⟩,⟨25817, by decide⟩]) unmarked_context_11_386_25818 node_context_11_386_25818
  intro a
  fin_cases a
  · exact context_12_1544_3161
  · exact context_12_1545_25230
  · exact context_12_1546_25601
  · exact context_12_1547_25817

theorem selected_cut_00576 : selected 8 ⟨25878, by decide⟩
    (prefixPartial 13 6192) = some ⟨13, 2, 0, 25878, 6192, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_6192_25878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6192 ⟨25878, by decide⟩ :=
  accepted_of_selected 13 6192 ⟨25878, by decide⟩ ⟨13, 2, 0, 25878, 6192, 2449, 16384⟩
    (by decide) selected_cut_00576

theorem selected_cut_00577 : selected 7 ⟨25924, by decide⟩
    (prefixPartial 14 24772) = some ⟨14, 2, 0, 25924, 24772, 1701, 4096⟩ := by
  decide +kernel

theorem context_14_24772_25924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24772 ⟨25924, by decide⟩ :=
  accepted_of_selected 14 24772 ⟨25924, by decide⟩ ⟨14, 2, 0, 25924, 24772, 1701, 4096⟩
    (by decide) selected_cut_00577

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
