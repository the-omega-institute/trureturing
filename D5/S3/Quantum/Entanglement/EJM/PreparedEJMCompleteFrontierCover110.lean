/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover109
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_25134_286280 : frontier 9 ⟨286280, by decide⟩
    (prefixCache 12 25134) (prefixPartial 12 25134) = false := by
  decide +kernel

theorem node_context_12_25134_286280 : EJMOriginalGlobalDAGData.nodes 9 ⟨286280, by decide⟩ =
    .split (coordinate 12) (![⟨286234, by decide⟩,⟨286261, by decide⟩,⟨286273, by decide⟩,⟨286279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25134_286280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25134 ⟨286280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25134
    ⟨286280, by decide⟩ (by decide) (![⟨286234, by decide⟩,⟨286261, by decide⟩,⟨286273, by decide⟩,⟨286279, by decide⟩]) unmarked_context_12_25134_286280 node_context_12_25134_286280
  intro a
  fin_cases a
  · exact context_13_100536_286234
  · exact context_13_100537_286261
  · exact context_13_100538_286273
  · exact context_13_100539_286279

theorem selected_cut_10564 : selected 8 ⟨286291, by decide⟩
    (prefixPartial 13 100540) = some ⟨13, 2, 0, 286291, 100540, 753, 16384⟩ := by
  decide +kernel

theorem context_13_100540_286291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100540 ⟨286291, by decide⟩ :=
  accepted_of_selected 13 100540 ⟨286291, by decide⟩ ⟨13, 2, 0, 286291, 100540, 753, 16384⟩
    (by decide) selected_cut_10564

theorem selected_cut_10565 : selected 8 ⟨286317, by decide⟩
    (prefixPartial 13 100541) = some ⟨13, 2, 0, 286317, 100541, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_100541_286317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100541 ⟨286317, by decide⟩ :=
  accepted_of_selected 13 100541 ⟨286317, by decide⟩ ⟨13, 2, 0, 286317, 100541, 2377, 16384⟩
    (by decide) selected_cut_10565

theorem selected_cut_10566 : selected 8 ⟨286336, by decide⟩
    (prefixPartial 13 100542) = some ⟨13, 2, 0, 286336, 100542, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_100542_286336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100542 ⟨286336, by decide⟩ :=
  accepted_of_selected 13 100542 ⟨286336, by decide⟩ ⟨13, 2, 0, 286336, 100542, 1417, 16384⟩
    (by decide) selected_cut_10566

theorem selected_cut_10567 : selected 8 ⟨286343, by decide⟩
    (prefixPartial 13 100543) = some ⟨13, 2, 0, 286343, 100543, 741, 16384⟩ := by
  decide +kernel

theorem context_13_100543_286343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100543 ⟨286343, by decide⟩ :=
  accepted_of_selected 13 100543 ⟨286343, by decide⟩ ⟨13, 2, 0, 286343, 100543, 741, 16384⟩
    (by decide) selected_cut_10567

theorem unmarked_context_12_25135_286344 : frontier 9 ⟨286344, by decide⟩
    (prefixCache 12 25135) (prefixPartial 12 25135) = false := by
  decide +kernel

theorem node_context_12_25135_286344 : EJMOriginalGlobalDAGData.nodes 9 ⟨286344, by decide⟩ =
    .split (coordinate 12) (![⟨286291, by decide⟩,⟨286317, by decide⟩,⟨286336, by decide⟩,⟨286343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25135_286344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25135 ⟨286344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25135
    ⟨286344, by decide⟩ (by decide) (![⟨286291, by decide⟩,⟨286317, by decide⟩,⟨286336, by decide⟩,⟨286343, by decide⟩]) unmarked_context_12_25135_286344 node_context_12_25135_286344
  intro a
  fin_cases a
  · exact context_13_100540_286291
  · exact context_13_100541_286317
  · exact context_13_100542_286336
  · exact context_13_100543_286343

theorem unmarked_context_11_6283_286345 : frontier 10 ⟨286345, by decide⟩
    (prefixCache 11 6283) (prefixPartial 11 6283) = false := by
  decide +kernel

theorem node_context_11_6283_286345 : EJMOriginalGlobalDAGData.nodes 10 ⟨286345, by decide⟩ =
    .split (coordinate 11) (![⟨286162, by decide⟩,⟨286225, by decide⟩,⟨286280, by decide⟩,⟨286344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6283_286345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6283 ⟨286345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6283
    ⟨286345, by decide⟩ (by decide) (![⟨286162, by decide⟩,⟨286225, by decide⟩,⟨286280, by decide⟩,⟨286344, by decide⟩]) unmarked_context_11_6283_286345 node_context_11_6283_286345
  intro a
  fin_cases a
  · exact context_12_25132_286162
  · exact context_12_25133_286225
  · exact context_12_25134_286280
  · exact context_12_25135_286344

theorem unmarked_context_10_1570_286346 : frontier 11 ⟨286346, by decide⟩
    (prefixCache 10 1570) (prefixPartial 10 1570) = false := by
  decide +kernel

theorem node_context_10_1570_286346 : EJMOriginalGlobalDAGData.nodes 11 ⟨286346, by decide⟩ =
    .split (coordinate 10) (![⟨285681, by decide⟩,⟨285925, by decide⟩,⟨286101, by decide⟩,⟨286345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1570_286346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1570 ⟨286346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1570
    ⟨286346, by decide⟩ (by decide) (![⟨285681, by decide⟩,⟨285925, by decide⟩,⟨286101, by decide⟩,⟨286345, by decide⟩]) unmarked_context_10_1570_286346 node_context_10_1570_286346
  intro a
  fin_cases a
  · exact context_11_6280_285681
  · exact context_11_6281_285925
  · exact context_11_6282_286101
  · exact context_11_6283_286345

theorem selected_cut_10568 : selected 9 ⟨286393, by decide⟩
    (prefixPartial 12 25136) = some ⟨12, 2, 0, 286393, 25136, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_25136_286393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25136 ⟨286393, by decide⟩ :=
  accepted_of_selected 12 25136 ⟨286393, by decide⟩ ⟨12, 2, 0, 286393, 25136, 3677, 65536⟩
    (by decide) selected_cut_10568

theorem selected_cut_10569 : selected 8 ⟨286404, by decide⟩
    (prefixPartial 13 100548) = some ⟨13, 2, 0, 286404, 100548, 661, 16384⟩ := by
  decide +kernel

theorem context_13_100548_286404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100548 ⟨286404, by decide⟩ :=
  accepted_of_selected 13 100548 ⟨286404, by decide⟩ ⟨13, 2, 0, 286404, 100548, 661, 16384⟩
    (by decide) selected_cut_10569

theorem selected_cut_10570 : selected 8 ⟨286427, by decide⟩
    (prefixPartial 13 100549) = some ⟨13, 2, 0, 286427, 100549, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_100549_286427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100549 ⟨286427, by decide⟩ :=
  accepted_of_selected 13 100549 ⟨286427, by decide⟩ ⟨13, 2, 0, 286427, 100549, 2013, 16384⟩
    (by decide) selected_cut_10570

theorem selected_cut_10571 : selected 8 ⟨286442, by decide⟩
    (prefixPartial 13 100550) = some ⟨13, 2, 0, 286442, 100550, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_100550_286442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100550 ⟨286442, by decide⟩ :=
  accepted_of_selected 13 100550 ⟨286442, by decide⟩ ⟨13, 2, 0, 286442, 100550, 1113, 16384⟩
    (by decide) selected_cut_10571

theorem selected_cut_10572 : selected 8 ⟨286446, by decide⟩
    (prefixPartial 13 100551) = some ⟨13, 2, 0, 286446, 100551, 621, 16384⟩ := by
  decide +kernel

theorem context_13_100551_286446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100551 ⟨286446, by decide⟩ :=
  accepted_of_selected 13 100551 ⟨286446, by decide⟩ ⟨13, 2, 0, 286446, 100551, 621, 16384⟩
    (by decide) selected_cut_10572

theorem unmarked_context_12_25137_286447 : frontier 9 ⟨286447, by decide⟩
    (prefixCache 12 25137) (prefixPartial 12 25137) = false := by
  decide +kernel

theorem node_context_12_25137_286447 : EJMOriginalGlobalDAGData.nodes 9 ⟨286447, by decide⟩ =
    .split (coordinate 12) (![⟨286404, by decide⟩,⟨286427, by decide⟩,⟨286442, by decide⟩,⟨286446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25137_286447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25137 ⟨286447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25137
    ⟨286447, by decide⟩ (by decide) (![⟨286404, by decide⟩,⟨286427, by decide⟩,⟨286442, by decide⟩,⟨286446, by decide⟩]) unmarked_context_12_25137_286447 node_context_12_25137_286447
  intro a
  fin_cases a
  · exact context_13_100548_286404
  · exact context_13_100549_286427
  · exact context_13_100550_286442
  · exact context_13_100551_286446

theorem selected_cut_10573 : selected 9 ⟨286490, by decide⟩
    (prefixPartial 12 25138) = some ⟨12, 2, 0, 286490, 25138, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_25138_286490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25138 ⟨286490, by decide⟩ :=
  accepted_of_selected 12 25138 ⟨286490, by decide⟩ ⟨12, 2, 0, 286490, 25138, 3589, 65536⟩
    (by decide) selected_cut_10573

theorem selected_cut_10574 : selected 8 ⟨286496, by decide⟩
    (prefixPartial 13 100556) = some ⟨13, 2, 0, 286496, 100556, 669, 16384⟩ := by
  decide +kernel

theorem context_13_100556_286496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100556 ⟨286496, by decide⟩ :=
  accepted_of_selected 13 100556 ⟨286496, by decide⟩ ⟨13, 2, 0, 286496, 100556, 669, 16384⟩
    (by decide) selected_cut_10574

theorem selected_cut_10575 : selected 8 ⟨286527, by decide⟩
    (prefixPartial 13 100557) = some ⟨13, 2, 0, 286527, 100557, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_100557_286527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100557 ⟨286527, by decide⟩ :=
  accepted_of_selected 13 100557 ⟨286527, by decide⟩ ⟨13, 2, 0, 286527, 100557, 2257, 16384⟩
    (by decide) selected_cut_10575

theorem selected_cut_10576 : selected 8 ⟨286545, by decide⟩
    (prefixPartial 13 100558) = some ⟨13, 2, 0, 286545, 100558, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_100558_286545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100558 ⟨286545, by decide⟩ :=
  accepted_of_selected 13 100558 ⟨286545, by decide⟩ ⟨13, 2, 0, 286545, 100558, 1273, 16384⟩
    (by decide) selected_cut_10576

theorem selected_cut_10577 : selected 8 ⟨286550, by decide⟩
    (prefixPartial 13 100559) = some ⟨13, 2, 0, 286550, 100559, 713, 16384⟩ := by
  decide +kernel

theorem context_13_100559_286550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100559 ⟨286550, by decide⟩ :=
  accepted_of_selected 13 100559 ⟨286550, by decide⟩ ⟨13, 2, 0, 286550, 100559, 713, 16384⟩
    (by decide) selected_cut_10577

theorem unmarked_context_12_25139_286551 : frontier 9 ⟨286551, by decide⟩
    (prefixCache 12 25139) (prefixPartial 12 25139) = false := by
  decide +kernel

theorem node_context_12_25139_286551 : EJMOriginalGlobalDAGData.nodes 9 ⟨286551, by decide⟩ =
    .split (coordinate 12) (![⟨286496, by decide⟩,⟨286527, by decide⟩,⟨286545, by decide⟩,⟨286550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25139_286551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25139 ⟨286551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25139
    ⟨286551, by decide⟩ (by decide) (![⟨286496, by decide⟩,⟨286527, by decide⟩,⟨286545, by decide⟩,⟨286550, by decide⟩]) unmarked_context_12_25139_286551 node_context_12_25139_286551
  intro a
  fin_cases a
  · exact context_13_100556_286496
  · exact context_13_100557_286527
  · exact context_13_100558_286545
  · exact context_13_100559_286550

theorem unmarked_context_11_6284_286552 : frontier 10 ⟨286552, by decide⟩
    (prefixCache 11 6284) (prefixPartial 11 6284) = false := by
  decide +kernel

theorem node_context_11_6284_286552 : EJMOriginalGlobalDAGData.nodes 10 ⟨286552, by decide⟩ =
    .split (coordinate 11) (![⟨286393, by decide⟩,⟨286447, by decide⟩,⟨286490, by decide⟩,⟨286551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6284_286552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6284 ⟨286552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6284
    ⟨286552, by decide⟩ (by decide) (![⟨286393, by decide⟩,⟨286447, by decide⟩,⟨286490, by decide⟩,⟨286551, by decide⟩]) unmarked_context_11_6284_286552 node_context_11_6284_286552
  intro a
  fin_cases a
  · exact context_12_25136_286393
  · exact context_12_25137_286447
  · exact context_12_25138_286490
  · exact context_12_25139_286551

theorem selected_cut_10578 : selected 8 ⟨286561, by decide⟩
    (prefixPartial 13 100560) = some ⟨13, 2, 0, 286561, 100560, 601, 16384⟩ := by
  decide +kernel

theorem context_13_100560_286561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100560 ⟨286561, by decide⟩ :=
  accepted_of_selected 13 100560 ⟨286561, by decide⟩ ⟨13, 2, 0, 286561, 100560, 601, 16384⟩
    (by decide) selected_cut_10578

theorem selected_cut_10579 : selected 8 ⟨286594, by decide⟩
    (prefixPartial 13 100561) = some ⟨13, 2, 0, 286594, 100561, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_100561_286594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100561 ⟨286594, by decide⟩ :=
  accepted_of_selected 13 100561 ⟨286594, by decide⟩ ⟨13, 2, 0, 286594, 100561, 2197, 16384⟩
    (by decide) selected_cut_10579

theorem selected_cut_10580 : selected 8 ⟨286609, by decide⟩
    (prefixPartial 13 100562) = some ⟨13, 2, 0, 286609, 100562, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_100562_286609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100562 ⟨286609, by decide⟩ :=
  accepted_of_selected 13 100562 ⟨286609, by decide⟩ ⟨13, 2, 0, 286609, 100562, 1105, 16384⟩
    (by decide) selected_cut_10580

theorem selected_cut_10581 : selected 8 ⟨286614, by decide⟩
    (prefixPartial 13 100563) = some ⟨13, 2, 0, 286614, 100563, 829, 16384⟩ := by
  decide +kernel

theorem context_13_100563_286614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100563 ⟨286614, by decide⟩ :=
  accepted_of_selected 13 100563 ⟨286614, by decide⟩ ⟨13, 2, 0, 286614, 100563, 829, 16384⟩
    (by decide) selected_cut_10581

theorem unmarked_context_12_25140_286615 : frontier 9 ⟨286615, by decide⟩
    (prefixCache 12 25140) (prefixPartial 12 25140) = false := by
  decide +kernel

theorem node_context_12_25140_286615 : EJMOriginalGlobalDAGData.nodes 9 ⟨286615, by decide⟩ =
    .split (coordinate 12) (![⟨286561, by decide⟩,⟨286594, by decide⟩,⟨286609, by decide⟩,⟨286614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25140_286615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25140 ⟨286615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25140
    ⟨286615, by decide⟩ (by decide) (![⟨286561, by decide⟩,⟨286594, by decide⟩,⟨286609, by decide⟩,⟨286614, by decide⟩]) unmarked_context_12_25140_286615 node_context_12_25140_286615
  intro a
  fin_cases a
  · exact context_13_100560_286561
  · exact context_13_100561_286594
  · exact context_13_100562_286609
  · exact context_13_100563_286614

theorem selected_cut_10582 : selected 8 ⟨286625, by decide⟩
    (prefixPartial 13 100564) = some ⟨13, 2, 0, 286625, 100564, 541, 16384⟩ := by
  decide +kernel

theorem context_13_100564_286625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100564 ⟨286625, by decide⟩ :=
  accepted_of_selected 13 100564 ⟨286625, by decide⟩ ⟨13, 2, 0, 286625, 100564, 541, 16384⟩
    (by decide) selected_cut_10582

theorem selected_cut_10583 : selected 8 ⟨286653, by decide⟩
    (prefixPartial 13 100565) = some ⟨13, 2, 0, 286653, 100565, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_100565_286653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100565 ⟨286653, by decide⟩ :=
  accepted_of_selected 13 100565 ⟨286653, by decide⟩ ⟨13, 2, 0, 286653, 100565, 2253, 16384⟩
    (by decide) selected_cut_10583

theorem selected_cut_10584 : selected 8 ⟨286671, by decide⟩
    (prefixPartial 13 100566) = some ⟨13, 2, 0, 286671, 100566, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_100566_286671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100566 ⟨286671, by decide⟩ :=
  accepted_of_selected 13 100566 ⟨286671, by decide⟩ ⟨13, 2, 0, 286671, 100566, 1317, 16384⟩
    (by decide) selected_cut_10584

theorem selected_cut_10585 : selected 8 ⟨286679, by decide⟩
    (prefixPartial 13 100567) = some ⟨13, 2, 0, 286679, 100567, 857, 16384⟩ := by
  decide +kernel

theorem context_13_100567_286679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100567 ⟨286679, by decide⟩ :=
  accepted_of_selected 13 100567 ⟨286679, by decide⟩ ⟨13, 2, 0, 286679, 100567, 857, 16384⟩
    (by decide) selected_cut_10585

theorem unmarked_context_12_25141_286680 : frontier 9 ⟨286680, by decide⟩
    (prefixCache 12 25141) (prefixPartial 12 25141) = false := by
  decide +kernel

theorem node_context_12_25141_286680 : EJMOriginalGlobalDAGData.nodes 9 ⟨286680, by decide⟩ =
    .split (coordinate 12) (![⟨286625, by decide⟩,⟨286653, by decide⟩,⟨286671, by decide⟩,⟨286679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25141_286680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25141 ⟨286680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25141
    ⟨286680, by decide⟩ (by decide) (![⟨286625, by decide⟩,⟨286653, by decide⟩,⟨286671, by decide⟩,⟨286679, by decide⟩]) unmarked_context_12_25141_286680 node_context_12_25141_286680
  intro a
  fin_cases a
  · exact context_13_100564_286625
  · exact context_13_100565_286653
  · exact context_13_100566_286671
  · exact context_13_100567_286679

theorem selected_cut_10586 : selected 8 ⟨286687, by decide⟩
    (prefixPartial 13 100568) = some ⟨13, 2, 0, 286687, 100568, 437, 16384⟩ := by
  decide +kernel

theorem context_13_100568_286687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100568 ⟨286687, by decide⟩ :=
  accepted_of_selected 13 100568 ⟨286687, by decide⟩ ⟨13, 2, 0, 286687, 100568, 437, 16384⟩
    (by decide) selected_cut_10586

theorem selected_cut_10587 : selected 8 ⟨286716, by decide⟩
    (prefixPartial 13 100569) = some ⟨13, 2, 0, 286716, 100569, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_100569_286716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100569 ⟨286716, by decide⟩ :=
  accepted_of_selected 13 100569 ⟨286716, by decide⟩ ⟨13, 2, 0, 286716, 100569, 2145, 16384⟩
    (by decide) selected_cut_10587

theorem selected_cut_10588 : selected 8 ⟨286732, by decide⟩
    (prefixPartial 13 100570) = some ⟨13, 2, 0, 286732, 100570, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_100570_286732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100570 ⟨286732, by decide⟩ :=
  accepted_of_selected 13 100570 ⟨286732, by decide⟩ ⟨13, 2, 0, 286732, 100570, 1077, 16384⟩
    (by decide) selected_cut_10588

theorem selected_cut_10589 : selected 8 ⟨286742, by decide⟩
    (prefixPartial 13 100571) = some ⟨13, 2, 0, 286742, 100571, 825, 16384⟩ := by
  decide +kernel

theorem context_13_100571_286742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100571 ⟨286742, by decide⟩ :=
  accepted_of_selected 13 100571 ⟨286742, by decide⟩ ⟨13, 2, 0, 286742, 100571, 825, 16384⟩
    (by decide) selected_cut_10589

theorem unmarked_context_12_25142_286743 : frontier 9 ⟨286743, by decide⟩
    (prefixCache 12 25142) (prefixPartial 12 25142) = false := by
  decide +kernel

theorem node_context_12_25142_286743 : EJMOriginalGlobalDAGData.nodes 9 ⟨286743, by decide⟩ =
    .split (coordinate 12) (![⟨286687, by decide⟩,⟨286716, by decide⟩,⟨286732, by decide⟩,⟨286742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25142_286743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25142 ⟨286743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25142
    ⟨286743, by decide⟩ (by decide) (![⟨286687, by decide⟩,⟨286716, by decide⟩,⟨286732, by decide⟩,⟨286742, by decide⟩]) unmarked_context_12_25142_286743 node_context_12_25142_286743
  intro a
  fin_cases a
  · exact context_13_100568_286687
  · exact context_13_100569_286716
  · exact context_13_100570_286732
  · exact context_13_100571_286742

theorem selected_cut_10590 : selected 8 ⟨286754, by decide⟩
    (prefixPartial 13 100572) = some ⟨13, 2, 0, 286754, 100572, 545, 16384⟩ := by
  decide +kernel

theorem context_13_100572_286754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100572 ⟨286754, by decide⟩ :=
  accepted_of_selected 13 100572 ⟨286754, by decide⟩ ⟨13, 2, 0, 286754, 100572, 545, 16384⟩
    (by decide) selected_cut_10590

theorem selected_cut_10591 : selected 8 ⟨286781, by decide⟩
    (prefixPartial 13 100573) = some ⟨13, 2, 0, 286781, 100573, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_100573_286781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100573 ⟨286781, by decide⟩ :=
  accepted_of_selected 13 100573 ⟨286781, by decide⟩ ⟨13, 2, 0, 286781, 100573, 2597, 16384⟩
    (by decide) selected_cut_10591

theorem selected_cut_10592 : selected 8 ⟨286799, by decide⟩
    (prefixPartial 13 100574) = some ⟨13, 2, 0, 286799, 100574, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_100574_286799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100574 ⟨286799, by decide⟩ :=
  accepted_of_selected 13 100574 ⟨286799, by decide⟩ ⟨13, 2, 0, 286799, 100574, 1409, 16384⟩
    (by decide) selected_cut_10592

theorem selected_cut_10593 : selected 8 ⟨286806, by decide⟩
    (prefixPartial 13 100575) = some ⟨13, 2, 0, 286806, 100575, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_100575_286806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100575 ⟨286806, by decide⟩ :=
  accepted_of_selected 13 100575 ⟨286806, by decide⟩ ⟨13, 2, 0, 286806, 100575, 1013, 16384⟩
    (by decide) selected_cut_10593

theorem unmarked_context_12_25143_286807 : frontier 9 ⟨286807, by decide⟩
    (prefixCache 12 25143) (prefixPartial 12 25143) = false := by
  decide +kernel

theorem node_context_12_25143_286807 : EJMOriginalGlobalDAGData.nodes 9 ⟨286807, by decide⟩ =
    .split (coordinate 12) (![⟨286754, by decide⟩,⟨286781, by decide⟩,⟨286799, by decide⟩,⟨286806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25143_286807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25143 ⟨286807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25143
    ⟨286807, by decide⟩ (by decide) (![⟨286754, by decide⟩,⟨286781, by decide⟩,⟨286799, by decide⟩,⟨286806, by decide⟩]) unmarked_context_12_25143_286807 node_context_12_25143_286807
  intro a
  fin_cases a
  · exact context_13_100572_286754
  · exact context_13_100573_286781
  · exact context_13_100574_286799
  · exact context_13_100575_286806

theorem unmarked_context_11_6285_286808 : frontier 10 ⟨286808, by decide⟩
    (prefixCache 11 6285) (prefixPartial 11 6285) = false := by
  decide +kernel

theorem node_context_11_6285_286808 : EJMOriginalGlobalDAGData.nodes 10 ⟨286808, by decide⟩ =
    .split (coordinate 11) (![⟨286615, by decide⟩,⟨286680, by decide⟩,⟨286743, by decide⟩,⟨286807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6285_286808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6285 ⟨286808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6285
    ⟨286808, by decide⟩ (by decide) (![⟨286615, by decide⟩,⟨286680, by decide⟩,⟨286743, by decide⟩,⟨286807, by decide⟩]) unmarked_context_11_6285_286808 node_context_11_6285_286808
  intro a
  fin_cases a
  · exact context_12_25140_286615
  · exact context_12_25141_286680
  · exact context_12_25142_286743
  · exact context_12_25143_286807

theorem selected_cut_10594 : selected 9 ⟨286855, by decide⟩
    (prefixPartial 12 25144) = some ⟨12, 2, 0, 286855, 25144, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_25144_286855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25144 ⟨286855, by decide⟩ :=
  accepted_of_selected 12 25144 ⟨286855, by decide⟩ ⟨12, 2, 0, 286855, 25144, 3825, 65536⟩
    (by decide) selected_cut_10594

theorem selected_cut_10595 : selected 8 ⟨286860, by decide⟩
    (prefixPartial 13 100580) = some ⟨13, 2, 0, 286860, 100580, 377, 16384⟩ := by
  decide +kernel

theorem context_13_100580_286860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100580 ⟨286860, by decide⟩ :=
  accepted_of_selected 13 100580 ⟨286860, by decide⟩ ⟨13, 2, 0, 286860, 100580, 377, 16384⟩
    (by decide) selected_cut_10595

theorem selected_cut_10596 : selected 8 ⟨286884, by decide⟩
    (prefixPartial 13 100581) = some ⟨13, 2, 0, 286884, 100581, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_100581_286884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100581 ⟨286884, by decide⟩ :=
  accepted_of_selected 13 100581 ⟨286884, by decide⟩ ⟨13, 2, 0, 286884, 100581, 2073, 16384⟩
    (by decide) selected_cut_10596

theorem selected_cut_10597 : selected 8 ⟨286901, by decide⟩
    (prefixPartial 13 100582) = some ⟨13, 2, 0, 286901, 100582, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_100582_286901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100582 ⟨286901, by decide⟩ :=
  accepted_of_selected 13 100582 ⟨286901, by decide⟩ ⟨13, 2, 0, 286901, 100582, 1329, 16384⟩
    (by decide) selected_cut_10597

theorem selected_cut_10598 : selected 8 ⟨286907, by decide⟩
    (prefixPartial 13 100583) = some ⟨13, 2, 0, 286907, 100583, 705, 16384⟩ := by
  decide +kernel

theorem context_13_100583_286907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100583 ⟨286907, by decide⟩ :=
  accepted_of_selected 13 100583 ⟨286907, by decide⟩ ⟨13, 2, 0, 286907, 100583, 705, 16384⟩
    (by decide) selected_cut_10598

theorem unmarked_context_12_25145_286908 : frontier 9 ⟨286908, by decide⟩
    (prefixCache 12 25145) (prefixPartial 12 25145) = false := by
  decide +kernel

theorem node_context_12_25145_286908 : EJMOriginalGlobalDAGData.nodes 9 ⟨286908, by decide⟩ =
    .split (coordinate 12) (![⟨286860, by decide⟩,⟨286884, by decide⟩,⟨286901, by decide⟩,⟨286907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25145_286908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25145 ⟨286908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25145
    ⟨286908, by decide⟩ (by decide) (![⟨286860, by decide⟩,⟨286884, by decide⟩,⟨286901, by decide⟩,⟨286907, by decide⟩]) unmarked_context_12_25145_286908 node_context_12_25145_286908
  intro a
  fin_cases a
  · exact context_13_100580_286860
  · exact context_13_100581_286884
  · exact context_13_100582_286901
  · exact context_13_100583_286907

theorem selected_cut_10599 : selected 8 ⟨286914, by decide⟩
    (prefixPartial 13 100584) = some ⟨13, 2, 0, 286914, 100584, 449, 16384⟩ := by
  decide +kernel

theorem context_13_100584_286914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100584 ⟨286914, by decide⟩ :=
  accepted_of_selected 13 100584 ⟨286914, by decide⟩ ⟨13, 2, 0, 286914, 100584, 449, 16384⟩
    (by decide) selected_cut_10599

theorem selected_cut_10600 : selected 8 ⟨286947, by decide⟩
    (prefixPartial 13 100585) = some ⟨13, 2, 0, 286947, 100585, 3493, 16384⟩ := by
  decide +kernel

theorem context_13_100585_286947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100585 ⟨286947, by decide⟩ :=
  accepted_of_selected 13 100585 ⟨286947, by decide⟩ ⟨13, 2, 0, 286947, 100585, 3493, 16384⟩
    (by decide) selected_cut_10600

theorem selected_cut_10601 : selected 8 ⟨286966, by decide⟩
    (prefixPartial 13 100586) = some ⟨13, 2, 0, 286966, 100586, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_100586_286966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100586 ⟨286966, by decide⟩ :=
  accepted_of_selected 13 100586 ⟨286966, by decide⟩ ⟨13, 2, 0, 286966, 100586, 2029, 16384⟩
    (by decide) selected_cut_10601

theorem selected_cut_10602 : selected 8 ⟨286971, by decide⟩
    (prefixPartial 13 100587) = some ⟨13, 2, 0, 286971, 100587, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_100587_286971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100587 ⟨286971, by decide⟩ :=
  accepted_of_selected 13 100587 ⟨286971, by decide⟩ ⟨13, 2, 0, 286971, 100587, 1021, 16384⟩
    (by decide) selected_cut_10602

theorem unmarked_context_12_25146_286972 : frontier 9 ⟨286972, by decide⟩
    (prefixCache 12 25146) (prefixPartial 12 25146) = false := by
  decide +kernel

theorem node_context_12_25146_286972 : EJMOriginalGlobalDAGData.nodes 9 ⟨286972, by decide⟩ =
    .split (coordinate 12) (![⟨286914, by decide⟩,⟨286947, by decide⟩,⟨286966, by decide⟩,⟨286971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25146_286972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25146 ⟨286972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25146
    ⟨286972, by decide⟩ (by decide) (![⟨286914, by decide⟩,⟨286947, by decide⟩,⟨286966, by decide⟩,⟨286971, by decide⟩]) unmarked_context_12_25146_286972 node_context_12_25146_286972
  intro a
  fin_cases a
  · exact context_13_100584_286914
  · exact context_13_100585_286947
  · exact context_13_100586_286966
  · exact context_13_100587_286971

theorem selected_cut_10603 : selected 8 ⟨286978, by decide⟩
    (prefixPartial 13 100588) = some ⟨13, 2, 0, 286978, 100588, 285, 16384⟩ := by
  decide +kernel

theorem context_13_100588_286978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100588 ⟨286978, by decide⟩ :=
  accepted_of_selected 13 100588 ⟨286978, by decide⟩ ⟨13, 2, 0, 286978, 100588, 285, 16384⟩
    (by decide) selected_cut_10603

theorem selected_cut_10604 : selected 8 ⟨287007, by decide⟩
    (prefixPartial 13 100589) = some ⟨13, 2, 0, 287007, 100589, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_100589_287007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100589 ⟨287007, by decide⟩ :=
  accepted_of_selected 13 100589 ⟨287007, by decide⟩ ⟨13, 2, 0, 287007, 100589, 2461, 16384⟩
    (by decide) selected_cut_10604

theorem selected_cut_10605 : selected 8 ⟨287025, by decide⟩
    (prefixPartial 13 100590) = some ⟨13, 2, 0, 287025, 100590, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_100590_287025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100590 ⟨287025, by decide⟩ :=
  accepted_of_selected 13 100590 ⟨287025, by decide⟩ ⟨13, 2, 0, 287025, 100590, 1333, 16384⟩
    (by decide) selected_cut_10605

theorem selected_cut_10606 : selected 8 ⟨287034, by decide⟩
    (prefixPartial 13 100591) = some ⟨13, 2, 0, 287034, 100591, 745, 16384⟩ := by
  decide +kernel

theorem context_13_100591_287034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100591 ⟨287034, by decide⟩ :=
  accepted_of_selected 13 100591 ⟨287034, by decide⟩ ⟨13, 2, 0, 287034, 100591, 745, 16384⟩
    (by decide) selected_cut_10606

theorem unmarked_context_12_25147_287035 : frontier 9 ⟨287035, by decide⟩
    (prefixCache 12 25147) (prefixPartial 12 25147) = false := by
  decide +kernel

theorem node_context_12_25147_287035 : EJMOriginalGlobalDAGData.nodes 9 ⟨287035, by decide⟩ =
    .split (coordinate 12) (![⟨286978, by decide⟩,⟨287007, by decide⟩,⟨287025, by decide⟩,⟨287034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25147_287035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25147 ⟨287035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25147
    ⟨287035, by decide⟩ (by decide) (![⟨286978, by decide⟩,⟨287007, by decide⟩,⟨287025, by decide⟩,⟨287034, by decide⟩]) unmarked_context_12_25147_287035 node_context_12_25147_287035
  intro a
  fin_cases a
  · exact context_13_100588_286978
  · exact context_13_100589_287007
  · exact context_13_100590_287025
  · exact context_13_100591_287034

theorem unmarked_context_11_6286_287036 : frontier 10 ⟨287036, by decide⟩
    (prefixCache 11 6286) (prefixPartial 11 6286) = false := by
  decide +kernel

theorem node_context_11_6286_287036 : EJMOriginalGlobalDAGData.nodes 10 ⟨287036, by decide⟩ =
    .split (coordinate 11) (![⟨286855, by decide⟩,⟨286908, by decide⟩,⟨286972, by decide⟩,⟨287035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6286_287036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6286 ⟨287036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6286
    ⟨287036, by decide⟩ (by decide) (![⟨286855, by decide⟩,⟨286908, by decide⟩,⟨286972, by decide⟩,⟨287035, by decide⟩]) unmarked_context_11_6286_287036 node_context_11_6286_287036
  intro a
  fin_cases a
  · exact context_12_25144_286855
  · exact context_12_25145_286908
  · exact context_12_25146_286972
  · exact context_12_25147_287035

theorem selected_cut_10607 : selected 8 ⟨287039, by decide⟩
    (prefixPartial 13 100592) = some ⟨13, 2, 0, 287039, 100592, 173, 16384⟩ := by
  decide +kernel

theorem context_13_100592_287039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100592 ⟨287039, by decide⟩ :=
  accepted_of_selected 13 100592 ⟨287039, by decide⟩ ⟨13, 2, 0, 287039, 100592, 173, 16384⟩
    (by decide) selected_cut_10607

theorem selected_cut_10608 : selected 8 ⟨287063, by decide⟩
    (prefixPartial 13 100593) = some ⟨13, 2, 0, 287063, 100593, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_100593_287063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100593 ⟨287063, by decide⟩ :=
  accepted_of_selected 13 100593 ⟨287063, by decide⟩ ⟨13, 2, 0, 287063, 100593, 2053, 16384⟩
    (by decide) selected_cut_10608

theorem selected_cut_10609 : selected 8 ⟨287079, by decide⟩
    (prefixPartial 13 100594) = some ⟨13, 2, 0, 287079, 100594, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_100594_287079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100594 ⟨287079, by decide⟩ :=
  accepted_of_selected 13 100594 ⟨287079, by decide⟩ ⟨13, 2, 0, 287079, 100594, 1221, 16384⟩
    (by decide) selected_cut_10609

theorem selected_cut_10610 : selected 8 ⟨287086, by decide⟩
    (prefixPartial 13 100595) = some ⟨13, 2, 0, 287086, 100595, 769, 16384⟩ := by
  decide +kernel

theorem context_13_100595_287086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100595 ⟨287086, by decide⟩ :=
  accepted_of_selected 13 100595 ⟨287086, by decide⟩ ⟨13, 2, 0, 287086, 100595, 769, 16384⟩
    (by decide) selected_cut_10610

theorem unmarked_context_12_25148_287087 : frontier 9 ⟨287087, by decide⟩
    (prefixCache 12 25148) (prefixPartial 12 25148) = false := by
  decide +kernel

theorem node_context_12_25148_287087 : EJMOriginalGlobalDAGData.nodes 9 ⟨287087, by decide⟩ =
    .split (coordinate 12) (![⟨287039, by decide⟩,⟨287063, by decide⟩,⟨287079, by decide⟩,⟨287086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25148_287087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25148 ⟨287087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25148
    ⟨287087, by decide⟩ (by decide) (![⟨287039, by decide⟩,⟨287063, by decide⟩,⟨287079, by decide⟩,⟨287086, by decide⟩]) unmarked_context_12_25148_287087 node_context_12_25148_287087
  intro a
  fin_cases a
  · exact context_13_100592_287039
  · exact context_13_100593_287063
  · exact context_13_100594_287079
  · exact context_13_100595_287086

theorem selected_cut_10611 : selected 8 ⟨287091, by decide⟩
    (prefixPartial 13 100596) = some ⟨13, 2, 0, 287091, 100596, 149, 16384⟩ := by
  decide +kernel

theorem context_13_100596_287091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100596 ⟨287091, by decide⟩ :=
  accepted_of_selected 13 100596 ⟨287091, by decide⟩ ⟨13, 2, 0, 287091, 100596, 149, 16384⟩
    (by decide) selected_cut_10611

theorem selected_cut_10612 : selected 8 ⟨287119, by decide⟩
    (prefixPartial 13 100597) = some ⟨13, 2, 0, 287119, 100597, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_100597_287119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100597 ⟨287119, by decide⟩ :=
  accepted_of_selected 13 100597 ⟨287119, by decide⟩ ⟨13, 2, 0, 287119, 100597, 2593, 16384⟩
    (by decide) selected_cut_10612

theorem selected_cut_10613 : selected 8 ⟨287138, by decide⟩
    (prefixPartial 13 100598) = some ⟨13, 2, 0, 287138, 100598, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_100598_287138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100598 ⟨287138, by decide⟩ :=
  accepted_of_selected 13 100598 ⟨287138, by decide⟩ ⟨13, 2, 0, 287138, 100598, 1365, 16384⟩
    (by decide) selected_cut_10613

theorem selected_cut_10614 : selected 8 ⟨287144, by decide⟩
    (prefixPartial 13 100599) = some ⟨13, 2, 0, 287144, 100599, 709, 16384⟩ := by
  decide +kernel

theorem context_13_100599_287144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100599 ⟨287144, by decide⟩ :=
  accepted_of_selected 13 100599 ⟨287144, by decide⟩ ⟨13, 2, 0, 287144, 100599, 709, 16384⟩
    (by decide) selected_cut_10614

theorem unmarked_context_12_25149_287145 : frontier 9 ⟨287145, by decide⟩
    (prefixCache 12 25149) (prefixPartial 12 25149) = false := by
  decide +kernel

theorem node_context_12_25149_287145 : EJMOriginalGlobalDAGData.nodes 9 ⟨287145, by decide⟩ =
    .split (coordinate 12) (![⟨287091, by decide⟩,⟨287119, by decide⟩,⟨287138, by decide⟩,⟨287144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25149_287145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25149 ⟨287145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25149
    ⟨287145, by decide⟩ (by decide) (![⟨287091, by decide⟩,⟨287119, by decide⟩,⟨287138, by decide⟩,⟨287144, by decide⟩]) unmarked_context_12_25149_287145 node_context_12_25149_287145
  intro a
  fin_cases a
  · exact context_13_100596_287091
  · exact context_13_100597_287119
  · exact context_13_100598_287138
  · exact context_13_100599_287144

theorem selected_cut_10615 : selected 8 ⟨287148, by decide⟩
    (prefixPartial 13 100600) = some ⟨13, 2, 0, 287148, 100600, 81, 16384⟩ := by
  decide +kernel

theorem context_13_100600_287148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100600 ⟨287148, by decide⟩ :=
  accepted_of_selected 13 100600 ⟨287148, by decide⟩ ⟨13, 2, 0, 287148, 100600, 81, 16384⟩
    (by decide) selected_cut_10615

theorem selected_cut_10616 : selected 8 ⟨287174, by decide⟩
    (prefixPartial 13 100601) = some ⟨13, 2, 0, 287174, 100601, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_100601_287174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100601 ⟨287174, by decide⟩ :=
  accepted_of_selected 13 100601 ⟨287174, by decide⟩ ⟨13, 2, 0, 287174, 100601, 2233, 16384⟩
    (by decide) selected_cut_10616

theorem selected_cut_10617 : selected 8 ⟨287190, by decide⟩
    (prefixPartial 13 100602) = some ⟨13, 2, 0, 287190, 100602, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_100602_287190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100602 ⟨287190, by decide⟩ :=
  accepted_of_selected 13 100602 ⟨287190, by decide⟩ ⟨13, 2, 0, 287190, 100602, 1149, 16384⟩
    (by decide) selected_cut_10617

theorem selected_cut_10618 : selected 8 ⟨287196, by decide⟩
    (prefixPartial 13 100603) = some ⟨13, 2, 0, 287196, 100603, 713, 16384⟩ := by
  decide +kernel

theorem context_13_100603_287196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100603 ⟨287196, by decide⟩ :=
  accepted_of_selected 13 100603 ⟨287196, by decide⟩ ⟨13, 2, 0, 287196, 100603, 713, 16384⟩
    (by decide) selected_cut_10618

theorem unmarked_context_12_25150_287197 : frontier 9 ⟨287197, by decide⟩
    (prefixCache 12 25150) (prefixPartial 12 25150) = false := by
  decide +kernel

theorem node_context_12_25150_287197 : EJMOriginalGlobalDAGData.nodes 9 ⟨287197, by decide⟩ =
    .split (coordinate 12) (![⟨287148, by decide⟩,⟨287174, by decide⟩,⟨287190, by decide⟩,⟨287196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25150_287197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25150 ⟨287197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25150
    ⟨287197, by decide⟩ (by decide) (![⟨287148, by decide⟩,⟨287174, by decide⟩,⟨287190, by decide⟩,⟨287196, by decide⟩]) unmarked_context_12_25150_287197 node_context_12_25150_287197
  intro a
  fin_cases a
  · exact context_13_100600_287148
  · exact context_13_100601_287174
  · exact context_13_100602_287190
  · exact context_13_100603_287196

theorem selected_cut_10619 : selected 8 ⟨287201, by decide⟩
    (prefixPartial 13 100604) = some ⟨13, 2, 0, 287201, 100604, 85, 16384⟩ := by
  decide +kernel

theorem context_13_100604_287201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100604 ⟨287201, by decide⟩ :=
  accepted_of_selected 13 100604 ⟨287201, by decide⟩ ⟨13, 2, 0, 287201, 100604, 85, 16384⟩
    (by decide) selected_cut_10619

theorem selected_cut_10620 : selected 8 ⟨287229, by decide⟩
    (prefixPartial 13 100605) = some ⟨13, 2, 0, 287229, 100605, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_100605_287229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100605 ⟨287229, by decide⟩ :=
  accepted_of_selected 13 100605 ⟨287229, by decide⟩ ⟨13, 2, 0, 287229, 100605, 2645, 16384⟩
    (by decide) selected_cut_10620

theorem selected_cut_10621 : selected 8 ⟨287248, by decide⟩
    (prefixPartial 13 100606) = some ⟨13, 2, 0, 287248, 100606, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_100606_287248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100606 ⟨287248, by decide⟩ :=
  accepted_of_selected 13 100606 ⟨287248, by decide⟩ ⟨13, 2, 0, 287248, 100606, 1521, 16384⟩
    (by decide) selected_cut_10621

theorem selected_cut_10622 : selected 8 ⟨287255, by decide⟩
    (prefixPartial 13 100607) = some ⟨13, 2, 0, 287255, 100607, 821, 16384⟩ := by
  decide +kernel

theorem context_13_100607_287255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100607 ⟨287255, by decide⟩ :=
  accepted_of_selected 13 100607 ⟨287255, by decide⟩ ⟨13, 2, 0, 287255, 100607, 821, 16384⟩
    (by decide) selected_cut_10622

theorem unmarked_context_12_25151_287256 : frontier 9 ⟨287256, by decide⟩
    (prefixCache 12 25151) (prefixPartial 12 25151) = false := by
  decide +kernel

theorem node_context_12_25151_287256 : EJMOriginalGlobalDAGData.nodes 9 ⟨287256, by decide⟩ =
    .split (coordinate 12) (![⟨287201, by decide⟩,⟨287229, by decide⟩,⟨287248, by decide⟩,⟨287255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25151_287256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25151 ⟨287256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25151
    ⟨287256, by decide⟩ (by decide) (![⟨287201, by decide⟩,⟨287229, by decide⟩,⟨287248, by decide⟩,⟨287255, by decide⟩]) unmarked_context_12_25151_287256 node_context_12_25151_287256
  intro a
  fin_cases a
  · exact context_13_100604_287201
  · exact context_13_100605_287229
  · exact context_13_100606_287248
  · exact context_13_100607_287255

theorem unmarked_context_11_6287_287257 : frontier 10 ⟨287257, by decide⟩
    (prefixCache 11 6287) (prefixPartial 11 6287) = false := by
  decide +kernel

theorem node_context_11_6287_287257 : EJMOriginalGlobalDAGData.nodes 10 ⟨287257, by decide⟩ =
    .split (coordinate 11) (![⟨287087, by decide⟩,⟨287145, by decide⟩,⟨287197, by decide⟩,⟨287256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6287_287257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6287 ⟨287257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6287
    ⟨287257, by decide⟩ (by decide) (![⟨287087, by decide⟩,⟨287145, by decide⟩,⟨287197, by decide⟩,⟨287256, by decide⟩]) unmarked_context_11_6287_287257 node_context_11_6287_287257
  intro a
  fin_cases a
  · exact context_12_25148_287087
  · exact context_12_25149_287145
  · exact context_12_25150_287197
  · exact context_12_25151_287256

theorem unmarked_context_10_1571_287258 : frontier 11 ⟨287258, by decide⟩
    (prefixCache 10 1571) (prefixPartial 10 1571) = false := by
  decide +kernel

theorem node_context_10_1571_287258 : EJMOriginalGlobalDAGData.nodes 11 ⟨287258, by decide⟩ =
    .split (coordinate 10) (![⟨286552, by decide⟩,⟨286808, by decide⟩,⟨287036, by decide⟩,⟨287257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1571_287258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1571 ⟨287258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1571
    ⟨287258, by decide⟩ (by decide) (![⟨286552, by decide⟩,⟨286808, by decide⟩,⟨287036, by decide⟩,⟨287257, by decide⟩]) unmarked_context_10_1571_287258 node_context_10_1571_287258
  intro a
  fin_cases a
  · exact context_11_6284_286552
  · exact context_11_6285_286808
  · exact context_11_6286_287036
  · exact context_11_6287_287257

theorem unmarked_context_9_392_287259 : frontier 12 ⟨287259, by decide⟩
    (prefixCache 9 392) (prefixPartial 9 392) = false := by
  decide +kernel

theorem node_context_9_392_287259 : EJMOriginalGlobalDAGData.nodes 12 ⟨287259, by decide⟩ =
    .split (coordinate 9) (![⟨284266, by decide⟩,⟨285466, by decide⟩,⟨286346, by decide⟩,⟨287258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_392_287259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 392 ⟨287259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 392
    ⟨287259, by decide⟩ (by decide) (![⟨284266, by decide⟩,⟨285466, by decide⟩,⟨286346, by decide⟩,⟨287258, by decide⟩]) unmarked_context_9_392_287259 node_context_9_392_287259
  intro a
  fin_cases a
  · exact context_10_1568_284266
  · exact context_10_1569_285466
  · exact context_10_1570_286346
  · exact context_10_1571_287258

theorem selected_cut_10623 : selected 9 ⟨287402, by decide⟩
    (prefixPartial 12 25152) = some ⟨12, 2, 0, 287402, 25152, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_25152_287402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25152 ⟨287402, by decide⟩ :=
  accepted_of_selected 12 25152 ⟨287402, by decide⟩ ⟨12, 2, 0, 287402, 25152, 2529, 65536⟩
    (by decide) selected_cut_10623

theorem selected_cut_10624 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100612) = some ⟨13, 1, 0, 3444, 100612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100612, 1, 16384⟩
    (by decide) selected_cut_10624

theorem selected_cut_10625 : selected 7 ⟨287426, by decide⟩
    (prefixPartial 14 402452) = some ⟨14, 2, 0, 287426, 402452, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_402452_287426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 402452 ⟨287426, by decide⟩ :=
  accepted_of_selected 14 402452 ⟨287426, by decide⟩ ⟨14, 2, 0, 287426, 402452, 1293, 4096⟩
    (by decide) selected_cut_10625

theorem selected_cut_10626 : selected 7 ⟨287444, by decide⟩
    (prefixPartial 14 402453) = some ⟨14, 2, 0, 287444, 402453, 893, 4096⟩ := by
  decide +kernel

theorem context_14_402453_287444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 402453 ⟨287444, by decide⟩ :=
  accepted_of_selected 14 402453 ⟨287444, by decide⟩ ⟨14, 2, 0, 287444, 402453, 893, 4096⟩
    (by decide) selected_cut_10626

theorem selected_cut_10627 : selected 7 ⟨287465, by decide⟩
    (prefixPartial 14 402454) = some ⟨14, 2, 0, 287465, 402454, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_402454_287465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 402454 ⟨287465, by decide⟩ :=
  accepted_of_selected 14 402454 ⟨287465, by decide⟩ ⟨14, 2, 0, 287465, 402454, 1173, 4096⟩
    (by decide) selected_cut_10627

theorem selected_cut_10628 : selected 7 ⟨287485, by decide⟩
    (prefixPartial 14 402455) = some ⟨14, 2, 0, 287485, 402455, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_402455_287485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 402455 ⟨287485, by decide⟩ :=
  accepted_of_selected 14 402455 ⟨287485, by decide⟩ ⟨14, 2, 0, 287485, 402455, 1153, 4096⟩
    (by decide) selected_cut_10628

theorem unmarked_context_13_100613_287486 : frontier 8 ⟨287486, by decide⟩
    (prefixCache 13 100613) (prefixPartial 13 100613) = false := by
  decide +kernel

theorem node_context_13_100613_287486 : EJMOriginalGlobalDAGData.nodes 8 ⟨287486, by decide⟩ =
    .split (coordinate 13) (![⟨287426, by decide⟩,⟨287444, by decide⟩,⟨287465, by decide⟩,⟨287485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_100613_287486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100613 ⟨287486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 100613
    ⟨287486, by decide⟩ (by decide) (![⟨287426, by decide⟩,⟨287444, by decide⟩,⟨287465, by decide⟩,⟨287485, by decide⟩]) unmarked_context_13_100613_287486 node_context_13_100613_287486
  intro a
  fin_cases a
  · exact context_14_402452_287426
  · exact context_14_402453_287444
  · exact context_14_402454_287465
  · exact context_14_402455_287485

theorem selected_cut_10629 : selected 8 ⟨287526, by decide⟩
    (prefixPartial 13 100614) = some ⟨13, 2, 0, 287526, 100614, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_100614_287526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100614 ⟨287526, by decide⟩ :=
  accepted_of_selected 13 100614 ⟨287526, by decide⟩ ⟨13, 2, 0, 287526, 100614, 2617, 16384⟩
    (by decide) selected_cut_10629

theorem selected_cut_10630 : selected 8 ⟨287540, by decide⟩
    (prefixPartial 13 100615) = some ⟨13, 2, 0, 287540, 100615, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_100615_287540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100615 ⟨287540, by decide⟩ :=
  accepted_of_selected 13 100615 ⟨287540, by decide⟩ ⟨13, 2, 0, 287540, 100615, 1269, 16384⟩
    (by decide) selected_cut_10630

theorem unmarked_context_12_25153_287541 : frontier 9 ⟨287541, by decide⟩
    (prefixCache 12 25153) (prefixPartial 12 25153) = false := by
  decide +kernel

theorem node_context_12_25153_287541 : EJMOriginalGlobalDAGData.nodes 9 ⟨287541, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨287486, by decide⟩,⟨287526, by decide⟩,⟨287540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25153_287541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25153 ⟨287541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25153
    ⟨287541, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨287486, by decide⟩,⟨287526, by decide⟩,⟨287540, by decide⟩]) unmarked_context_12_25153_287541 node_context_12_25153_287541
  intro a
  fin_cases a
  · exact context_13_100612_3444
  · exact context_13_100613_287486
  · exact context_13_100614_287526
  · exact context_13_100615_287540

theorem selected_cut_10631 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100616) = some ⟨13, 1, 0, 3444, 100616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100616, 1, 16384⟩
    (by decide) selected_cut_10631

theorem selected_cut_10632 : selected 8 ⟨287583, by decide⟩
    (prefixPartial 13 100617) = some ⟨13, 2, 0, 287583, 100617, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_100617_287583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100617 ⟨287583, by decide⟩ :=
  accepted_of_selected 13 100617 ⟨287583, by decide⟩ ⟨13, 2, 0, 287583, 100617, 3061, 16384⟩
    (by decide) selected_cut_10632

theorem selected_cut_10633 : selected 8 ⟨287603, by decide⟩
    (prefixPartial 13 100618) = some ⟨13, 2, 0, 287603, 100618, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_100618_287603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100618 ⟨287603, by decide⟩ :=
  accepted_of_selected 13 100618 ⟨287603, by decide⟩ ⟨13, 2, 0, 287603, 100618, 1685, 16384⟩
    (by decide) selected_cut_10633

theorem selected_cut_10634 : selected 8 ⟨287609, by decide⟩
    (prefixPartial 13 100619) = some ⟨13, 2, 0, 287609, 100619, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_100619_287609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100619 ⟨287609, by decide⟩ :=
  accepted_of_selected 13 100619 ⟨287609, by decide⟩ ⟨13, 2, 0, 287609, 100619, 1025, 16384⟩
    (by decide) selected_cut_10634

theorem unmarked_context_12_25154_287610 : frontier 9 ⟨287610, by decide⟩
    (prefixCache 12 25154) (prefixPartial 12 25154) = false := by
  decide +kernel

theorem node_context_12_25154_287610 : EJMOriginalGlobalDAGData.nodes 9 ⟨287610, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨287583, by decide⟩,⟨287603, by decide⟩,⟨287609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25154_287610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25154 ⟨287610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25154
    ⟨287610, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨287583, by decide⟩,⟨287603, by decide⟩,⟨287609, by decide⟩]) unmarked_context_12_25154_287610 node_context_12_25154_287610
  intro a
  fin_cases a
  · exact context_13_100616_3444
  · exact context_13_100617_287583
  · exact context_13_100618_287603
  · exact context_13_100619_287609

theorem selected_cut_10635 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100620) = some ⟨13, 1, 0, 3444, 100620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100620, 1, 16384⟩
    (by decide) selected_cut_10635

theorem selected_cut_10636 : selected 8 ⟨287655, by decide⟩
    (prefixPartial 13 100621) = some ⟨13, 2, 0, 287655, 100621, 3497, 16384⟩ := by
  decide +kernel

theorem context_13_100621_287655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100621 ⟨287655, by decide⟩ :=
  accepted_of_selected 13 100621 ⟨287655, by decide⟩ ⟨13, 2, 0, 287655, 100621, 3497, 16384⟩
    (by decide) selected_cut_10636

theorem selected_cut_10637 : selected 8 ⟨287681, by decide⟩
    (prefixPartial 13 100622) = some ⟨13, 2, 0, 287681, 100622, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_100622_287681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100622 ⟨287681, by decide⟩ :=
  accepted_of_selected 13 100622 ⟨287681, by decide⟩ ⟨13, 2, 0, 287681, 100622, 2221, 16384⟩
    (by decide) selected_cut_10637

theorem selected_cut_10638 : selected 8 ⟨287689, by decide⟩
    (prefixPartial 13 100623) = some ⟨13, 2, 0, 287689, 100623, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_100623_287689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100623 ⟨287689, by decide⟩ :=
  accepted_of_selected 13 100623 ⟨287689, by decide⟩ ⟨13, 2, 0, 287689, 100623, 1125, 16384⟩
    (by decide) selected_cut_10638

theorem unmarked_context_12_25155_287690 : frontier 9 ⟨287690, by decide⟩
    (prefixCache 12 25155) (prefixPartial 12 25155) = false := by
  decide +kernel

theorem node_context_12_25155_287690 : EJMOriginalGlobalDAGData.nodes 9 ⟨287690, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨287655, by decide⟩,⟨287681, by decide⟩,⟨287689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25155_287690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25155 ⟨287690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25155
    ⟨287690, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨287655, by decide⟩,⟨287681, by decide⟩,⟨287689, by decide⟩]) unmarked_context_12_25155_287690 node_context_12_25155_287690
  intro a
  fin_cases a
  · exact context_13_100620_3444
  · exact context_13_100621_287655
  · exact context_13_100622_287681
  · exact context_13_100623_287689

theorem unmarked_context_11_6288_287691 : frontier 10 ⟨287691, by decide⟩
    (prefixCache 11 6288) (prefixPartial 11 6288) = false := by
  decide +kernel

theorem node_context_11_6288_287691 : EJMOriginalGlobalDAGData.nodes 10 ⟨287691, by decide⟩ =
    .split (coordinate 11) (![⟨287402, by decide⟩,⟨287541, by decide⟩,⟨287610, by decide⟩,⟨287690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6288_287691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6288 ⟨287691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6288
    ⟨287691, by decide⟩ (by decide) (![⟨287402, by decide⟩,⟨287541, by decide⟩,⟨287610, by decide⟩,⟨287690, by decide⟩]) unmarked_context_11_6288_287691 node_context_11_6288_287691
  intro a
  fin_cases a
  · exact context_12_25152_287402
  · exact context_12_25153_287541
  · exact context_12_25154_287610
  · exact context_12_25155_287690

theorem selected_cut_10639 : selected 9 ⟨287734, by decide⟩
    (prefixPartial 12 25156) = some ⟨12, 2, 0, 287734, 25156, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_25156_287734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25156 ⟨287734, by decide⟩ :=
  accepted_of_selected 12 25156 ⟨287734, by decide⟩ ⟨12, 2, 0, 287734, 25156, 3521, 65536⟩
    (by decide) selected_cut_10639

theorem selected_cut_10640 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100628) = some ⟨13, 1, 0, 3444, 100628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100628, 1, 16384⟩
    (by decide) selected_cut_10640

theorem selected_cut_10641 : selected 8 ⟨287772, by decide⟩
    (prefixPartial 13 100629) = some ⟨13, 2, 0, 287772, 100629, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_100629_287772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100629 ⟨287772, by decide⟩ :=
  accepted_of_selected 13 100629 ⟨287772, by decide⟩ ⟨13, 2, 0, 287772, 100629, 2701, 16384⟩
    (by decide) selected_cut_10641

theorem selected_cut_10642 : selected 8 ⟨287792, by decide⟩
    (prefixPartial 13 100630) = some ⟨13, 2, 0, 287792, 100630, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_100630_287792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100630 ⟨287792, by decide⟩ :=
  accepted_of_selected 13 100630 ⟨287792, by decide⟩ ⟨13, 2, 0, 287792, 100630, 1925, 16384⟩
    (by decide) selected_cut_10642

theorem selected_cut_10643 : selected 8 ⟨287801, by decide⟩
    (prefixPartial 13 100631) = some ⟨13, 2, 0, 287801, 100631, 877, 16384⟩ := by
  decide +kernel

theorem context_13_100631_287801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100631 ⟨287801, by decide⟩ :=
  accepted_of_selected 13 100631 ⟨287801, by decide⟩ ⟨13, 2, 0, 287801, 100631, 877, 16384⟩
    (by decide) selected_cut_10643

theorem unmarked_context_12_25157_287802 : frontier 9 ⟨287802, by decide⟩
    (prefixCache 12 25157) (prefixPartial 12 25157) = false := by
  decide +kernel

theorem node_context_12_25157_287802 : EJMOriginalGlobalDAGData.nodes 9 ⟨287802, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨287772, by decide⟩,⟨287792, by decide⟩,⟨287801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25157_287802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25157 ⟨287802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25157
    ⟨287802, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨287772, by decide⟩,⟨287792, by decide⟩,⟨287801, by decide⟩]) unmarked_context_12_25157_287802 node_context_12_25157_287802
  intro a
  fin_cases a
  · exact context_13_100628_3444
  · exact context_13_100629_287772
  · exact context_13_100630_287792
  · exact context_13_100631_287801

theorem selected_cut_10644 : selected 9 ⟨287852, by decide⟩
    (prefixPartial 12 25158) = some ⟨12, 2, 0, 287852, 25158, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_25158_287852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25158 ⟨287852, by decide⟩ :=
  accepted_of_selected 12 25158 ⟨287852, by decide⟩ ⟨12, 2, 0, 287852, 25158, 4021, 65536⟩
    (by decide) selected_cut_10644

theorem selected_cut_10645 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100636) = some ⟨13, 1, 0, 3444, 100636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100636, 1, 16384⟩
    (by decide) selected_cut_10645

theorem selected_cut_10646 : selected 8 ⟨287878, by decide⟩
    (prefixPartial 13 100637) = some ⟨13, 2, 0, 287878, 100637, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_100637_287878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100637 ⟨287878, by decide⟩ :=
  accepted_of_selected 13 100637 ⟨287878, by decide⟩ ⟨13, 2, 0, 287878, 100637, 2193, 16384⟩
    (by decide) selected_cut_10646

theorem selected_cut_10647 : selected 8 ⟨287898, by decide⟩
    (prefixPartial 13 100638) = some ⟨13, 2, 0, 287898, 100638, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_100638_287898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100638 ⟨287898, by decide⟩ :=
  accepted_of_selected 13 100638 ⟨287898, by decide⟩ ⟨13, 2, 0, 287898, 100638, 1597, 16384⟩
    (by decide) selected_cut_10647

theorem selected_cut_10648 : selected 8 ⟨287907, by decide⟩
    (prefixPartial 13 100639) = some ⟨13, 2, 0, 287907, 100639, 869, 16384⟩ := by
  decide +kernel

theorem context_13_100639_287907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100639 ⟨287907, by decide⟩ :=
  accepted_of_selected 13 100639 ⟨287907, by decide⟩ ⟨13, 2, 0, 287907, 100639, 869, 16384⟩
    (by decide) selected_cut_10648

theorem unmarked_context_12_25159_287908 : frontier 9 ⟨287908, by decide⟩
    (prefixCache 12 25159) (prefixPartial 12 25159) = false := by
  decide +kernel

theorem node_context_12_25159_287908 : EJMOriginalGlobalDAGData.nodes 9 ⟨287908, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨287878, by decide⟩,⟨287898, by decide⟩,⟨287907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25159_287908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25159 ⟨287908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25159
    ⟨287908, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨287878, by decide⟩,⟨287898, by decide⟩,⟨287907, by decide⟩]) unmarked_context_12_25159_287908 node_context_12_25159_287908
  intro a
  fin_cases a
  · exact context_13_100636_3444
  · exact context_13_100637_287878
  · exact context_13_100638_287898
  · exact context_13_100639_287907

theorem unmarked_context_11_6289_287909 : frontier 10 ⟨287909, by decide⟩
    (prefixCache 11 6289) (prefixPartial 11 6289) = false := by
  decide +kernel

theorem node_context_11_6289_287909 : EJMOriginalGlobalDAGData.nodes 10 ⟨287909, by decide⟩ =
    .split (coordinate 11) (![⟨287734, by decide⟩,⟨287802, by decide⟩,⟨287852, by decide⟩,⟨287908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6289_287909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6289 ⟨287909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6289
    ⟨287909, by decide⟩ (by decide) (![⟨287734, by decide⟩,⟨287802, by decide⟩,⟨287852, by decide⟩,⟨287908, by decide⟩]) unmarked_context_11_6289_287909 node_context_11_6289_287909
  intro a
  fin_cases a
  · exact context_12_25156_287734
  · exact context_12_25157_287802
  · exact context_12_25158_287852
  · exact context_12_25159_287908

theorem selected_cut_10649 : selected 9 ⟨287944, by decide⟩
    (prefixPartial 12 25160) = some ⟨12, 2, 0, 287944, 25160, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_25160_287944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25160 ⟨287944, by decide⟩ :=
  accepted_of_selected 12 25160 ⟨287944, by decide⟩ ⟨12, 2, 0, 287944, 25160, 2929, 65536⟩
    (by decide) selected_cut_10649

theorem selected_cut_10650 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100644) = some ⟨13, 1, 0, 3444, 100644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100644, 1, 16384⟩
    (by decide) selected_cut_10650

theorem selected_cut_10651 : selected 8 ⟨287966, by decide⟩
    (prefixPartial 13 100645) = some ⟨13, 2, 0, 287966, 100645, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_100645_287966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100645 ⟨287966, by decide⟩ :=
  accepted_of_selected 13 100645 ⟨287966, by decide⟩ ⟨13, 2, 0, 287966, 100645, 2221, 16384⟩
    (by decide) selected_cut_10651

theorem selected_cut_10652 : selected 8 ⟨287985, by decide⟩
    (prefixPartial 13 100646) = some ⟨13, 2, 0, 287985, 100646, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_100646_287985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100646 ⟨287985, by decide⟩ :=
  accepted_of_selected 13 100646 ⟨287985, by decide⟩ ⟨13, 2, 0, 287985, 100646, 1933, 16384⟩
    (by decide) selected_cut_10652

theorem selected_cut_10653 : selected 8 ⟨287991, by decide⟩
    (prefixPartial 13 100647) = some ⟨13, 2, 0, 287991, 100647, 905, 16384⟩ := by
  decide +kernel

theorem context_13_100647_287991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100647 ⟨287991, by decide⟩ :=
  accepted_of_selected 13 100647 ⟨287991, by decide⟩ ⟨13, 2, 0, 287991, 100647, 905, 16384⟩
    (by decide) selected_cut_10653

theorem unmarked_context_12_25161_287992 : frontier 9 ⟨287992, by decide⟩
    (prefixCache 12 25161) (prefixPartial 12 25161) = false := by
  decide +kernel

theorem node_context_12_25161_287992 : EJMOriginalGlobalDAGData.nodes 9 ⟨287992, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨287966, by decide⟩,⟨287985, by decide⟩,⟨287991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25161_287992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25161 ⟨287992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25161
    ⟨287992, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨287966, by decide⟩,⟨287985, by decide⟩,⟨287991, by decide⟩]) unmarked_context_12_25161_287992 node_context_12_25161_287992
  intro a
  fin_cases a
  · exact context_13_100644_3444
  · exact context_13_100645_287966
  · exact context_13_100646_287985
  · exact context_13_100647_287991

theorem selected_cut_10654 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100648) = some ⟨13, 1, 0, 3444, 100648, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100648_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100648 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100648 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100648, 1, 16384⟩
    (by decide) selected_cut_10654

theorem selected_cut_10655 : selected 8 ⟨288025, by decide⟩
    (prefixPartial 13 100649) = some ⟨13, 2, 0, 288025, 100649, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_100649_288025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100649 ⟨288025, by decide⟩ :=
  accepted_of_selected 13 100649 ⟨288025, by decide⟩ ⟨13, 2, 0, 288025, 100649, 2849, 16384⟩
    (by decide) selected_cut_10655

theorem selected_cut_10656 : selected 8 ⟨288042, by decide⟩
    (prefixPartial 13 100650) = some ⟨13, 2, 0, 288042, 100650, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_100650_288042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100650 ⟨288042, by decide⟩ :=
  accepted_of_selected 13 100650 ⟨288042, by decide⟩ ⟨13, 2, 0, 288042, 100650, 2329, 16384⟩
    (by decide) selected_cut_10656

theorem selected_cut_10657 : selected 8 ⟨288048, by decide⟩
    (prefixPartial 13 100651) = some ⟨13, 2, 0, 288048, 100651, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_100651_288048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100651 ⟨288048, by decide⟩ :=
  accepted_of_selected 13 100651 ⟨288048, by decide⟩ ⟨13, 2, 0, 288048, 100651, 1109, 16384⟩
    (by decide) selected_cut_10657

theorem unmarked_context_12_25162_288049 : frontier 9 ⟨288049, by decide⟩
    (prefixCache 12 25162) (prefixPartial 12 25162) = false := by
  decide +kernel

theorem node_context_12_25162_288049 : EJMOriginalGlobalDAGData.nodes 9 ⟨288049, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288025, by decide⟩,⟨288042, by decide⟩,⟨288048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25162_288049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25162 ⟨288049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25162
    ⟨288049, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288025, by decide⟩,⟨288042, by decide⟩,⟨288048, by decide⟩]) unmarked_context_12_25162_288049 node_context_12_25162_288049
  intro a
  fin_cases a
  · exact context_13_100648_3444
  · exact context_13_100649_288025
  · exact context_13_100650_288042
  · exact context_13_100651_288048

theorem selected_cut_10658 : selected 9 ⟨288095, by decide⟩
    (prefixPartial 12 25163) = some ⟨12, 2, 0, 288095, 25163, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_25163_288095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25163 ⟨288095, by decide⟩ :=
  accepted_of_selected 12 25163 ⟨288095, by decide⟩ ⟨12, 2, 0, 288095, 25163, 4065, 65536⟩
    (by decide) selected_cut_10658

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
