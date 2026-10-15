/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover506
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48675 : selected 10 ⟨1367147, by decide⟩
    (prefixPartial 11 100557) = some ⟨11, 2, 0, 1367147, 100557, 2661, 262144⟩ := by
  decide +kernel

theorem context_11_100557_1367147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100557 ⟨1367147, by decide⟩ :=
  accepted_of_selected 11 100557 ⟨1367147, by decide⟩ ⟨11, 2, 0, 1367147, 100557, 2661, 262144⟩
    (by decide) selected_cut_48675

theorem selected_cut_48676 : selected 10 ⟨1367211, by decide⟩
    (prefixPartial 11 100558) = some ⟨11, 2, 0, 1367211, 100558, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_100558_1367211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100558 ⟨1367211, by decide⟩ :=
  accepted_of_selected 11 100558 ⟨1367211, by decide⟩ ⟨11, 2, 0, 1367211, 100558, 2441, 262144⟩
    (by decide) selected_cut_48676

theorem selected_cut_48677 : selected 10 ⟨612961, by decide⟩
    (prefixPartial 11 100559) = some ⟨11, 1, 0, 612961, 100559, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100559_612961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100559 ⟨612961, by decide⟩ :=
  accepted_of_selected 11 100559 ⟨612961, by decide⟩ ⟨11, 1, 0, 612961, 100559, 1, 262144⟩
    (by decide) selected_cut_48677

theorem unmarked_context_10_25139_1367212 : frontier 11 ⟨1367212, by decide⟩
    (prefixCache 10 25139) (prefixPartial 10 25139) = false := by
  decide +kernel

theorem node_context_10_25139_1367212 : EJMOriginalGlobalDAGData.nodes 11 ⟨1367212, by decide⟩ =
    .split (coordinate 10) (![⟨1367069, by decide⟩,⟨1367147, by decide⟩,⟨1367211, by decide⟩,⟨612961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25139_1367212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25139 ⟨1367212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25139
    ⟨1367212, by decide⟩ (by decide) (![⟨1367069, by decide⟩,⟨1367147, by decide⟩,⟨1367211, by decide⟩,⟨612961, by decide⟩]) unmarked_context_10_25139_1367212 node_context_10_25139_1367212
  intro a
  fin_cases a
  · exact context_11_100556_1367069
  · exact context_11_100557_1367147
  · exact context_11_100558_1367211
  · exact context_11_100559_612961

theorem unmarked_context_9_6284_1367213 : frontier 12 ⟨1367213, by decide⟩
    (prefixCache 9 6284) (prefixPartial 9 6284) = false := by
  decide +kernel

theorem node_context_9_6284_1367213 : EJMOriginalGlobalDAGData.nodes 12 ⟨1367213, by decide⟩ =
    .split (coordinate 9) (![⟨1366335, by decide⟩,⟨1366709, by decide⟩,⟨1366960, by decide⟩,⟨1367212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6284_1367213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6284 ⟨1367213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6284
    ⟨1367213, by decide⟩ (by decide) (![⟨1366335, by decide⟩,⟨1366709, by decide⟩,⟨1366960, by decide⟩,⟨1367212, by decide⟩]) unmarked_context_9_6284_1367213 node_context_9_6284_1367213
  intro a
  fin_cases a
  · exact context_10_25136_1366335
  · exact context_10_25137_1366709
  · exact context_10_25138_1366960
  · exact context_10_25139_1367212

theorem selected_cut_48678 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 25140) = some ⟨10, 1, 0, 3442, 25140, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25140_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25140 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 25140 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 25140, 1, 1048576⟩
    (by decide) selected_cut_48678

theorem selected_cut_48679 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25141) = some ⟨10, 1, 0, 893098, 25141, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25141_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25141 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25141 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25141, 1, 1048576⟩
    (by decide) selected_cut_48679

theorem selected_cut_48680 : selected 10 ⟨1367313, by decide⟩
    (prefixPartial 11 100568) = some ⟨11, 2, 0, 1367313, 100568, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_100568_1367313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100568 ⟨1367313, by decide⟩ :=
  accepted_of_selected 11 100568 ⟨1367313, by decide⟩ ⟨11, 2, 0, 1367313, 100568, 3149, 262144⟩
    (by decide) selected_cut_48680

theorem selected_cut_48681 : selected 10 ⟨1367407, by decide⟩
    (prefixPartial 11 100569) = some ⟨11, 2, 0, 1367407, 100569, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_100569_1367407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100569 ⟨1367407, by decide⟩ :=
  accepted_of_selected 11 100569 ⟨1367407, by decide⟩ ⟨11, 2, 0, 1367407, 100569, 2869, 262144⟩
    (by decide) selected_cut_48681

theorem selected_cut_48682 : selected 10 ⟨1367467, by decide⟩
    (prefixPartial 11 100570) = some ⟨11, 2, 0, 1367467, 100570, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_100570_1367467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100570 ⟨1367467, by decide⟩ :=
  accepted_of_selected 11 100570 ⟨1367467, by decide⟩ ⟨11, 2, 0, 1367467, 100570, 1897, 262144⟩
    (by decide) selected_cut_48682

theorem selected_cut_48683 : selected 10 ⟨1367529, by decide⟩
    (prefixPartial 11 100571) = some ⟨11, 2, 0, 1367529, 100571, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_100571_1367529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100571 ⟨1367529, by decide⟩ :=
  accepted_of_selected 11 100571 ⟨1367529, by decide⟩ ⟨11, 2, 0, 1367529, 100571, 2313, 262144⟩
    (by decide) selected_cut_48683

theorem unmarked_context_10_25142_1367530 : frontier 11 ⟨1367530, by decide⟩
    (prefixCache 10 25142) (prefixPartial 10 25142) = false := by
  decide +kernel

theorem node_context_10_25142_1367530 : EJMOriginalGlobalDAGData.nodes 11 ⟨1367530, by decide⟩ =
    .split (coordinate 10) (![⟨1367313, by decide⟩,⟨1367407, by decide⟩,⟨1367467, by decide⟩,⟨1367529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25142_1367530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25142 ⟨1367530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25142
    ⟨1367530, by decide⟩ (by decide) (![⟨1367313, by decide⟩,⟨1367407, by decide⟩,⟨1367467, by decide⟩,⟨1367529, by decide⟩]) unmarked_context_10_25142_1367530 node_context_10_25142_1367530
  intro a
  fin_cases a
  · exact context_11_100568_1367313
  · exact context_11_100569_1367407
  · exact context_11_100570_1367467
  · exact context_11_100571_1367529

theorem selected_cut_48684 : selected 10 ⟨1367570, by decide⟩
    (prefixPartial 11 100572) = some ⟨11, 2, 0, 1367570, 100572, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_100572_1367570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100572 ⟨1367570, by decide⟩ :=
  accepted_of_selected 11 100572 ⟨1367570, by decide⟩ ⟨11, 2, 0, 1367570, 100572, 1373, 262144⟩
    (by decide) selected_cut_48684

theorem selected_cut_48685 : selected 10 ⟨1367628, by decide⟩
    (prefixPartial 11 100573) = some ⟨11, 2, 0, 1367628, 100573, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_100573_1367628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100573 ⟨1367628, by decide⟩ :=
  accepted_of_selected 11 100573 ⟨1367628, by decide⟩ ⟨11, 2, 0, 1367628, 100573, 1985, 262144⟩
    (by decide) selected_cut_48685

theorem selected_cut_48686 : selected 10 ⟨1367677, by decide⟩
    (prefixPartial 11 100574) = some ⟨11, 2, 0, 1367677, 100574, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_100574_1367677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100574 ⟨1367677, by decide⟩ :=
  accepted_of_selected 11 100574 ⟨1367677, by decide⟩ ⟨11, 2, 0, 1367677, 100574, 1633, 262144⟩
    (by decide) selected_cut_48686

theorem selected_cut_48687 : selected 10 ⟨1367710, by decide⟩
    (prefixPartial 11 100575) = some ⟨11, 2, 0, 1367710, 100575, 909, 262144⟩ := by
  decide +kernel

theorem context_11_100575_1367710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100575 ⟨1367710, by decide⟩ :=
  accepted_of_selected 11 100575 ⟨1367710, by decide⟩ ⟨11, 2, 0, 1367710, 100575, 909, 262144⟩
    (by decide) selected_cut_48687

theorem unmarked_context_10_25143_1367711 : frontier 11 ⟨1367711, by decide⟩
    (prefixCache 10 25143) (prefixPartial 10 25143) = false := by
  decide +kernel

theorem node_context_10_25143_1367711 : EJMOriginalGlobalDAGData.nodes 11 ⟨1367711, by decide⟩ =
    .split (coordinate 10) (![⟨1367570, by decide⟩,⟨1367628, by decide⟩,⟨1367677, by decide⟩,⟨1367710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25143_1367711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25143 ⟨1367711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25143
    ⟨1367711, by decide⟩ (by decide) (![⟨1367570, by decide⟩,⟨1367628, by decide⟩,⟨1367677, by decide⟩,⟨1367710, by decide⟩]) unmarked_context_10_25143_1367711 node_context_10_25143_1367711
  intro a
  fin_cases a
  · exact context_11_100572_1367570
  · exact context_11_100573_1367628
  · exact context_11_100574_1367677
  · exact context_11_100575_1367710

theorem unmarked_context_9_6285_1367712 : frontier 12 ⟨1367712, by decide⟩
    (prefixCache 9 6285) (prefixPartial 9 6285) = false := by
  decide +kernel

theorem node_context_9_6285_1367712 : EJMOriginalGlobalDAGData.nodes 12 ⟨1367712, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1367530, by decide⟩,⟨1367711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6285_1367712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6285 ⟨1367712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6285
    ⟨1367712, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1367530, by decide⟩,⟨1367711, by decide⟩]) unmarked_context_9_6285_1367712 node_context_9_6285_1367712
  intro a
  fin_cases a
  · exact context_10_25140_3442
  · exact context_10_25141_893098
  · exact context_10_25142_1367530
  · exact context_10_25143_1367711

theorem selected_cut_48688 : selected 12 ⟨1367827, by decide⟩
    (prefixPartial 9 6286) = some ⟨9, 2, 0, 1367827, 6286, 2613, 4194304⟩ := by
  decide +kernel

theorem context_9_6286_1367827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6286 ⟨1367827, by decide⟩ :=
  accepted_of_selected 9 6286 ⟨1367827, by decide⟩ ⟨9, 2, 0, 1367827, 6286, 2613, 4194304⟩
    (by decide) selected_cut_48688

theorem selected_cut_48689 : selected 12 ⟨1367835, by decide⟩
    (prefixPartial 9 6287) = some ⟨9, 2, 0, 1367835, 6287, 57, 4194304⟩ := by
  decide +kernel

theorem context_9_6287_1367835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6287 ⟨1367835, by decide⟩ :=
  accepted_of_selected 9 6287 ⟨1367835, by decide⟩ ⟨9, 2, 0, 1367835, 6287, 57, 4194304⟩
    (by decide) selected_cut_48689

theorem unmarked_context_8_1571_1367836 : frontier 13 ⟨1367836, by decide⟩
    (prefixCache 8 1571) (prefixPartial 8 1571) = false := by
  decide +kernel

theorem node_context_8_1571_1367836 : EJMOriginalGlobalDAGData.nodes 13 ⟨1367836, by decide⟩ =
    .split (coordinate 8) (![⟨1367213, by decide⟩,⟨1367712, by decide⟩,⟨1367827, by decide⟩,⟨1367835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1571_1367836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1571 ⟨1367836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1571
    ⟨1367836, by decide⟩ (by decide) (![⟨1367213, by decide⟩,⟨1367712, by decide⟩,⟨1367827, by decide⟩,⟨1367835, by decide⟩]) unmarked_context_8_1571_1367836 node_context_8_1571_1367836
  intro a
  fin_cases a
  · exact context_9_6284_1367213
  · exact context_9_6285_1367712
  · exact context_9_6286_1367827
  · exact context_9_6287_1367835

theorem unmarked_context_7_392_1367837 : frontier 14 ⟨1367837, by decide⟩
    (prefixCache 7 392) (prefixPartial 7 392) = false := by
  decide +kernel

theorem node_context_7_392_1367837 : EJMOriginalGlobalDAGData.nodes 14 ⟨1367837, by decide⟩ =
    .split (coordinate 7) (![⟨1364555, by decide⟩,⟨1366234, by decide⟩,⟨1366235, by decide⟩,⟨1367836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_392_1367837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 392 ⟨1367837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 392
    ⟨1367837, by decide⟩ (by decide) (![⟨1364555, by decide⟩,⟨1366234, by decide⟩,⟨1366235, by decide⟩,⟨1367836, by decide⟩]) unmarked_context_7_392_1367837 node_context_7_392_1367837
  intro a
  fin_cases a
  · exact context_8_1568_1364555
  · exact context_8_1569_1366234
  · exact context_8_1570_1366235
  · exact context_8_1571_1367836

theorem selected_cut_48690 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 1572) = some ⟨8, 1, 0, 1364555, 1572, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1572_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1572 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 1572 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 1572, 1, 16777216⟩
    (by decide) selected_cut_48690

theorem selected_cut_48691 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 100672) = some ⟨11, 1, 0, 434745, 100672, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100672_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100672 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 100672 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 100672, 1, 262144⟩
    (by decide) selected_cut_48691

theorem selected_cut_48692 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 100673) = some ⟨11, 1, 0, 434745, 100673, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100673_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100673 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 100673 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 100673, 1, 262144⟩
    (by decide) selected_cut_48692

theorem selected_cut_48693 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 402696) = some ⟨12, 1, 0, 448748, 402696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402696_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402696 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 402696 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 402696, 1, 65536⟩
    (by decide) selected_cut_48693

theorem selected_cut_48694 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 402697) = some ⟨12, 1, 0, 448748, 402697, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402697_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402697 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 402697 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 402697, 1, 65536⟩
    (by decide) selected_cut_48694

theorem selected_cut_48695 : selected 9 ⟨1367946, by decide⟩
    (prefixPartial 12 402698) = some ⟨12, 2, 0, 1367946, 402698, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_402698_1367946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402698 ⟨1367946, by decide⟩ :=
  accepted_of_selected 12 402698 ⟨1367946, by decide⟩ ⟨12, 2, 0, 1367946, 402698, 2289, 65536⟩
    (by decide) selected_cut_48695

theorem selected_cut_48696 : selected 9 ⟨1368023, by decide⟩
    (prefixPartial 12 402699) = some ⟨12, 2, 0, 1368023, 402699, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_402699_1368023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402699 ⟨1368023, by decide⟩ :=
  accepted_of_selected 12 402699 ⟨1368023, by decide⟩ ⟨12, 2, 0, 1368023, 402699, 2257, 65536⟩
    (by decide) selected_cut_48696

theorem unmarked_context_11_100674_1368024 : frontier 10 ⟨1368024, by decide⟩
    (prefixCache 11 100674) (prefixPartial 11 100674) = false := by
  decide +kernel

theorem node_context_11_100674_1368024 : EJMOriginalGlobalDAGData.nodes 10 ⟨1368024, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1367946, by decide⟩,⟨1368023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100674_1368024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100674 ⟨1368024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100674
    ⟨1368024, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1367946, by decide⟩,⟨1368023, by decide⟩]) unmarked_context_11_100674_1368024 node_context_11_100674_1368024
  intro a
  fin_cases a
  · exact context_12_402696_448748
  · exact context_12_402697_448748
  · exact context_12_402698_1367946
  · exact context_12_402699_1368023

theorem selected_cut_48697 : selected 10 ⟨1368136, by decide⟩
    (prefixPartial 11 100675) = some ⟨11, 2, 0, 1368136, 100675, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_100675_1368136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100675 ⟨1368136, by decide⟩ :=
  accepted_of_selected 11 100675 ⟨1368136, by decide⟩ ⟨11, 2, 0, 1368136, 100675, 3417, 262144⟩
    (by decide) selected_cut_48697

theorem unmarked_context_10_25168_1368137 : frontier 11 ⟨1368137, by decide⟩
    (prefixCache 10 25168) (prefixPartial 10 25168) = false := by
  decide +kernel

theorem node_context_10_25168_1368137 : EJMOriginalGlobalDAGData.nodes 11 ⟨1368137, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1368024, by decide⟩,⟨1368136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25168_1368137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25168 ⟨1368137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25168
    ⟨1368137, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1368024, by decide⟩,⟨1368136, by decide⟩]) unmarked_context_10_25168_1368137 node_context_10_25168_1368137
  intro a
  fin_cases a
  · exact context_11_100672_434745
  · exact context_11_100673_434745
  · exact context_11_100674_1368024
  · exact context_11_100675_1368136

theorem selected_cut_48698 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402704) = some ⟨12, 1, 0, 1108174, 402704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402704_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402704 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402704 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402704, 1, 65536⟩
    (by decide) selected_cut_48698

theorem selected_cut_48699 : selected 9 ⟨1368192, by decide⟩
    (prefixPartial 12 402705) = some ⟨12, 2, 0, 1368192, 402705, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_402705_1368192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402705 ⟨1368192, by decide⟩ :=
  accepted_of_selected 12 402705 ⟨1368192, by decide⟩ ⟨12, 2, 0, 1368192, 402705, 2125, 65536⟩
    (by decide) selected_cut_48699

theorem selected_cut_48700 : selected 9 ⟨1368255, by decide⟩
    (prefixPartial 12 402706) = some ⟨12, 2, 0, 1368255, 402706, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_402706_1368255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402706 ⟨1368255, by decide⟩ :=
  accepted_of_selected 12 402706 ⟨1368255, by decide⟩ ⟨12, 2, 0, 1368255, 402706, 2405, 65536⟩
    (by decide) selected_cut_48700

theorem selected_cut_48701 : selected 9 ⟨1368331, by decide⟩
    (prefixPartial 12 402707) = some ⟨12, 2, 0, 1368331, 402707, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_402707_1368331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402707 ⟨1368331, by decide⟩ :=
  accepted_of_selected 12 402707 ⟨1368331, by decide⟩ ⟨12, 2, 0, 1368331, 402707, 2329, 65536⟩
    (by decide) selected_cut_48701

theorem unmarked_context_11_100676_1368332 : frontier 10 ⟨1368332, by decide⟩
    (prefixCache 11 100676) (prefixPartial 11 100676) = false := by
  decide +kernel

theorem node_context_11_100676_1368332 : EJMOriginalGlobalDAGData.nodes 10 ⟨1368332, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1368192, by decide⟩,⟨1368255, by decide⟩,⟨1368331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100676_1368332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100676 ⟨1368332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100676
    ⟨1368332, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1368192, by decide⟩,⟨1368255, by decide⟩,⟨1368331, by decide⟩]) unmarked_context_11_100676_1368332 node_context_11_100676_1368332
  intro a
  fin_cases a
  · exact context_12_402704_1108174
  · exact context_12_402705_1368192
  · exact context_12_402706_1368255
  · exact context_12_402707_1368331

theorem selected_cut_48702 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 100677) = some ⟨11, 1, 0, 892405, 100677, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100677_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100677 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 100677 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 100677, 1, 262144⟩
    (by decide) selected_cut_48702

theorem selected_cut_48703 : selected 10 ⟨1368433, by decide⟩
    (prefixPartial 11 100678) = some ⟨11, 2, 0, 1368433, 100678, 3865, 262144⟩ := by
  decide +kernel

theorem context_11_100678_1368433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100678 ⟨1368433, by decide⟩ :=
  accepted_of_selected 11 100678 ⟨1368433, by decide⟩ ⟨11, 2, 0, 1368433, 100678, 3865, 262144⟩
    (by decide) selected_cut_48703

theorem selected_cut_48704 : selected 10 ⟨1368520, by decide⟩
    (prefixPartial 11 100679) = some ⟨11, 2, 0, 1368520, 100679, 3853, 262144⟩ := by
  decide +kernel

theorem context_11_100679_1368520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100679 ⟨1368520, by decide⟩ :=
  accepted_of_selected 11 100679 ⟨1368520, by decide⟩ ⟨11, 2, 0, 1368520, 100679, 3853, 262144⟩
    (by decide) selected_cut_48704

theorem unmarked_context_10_25169_1368521 : frontier 11 ⟨1368521, by decide⟩
    (prefixCache 10 25169) (prefixPartial 10 25169) = false := by
  decide +kernel

theorem node_context_10_25169_1368521 : EJMOriginalGlobalDAGData.nodes 11 ⟨1368521, by decide⟩ =
    .split (coordinate 10) (![⟨1368332, by decide⟩,⟨892405, by decide⟩,⟨1368433, by decide⟩,⟨1368520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25169_1368521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25169 ⟨1368521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25169
    ⟨1368521, by decide⟩ (by decide) (![⟨1368332, by decide⟩,⟨892405, by decide⟩,⟨1368433, by decide⟩,⟨1368520, by decide⟩]) unmarked_context_10_25169_1368521 node_context_10_25169_1368521
  intro a
  fin_cases a
  · exact context_11_100676_1368332
  · exact context_11_100677_892405
  · exact context_11_100678_1368433
  · exact context_11_100679_1368520

theorem selected_cut_48705 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402720) = some ⟨12, 1, 0, 1108174, 402720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402720_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402720 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402720 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402720, 1, 65536⟩
    (by decide) selected_cut_48705

theorem selected_cut_48706 : selected 9 ⟨1368584, by decide⟩
    (prefixPartial 12 402721) = some ⟨12, 2, 0, 1368584, 402721, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_402721_1368584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402721 ⟨1368584, by decide⟩ :=
  accepted_of_selected 12 402721 ⟨1368584, by decide⟩ ⟨12, 2, 0, 1368584, 402721, 2257, 65536⟩
    (by decide) selected_cut_48706

theorem selected_cut_48707 : selected 9 ⟨1368644, by decide⟩
    (prefixPartial 12 402722) = some ⟨12, 2, 0, 1368644, 402722, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_402722_1368644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402722 ⟨1368644, by decide⟩ :=
  accepted_of_selected 12 402722 ⟨1368644, by decide⟩ ⟨12, 2, 0, 1368644, 402722, 2145, 65536⟩
    (by decide) selected_cut_48707

theorem selected_cut_48708 : selected 9 ⟨1368707, by decide⟩
    (prefixPartial 12 402723) = some ⟨12, 2, 0, 1368707, 402723, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_402723_1368707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402723 ⟨1368707, by decide⟩ :=
  accepted_of_selected 12 402723 ⟨1368707, by decide⟩ ⟨12, 2, 0, 1368707, 402723, 2237, 65536⟩
    (by decide) selected_cut_48708

theorem unmarked_context_11_100680_1368708 : frontier 10 ⟨1368708, by decide⟩
    (prefixCache 11 100680) (prefixPartial 11 100680) = false := by
  decide +kernel

theorem node_context_11_100680_1368708 : EJMOriginalGlobalDAGData.nodes 10 ⟨1368708, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1368584, by decide⟩,⟨1368644, by decide⟩,⟨1368707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100680_1368708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100680 ⟨1368708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100680
    ⟨1368708, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1368584, by decide⟩,⟨1368644, by decide⟩,⟨1368707, by decide⟩]) unmarked_context_11_100680_1368708 node_context_11_100680_1368708
  intro a
  fin_cases a
  · exact context_12_402720_1108174
  · exact context_12_402721_1368584
  · exact context_12_402722_1368644
  · exact context_12_402723_1368707

theorem selected_cut_48709 : selected 10 ⟨1368800, by decide⟩
    (prefixPartial 11 100681) = some ⟨11, 2, 0, 1368800, 100681, 3781, 262144⟩ := by
  decide +kernel

theorem context_11_100681_1368800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100681 ⟨1368800, by decide⟩ :=
  accepted_of_selected 11 100681 ⟨1368800, by decide⟩ ⟨11, 2, 0, 1368800, 100681, 3781, 262144⟩
    (by decide) selected_cut_48709

theorem selected_cut_48710 : selected 10 ⟨1368854, by decide⟩
    (prefixPartial 11 100682) = some ⟨11, 2, 0, 1368854, 100682, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_100682_1368854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100682 ⟨1368854, by decide⟩ :=
  accepted_of_selected 11 100682 ⟨1368854, by decide⟩ ⟨11, 2, 0, 1368854, 100682, 1997, 262144⟩
    (by decide) selected_cut_48710

theorem selected_cut_48711 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402732) = some ⟨12, 1, 0, 1108174, 402732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402732_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402732 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402732 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402732, 1, 65536⟩
    (by decide) selected_cut_48711

theorem selected_cut_48712 : selected 9 ⟨1368899, by decide⟩
    (prefixPartial 12 402733) = some ⟨12, 2, 0, 1368899, 402733, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_402733_1368899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402733 ⟨1368899, by decide⟩ :=
  accepted_of_selected 12 402733 ⟨1368899, by decide⟩ ⟨12, 2, 0, 1368899, 402733, 1833, 65536⟩
    (by decide) selected_cut_48712

theorem selected_cut_48713 : selected 9 ⟨1368937, by decide⟩
    (prefixPartial 12 402734) = some ⟨12, 2, 0, 1368937, 402734, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_402734_1368937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402734 ⟨1368937, by decide⟩ :=
  accepted_of_selected 12 402734 ⟨1368937, by decide⟩ ⟨12, 2, 0, 1368937, 402734, 1769, 65536⟩
    (by decide) selected_cut_48713

theorem selected_cut_48714 : selected 9 ⟨1368981, by decide⟩
    (prefixPartial 12 402735) = some ⟨12, 2, 0, 1368981, 402735, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_402735_1368981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402735 ⟨1368981, by decide⟩ :=
  accepted_of_selected 12 402735 ⟨1368981, by decide⟩ ⟨12, 2, 0, 1368981, 402735, 1861, 65536⟩
    (by decide) selected_cut_48714

theorem unmarked_context_11_100683_1368982 : frontier 10 ⟨1368982, by decide⟩
    (prefixCache 11 100683) (prefixPartial 11 100683) = false := by
  decide +kernel

theorem node_context_11_100683_1368982 : EJMOriginalGlobalDAGData.nodes 10 ⟨1368982, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1368899, by decide⟩,⟨1368937, by decide⟩,⟨1368981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100683_1368982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100683 ⟨1368982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100683
    ⟨1368982, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1368899, by decide⟩,⟨1368937, by decide⟩,⟨1368981, by decide⟩]) unmarked_context_11_100683_1368982 node_context_11_100683_1368982
  intro a
  fin_cases a
  · exact context_12_402732_1108174
  · exact context_12_402733_1368899
  · exact context_12_402734_1368937
  · exact context_12_402735_1368981

theorem unmarked_context_10_25170_1368983 : frontier 11 ⟨1368983, by decide⟩
    (prefixCache 10 25170) (prefixPartial 10 25170) = false := by
  decide +kernel

theorem node_context_10_25170_1368983 : EJMOriginalGlobalDAGData.nodes 11 ⟨1368983, by decide⟩ =
    .split (coordinate 10) (![⟨1368708, by decide⟩,⟨1368800, by decide⟩,⟨1368854, by decide⟩,⟨1368982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25170_1368983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25170 ⟨1368983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25170
    ⟨1368983, by decide⟩ (by decide) (![⟨1368708, by decide⟩,⟨1368800, by decide⟩,⟨1368854, by decide⟩,⟨1368982, by decide⟩]) unmarked_context_10_25170_1368983 node_context_10_25170_1368983
  intro a
  fin_cases a
  · exact context_11_100680_1368708
  · exact context_11_100681_1368800
  · exact context_11_100682_1368854
  · exact context_11_100683_1368982

theorem selected_cut_48715 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402736) = some ⟨12, 1, 0, 1108174, 402736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402736_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402736 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402736 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402736, 1, 65536⟩
    (by decide) selected_cut_48715

theorem selected_cut_48716 : selected 9 ⟨1369044, by decide⟩
    (prefixPartial 12 402737) = some ⟨12, 2, 0, 1369044, 402737, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_402737_1369044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402737 ⟨1369044, by decide⟩ :=
  accepted_of_selected 12 402737 ⟨1369044, by decide⟩ ⟨12, 2, 0, 1369044, 402737, 2005, 65536⟩
    (by decide) selected_cut_48716

theorem selected_cut_48717 : selected 9 ⟨1369102, by decide⟩
    (prefixPartial 12 402738) = some ⟨12, 2, 0, 1369102, 402738, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_402738_1369102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402738 ⟨1369102, by decide⟩ :=
  accepted_of_selected 12 402738 ⟨1369102, by decide⟩ ⟨12, 2, 0, 1369102, 402738, 1929, 65536⟩
    (by decide) selected_cut_48717

theorem selected_cut_48718 : selected 9 ⟨1369169, by decide⟩
    (prefixPartial 12 402739) = some ⟨12, 2, 0, 1369169, 402739, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_402739_1369169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402739 ⟨1369169, by decide⟩ :=
  accepted_of_selected 12 402739 ⟨1369169, by decide⟩ ⟨12, 2, 0, 1369169, 402739, 2189, 65536⟩
    (by decide) selected_cut_48718

theorem unmarked_context_11_100684_1369170 : frontier 10 ⟨1369170, by decide⟩
    (prefixCache 11 100684) (prefixPartial 11 100684) = false := by
  decide +kernel

theorem node_context_11_100684_1369170 : EJMOriginalGlobalDAGData.nodes 10 ⟨1369170, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1369044, by decide⟩,⟨1369102, by decide⟩,⟨1369169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100684_1369170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100684 ⟨1369170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100684
    ⟨1369170, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1369044, by decide⟩,⟨1369102, by decide⟩,⟨1369169, by decide⟩]) unmarked_context_11_100684_1369170 node_context_11_100684_1369170
  intro a
  fin_cases a
  · exact context_12_402736_1108174
  · exact context_12_402737_1369044
  · exact context_12_402738_1369102
  · exact context_12_402739_1369169

theorem selected_cut_48719 : selected 10 ⟨1369269, by decide⟩
    (prefixPartial 11 100685) = some ⟨11, 2, 0, 1369269, 100685, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_100685_1369269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100685 ⟨1369269, by decide⟩ :=
  accepted_of_selected 11 100685 ⟨1369269, by decide⟩ ⟨11, 2, 0, 1369269, 100685, 3545, 262144⟩
    (by decide) selected_cut_48719

theorem selected_cut_48720 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402744) = some ⟨12, 1, 0, 1108174, 402744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402744_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402744 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402744 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402744, 1, 65536⟩
    (by decide) selected_cut_48720

theorem selected_cut_48721 : selected 9 ⟨1369301, by decide⟩
    (prefixPartial 12 402745) = some ⟨12, 2, 0, 1369301, 402745, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_402745_1369301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402745 ⟨1369301, by decide⟩ :=
  accepted_of_selected 12 402745 ⟨1369301, by decide⟩ ⟨12, 2, 0, 1369301, 402745, 1529, 65536⟩
    (by decide) selected_cut_48721

theorem selected_cut_48722 : selected 9 ⟨1369332, by decide⟩
    (prefixPartial 12 402746) = some ⟨12, 2, 0, 1369332, 402746, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_402746_1369332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402746 ⟨1369332, by decide⟩ :=
  accepted_of_selected 12 402746 ⟨1369332, by decide⟩ ⟨12, 2, 0, 1369332, 402746, 1549, 65536⟩
    (by decide) selected_cut_48722

theorem selected_cut_48723 : selected 9 ⟨1369382, by decide⟩
    (prefixPartial 12 402747) = some ⟨12, 2, 0, 1369382, 402747, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_402747_1369382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402747 ⟨1369382, by decide⟩ :=
  accepted_of_selected 12 402747 ⟨1369382, by decide⟩ ⟨12, 2, 0, 1369382, 402747, 1733, 65536⟩
    (by decide) selected_cut_48723

theorem unmarked_context_11_100686_1369383 : frontier 10 ⟨1369383, by decide⟩
    (prefixCache 11 100686) (prefixPartial 11 100686) = false := by
  decide +kernel

theorem node_context_11_100686_1369383 : EJMOriginalGlobalDAGData.nodes 10 ⟨1369383, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1369301, by decide⟩,⟨1369332, by decide⟩,⟨1369382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100686_1369383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100686 ⟨1369383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100686
    ⟨1369383, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1369301, by decide⟩,⟨1369332, by decide⟩,⟨1369382, by decide⟩]) unmarked_context_11_100686_1369383 node_context_11_100686_1369383
  intro a
  fin_cases a
  · exact context_12_402744_1108174
  · exact context_12_402745_1369301
  · exact context_12_402746_1369332
  · exact context_12_402747_1369382

theorem selected_cut_48724 : selected 10 ⟨1369425, by decide⟩
    (prefixPartial 11 100687) = some ⟨11, 2, 0, 1369425, 100687, 1657, 262144⟩ := by
  decide +kernel

theorem context_11_100687_1369425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100687 ⟨1369425, by decide⟩ :=
  accepted_of_selected 11 100687 ⟨1369425, by decide⟩ ⟨11, 2, 0, 1369425, 100687, 1657, 262144⟩
    (by decide) selected_cut_48724

theorem unmarked_context_10_25171_1369426 : frontier 11 ⟨1369426, by decide⟩
    (prefixCache 10 25171) (prefixPartial 10 25171) = false := by
  decide +kernel

theorem node_context_10_25171_1369426 : EJMOriginalGlobalDAGData.nodes 11 ⟨1369426, by decide⟩ =
    .split (coordinate 10) (![⟨1369170, by decide⟩,⟨1369269, by decide⟩,⟨1369383, by decide⟩,⟨1369425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25171_1369426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25171 ⟨1369426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25171
    ⟨1369426, by decide⟩ (by decide) (![⟨1369170, by decide⟩,⟨1369269, by decide⟩,⟨1369383, by decide⟩,⟨1369425, by decide⟩]) unmarked_context_10_25171_1369426 node_context_10_25171_1369426
  intro a
  fin_cases a
  · exact context_11_100684_1369170
  · exact context_11_100685_1369269
  · exact context_11_100686_1369383
  · exact context_11_100687_1369425

theorem unmarked_context_9_6292_1369427 : frontier 12 ⟨1369427, by decide⟩
    (prefixCache 9 6292) (prefixPartial 9 6292) = false := by
  decide +kernel

theorem node_context_9_6292_1369427 : EJMOriginalGlobalDAGData.nodes 12 ⟨1369427, by decide⟩ =
    .split (coordinate 9) (![⟨1368137, by decide⟩,⟨1368521, by decide⟩,⟨1368983, by decide⟩,⟨1369426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6292_1369427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6292 ⟨1369427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6292
    ⟨1369427, by decide⟩ (by decide) (![⟨1368137, by decide⟩,⟨1368521, by decide⟩,⟨1368983, by decide⟩,⟨1369426, by decide⟩]) unmarked_context_9_6292_1369427 node_context_9_6292_1369427
  intro a
  fin_cases a
  · exact context_10_25168_1368137
  · exact context_10_25169_1368521
  · exact context_10_25170_1368983
  · exact context_10_25171_1369426

theorem selected_cut_48725 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 100688) = some ⟨11, 1, 0, 1369428, 100688, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100688_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100688 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 100688 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 100688, 1, 262144⟩
    (by decide) selected_cut_48725

theorem selected_cut_48726 : selected 10 ⟨1369510, by decide⟩
    (prefixPartial 11 100689) = some ⟨11, 2, 0, 1369510, 100689, 3865, 262144⟩ := by
  decide +kernel

theorem context_11_100689_1369510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100689 ⟨1369510, by decide⟩ :=
  accepted_of_selected 11 100689 ⟨1369510, by decide⟩ ⟨11, 2, 0, 1369510, 100689, 3865, 262144⟩
    (by decide) selected_cut_48726

theorem selected_cut_48727 : selected 10 ⟨1369569, by decide⟩
    (prefixPartial 11 100690) = some ⟨11, 2, 0, 1369569, 100690, 2685, 262144⟩ := by
  decide +kernel

theorem context_11_100690_1369569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100690 ⟨1369569, by decide⟩ :=
  accepted_of_selected 11 100690 ⟨1369569, by decide⟩ ⟨11, 2, 0, 1369569, 100690, 2685, 262144⟩
    (by decide) selected_cut_48727

theorem selected_cut_48728 : selected 10 ⟨1369634, by decide⟩
    (prefixPartial 11 100691) = some ⟨11, 2, 0, 1369634, 100691, 2797, 262144⟩ := by
  decide +kernel

theorem context_11_100691_1369634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100691 ⟨1369634, by decide⟩ :=
  accepted_of_selected 11 100691 ⟨1369634, by decide⟩ ⟨11, 2, 0, 1369634, 100691, 2797, 262144⟩
    (by decide) selected_cut_48728

theorem unmarked_context_10_25172_1369635 : frontier 11 ⟨1369635, by decide⟩
    (prefixCache 10 25172) (prefixPartial 10 25172) = false := by
  decide +kernel

theorem node_context_10_25172_1369635 : EJMOriginalGlobalDAGData.nodes 11 ⟨1369635, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1369510, by decide⟩,⟨1369569, by decide⟩,⟨1369634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25172_1369635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25172 ⟨1369635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25172
    ⟨1369635, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1369510, by decide⟩,⟨1369569, by decide⟩,⟨1369634, by decide⟩]) unmarked_context_10_25172_1369635 node_context_10_25172_1369635
  intro a
  fin_cases a
  · exact context_11_100688_1369428
  · exact context_11_100689_1369510
  · exact context_11_100690_1369569
  · exact context_11_100691_1369634

theorem selected_cut_48729 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25173) = some ⟨10, 1, 0, 893098, 25173, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25173_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25173 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25173 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25173, 1, 1048576⟩
    (by decide) selected_cut_48729

theorem selected_cut_48730 : selected 10 ⟨1369693, by decide⟩
    (prefixPartial 11 100696) = some ⟨11, 2, 0, 1369693, 100696, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_100696_1369693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100696 ⟨1369693, by decide⟩ :=
  accepted_of_selected 11 100696 ⟨1369693, by decide⟩ ⟨11, 2, 0, 1369693, 100696, 2869, 262144⟩
    (by decide) selected_cut_48730

theorem selected_cut_48731 : selected 10 ⟨1369758, by decide⟩
    (prefixPartial 11 100697) = some ⟨11, 2, 0, 1369758, 100697, 3353, 262144⟩ := by
  decide +kernel

theorem context_11_100697_1369758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100697 ⟨1369758, by decide⟩ :=
  accepted_of_selected 11 100697 ⟨1369758, by decide⟩ ⟨11, 2, 0, 1369758, 100697, 3353, 262144⟩
    (by decide) selected_cut_48731

theorem selected_cut_48732 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 100698) = some ⟨11, 1, 0, 1369759, 100698, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100698_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100698 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 100698 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 100698, 1, 262144⟩
    (by decide) selected_cut_48732

theorem selected_cut_48733 : selected 10 ⟨1369832, by decide⟩
    (prefixPartial 11 100699) = some ⟨11, 2, 0, 1369832, 100699, 3657, 262144⟩ := by
  decide +kernel

theorem context_11_100699_1369832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100699 ⟨1369832, by decide⟩ :=
  accepted_of_selected 11 100699 ⟨1369832, by decide⟩ ⟨11, 2, 0, 1369832, 100699, 3657, 262144⟩
    (by decide) selected_cut_48733

theorem unmarked_context_10_25174_1369833 : frontier 11 ⟨1369833, by decide⟩
    (prefixCache 10 25174) (prefixPartial 10 25174) = false := by
  decide +kernel

theorem node_context_10_25174_1369833 : EJMOriginalGlobalDAGData.nodes 11 ⟨1369833, by decide⟩ =
    .split (coordinate 10) (![⟨1369693, by decide⟩,⟨1369758, by decide⟩,⟨1369759, by decide⟩,⟨1369832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25174_1369833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25174 ⟨1369833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25174
    ⟨1369833, by decide⟩ (by decide) (![⟨1369693, by decide⟩,⟨1369758, by decide⟩,⟨1369759, by decide⟩,⟨1369832, by decide⟩]) unmarked_context_10_25174_1369833 node_context_10_25174_1369833
  intro a
  fin_cases a
  · exact context_11_100696_1369693
  · exact context_11_100697_1369758
  · exact context_11_100698_1369759
  · exact context_11_100699_1369832

theorem selected_cut_48734 : selected 10 ⟨1369908, by decide⟩
    (prefixPartial 11 100700) = some ⟨11, 2, 0, 1369908, 100700, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_100700_1369908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100700 ⟨1369908, by decide⟩ :=
  accepted_of_selected 11 100700 ⟨1369908, by decide⟩ ⟨11, 2, 0, 1369908, 100700, 2989, 262144⟩
    (by decide) selected_cut_48734

theorem selected_cut_48735 : selected 10 ⟨1369978, by decide⟩
    (prefixPartial 11 100701) = some ⟨11, 2, 0, 1369978, 100701, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_100701_1369978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100701 ⟨1369978, by decide⟩ :=
  accepted_of_selected 11 100701 ⟨1369978, by decide⟩ ⟨11, 2, 0, 1369978, 100701, 3469, 262144⟩
    (by decide) selected_cut_48735

theorem selected_cut_48736 : selected 10 ⟨1370050, by decide⟩
    (prefixPartial 11 100702) = some ⟨11, 2, 0, 1370050, 100702, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_100702_1370050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100702 ⟨1370050, by decide⟩ :=
  accepted_of_selected 11 100702 ⟨1370050, by decide⟩ ⟨11, 2, 0, 1370050, 100702, 3337, 262144⟩
    (by decide) selected_cut_48736

theorem selected_cut_48737 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 100703) = some ⟨11, 1, 0, 1370051, 100703, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100703_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100703 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 100703 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 100703, 1, 262144⟩
    (by decide) selected_cut_48737

theorem unmarked_context_10_25175_1370052 : frontier 11 ⟨1370052, by decide⟩
    (prefixCache 10 25175) (prefixPartial 10 25175) = false := by
  decide +kernel

theorem node_context_10_25175_1370052 : EJMOriginalGlobalDAGData.nodes 11 ⟨1370052, by decide⟩ =
    .split (coordinate 10) (![⟨1369908, by decide⟩,⟨1369978, by decide⟩,⟨1370050, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25175_1370052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25175 ⟨1370052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25175
    ⟨1370052, by decide⟩ (by decide) (![⟨1369908, by decide⟩,⟨1369978, by decide⟩,⟨1370050, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_25175_1370052 node_context_10_25175_1370052
  intro a
  fin_cases a
  · exact context_11_100700_1369908
  · exact context_11_100701_1369978
  · exact context_11_100702_1370050
  · exact context_11_100703_1370051

theorem unmarked_context_9_6293_1370053 : frontier 12 ⟨1370053, by decide⟩
    (prefixCache 9 6293) (prefixPartial 9 6293) = false := by
  decide +kernel

theorem node_context_9_6293_1370053 : EJMOriginalGlobalDAGData.nodes 12 ⟨1370053, by decide⟩ =
    .split (coordinate 9) (![⟨1369635, by decide⟩,⟨893098, by decide⟩,⟨1369833, by decide⟩,⟨1370052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6293_1370053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6293 ⟨1370053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6293
    ⟨1370053, by decide⟩ (by decide) (![⟨1369635, by decide⟩,⟨893098, by decide⟩,⟨1369833, by decide⟩,⟨1370052, by decide⟩]) unmarked_context_9_6293_1370053 node_context_9_6293_1370053
  intro a
  fin_cases a
  · exact context_10_25172_1369635
  · exact context_10_25173_893098
  · exact context_10_25174_1369833
  · exact context_10_25175_1370052

theorem selected_cut_48738 : selected 10 ⟨1370082, by decide⟩
    (prefixPartial 11 100704) = some ⟨11, 2, 0, 1370082, 100704, 1173, 262144⟩ := by
  decide +kernel

theorem context_11_100704_1370082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100704 ⟨1370082, by decide⟩ :=
  accepted_of_selected 11 100704 ⟨1370082, by decide⟩ ⟨11, 2, 0, 1370082, 100704, 1173, 262144⟩
    (by decide) selected_cut_48738

theorem selected_cut_48739 : selected 10 ⟨1370129, by decide⟩
    (prefixPartial 11 100705) = some ⟨11, 2, 0, 1370129, 100705, 1973, 262144⟩ := by
  decide +kernel

theorem context_11_100705_1370129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100705 ⟨1370129, by decide⟩ :=
  accepted_of_selected 11 100705 ⟨1370129, by decide⟩ ⟨11, 2, 0, 1370129, 100705, 1973, 262144⟩
    (by decide) selected_cut_48739

theorem selected_cut_48740 : selected 10 ⟨1370189, by decide⟩
    (prefixPartial 11 100706) = some ⟨11, 2, 0, 1370189, 100706, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_100706_1370189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100706 ⟨1370189, by decide⟩ :=
  accepted_of_selected 11 100706 ⟨1370189, by decide⟩ ⟨11, 2, 0, 1370189, 100706, 2781, 262144⟩
    (by decide) selected_cut_48740

theorem selected_cut_48741 : selected 10 ⟨1370251, by decide⟩
    (prefixPartial 11 100707) = some ⟨11, 2, 0, 1370251, 100707, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_100707_1370251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100707 ⟨1370251, by decide⟩ :=
  accepted_of_selected 11 100707 ⟨1370251, by decide⟩ ⟨11, 2, 0, 1370251, 100707, 2729, 262144⟩
    (by decide) selected_cut_48741

theorem unmarked_context_10_25176_1370252 : frontier 11 ⟨1370252, by decide⟩
    (prefixCache 10 25176) (prefixPartial 10 25176) = false := by
  decide +kernel

theorem node_context_10_25176_1370252 : EJMOriginalGlobalDAGData.nodes 11 ⟨1370252, by decide⟩ =
    .split (coordinate 10) (![⟨1370082, by decide⟩,⟨1370129, by decide⟩,⟨1370189, by decide⟩,⟨1370251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25176_1370252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25176 ⟨1370252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25176
    ⟨1370252, by decide⟩ (by decide) (![⟨1370082, by decide⟩,⟨1370129, by decide⟩,⟨1370189, by decide⟩,⟨1370251, by decide⟩]) unmarked_context_10_25176_1370252 node_context_10_25176_1370252
  intro a
  fin_cases a
  · exact context_11_100704_1370082
  · exact context_11_100705_1370129
  · exact context_11_100706_1370189
  · exact context_11_100707_1370251

theorem selected_cut_48742 : selected 10 ⟨1370294, by decide⟩
    (prefixPartial 11 100708) = some ⟨11, 2, 0, 1370294, 100708, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_100708_1370294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100708 ⟨1370294, by decide⟩ :=
  accepted_of_selected 11 100708 ⟨1370294, by decide⟩ ⟨11, 2, 0, 1370294, 100708, 1777, 262144⟩
    (by decide) selected_cut_48742

theorem selected_cut_48743 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 100709) = some ⟨11, 1, 0, 892405, 100709, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100709_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100709 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 100709 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 100709, 1, 262144⟩
    (by decide) selected_cut_48743

theorem selected_cut_48744 : selected 10 ⟨1370332, by decide⟩
    (prefixPartial 11 100710) = some ⟨11, 2, 0, 1370332, 100710, 2161, 262144⟩ := by
  decide +kernel

theorem context_11_100710_1370332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100710 ⟨1370332, by decide⟩ :=
  accepted_of_selected 11 100710 ⟨1370332, by decide⟩ ⟨11, 2, 0, 1370332, 100710, 2161, 262144⟩
    (by decide) selected_cut_48744

theorem selected_cut_48745 : selected 10 ⟨1370377, by decide⟩
    (prefixPartial 11 100711) = some ⟨11, 2, 0, 1370377, 100711, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_100711_1370377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100711 ⟨1370377, by decide⟩ :=
  accepted_of_selected 11 100711 ⟨1370377, by decide⟩ ⟨11, 2, 0, 1370377, 100711, 1985, 262144⟩
    (by decide) selected_cut_48745

theorem unmarked_context_10_25177_1370378 : frontier 11 ⟨1370378, by decide⟩
    (prefixCache 10 25177) (prefixPartial 10 25177) = false := by
  decide +kernel

theorem node_context_10_25177_1370378 : EJMOriginalGlobalDAGData.nodes 11 ⟨1370378, by decide⟩ =
    .split (coordinate 10) (![⟨1370294, by decide⟩,⟨892405, by decide⟩,⟨1370332, by decide⟩,⟨1370377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25177_1370378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25177 ⟨1370378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25177
    ⟨1370378, by decide⟩ (by decide) (![⟨1370294, by decide⟩,⟨892405, by decide⟩,⟨1370332, by decide⟩,⟨1370377, by decide⟩]) unmarked_context_10_25177_1370378 node_context_10_25177_1370378
  intro a
  fin_cases a
  · exact context_11_100708_1370294
  · exact context_11_100709_892405
  · exact context_11_100710_1370332
  · exact context_11_100711_1370377

theorem selected_cut_48746 : selected 11 ⟨1370429, by decide⟩
    (prefixPartial 10 25178) = some ⟨10, 2, 0, 1370429, 25178, 2285, 1048576⟩ := by
  decide +kernel

theorem context_10_25178_1370429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25178 ⟨1370429, by decide⟩ :=
  accepted_of_selected 10 25178 ⟨1370429, by decide⟩ ⟨10, 2, 0, 1370429, 25178, 2285, 1048576⟩
    (by decide) selected_cut_48746

theorem selected_cut_48747 : selected 10 ⟨1370464, by decide⟩
    (prefixPartial 11 100716) = some ⟨11, 2, 0, 1370464, 100716, 1881, 262144⟩ := by
  decide +kernel

theorem context_11_100716_1370464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100716 ⟨1370464, by decide⟩ :=
  accepted_of_selected 11 100716 ⟨1370464, by decide⟩ ⟨11, 2, 0, 1370464, 100716, 1881, 262144⟩
    (by decide) selected_cut_48747

theorem selected_cut_48748 : selected 10 ⟨1370501, by decide⟩
    (prefixPartial 11 100717) = some ⟨11, 2, 0, 1370501, 100717, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_100717_1370501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100717 ⟨1370501, by decide⟩ :=
  accepted_of_selected 11 100717 ⟨1370501, by decide⟩ ⟨11, 2, 0, 1370501, 100717, 1705, 262144⟩
    (by decide) selected_cut_48748

theorem selected_cut_48749 : selected 10 ⟨1370531, by decide⟩
    (prefixPartial 11 100718) = some ⟨11, 2, 0, 1370531, 100718, 1457, 262144⟩ := by
  decide +kernel

theorem context_11_100718_1370531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100718 ⟨1370531, by decide⟩ :=
  accepted_of_selected 11 100718 ⟨1370531, by decide⟩ ⟨11, 2, 0, 1370531, 100718, 1457, 262144⟩
    (by decide) selected_cut_48749

theorem selected_cut_48750 : selected 10 ⟨1370554, by decide⟩
    (prefixPartial 11 100719) = some ⟨11, 2, 0, 1370554, 100719, 953, 262144⟩ := by
  decide +kernel

theorem context_11_100719_1370554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100719 ⟨1370554, by decide⟩ :=
  accepted_of_selected 11 100719 ⟨1370554, by decide⟩ ⟨11, 2, 0, 1370554, 100719, 953, 262144⟩
    (by decide) selected_cut_48750

theorem unmarked_context_10_25179_1370555 : frontier 11 ⟨1370555, by decide⟩
    (prefixCache 10 25179) (prefixPartial 10 25179) = false := by
  decide +kernel

theorem node_context_10_25179_1370555 : EJMOriginalGlobalDAGData.nodes 11 ⟨1370555, by decide⟩ =
    .split (coordinate 10) (![⟨1370464, by decide⟩,⟨1370501, by decide⟩,⟨1370531, by decide⟩,⟨1370554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25179_1370555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25179 ⟨1370555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25179
    ⟨1370555, by decide⟩ (by decide) (![⟨1370464, by decide⟩,⟨1370501, by decide⟩,⟨1370531, by decide⟩,⟨1370554, by decide⟩]) unmarked_context_10_25179_1370555 node_context_10_25179_1370555
  intro a
  fin_cases a
  · exact context_11_100716_1370464
  · exact context_11_100717_1370501
  · exact context_11_100718_1370531
  · exact context_11_100719_1370554

theorem unmarked_context_9_6294_1370556 : frontier 12 ⟨1370556, by decide⟩
    (prefixCache 9 6294) (prefixPartial 9 6294) = false := by
  decide +kernel

theorem node_context_9_6294_1370556 : EJMOriginalGlobalDAGData.nodes 12 ⟨1370556, by decide⟩ =
    .split (coordinate 9) (![⟨1370252, by decide⟩,⟨1370378, by decide⟩,⟨1370429, by decide⟩,⟨1370555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6294_1370556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6294 ⟨1370556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6294
    ⟨1370556, by decide⟩ (by decide) (![⟨1370252, by decide⟩,⟨1370378, by decide⟩,⟨1370429, by decide⟩,⟨1370555, by decide⟩]) unmarked_context_9_6294_1370556 node_context_9_6294_1370556
  intro a
  fin_cases a
  · exact context_10_25176_1370252
  · exact context_10_25177_1370378
  · exact context_10_25178_1370429
  · exact context_10_25179_1370555

theorem selected_cut_48751 : selected 11 ⟨1370644, by decide⟩
    (prefixPartial 10 25180) = some ⟨10, 2, 0, 1370644, 25180, 3585, 1048576⟩ := by
  decide +kernel

theorem context_10_25180_1370644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25180 ⟨1370644, by decide⟩ :=
  accepted_of_selected 10 25180 ⟨1370644, by decide⟩ ⟨10, 2, 0, 1370644, 25180, 3585, 1048576⟩
    (by decide) selected_cut_48751

theorem selected_cut_48752 : selected 11 ⟨1370695, by decide⟩
    (prefixPartial 10 25181) = some ⟨10, 2, 0, 1370695, 25181, 2033, 1048576⟩ := by
  decide +kernel

theorem context_10_25181_1370695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25181 ⟨1370695, by decide⟩ :=
  accepted_of_selected 10 25181 ⟨1370695, by decide⟩ ⟨10, 2, 0, 1370695, 25181, 2033, 1048576⟩
    (by decide) selected_cut_48752

theorem selected_cut_48753 : selected 11 ⟨1370747, by decide⟩
    (prefixPartial 10 25182) = some ⟨10, 2, 0, 1370747, 25182, 1457, 1048576⟩ := by
  decide +kernel

theorem context_10_25182_1370747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25182 ⟨1370747, by decide⟩ :=
  accepted_of_selected 10 25182 ⟨1370747, by decide⟩ ⟨10, 2, 0, 1370747, 25182, 1457, 1048576⟩
    (by decide) selected_cut_48753

theorem selected_cut_48754 : selected 11 ⟨1370756, by decide⟩
    (prefixPartial 10 25183) = some ⟨10, 2, 0, 1370756, 25183, 141, 1048576⟩ := by
  decide +kernel

theorem context_10_25183_1370756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25183 ⟨1370756, by decide⟩ :=
  accepted_of_selected 10 25183 ⟨1370756, by decide⟩ ⟨10, 2, 0, 1370756, 25183, 141, 1048576⟩
    (by decide) selected_cut_48754

theorem unmarked_context_9_6295_1370757 : frontier 12 ⟨1370757, by decide⟩
    (prefixCache 9 6295) (prefixPartial 9 6295) = false := by
  decide +kernel

theorem node_context_9_6295_1370757 : EJMOriginalGlobalDAGData.nodes 12 ⟨1370757, by decide⟩ =
    .split (coordinate 9) (![⟨1370644, by decide⟩,⟨1370695, by decide⟩,⟨1370747, by decide⟩,⟨1370756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6295_1370757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6295 ⟨1370757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6295
    ⟨1370757, by decide⟩ (by decide) (![⟨1370644, by decide⟩,⟨1370695, by decide⟩,⟨1370747, by decide⟩,⟨1370756, by decide⟩]) unmarked_context_9_6295_1370757 node_context_9_6295_1370757
  intro a
  fin_cases a
  · exact context_10_25180_1370644
  · exact context_10_25181_1370695
  · exact context_10_25182_1370747
  · exact context_10_25183_1370756

theorem unmarked_context_8_1573_1370758 : frontier 13 ⟨1370758, by decide⟩
    (prefixCache 8 1573) (prefixPartial 8 1573) = false := by
  decide +kernel

theorem node_context_8_1573_1370758 : EJMOriginalGlobalDAGData.nodes 13 ⟨1370758, by decide⟩ =
    .split (coordinate 8) (![⟨1369427, by decide⟩,⟨1370053, by decide⟩,⟨1370556, by decide⟩,⟨1370757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1573_1370758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1573 ⟨1370758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1573
    ⟨1370758, by decide⟩ (by decide) (![⟨1369427, by decide⟩,⟨1370053, by decide⟩,⟨1370556, by decide⟩,⟨1370757, by decide⟩]) unmarked_context_8_1573_1370758 node_context_8_1573_1370758
  intro a
  fin_cases a
  · exact context_9_6292_1369427
  · exact context_9_6293_1370053
  · exact context_9_6294_1370556
  · exact context_9_6295_1370757

theorem selected_cut_48755 : selected 13 ⟨1366235, by decide⟩
    (prefixPartial 8 1574) = some ⟨8, 1, 0, 1366235, 1574, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1574_1366235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1574 ⟨1366235, by decide⟩ :=
  accepted_of_selected 8 1574 ⟨1366235, by decide⟩ ⟨8, 1, 0, 1366235, 1574, 1, 16777216⟩
    (by decide) selected_cut_48755

theorem selected_cut_48756 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 100800) = some ⟨11, 1, 0, 434745, 100800, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100800_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100800 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 100800 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 100800, 1, 262144⟩
    (by decide) selected_cut_48756

theorem selected_cut_48757 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 100801) = some ⟨11, 1, 0, 434745, 100801, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100801_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100801 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 100801 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 100801, 1, 262144⟩
    (by decide) selected_cut_48757

theorem selected_cut_48758 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 403208) = some ⟨12, 1, 0, 448748, 403208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403208_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403208 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 403208 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 403208, 1, 65536⟩
    (by decide) selected_cut_48758

theorem selected_cut_48759 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 403209) = some ⟨12, 1, 0, 448748, 403209, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403209_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403209 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 403209 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 403209, 1, 65536⟩
    (by decide) selected_cut_48759

theorem selected_cut_48760 : selected 9 ⟨1370839, by decide⟩
    (prefixPartial 12 403210) = some ⟨12, 2, 0, 1370839, 403210, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_403210_1370839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403210 ⟨1370839, by decide⟩ :=
  accepted_of_selected 12 403210 ⟨1370839, by decide⟩ ⟨12, 2, 0, 1370839, 403210, 2377, 65536⟩
    (by decide) selected_cut_48760

theorem selected_cut_48761 : selected 9 ⟨1370897, by decide⟩
    (prefixPartial 12 403211) = some ⟨12, 2, 0, 1370897, 403211, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_403211_1370897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403211 ⟨1370897, by decide⟩ :=
  accepted_of_selected 12 403211 ⟨1370897, by decide⟩ ⟨12, 2, 0, 1370897, 403211, 2197, 65536⟩
    (by decide) selected_cut_48761

theorem unmarked_context_11_100802_1370898 : frontier 10 ⟨1370898, by decide⟩
    (prefixCache 11 100802) (prefixPartial 11 100802) = false := by
  decide +kernel

theorem node_context_11_100802_1370898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1370898, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1370839, by decide⟩,⟨1370897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100802_1370898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100802 ⟨1370898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100802
    ⟨1370898, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1370839, by decide⟩,⟨1370897, by decide⟩]) unmarked_context_11_100802_1370898 node_context_11_100802_1370898
  intro a
  fin_cases a
  · exact context_12_403208_448748
  · exact context_12_403209_448748
  · exact context_12_403210_1370839
  · exact context_12_403211_1370897

theorem selected_cut_48762 : selected 10 ⟨1370960, by decide⟩
    (prefixPartial 11 100803) = some ⟨11, 2, 0, 1370960, 100803, 2437, 262144⟩ := by
  decide +kernel

theorem context_11_100803_1370960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100803 ⟨1370960, by decide⟩ :=
  accepted_of_selected 11 100803 ⟨1370960, by decide⟩ ⟨11, 2, 0, 1370960, 100803, 2437, 262144⟩
    (by decide) selected_cut_48762

theorem unmarked_context_10_25200_1370961 : frontier 11 ⟨1370961, by decide⟩
    (prefixCache 10 25200) (prefixPartial 10 25200) = false := by
  decide +kernel

theorem node_context_10_25200_1370961 : EJMOriginalGlobalDAGData.nodes 11 ⟨1370961, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1370898, by decide⟩,⟨1370960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25200_1370961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25200 ⟨1370961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25200
    ⟨1370961, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1370898, by decide⟩,⟨1370960, by decide⟩]) unmarked_context_10_25200_1370961 node_context_10_25200_1370961
  intro a
  fin_cases a
  · exact context_11_100800_434745
  · exact context_11_100801_434745
  · exact context_11_100802_1370898
  · exact context_11_100803_1370960

theorem selected_cut_48763 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403216) = some ⟨12, 1, 0, 1108174, 403216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403216_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403216 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403216 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403216, 1, 65536⟩
    (by decide) selected_cut_48763

theorem selected_cut_48764 : selected 9 ⟨1371035, by decide⟩
    (prefixPartial 12 403217) = some ⟨12, 2, 0, 1371035, 403217, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_403217_1371035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403217 ⟨1371035, by decide⟩ :=
  accepted_of_selected 12 403217 ⟨1371035, by decide⟩ ⟨12, 2, 0, 1371035, 403217, 2497, 65536⟩
    (by decide) selected_cut_48764

theorem selected_cut_48765 : selected 9 ⟨1371107, by decide⟩
    (prefixPartial 12 403218) = some ⟨12, 2, 0, 1371107, 403218, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_403218_1371107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403218 ⟨1371107, by decide⟩ :=
  accepted_of_selected 12 403218 ⟨1371107, by decide⟩ ⟨12, 2, 0, 1371107, 403218, 2585, 65536⟩
    (by decide) selected_cut_48765

theorem selected_cut_48766 : selected 9 ⟨1371176, by decide⟩
    (prefixPartial 12 403219) = some ⟨12, 2, 0, 1371176, 403219, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_403219_1371176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403219 ⟨1371176, by decide⟩ :=
  accepted_of_selected 12 403219 ⟨1371176, by decide⟩ ⟨12, 2, 0, 1371176, 403219, 2613, 65536⟩
    (by decide) selected_cut_48766

theorem unmarked_context_11_100804_1371177 : frontier 10 ⟨1371177, by decide⟩
    (prefixCache 11 100804) (prefixPartial 11 100804) = false := by
  decide +kernel

theorem node_context_11_100804_1371177 : EJMOriginalGlobalDAGData.nodes 10 ⟨1371177, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1371035, by decide⟩,⟨1371107, by decide⟩,⟨1371176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100804_1371177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100804 ⟨1371177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100804
    ⟨1371177, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1371035, by decide⟩,⟨1371107, by decide⟩,⟨1371176, by decide⟩]) unmarked_context_11_100804_1371177 node_context_11_100804_1371177
  intro a
  fin_cases a
  · exact context_12_403216_1108174
  · exact context_12_403217_1371035
  · exact context_12_403218_1371107
  · exact context_12_403219_1371176

theorem selected_cut_48767 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 100805) = some ⟨11, 1, 0, 892405, 100805, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100805_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100805 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 100805 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 100805, 1, 262144⟩
    (by decide) selected_cut_48767

theorem selected_cut_48768 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403224) = some ⟨12, 1, 0, 1108174, 403224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403224_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403224 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403224 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403224, 1, 65536⟩
    (by decide) selected_cut_48768

theorem selected_cut_48769 : selected 9 ⟨1371219, by decide⟩
    (prefixPartial 12 403225) = some ⟨12, 2, 0, 1371219, 403225, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_403225_1371219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403225 ⟨1371219, by decide⟩ :=
  accepted_of_selected 12 403225 ⟨1371219, by decide⟩ ⟨12, 2, 0, 1371219, 403225, 2045, 65536⟩
    (by decide) selected_cut_48769

theorem selected_cut_48770 : selected 9 ⟨1371268, by decide⟩
    (prefixPartial 12 403226) = some ⟨12, 2, 0, 1371268, 403226, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_403226_1371268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403226 ⟨1371268, by decide⟩ :=
  accepted_of_selected 12 403226 ⟨1371268, by decide⟩ ⟨12, 2, 0, 1371268, 403226, 2077, 65536⟩
    (by decide) selected_cut_48770

theorem selected_cut_48771 : selected 9 ⟨1371311, by decide⟩
    (prefixPartial 12 403227) = some ⟨12, 2, 0, 1371311, 403227, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_403227_1371311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403227 ⟨1371311, by decide⟩ :=
  accepted_of_selected 12 403227 ⟨1371311, by decide⟩ ⟨12, 2, 0, 1371311, 403227, 2013, 65536⟩
    (by decide) selected_cut_48771

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
