/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover526
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_106444_1447209 : frontier 10 ⟨1447209, by decide⟩
    (prefixCache 11 106444) (prefixPartial 11 106444) = false := by
  decide +kernel

theorem node_context_11_106444_1447209 : EJMOriginalGlobalDAGData.nodes 10 ⟨1447209, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1447138, by decide⟩,⟨1447176, by decide⟩,⟨1447208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106444_1447209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106444 ⟨1447209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106444
    ⟨1447209, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1447138, by decide⟩,⟨1447176, by decide⟩,⟨1447208, by decide⟩]) unmarked_context_11_106444_1447209 node_context_11_106444_1447209
  intro a
  fin_cases a
  · exact context_12_425776_1416143
  · exact context_12_425777_1447138
  · exact context_12_425778_1447176
  · exact context_12_425779_1447208

theorem selected_cut_50597 : selected 10 ⟨1447277, by decide⟩
    (prefixPartial 11 106445) = some ⟨11, 2, 0, 1447277, 106445, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_106445_1447277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106445 ⟨1447277, by decide⟩ :=
  accepted_of_selected 11 106445 ⟨1447277, by decide⟩ ⟨11, 2, 0, 1447277, 106445, 2657, 262144⟩
    (by decide) selected_cut_50597

theorem selected_cut_50598 : selected 10 ⟨1447339, by decide⟩
    (prefixPartial 11 106446) = some ⟨11, 2, 0, 1447339, 106446, 2641, 262144⟩ := by
  decide +kernel

theorem context_11_106446_1447339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106446 ⟨1447339, by decide⟩ :=
  accepted_of_selected 11 106446 ⟨1447339, by decide⟩ ⟨11, 2, 0, 1447339, 106446, 2641, 262144⟩
    (by decide) selected_cut_50598

theorem selected_cut_50599 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106447) = some ⟨11, 1, 0, 977886, 106447, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106447_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106447 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106447 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106447, 1, 262144⟩
    (by decide) selected_cut_50599

theorem unmarked_context_10_26611_1447340 : frontier 11 ⟨1447340, by decide⟩
    (prefixCache 10 26611) (prefixPartial 10 26611) = false := by
  decide +kernel

theorem node_context_10_26611_1447340 : EJMOriginalGlobalDAGData.nodes 11 ⟨1447340, by decide⟩ =
    .split (coordinate 10) (![⟨1447209, by decide⟩,⟨1447277, by decide⟩,⟨1447339, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26611_1447340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26611 ⟨1447340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26611
    ⟨1447340, by decide⟩ (by decide) (![⟨1447209, by decide⟩,⟨1447277, by decide⟩,⟨1447339, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26611_1447340 node_context_10_26611_1447340
  intro a
  fin_cases a
  · exact context_11_106444_1447209
  · exact context_11_106445_1447277
  · exact context_11_106446_1447339
  · exact context_11_106447_977886

theorem unmarked_context_9_6652_1447341 : frontier 12 ⟨1447341, by decide⟩
    (prefixCache 9 6652) (prefixPartial 9 6652) = false := by
  decide +kernel

theorem node_context_9_6652_1447341 : EJMOriginalGlobalDAGData.nodes 12 ⟨1447341, by decide⟩ =
    .split (coordinate 9) (![⟨1446307, by decide⟩,⟨1446711, by decide⟩,⟨1447100, by decide⟩,⟨1447340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6652_1447341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6652 ⟨1447341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6652
    ⟨1447341, by decide⟩ (by decide) (![⟨1446307, by decide⟩,⟨1446711, by decide⟩,⟨1447100, by decide⟩,⟨1447340, by decide⟩]) unmarked_context_9_6652_1447341 node_context_9_6652_1447341
  intro a
  fin_cases a
  · exact context_10_26608_1446307
  · exact context_10_26609_1446711
  · exact context_10_26610_1447100
  · exact context_10_26611_1447340

theorem selected_cut_50600 : selected 10 ⟨1447403, by decide⟩
    (prefixPartial 11 106448) = some ⟨11, 2, 0, 1447403, 106448, 757, 262144⟩ := by
  decide +kernel

theorem context_11_106448_1447403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106448 ⟨1447403, by decide⟩ :=
  accepted_of_selected 11 106448 ⟨1447403, by decide⟩ ⟨11, 2, 0, 1447403, 106448, 757, 262144⟩
    (by decide) selected_cut_50600

theorem selected_cut_50601 : selected 10 ⟨1447499, by decide⟩
    (prefixPartial 11 106449) = some ⟨11, 2, 0, 1447499, 106449, 3693, 262144⟩ := by
  decide +kernel

theorem context_11_106449_1447499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106449 ⟨1447499, by decide⟩ :=
  accepted_of_selected 11 106449 ⟨1447499, by decide⟩ ⟨11, 2, 0, 1447499, 106449, 3693, 262144⟩
    (by decide) selected_cut_50601

theorem selected_cut_50602 : selected 10 ⟨1447608, by decide⟩
    (prefixPartial 11 106450) = some ⟨11, 2, 0, 1447608, 106450, 2937, 262144⟩ := by
  decide +kernel

theorem context_11_106450_1447608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106450 ⟨1447608, by decide⟩ :=
  accepted_of_selected 11 106450 ⟨1447608, by decide⟩ ⟨11, 2, 0, 1447608, 106450, 2937, 262144⟩
    (by decide) selected_cut_50602

theorem selected_cut_50603 : selected 10 ⟨1447663, by decide⟩
    (prefixPartial 11 106451) = some ⟨11, 2, 0, 1447663, 106451, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_106451_1447663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106451 ⟨1447663, by decide⟩ :=
  accepted_of_selected 11 106451 ⟨1447663, by decide⟩ ⟨11, 2, 0, 1447663, 106451, 2361, 262144⟩
    (by decide) selected_cut_50603

theorem unmarked_context_10_26612_1447664 : frontier 11 ⟨1447664, by decide⟩
    (prefixCache 10 26612) (prefixPartial 10 26612) = false := by
  decide +kernel

theorem node_context_10_26612_1447664 : EJMOriginalGlobalDAGData.nodes 11 ⟨1447664, by decide⟩ =
    .split (coordinate 10) (![⟨1447403, by decide⟩,⟨1447499, by decide⟩,⟨1447608, by decide⟩,⟨1447663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26612_1447664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26612 ⟨1447664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26612
    ⟨1447664, by decide⟩ (by decide) (![⟨1447403, by decide⟩,⟨1447499, by decide⟩,⟨1447608, by decide⟩,⟨1447663, by decide⟩]) unmarked_context_10_26612_1447664 node_context_10_26612_1447664
  intro a
  fin_cases a
  · exact context_11_106448_1447403
  · exact context_11_106449_1447499
  · exact context_11_106450_1447608
  · exact context_11_106451_1447663

theorem selected_cut_50604 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26613) = some ⟨10, 1, 0, 893098, 26613, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26613_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26613 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26613 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26613, 1, 1048576⟩
    (by decide) selected_cut_50604

theorem selected_cut_50605 : selected 10 ⟨1447780, by decide⟩
    (prefixPartial 11 106456) = some ⟨11, 2, 0, 1447780, 106456, 2705, 262144⟩ := by
  decide +kernel

theorem context_11_106456_1447780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106456 ⟨1447780, by decide⟩ :=
  accepted_of_selected 11 106456 ⟨1447780, by decide⟩ ⟨11, 2, 0, 1447780, 106456, 2705, 262144⟩
    (by decide) selected_cut_50605

theorem selected_cut_50606 : selected 10 ⟨1447836, by decide⟩
    (prefixPartial 11 106457) = some ⟨11, 2, 0, 1447836, 106457, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_106457_1447836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106457 ⟨1447836, by decide⟩ :=
  accepted_of_selected 11 106457 ⟨1447836, by decide⟩ ⟨11, 2, 0, 1447836, 106457, 2621, 262144⟩
    (by decide) selected_cut_50606

theorem selected_cut_50607 : selected 10 ⟨1447866, by decide⟩
    (prefixPartial 11 106458) = some ⟨11, 2, 0, 1447866, 106458, 321, 262144⟩ := by
  decide +kernel

theorem context_11_106458_1447866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106458 ⟨1447866, by decide⟩ :=
  accepted_of_selected 11 106458 ⟨1447866, by decide⟩ ⟨11, 2, 0, 1447866, 106458, 321, 262144⟩
    (by decide) selected_cut_50607

theorem selected_cut_50608 : selected 10 ⟨1447890, by decide⟩
    (prefixPartial 11 106459) = some ⟨11, 2, 0, 1447890, 106459, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_106459_1447890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106459 ⟨1447890, by decide⟩ :=
  accepted_of_selected 11 106459 ⟨1447890, by decide⟩ ⟨11, 2, 0, 1447890, 106459, 1533, 262144⟩
    (by decide) selected_cut_50608

theorem unmarked_context_10_26614_1447891 : frontier 11 ⟨1447891, by decide⟩
    (prefixCache 10 26614) (prefixPartial 10 26614) = false := by
  decide +kernel

theorem node_context_10_26614_1447891 : EJMOriginalGlobalDAGData.nodes 11 ⟨1447891, by decide⟩ =
    .split (coordinate 10) (![⟨1447780, by decide⟩,⟨1447836, by decide⟩,⟨1447866, by decide⟩,⟨1447890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26614_1447891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26614 ⟨1447891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26614
    ⟨1447891, by decide⟩ (by decide) (![⟨1447780, by decide⟩,⟨1447836, by decide⟩,⟨1447866, by decide⟩,⟨1447890, by decide⟩]) unmarked_context_10_26614_1447891 node_context_10_26614_1447891
  intro a
  fin_cases a
  · exact context_11_106456_1447780
  · exact context_11_106457_1447836
  · exact context_11_106458_1447866
  · exact context_11_106459_1447890

theorem selected_cut_50609 : selected 10 ⟨1447921, by decide⟩
    (prefixPartial 11 106460) = some ⟨11, 2, 0, 1447921, 106460, 1393, 262144⟩ := by
  decide +kernel

theorem context_11_106460_1447921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106460 ⟨1447921, by decide⟩ :=
  accepted_of_selected 11 106460 ⟨1447921, by decide⟩ ⟨11, 2, 0, 1447921, 106460, 1393, 262144⟩
    (by decide) selected_cut_50609

theorem selected_cut_50610 : selected 10 ⟨1447958, by decide⟩
    (prefixPartial 11 106461) = some ⟨11, 2, 0, 1447958, 106461, 2017, 262144⟩ := by
  decide +kernel

theorem context_11_106461_1447958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106461 ⟨1447958, by decide⟩ :=
  accepted_of_selected 11 106461 ⟨1447958, by decide⟩ ⟨11, 2, 0, 1447958, 106461, 2017, 262144⟩
    (by decide) selected_cut_50610

theorem selected_cut_50611 : selected 10 ⟨1447986, by decide⟩
    (prefixPartial 11 106462) = some ⟨11, 2, 0, 1447986, 106462, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_106462_1447986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106462 ⟨1447986, by decide⟩ :=
  accepted_of_selected 11 106462 ⟨1447986, by decide⟩ ⟨11, 2, 0, 1447986, 106462, 1213, 262144⟩
    (by decide) selected_cut_50611

theorem selected_cut_50612 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106463) = some ⟨11, 1, 0, 977886, 106463, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106463_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106463 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106463 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106463, 1, 262144⟩
    (by decide) selected_cut_50612

theorem unmarked_context_10_26615_1447987 : frontier 11 ⟨1447987, by decide⟩
    (prefixCache 10 26615) (prefixPartial 10 26615) = false := by
  decide +kernel

theorem node_context_10_26615_1447987 : EJMOriginalGlobalDAGData.nodes 11 ⟨1447987, by decide⟩ =
    .split (coordinate 10) (![⟨1447921, by decide⟩,⟨1447958, by decide⟩,⟨1447986, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26615_1447987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26615 ⟨1447987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26615
    ⟨1447987, by decide⟩ (by decide) (![⟨1447921, by decide⟩,⟨1447958, by decide⟩,⟨1447986, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26615_1447987 node_context_10_26615_1447987
  intro a
  fin_cases a
  · exact context_11_106460_1447921
  · exact context_11_106461_1447958
  · exact context_11_106462_1447986
  · exact context_11_106463_977886

theorem unmarked_context_9_6653_1447988 : frontier 12 ⟨1447988, by decide⟩
    (prefixCache 9 6653) (prefixPartial 9 6653) = false := by
  decide +kernel

theorem node_context_9_6653_1447988 : EJMOriginalGlobalDAGData.nodes 12 ⟨1447988, by decide⟩ =
    .split (coordinate 9) (![⟨1447664, by decide⟩,⟨893098, by decide⟩,⟨1447891, by decide⟩,⟨1447987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6653_1447988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6653 ⟨1447988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6653
    ⟨1447988, by decide⟩ (by decide) (![⟨1447664, by decide⟩,⟨893098, by decide⟩,⟨1447891, by decide⟩,⟨1447987, by decide⟩]) unmarked_context_9_6653_1447988 node_context_9_6653_1447988
  intro a
  fin_cases a
  · exact context_10_26612_1447664
  · exact context_10_26613_893098
  · exact context_10_26614_1447891
  · exact context_10_26615_1447987

theorem selected_cut_50613 : selected 10 ⟨1447989, by decide⟩
    (prefixPartial 11 106464) = some ⟨11, 2, 0, 1447989, 106464, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106464_1447989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106464 ⟨1447989, by decide⟩ :=
  accepted_of_selected 11 106464 ⟨1447989, by decide⟩ ⟨11, 2, 0, 1447989, 106464, 5, 262144⟩
    (by decide) selected_cut_50613

theorem selected_cut_50614 : selected 10 ⟨1448027, by decide⟩
    (prefixPartial 11 106465) = some ⟨11, 2, 0, 1448027, 106465, 1501, 262144⟩ := by
  decide +kernel

theorem context_11_106465_1448027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106465 ⟨1448027, by decide⟩ :=
  accepted_of_selected 11 106465 ⟨1448027, by decide⟩ ⟨11, 2, 0, 1448027, 106465, 1501, 262144⟩
    (by decide) selected_cut_50614

theorem selected_cut_50615 : selected 10 ⟨1448079, by decide⟩
    (prefixPartial 11 106466) = some ⟨11, 2, 0, 1448079, 106466, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_106466_1448079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106466 ⟨1448079, by decide⟩ :=
  accepted_of_selected 11 106466 ⟨1448079, by decide⟩ ⟨11, 2, 0, 1448079, 106466, 2141, 262144⟩
    (by decide) selected_cut_50615

theorem selected_cut_50616 : selected 10 ⟨1448118, by decide⟩
    (prefixPartial 11 106467) = some ⟨11, 2, 0, 1448118, 106467, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_106467_1448118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106467 ⟨1448118, by decide⟩ :=
  accepted_of_selected 11 106467 ⟨1448118, by decide⟩ ⟨11, 2, 0, 1448118, 106467, 1313, 262144⟩
    (by decide) selected_cut_50616

theorem unmarked_context_10_26616_1448119 : frontier 11 ⟨1448119, by decide⟩
    (prefixCache 10 26616) (prefixPartial 10 26616) = false := by
  decide +kernel

theorem node_context_10_26616_1448119 : EJMOriginalGlobalDAGData.nodes 11 ⟨1448119, by decide⟩ =
    .split (coordinate 10) (![⟨1447989, by decide⟩,⟨1448027, by decide⟩,⟨1448079, by decide⟩,⟨1448118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26616_1448119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26616 ⟨1448119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26616
    ⟨1448119, by decide⟩ (by decide) (![⟨1447989, by decide⟩,⟨1448027, by decide⟩,⟨1448079, by decide⟩,⟨1448118, by decide⟩]) unmarked_context_10_26616_1448119 node_context_10_26616_1448119
  intro a
  fin_cases a
  · exact context_11_106464_1447989
  · exact context_11_106465_1448027
  · exact context_11_106466_1448079
  · exact context_11_106467_1448118

theorem selected_cut_50617 : selected 11 ⟨1448185, by decide⟩
    (prefixPartial 10 26617) = some ⟨10, 2, 0, 1448185, 26617, 3425, 1048576⟩ := by
  decide +kernel

theorem context_10_26617_1448185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26617 ⟨1448185, by decide⟩ :=
  accepted_of_selected 10 26617 ⟨1448185, by decide⟩ ⟨10, 2, 0, 1448185, 26617, 3425, 1048576⟩
    (by decide) selected_cut_50617

theorem selected_cut_50618 : selected 11 ⟨1448191, by decide⟩
    (prefixPartial 10 26618) = some ⟨10, 2, 0, 1448191, 26618, 141, 1048576⟩ := by
  decide +kernel

theorem context_10_26618_1448191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26618 ⟨1448191, by decide⟩ :=
  accepted_of_selected 10 26618 ⟨1448191, by decide⟩ ⟨10, 2, 0, 1448191, 26618, 141, 1048576⟩
    (by decide) selected_cut_50618

theorem selected_cut_50619 : selected 11 ⟨1448249, by decide⟩
    (prefixPartial 10 26619) = some ⟨10, 2, 0, 1448249, 26619, 2393, 1048576⟩ := by
  decide +kernel

theorem context_10_26619_1448249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26619 ⟨1448249, by decide⟩ :=
  accepted_of_selected 10 26619 ⟨1448249, by decide⟩ ⟨10, 2, 0, 1448249, 26619, 2393, 1048576⟩
    (by decide) selected_cut_50619

theorem unmarked_context_9_6654_1448250 : frontier 12 ⟨1448250, by decide⟩
    (prefixCache 9 6654) (prefixPartial 9 6654) = false := by
  decide +kernel

theorem node_context_9_6654_1448250 : EJMOriginalGlobalDAGData.nodes 12 ⟨1448250, by decide⟩ =
    .split (coordinate 9) (![⟨1448119, by decide⟩,⟨1448185, by decide⟩,⟨1448191, by decide⟩,⟨1448249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6654_1448250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6654 ⟨1448250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6654
    ⟨1448250, by decide⟩ (by decide) (![⟨1448119, by decide⟩,⟨1448185, by decide⟩,⟨1448191, by decide⟩,⟨1448249, by decide⟩]) unmarked_context_9_6654_1448250 node_context_9_6654_1448250
  intro a
  fin_cases a
  · exact context_10_26616_1448119
  · exact context_10_26617_1448185
  · exact context_10_26618_1448191
  · exact context_10_26619_1448249

theorem selected_cut_50620 : selected 12 ⟨1448339, by decide⟩
    (prefixPartial 9 6655) = some ⟨9, 2, 0, 1448339, 6655, 2493, 4194304⟩ := by
  decide +kernel

theorem context_9_6655_1448339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6655 ⟨1448339, by decide⟩ :=
  accepted_of_selected 9 6655 ⟨1448339, by decide⟩ ⟨9, 2, 0, 1448339, 6655, 2493, 4194304⟩
    (by decide) selected_cut_50620

theorem unmarked_context_8_1663_1448340 : frontier 13 ⟨1448340, by decide⟩
    (prefixCache 8 1663) (prefixPartial 8 1663) = false := by
  decide +kernel

theorem node_context_8_1663_1448340 : EJMOriginalGlobalDAGData.nodes 13 ⟨1448340, by decide⟩ =
    .split (coordinate 8) (![⟨1447341, by decide⟩,⟨1447988, by decide⟩,⟨1448250, by decide⟩,⟨1448339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1663_1448340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1663 ⟨1448340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1663
    ⟨1448340, by decide⟩ (by decide) (![⟨1447341, by decide⟩,⟨1447988, by decide⟩,⟨1448250, by decide⟩,⟨1448339, by decide⟩]) unmarked_context_8_1663_1448340 node_context_8_1663_1448340
  intro a
  fin_cases a
  · exact context_9_6652_1447341
  · exact context_9_6653_1447988
  · exact context_9_6654_1448250
  · exact context_9_6655_1448339

theorem unmarked_context_7_415_1448341 : frontier 14 ⟨1448341, by decide⟩
    (prefixCache 7 415) (prefixPartial 7 415) = false := by
  decide +kernel

theorem node_context_7_415_1448341 : EJMOriginalGlobalDAGData.nodes 14 ⟨1448341, by decide⟩ =
    .split (coordinate 7) (![⟨1442329, by decide⟩,⟨1444274, by decide⟩,⟨1446220, by decide⟩,⟨1448340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_415_1448341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 415 ⟨1448341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 415
    ⟨1448341, by decide⟩ (by decide) (![⟨1442329, by decide⟩,⟨1444274, by decide⟩,⟨1446220, by decide⟩,⟨1448340, by decide⟩]) unmarked_context_7_415_1448341 node_context_7_415_1448341
  intro a
  fin_cases a
  · exact context_8_1660_1442329
  · exact context_8_1661_1444274
  · exact context_8_1662_1446220
  · exact context_8_1663_1448340

theorem unmarked_context_6_103_1448342 : frontier 15 ⟨1448342, by decide⟩
    (prefixCache 6 103) (prefixPartial 6 103) = false := by
  decide +kernel

theorem node_context_6_103_1448342 : EJMOriginalGlobalDAGData.nodes 15 ⟨1448342, by decide⟩ =
    .split (coordinate 6) (![⟨1423770, by decide⟩,⟨1430330, by decide⟩,⟨1440092, by decide⟩,⟨1448341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_103_1448342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 103 ⟨1448342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 103
    ⟨1448342, by decide⟩ (by decide) (![⟨1423770, by decide⟩,⟨1430330, by decide⟩,⟨1440092, by decide⟩,⟨1448341, by decide⟩]) unmarked_context_6_103_1448342 node_context_6_103_1448342
  intro a
  fin_cases a
  · exact context_7_412_1423770
  · exact context_7_413_1430330
  · exact context_7_414_1440092
  · exact context_7_415_1448341

theorem unmarked_context_5_25_1448343 : frontier 16 ⟨1448343, by decide⟩
    (prefixCache 5 25) (prefixPartial 5 25) = false := by
  decide +kernel

theorem node_context_5_25_1448343 : EJMOriginalGlobalDAGData.nodes 16 ⟨1448343, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨434744, by decide⟩,⟨1423769, by decide⟩,⟨1448342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_25_1448343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 25 ⟨1448343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 25
    ⟨1448343, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨434744, by decide⟩,⟨1423769, by decide⟩,⟨1448342, by decide⟩]) unmarked_context_5_25_1448343 node_context_5_25_1448343
  intro a
  fin_cases a
  · exact context_6_100_434744
  · exact context_6_101_434744
  · exact context_6_102_1423769
  · exact context_6_103_1448342

theorem selected_cut_50621 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 104) = some ⟨6, 1, 0, 434744, 104, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_104_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 104 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 104 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 104, 1, 268435456⟩
    (by decide) selected_cut_50621

theorem selected_cut_50622 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 105) = some ⟨6, 1, 0, 434744, 105, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_105_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 105 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 105 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 105, 1, 268435456⟩
    (by decide) selected_cut_50622

theorem selected_cut_50623 : selected 15 ⟨1448347, by decide⟩
    (prefixPartial 6 106) = some ⟨6, 2, 0, 1448347, 106, 13, 268435456⟩ := by
  decide +kernel

theorem context_6_106_1448347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 106 ⟨1448347, by decide⟩ :=
  accepted_of_selected 6 106 ⟨1448347, by decide⟩ ⟨6, 2, 0, 1448347, 106, 13, 268435456⟩
    (by decide) selected_cut_50623

theorem selected_cut_50624 : selected 14 ⟨1423770, by decide⟩
    (prefixPartial 7 428) = some ⟨7, 1, 0, 1423770, 428, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_428_1423770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 428 ⟨1423770, by decide⟩ :=
  accepted_of_selected 7 428 ⟨1423770, by decide⟩ ⟨7, 1, 0, 1423770, 428, 1, 67108864⟩
    (by decide) selected_cut_50624

theorem selected_cut_50625 : selected 14 ⟨1423770, by decide⟩
    (prefixPartial 7 429) = some ⟨7, 1, 0, 1423770, 429, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_429_1423770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 429 ⟨1423770, by decide⟩ :=
  accepted_of_selected 7 429 ⟨1423770, by decide⟩ ⟨7, 1, 0, 1423770, 429, 1, 67108864⟩
    (by decide) selected_cut_50625

theorem selected_cut_50626 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 110080) = some ⟨11, 1, 0, 434745, 110080, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110080_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110080 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 110080 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 110080, 1, 262144⟩
    (by decide) selected_cut_50626

theorem selected_cut_50627 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 110081) = some ⟨11, 1, 0, 434745, 110081, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110081_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110081 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 110081 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 110081, 1, 262144⟩
    (by decide) selected_cut_50627

theorem selected_cut_50628 : selected 10 ⟨1448408, by decide⟩
    (prefixPartial 11 110082) = some ⟨11, 2, 0, 1448408, 110082, 1253, 262144⟩ := by
  decide +kernel

theorem context_11_110082_1448408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110082 ⟨1448408, by decide⟩ :=
  accepted_of_selected 11 110082 ⟨1448408, by decide⟩ ⟨11, 2, 0, 1448408, 110082, 1253, 262144⟩
    (by decide) selected_cut_50628

theorem selected_cut_50629 : selected 10 ⟨1448537, by decide⟩
    (prefixPartial 11 110083) = some ⟨11, 2, 0, 1448537, 110083, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_110083_1448537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110083 ⟨1448537, by decide⟩ :=
  accepted_of_selected 11 110083 ⟨1448537, by decide⟩ ⟨11, 2, 0, 1448537, 110083, 2917, 262144⟩
    (by decide) selected_cut_50629

theorem unmarked_context_10_27520_1448538 : frontier 11 ⟨1448538, by decide⟩
    (prefixCache 10 27520) (prefixPartial 10 27520) = false := by
  decide +kernel

theorem node_context_10_27520_1448538 : EJMOriginalGlobalDAGData.nodes 11 ⟨1448538, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1448408, by decide⟩,⟨1448537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27520_1448538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27520 ⟨1448538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27520
    ⟨1448538, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1448408, by decide⟩,⟨1448537, by decide⟩]) unmarked_context_10_27520_1448538 node_context_10_27520_1448538
  intro a
  fin_cases a
  · exact context_11_110080_434745
  · exact context_11_110081_434745
  · exact context_11_110082_1448408
  · exact context_11_110083_1448537

theorem selected_cut_50630 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 440336) = some ⟨12, 1, 0, 435790, 440336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440336_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440336 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 440336 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 440336, 1, 65536⟩
    (by decide) selected_cut_50630

theorem selected_cut_50631 : selected 9 ⟨1448597, by decide⟩
    (prefixPartial 12 440337) = some ⟨12, 2, 0, 1448597, 440337, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_440337_1448597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440337 ⟨1448597, by decide⟩ :=
  accepted_of_selected 12 440337 ⟨1448597, by decide⟩ ⟨12, 2, 0, 1448597, 440337, 2121, 65536⟩
    (by decide) selected_cut_50631

theorem selected_cut_50632 : selected 9 ⟨1448648, by decide⟩
    (prefixPartial 12 440338) = some ⟨12, 2, 0, 1448648, 440338, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_440338_1448648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440338 ⟨1448648, by decide⟩ :=
  accepted_of_selected 12 440338 ⟨1448648, by decide⟩ ⟨12, 2, 0, 1448648, 440338, 1981, 65536⟩
    (by decide) selected_cut_50632

theorem selected_cut_50633 : selected 9 ⟨1448699, by decide⟩
    (prefixPartial 12 440339) = some ⟨12, 2, 0, 1448699, 440339, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_440339_1448699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440339 ⟨1448699, by decide⟩ :=
  accepted_of_selected 12 440339 ⟨1448699, by decide⟩ ⟨12, 2, 0, 1448699, 440339, 1845, 65536⟩
    (by decide) selected_cut_50633

theorem unmarked_context_11_110084_1448700 : frontier 10 ⟨1448700, by decide⟩
    (prefixCache 11 110084) (prefixPartial 11 110084) = false := by
  decide +kernel

theorem node_context_11_110084_1448700 : EJMOriginalGlobalDAGData.nodes 10 ⟨1448700, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1448597, by decide⟩,⟨1448648, by decide⟩,⟨1448699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110084_1448700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110084 ⟨1448700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110084
    ⟨1448700, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1448597, by decide⟩,⟨1448648, by decide⟩,⟨1448699, by decide⟩]) unmarked_context_11_110084_1448700 node_context_11_110084_1448700
  intro a
  fin_cases a
  · exact context_12_440336_435790
  · exact context_12_440337_1448597
  · exact context_12_440338_1448648
  · exact context_12_440339_1448699

theorem selected_cut_50634 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 110085) = some ⟨11, 1, 0, 1192826, 110085, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110085_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110085 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 110085 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 110085, 1, 262144⟩
    (by decide) selected_cut_50634

theorem selected_cut_50635 : selected 10 ⟨1448792, by decide⟩
    (prefixPartial 11 110086) = some ⟨11, 2, 0, 1448792, 110086, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_110086_1448792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110086 ⟨1448792, by decide⟩ :=
  accepted_of_selected 11 110086 ⟨1448792, by decide⟩ ⟨11, 2, 0, 1448792, 110086, 3725, 262144⟩
    (by decide) selected_cut_50635

theorem selected_cut_50636 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 440348) = some ⟨12, 1, 0, 450498, 440348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440348_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440348 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 440348 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 440348, 1, 65536⟩
    (by decide) selected_cut_50636

theorem selected_cut_50637 : selected 9 ⟨1448842, by decide⟩
    (prefixPartial 12 440349) = some ⟨12, 2, 0, 1448842, 440349, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_440349_1448842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440349 ⟨1448842, by decide⟩ :=
  accepted_of_selected 12 440349 ⟨1448842, by decide⟩ ⟨12, 2, 0, 1448842, 440349, 2113, 65536⟩
    (by decide) selected_cut_50637

theorem selected_cut_50638 : selected 9 ⟨1448894, by decide⟩
    (prefixPartial 12 440350) = some ⟨12, 2, 0, 1448894, 440350, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_440350_1448894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440350 ⟨1448894, by decide⟩ :=
  accepted_of_selected 12 440350 ⟨1448894, by decide⟩ ⟨12, 2, 0, 1448894, 440350, 2109, 65536⟩
    (by decide) selected_cut_50638

theorem selected_cut_50639 : selected 9 ⟨517541, by decide⟩
    (prefixPartial 12 440351) = some ⟨12, 1, 0, 517541, 440351, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440351_517541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440351 ⟨517541, by decide⟩ :=
  accepted_of_selected 12 440351 ⟨517541, by decide⟩ ⟨12, 1, 0, 517541, 440351, 1, 65536⟩
    (by decide) selected_cut_50639

theorem unmarked_context_11_110087_1448895 : frontier 10 ⟨1448895, by decide⟩
    (prefixCache 11 110087) (prefixPartial 11 110087) = false := by
  decide +kernel

theorem node_context_11_110087_1448895 : EJMOriginalGlobalDAGData.nodes 10 ⟨1448895, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1448842, by decide⟩,⟨1448894, by decide⟩,⟨517541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110087_1448895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110087 ⟨1448895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110087
    ⟨1448895, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1448842, by decide⟩,⟨1448894, by decide⟩,⟨517541, by decide⟩]) unmarked_context_11_110087_1448895 node_context_11_110087_1448895
  intro a
  fin_cases a
  · exact context_12_440348_450498
  · exact context_12_440349_1448842
  · exact context_12_440350_1448894
  · exact context_12_440351_517541

theorem unmarked_context_10_27521_1448896 : frontier 11 ⟨1448896, by decide⟩
    (prefixCache 10 27521) (prefixPartial 10 27521) = false := by
  decide +kernel

theorem node_context_10_27521_1448896 : EJMOriginalGlobalDAGData.nodes 11 ⟨1448896, by decide⟩ =
    .split (coordinate 10) (![⟨1448700, by decide⟩,⟨1192826, by decide⟩,⟨1448792, by decide⟩,⟨1448895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27521_1448896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27521 ⟨1448896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27521
    ⟨1448896, by decide⟩ (by decide) (![⟨1448700, by decide⟩,⟨1192826, by decide⟩,⟨1448792, by decide⟩,⟨1448895, by decide⟩]) unmarked_context_10_27521_1448896 node_context_10_27521_1448896
  intro a
  fin_cases a
  · exact context_11_110084_1448700
  · exact context_11_110085_1192826
  · exact context_11_110086_1448792
  · exact context_11_110087_1448895

theorem selected_cut_50640 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 440352) = some ⟨12, 1, 0, 1448897, 440352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440352_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440352 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 440352 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 440352, 1, 65536⟩
    (by decide) selected_cut_50640

theorem selected_cut_50641 : selected 9 ⟨1448946, by decide⟩
    (prefixPartial 12 440353) = some ⟨12, 2, 0, 1448946, 440353, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_440353_1448946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440353 ⟨1448946, by decide⟩ :=
  accepted_of_selected 12 440353 ⟨1448946, by decide⟩ ⟨12, 2, 0, 1448946, 440353, 1865, 65536⟩
    (by decide) selected_cut_50641

theorem selected_cut_50642 : selected 9 ⟨1448989, by decide⟩
    (prefixPartial 12 440354) = some ⟨12, 2, 0, 1448989, 440354, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_440354_1448989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440354 ⟨1448989, by decide⟩ :=
  accepted_of_selected 12 440354 ⟨1448989, by decide⟩ ⟨12, 2, 0, 1448989, 440354, 1669, 65536⟩
    (by decide) selected_cut_50642

theorem selected_cut_50643 : selected 9 ⟨1449026, by decide⟩
    (prefixPartial 12 440355) = some ⟨12, 2, 0, 1449026, 440355, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_440355_1449026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440355 ⟨1449026, by decide⟩ :=
  accepted_of_selected 12 440355 ⟨1449026, by decide⟩ ⟨12, 2, 0, 1449026, 440355, 1605, 65536⟩
    (by decide) selected_cut_50643

theorem unmarked_context_11_110088_1449027 : frontier 10 ⟨1449027, by decide⟩
    (prefixCache 11 110088) (prefixPartial 11 110088) = false := by
  decide +kernel

theorem node_context_11_110088_1449027 : EJMOriginalGlobalDAGData.nodes 10 ⟨1449027, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1448946, by decide⟩,⟨1448989, by decide⟩,⟨1449026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110088_1449027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110088 ⟨1449027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110088
    ⟨1449027, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1448946, by decide⟩,⟨1448989, by decide⟩,⟨1449026, by decide⟩]) unmarked_context_11_110088_1449027 node_context_11_110088_1449027
  intro a
  fin_cases a
  · exact context_12_440352_1448897
  · exact context_12_440353_1448946
  · exact context_12_440354_1448989
  · exact context_12_440355_1449026

theorem selected_cut_50644 : selected 10 ⟨1449116, by decide⟩
    (prefixPartial 11 110089) = some ⟨11, 2, 0, 1449116, 110089, 3621, 262144⟩ := by
  decide +kernel

theorem context_11_110089_1449116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110089 ⟨1449116, by decide⟩ :=
  accepted_of_selected 11 110089 ⟨1449116, by decide⟩ ⟨11, 2, 0, 1449116, 110089, 3621, 262144⟩
    (by decide) selected_cut_50644

theorem selected_cut_50645 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110090) = some ⟨11, 1, 0, 900587, 110090, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110090_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110090 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110090 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110090, 1, 262144⟩
    (by decide) selected_cut_50645

theorem selected_cut_50646 : selected 10 ⟨1449195, by decide⟩
    (prefixPartial 11 110091) = some ⟨11, 2, 0, 1449195, 110091, 3613, 262144⟩ := by
  decide +kernel

theorem context_11_110091_1449195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110091 ⟨1449195, by decide⟩ :=
  accepted_of_selected 11 110091 ⟨1449195, by decide⟩ ⟨11, 2, 0, 1449195, 110091, 3613, 262144⟩
    (by decide) selected_cut_50646

theorem unmarked_context_10_27522_1449196 : frontier 11 ⟨1449196, by decide⟩
    (prefixCache 10 27522) (prefixPartial 10 27522) = false := by
  decide +kernel

theorem node_context_10_27522_1449196 : EJMOriginalGlobalDAGData.nodes 11 ⟨1449196, by decide⟩ =
    .split (coordinate 10) (![⟨1449027, by decide⟩,⟨1449116, by decide⟩,⟨900587, by decide⟩,⟨1449195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27522_1449196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27522 ⟨1449196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27522
    ⟨1449196, by decide⟩ (by decide) (![⟨1449027, by decide⟩,⟨1449116, by decide⟩,⟨900587, by decide⟩,⟨1449195, by decide⟩]) unmarked_context_10_27522_1449196 node_context_10_27522_1449196
  intro a
  fin_cases a
  · exact context_11_110088_1449027
  · exact context_11_110089_1449116
  · exact context_11_110090_900587
  · exact context_11_110091_1449195

theorem selected_cut_50647 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 440368) = some ⟨12, 1, 0, 985390, 440368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440368_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440368 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 440368 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 440368, 1, 65536⟩
    (by decide) selected_cut_50647

theorem selected_cut_50648 : selected 9 ⟨1449237, by decide⟩
    (prefixPartial 12 440369) = some ⟨12, 2, 0, 1449237, 440369, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_440369_1449237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440369 ⟨1449237, by decide⟩ :=
  accepted_of_selected 12 440369 ⟨1449237, by decide⟩ ⟨12, 2, 0, 1449237, 440369, 1793, 65536⟩
    (by decide) selected_cut_50648

theorem selected_cut_50649 : selected 9 ⟨1449276, by decide⟩
    (prefixPartial 12 440370) = some ⟨12, 2, 0, 1449276, 440370, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_440370_1449276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440370 ⟨1449276, by decide⟩ :=
  accepted_of_selected 12 440370 ⟨1449276, by decide⟩ ⟨12, 2, 0, 1449276, 440370, 1629, 65536⟩
    (by decide) selected_cut_50649

theorem selected_cut_50650 : selected 9 ⟨1449314, by decide⟩
    (prefixPartial 12 440371) = some ⟨12, 2, 0, 1449314, 440371, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_440371_1449314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440371 ⟨1449314, by decide⟩ :=
  accepted_of_selected 12 440371 ⟨1449314, by decide⟩ ⟨12, 2, 0, 1449314, 440371, 1549, 65536⟩
    (by decide) selected_cut_50650

theorem unmarked_context_11_110092_1449315 : frontier 10 ⟨1449315, by decide⟩
    (prefixCache 11 110092) (prefixPartial 11 110092) = false := by
  decide +kernel

theorem node_context_11_110092_1449315 : EJMOriginalGlobalDAGData.nodes 10 ⟨1449315, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1449237, by decide⟩,⟨1449276, by decide⟩,⟨1449314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110092_1449315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110092 ⟨1449315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110092
    ⟨1449315, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1449237, by decide⟩,⟨1449276, by decide⟩,⟨1449314, by decide⟩]) unmarked_context_11_110092_1449315 node_context_11_110092_1449315
  intro a
  fin_cases a
  · exact context_12_440368_985390
  · exact context_12_440369_1449237
  · exact context_12_440370_1449276
  · exact context_12_440371_1449314

theorem selected_cut_50651 : selected 10 ⟨1449406, by decide⟩
    (prefixPartial 11 110093) = some ⟨11, 2, 0, 1449406, 110093, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_110093_1449406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110093 ⟨1449406, by decide⟩ :=
  accepted_of_selected 11 110093 ⟨1449406, by decide⟩ ⟨11, 2, 0, 1449406, 110093, 3417, 262144⟩
    (by decide) selected_cut_50651

theorem selected_cut_50652 : selected 10 ⟨1449465, by decide⟩
    (prefixPartial 11 110094) = some ⟨11, 2, 0, 1449465, 110094, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_110094_1449465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110094 ⟨1449465, by decide⟩ :=
  accepted_of_selected 11 110094 ⟨1449465, by decide⟩ ⟨11, 2, 0, 1449465, 110094, 2621, 262144⟩
    (by decide) selected_cut_50652

theorem selected_cut_50653 : selected 10 ⟨1449505, by decide⟩
    (prefixPartial 11 110095) = some ⟨11, 2, 0, 1449505, 110095, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_110095_1449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110095 ⟨1449505, by decide⟩ :=
  accepted_of_selected 11 110095 ⟨1449505, by decide⟩ ⟨11, 2, 0, 1449505, 110095, 1569, 262144⟩
    (by decide) selected_cut_50653

theorem unmarked_context_10_27523_1449506 : frontier 11 ⟨1449506, by decide⟩
    (prefixCache 10 27523) (prefixPartial 10 27523) = false := by
  decide +kernel

theorem node_context_10_27523_1449506 : EJMOriginalGlobalDAGData.nodes 11 ⟨1449506, by decide⟩ =
    .split (coordinate 10) (![⟨1449315, by decide⟩,⟨1449406, by decide⟩,⟨1449465, by decide⟩,⟨1449505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27523_1449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27523 ⟨1449506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27523
    ⟨1449506, by decide⟩ (by decide) (![⟨1449315, by decide⟩,⟨1449406, by decide⟩,⟨1449465, by decide⟩,⟨1449505, by decide⟩]) unmarked_context_10_27523_1449506 node_context_10_27523_1449506
  intro a
  fin_cases a
  · exact context_11_110092_1449315
  · exact context_11_110093_1449406
  · exact context_11_110094_1449465
  · exact context_11_110095_1449505

theorem unmarked_context_9_6880_1449507 : frontier 12 ⟨1449507, by decide⟩
    (prefixCache 9 6880) (prefixPartial 9 6880) = false := by
  decide +kernel

theorem node_context_9_6880_1449507 : EJMOriginalGlobalDAGData.nodes 12 ⟨1449507, by decide⟩ =
    .split (coordinate 9) (![⟨1448538, by decide⟩,⟨1448896, by decide⟩,⟨1449196, by decide⟩,⟨1449506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6880_1449507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6880 ⟨1449507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6880
    ⟨1449507, by decide⟩ (by decide) (![⟨1448538, by decide⟩,⟨1448896, by decide⟩,⟨1449196, by decide⟩,⟨1449506, by decide⟩]) unmarked_context_9_6880_1449507 node_context_9_6880_1449507
  intro a
  fin_cases a
  · exact context_10_27520_1448538
  · exact context_10_27521_1448896
  · exact context_10_27522_1449196
  · exact context_10_27523_1449506

theorem selected_cut_50654 : selected 10 ⟨1449508, by decide⟩
    (prefixPartial 11 110096) = some ⟨11, 2, 0, 1449508, 110096, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110096_1449508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110096 ⟨1449508, by decide⟩ :=
  accepted_of_selected 11 110096 ⟨1449508, by decide⟩ ⟨11, 2, 0, 1449508, 110096, 5, 262144⟩
    (by decide) selected_cut_50654

theorem selected_cut_50655 : selected 9 ⟨1449547, by decide⟩
    (prefixPartial 12 440388) = some ⟨12, 2, 0, 1449547, 440388, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_440388_1449547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440388 ⟨1449547, by decide⟩ :=
  accepted_of_selected 12 440388 ⟨1449547, by decide⟩ ⟨12, 2, 0, 1449547, 440388, 1441, 65536⟩
    (by decide) selected_cut_50655

theorem selected_cut_50656 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 440389) = some ⟨12, 1, 0, 1256866, 440389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440389_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440389 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 440389 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 440389, 1, 65536⟩
    (by decide) selected_cut_50656

theorem selected_cut_50657 : selected 9 ⟨1449593, by decide⟩
    (prefixPartial 12 440390) = some ⟨12, 2, 0, 1449593, 440390, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_440390_1449593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440390 ⟨1449593, by decide⟩ :=
  accepted_of_selected 12 440390 ⟨1449593, by decide⟩ ⟨12, 2, 0, 1449593, 440390, 1485, 65536⟩
    (by decide) selected_cut_50657

theorem selected_cut_50658 : selected 9 ⟨1449625, by decide⟩
    (prefixPartial 12 440391) = some ⟨12, 2, 0, 1449625, 440391, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_440391_1449625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440391 ⟨1449625, by decide⟩ :=
  accepted_of_selected 12 440391 ⟨1449625, by decide⟩ ⟨12, 2, 0, 1449625, 440391, 1349, 65536⟩
    (by decide) selected_cut_50658

theorem unmarked_context_11_110097_1449626 : frontier 10 ⟨1449626, by decide⟩
    (prefixCache 11 110097) (prefixPartial 11 110097) = false := by
  decide +kernel

theorem node_context_11_110097_1449626 : EJMOriginalGlobalDAGData.nodes 10 ⟨1449626, by decide⟩ =
    .split (coordinate 11) (![⟨1449547, by decide⟩,⟨1256866, by decide⟩,⟨1449593, by decide⟩,⟨1449625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110097_1449626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110097 ⟨1449626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110097
    ⟨1449626, by decide⟩ (by decide) (![⟨1449547, by decide⟩,⟨1256866, by decide⟩,⟨1449593, by decide⟩,⟨1449625, by decide⟩]) unmarked_context_11_110097_1449626 node_context_11_110097_1449626
  intro a
  fin_cases a
  · exact context_12_440388_1449547
  · exact context_12_440389_1256866
  · exact context_12_440390_1449593
  · exact context_12_440391_1449625

theorem selected_cut_50659 : selected 10 ⟨1449677, by decide⟩
    (prefixPartial 11 110098) = some ⟨11, 2, 0, 1449677, 110098, 2281, 262144⟩ := by
  decide +kernel

theorem context_11_110098_1449677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110098 ⟨1449677, by decide⟩ :=
  accepted_of_selected 11 110098 ⟨1449677, by decide⟩ ⟨11, 2, 0, 1449677, 110098, 2281, 262144⟩
    (by decide) selected_cut_50659

theorem selected_cut_50660 : selected 10 ⟨1449742, by decide⟩
    (prefixPartial 11 110099) = some ⟨11, 2, 0, 1449742, 110099, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_110099_1449742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110099 ⟨1449742, by decide⟩ :=
  accepted_of_selected 11 110099 ⟨1449742, by decide⟩ ⟨11, 2, 0, 1449742, 110099, 2729, 262144⟩
    (by decide) selected_cut_50660

theorem unmarked_context_10_27524_1449743 : frontier 11 ⟨1449743, by decide⟩
    (prefixCache 10 27524) (prefixPartial 10 27524) = false := by
  decide +kernel

theorem node_context_10_27524_1449743 : EJMOriginalGlobalDAGData.nodes 11 ⟨1449743, by decide⟩ =
    .split (coordinate 10) (![⟨1449508, by decide⟩,⟨1449626, by decide⟩,⟨1449677, by decide⟩,⟨1449742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27524_1449743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27524 ⟨1449743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27524
    ⟨1449743, by decide⟩ (by decide) (![⟨1449508, by decide⟩,⟨1449626, by decide⟩,⟨1449677, by decide⟩,⟨1449742, by decide⟩]) unmarked_context_10_27524_1449743 node_context_10_27524_1449743
  intro a
  fin_cases a
  · exact context_11_110096_1449508
  · exact context_11_110097_1449626
  · exact context_11_110098_1449677
  · exact context_11_110099_1449742

theorem selected_cut_50661 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 27525) = some ⟨10, 1, 0, 893098, 27525, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27525_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27525 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 27525 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 27525, 1, 1048576⟩
    (by decide) selected_cut_50661

theorem selected_cut_50662 : selected 10 ⟨1449792, by decide⟩
    (prefixPartial 11 110104) = some ⟨11, 2, 0, 1449792, 110104, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_110104_1449792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110104 ⟨1449792, by decide⟩ :=
  accepted_of_selected 11 110104 ⟨1449792, by decide⟩ ⟨11, 2, 0, 1449792, 110104, 1981, 262144⟩
    (by decide) selected_cut_50662

theorem selected_cut_50663 : selected 10 ⟨1449853, by decide⟩
    (prefixPartial 11 110105) = some ⟨11, 2, 0, 1449853, 110105, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_110105_1449853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110105 ⟨1449853, by decide⟩ :=
  accepted_of_selected 11 110105 ⟨1449853, by decide⟩ ⟨11, 2, 0, 1449853, 110105, 2893, 262144⟩
    (by decide) selected_cut_50663

theorem selected_cut_50664 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110106) = some ⟨11, 1, 0, 900587, 110106, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110106_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110106 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110106 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110106, 1, 262144⟩
    (by decide) selected_cut_50664

theorem selected_cut_50665 : selected 10 ⟨1449902, by decide⟩
    (prefixPartial 11 110107) = some ⟨11, 2, 0, 1449902, 110107, 2705, 262144⟩ := by
  decide +kernel

theorem context_11_110107_1449902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110107 ⟨1449902, by decide⟩ :=
  accepted_of_selected 11 110107 ⟨1449902, by decide⟩ ⟨11, 2, 0, 1449902, 110107, 2705, 262144⟩
    (by decide) selected_cut_50665

theorem unmarked_context_10_27526_1449903 : frontier 11 ⟨1449903, by decide⟩
    (prefixCache 10 27526) (prefixPartial 10 27526) = false := by
  decide +kernel

theorem node_context_10_27526_1449903 : EJMOriginalGlobalDAGData.nodes 11 ⟨1449903, by decide⟩ =
    .split (coordinate 10) (![⟨1449792, by decide⟩,⟨1449853, by decide⟩,⟨900587, by decide⟩,⟨1449902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27526_1449903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27526 ⟨1449903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27526
    ⟨1449903, by decide⟩ (by decide) (![⟨1449792, by decide⟩,⟨1449853, by decide⟩,⟨900587, by decide⟩,⟨1449902, by decide⟩]) unmarked_context_10_27526_1449903 node_context_10_27526_1449903
  intro a
  fin_cases a
  · exact context_11_110104_1449792
  · exact context_11_110105_1449853
  · exact context_11_110106_900587
  · exact context_11_110107_1449902

theorem selected_cut_50666 : selected 10 ⟨1449946, by decide⟩
    (prefixPartial 11 110108) = some ⟨11, 2, 0, 1449946, 110108, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_110108_1449946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110108 ⟨1449946, by decide⟩ :=
  accepted_of_selected 11 110108 ⟨1449946, by decide⟩ ⟨11, 2, 0, 1449946, 110108, 1769, 262144⟩
    (by decide) selected_cut_50666

theorem selected_cut_50667 : selected 10 ⟨1450009, by decide⟩
    (prefixPartial 11 110109) = some ⟨11, 2, 0, 1450009, 110109, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_110109_1450009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110109 ⟨1450009, by decide⟩ :=
  accepted_of_selected 11 110109 ⟨1450009, by decide⟩ ⟨11, 2, 0, 1450009, 110109, 2621, 262144⟩
    (by decide) selected_cut_50667

theorem selected_cut_50668 : selected 10 ⟨1450039, by decide⟩
    (prefixPartial 11 110110) = some ⟨11, 2, 0, 1450039, 110110, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_110110_1450039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110110 ⟨1450039, by decide⟩ :=
  accepted_of_selected 11 110110 ⟨1450039, by decide⟩ ⟨11, 2, 0, 1450039, 110110, 1397, 262144⟩
    (by decide) selected_cut_50668

theorem selected_cut_50669 : selected 10 ⟨1450055, by decide⟩
    (prefixPartial 11 110111) = some ⟨11, 2, 0, 1450055, 110111, 709, 262144⟩ := by
  decide +kernel

theorem context_11_110111_1450055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110111 ⟨1450055, by decide⟩ :=
  accepted_of_selected 11 110111 ⟨1450055, by decide⟩ ⟨11, 2, 0, 1450055, 110111, 709, 262144⟩
    (by decide) selected_cut_50669

theorem unmarked_context_10_27527_1450056 : frontier 11 ⟨1450056, by decide⟩
    (prefixCache 10 27527) (prefixPartial 10 27527) = false := by
  decide +kernel

theorem node_context_10_27527_1450056 : EJMOriginalGlobalDAGData.nodes 11 ⟨1450056, by decide⟩ =
    .split (coordinate 10) (![⟨1449946, by decide⟩,⟨1450009, by decide⟩,⟨1450039, by decide⟩,⟨1450055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27527_1450056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27527 ⟨1450056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27527
    ⟨1450056, by decide⟩ (by decide) (![⟨1449946, by decide⟩,⟨1450009, by decide⟩,⟨1450039, by decide⟩,⟨1450055, by decide⟩]) unmarked_context_10_27527_1450056 node_context_10_27527_1450056
  intro a
  fin_cases a
  · exact context_11_110108_1449946
  · exact context_11_110109_1450009
  · exact context_11_110110_1450039
  · exact context_11_110111_1450055

theorem unmarked_context_9_6881_1450057 : frontier 12 ⟨1450057, by decide⟩
    (prefixCache 9 6881) (prefixPartial 9 6881) = false := by
  decide +kernel

theorem node_context_9_6881_1450057 : EJMOriginalGlobalDAGData.nodes 12 ⟨1450057, by decide⟩ =
    .split (coordinate 9) (![⟨1449743, by decide⟩,⟨893098, by decide⟩,⟨1449903, by decide⟩,⟨1450056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6881_1450057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6881 ⟨1450057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6881
    ⟨1450057, by decide⟩ (by decide) (![⟨1449743, by decide⟩,⟨893098, by decide⟩,⟨1449903, by decide⟩,⟨1450056, by decide⟩]) unmarked_context_9_6881_1450057 node_context_9_6881_1450057
  intro a
  fin_cases a
  · exact context_10_27524_1449743
  · exact context_10_27525_893098
  · exact context_10_27526_1449903
  · exact context_10_27527_1450056

theorem selected_cut_50670 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 110112) = some ⟨11, 1, 0, 1375697, 110112, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110112_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110112 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 110112 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 110112, 1, 262144⟩
    (by decide) selected_cut_50670

theorem selected_cut_50671 : selected 10 ⟨1450102, by decide⟩
    (prefixPartial 11 110113) = some ⟨11, 2, 0, 1450102, 110113, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_110113_1450102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110113 ⟨1450102, by decide⟩ :=
  accepted_of_selected 11 110113 ⟨1450102, by decide⟩ ⟨11, 2, 0, 1450102, 110113, 1717, 262144⟩
    (by decide) selected_cut_50671

theorem selected_cut_50672 : selected 10 ⟨1450148, by decide⟩
    (prefixPartial 11 110114) = some ⟨11, 2, 0, 1450148, 110114, 2065, 262144⟩ := by
  decide +kernel

theorem context_11_110114_1450148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110114 ⟨1450148, by decide⟩ :=
  accepted_of_selected 11 110114 ⟨1450148, by decide⟩ ⟨11, 2, 0, 1450148, 110114, 2065, 262144⟩
    (by decide) selected_cut_50672

theorem selected_cut_50673 : selected 10 ⟨1450192, by decide⟩
    (prefixPartial 11 110115) = some ⟨11, 2, 0, 1450192, 110115, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_110115_1450192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110115 ⟨1450192, by decide⟩ :=
  accepted_of_selected 11 110115 ⟨1450192, by decide⟩ ⟨11, 2, 0, 1450192, 110115, 1513, 262144⟩
    (by decide) selected_cut_50673

theorem unmarked_context_10_27528_1450193 : frontier 11 ⟨1450193, by decide⟩
    (prefixCache 10 27528) (prefixPartial 10 27528) = false := by
  decide +kernel

theorem node_context_10_27528_1450193 : EJMOriginalGlobalDAGData.nodes 11 ⟨1450193, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1450102, by decide⟩,⟨1450148, by decide⟩,⟨1450192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27528_1450193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27528 ⟨1450193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27528
    ⟨1450193, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1450102, by decide⟩,⟨1450148, by decide⟩,⟨1450192, by decide⟩]) unmarked_context_10_27528_1450193 node_context_10_27528_1450193
  intro a
  fin_cases a
  · exact context_11_110112_1375697
  · exact context_11_110113_1450102
  · exact context_11_110114_1450148
  · exact context_11_110115_1450192

theorem selected_cut_50674 : selected 10 ⟨1450222, by decide⟩
    (prefixPartial 11 110116) = some ⟨11, 2, 0, 1450222, 110116, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_110116_1450222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110116 ⟨1450222, by decide⟩ :=
  accepted_of_selected 11 110116 ⟨1450222, by decide⟩ ⟨11, 2, 0, 1450222, 110116, 1217, 262144⟩
    (by decide) selected_cut_50674

theorem selected_cut_50675 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 110117) = some ⟨11, 1, 0, 1378525, 110117, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110117_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110117 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 110117 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 110117, 1, 262144⟩
    (by decide) selected_cut_50675

theorem selected_cut_50676 : selected 10 ⟨1450246, by decide⟩
    (prefixPartial 11 110118) = some ⟨11, 2, 0, 1450246, 110118, 1529, 262144⟩ := by
  decide +kernel

theorem context_11_110118_1450246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110118 ⟨1450246, by decide⟩ :=
  accepted_of_selected 11 110118 ⟨1450246, by decide⟩ ⟨11, 2, 0, 1450246, 110118, 1529, 262144⟩
    (by decide) selected_cut_50676

theorem selected_cut_50677 : selected 10 ⟨1450277, by decide⟩
    (prefixPartial 11 110119) = some ⟨11, 2, 0, 1450277, 110119, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_110119_1450277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110119 ⟨1450277, by decide⟩ :=
  accepted_of_selected 11 110119 ⟨1450277, by decide⟩ ⟨11, 2, 0, 1450277, 110119, 1461, 262144⟩
    (by decide) selected_cut_50677

theorem unmarked_context_10_27529_1450278 : frontier 11 ⟨1450278, by decide⟩
    (prefixCache 10 27529) (prefixPartial 10 27529) = false := by
  decide +kernel

theorem node_context_10_27529_1450278 : EJMOriginalGlobalDAGData.nodes 11 ⟨1450278, by decide⟩ =
    .split (coordinate 10) (![⟨1450222, by decide⟩,⟨1378525, by decide⟩,⟨1450246, by decide⟩,⟨1450277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27529_1450278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27529 ⟨1450278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27529
    ⟨1450278, by decide⟩ (by decide) (![⟨1450222, by decide⟩,⟨1378525, by decide⟩,⟨1450246, by decide⟩,⟨1450277, by decide⟩]) unmarked_context_10_27529_1450278 node_context_10_27529_1450278
  intro a
  fin_cases a
  · exact context_11_110116_1450222
  · exact context_11_110117_1378525
  · exact context_11_110118_1450246
  · exact context_11_110119_1450277

theorem selected_cut_50678 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 27530) = some ⟨10, 2, 0, 1432895, 27530, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_27530_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27530 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 27530 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 27530, 5, 1048576⟩
    (by decide) selected_cut_50678

theorem selected_cut_50679 : selected 11 ⟨1450349, by decide⟩
    (prefixPartial 10 27531) = some ⟨10, 2, 0, 1450349, 27531, 2609, 1048576⟩ := by
  decide +kernel

theorem context_10_27531_1450349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27531 ⟨1450349, by decide⟩ :=
  accepted_of_selected 10 27531 ⟨1450349, by decide⟩ ⟨10, 2, 0, 1450349, 27531, 2609, 1048576⟩
    (by decide) selected_cut_50679

theorem unmarked_context_9_6882_1450350 : frontier 12 ⟨1450350, by decide⟩
    (prefixCache 9 6882) (prefixPartial 9 6882) = false := by
  decide +kernel

theorem node_context_9_6882_1450350 : EJMOriginalGlobalDAGData.nodes 12 ⟨1450350, by decide⟩ =
    .split (coordinate 9) (![⟨1450193, by decide⟩,⟨1450278, by decide⟩,⟨1432895, by decide⟩,⟨1450349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6882_1450350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6882 ⟨1450350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6882
    ⟨1450350, by decide⟩ (by decide) (![⟨1450193, by decide⟩,⟨1450278, by decide⟩,⟨1432895, by decide⟩,⟨1450349, by decide⟩]) unmarked_context_9_6882_1450350 node_context_9_6882_1450350
  intro a
  fin_cases a
  · exact context_10_27528_1450193
  · exact context_10_27529_1450278
  · exact context_10_27530_1432895
  · exact context_10_27531_1450349

theorem selected_cut_50680 : selected 11 ⟨1450409, by decide⟩
    (prefixPartial 10 27532) = some ⟨10, 2, 0, 1450409, 27532, 2341, 1048576⟩ := by
  decide +kernel

theorem context_10_27532_1450409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27532 ⟨1450409, by decide⟩ :=
  accepted_of_selected 10 27532 ⟨1450409, by decide⟩ ⟨10, 2, 0, 1450409, 27532, 2341, 1048576⟩
    (by decide) selected_cut_50680

theorem selected_cut_50681 : selected 11 ⟨1450449, by decide⟩
    (prefixPartial 10 27533) = some ⟨10, 2, 0, 1450449, 27533, 1549, 1048576⟩ := by
  decide +kernel

theorem context_10_27533_1450449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27533 ⟨1450449, by decide⟩ :=
  accepted_of_selected 10 27533 ⟨1450449, by decide⟩ ⟨10, 2, 0, 1450449, 27533, 1549, 1048576⟩
    (by decide) selected_cut_50681

theorem selected_cut_50682 : selected 11 ⟨1450483, by decide⟩
    (prefixPartial 10 27534) = some ⟨10, 2, 0, 1450483, 27534, 641, 1048576⟩ := by
  decide +kernel

theorem context_10_27534_1450483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27534 ⟨1450483, by decide⟩ :=
  accepted_of_selected 10 27534 ⟨1450483, by decide⟩ ⟨10, 2, 0, 1450483, 27534, 641, 1048576⟩
    (by decide) selected_cut_50682

theorem selected_cut_50683 : selected 11 ⟨1450485, by decide⟩
    (prefixPartial 10 27535) = some ⟨10, 2, 0, 1450485, 27535, 73, 1048576⟩ := by
  decide +kernel

theorem context_10_27535_1450485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27535 ⟨1450485, by decide⟩ :=
  accepted_of_selected 10 27535 ⟨1450485, by decide⟩ ⟨10, 2, 0, 1450485, 27535, 73, 1048576⟩
    (by decide) selected_cut_50683

theorem unmarked_context_9_6883_1450486 : frontier 12 ⟨1450486, by decide⟩
    (prefixCache 9 6883) (prefixPartial 9 6883) = false := by
  decide +kernel

theorem node_context_9_6883_1450486 : EJMOriginalGlobalDAGData.nodes 12 ⟨1450486, by decide⟩ =
    .split (coordinate 9) (![⟨1450409, by decide⟩,⟨1450449, by decide⟩,⟨1450483, by decide⟩,⟨1450485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6883_1450486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6883 ⟨1450486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6883
    ⟨1450486, by decide⟩ (by decide) (![⟨1450409, by decide⟩,⟨1450449, by decide⟩,⟨1450483, by decide⟩,⟨1450485, by decide⟩]) unmarked_context_9_6883_1450486 node_context_9_6883_1450486
  intro a
  fin_cases a
  · exact context_10_27532_1450409
  · exact context_10_27533_1450449
  · exact context_10_27534_1450483
  · exact context_10_27535_1450485

theorem unmarked_context_8_1720_1450487 : frontier 13 ⟨1450487, by decide⟩
    (prefixCache 8 1720) (prefixPartial 8 1720) = false := by
  decide +kernel

theorem node_context_8_1720_1450487 : EJMOriginalGlobalDAGData.nodes 13 ⟨1450487, by decide⟩ =
    .split (coordinate 8) (![⟨1449507, by decide⟩,⟨1450057, by decide⟩,⟨1450350, by decide⟩,⟨1450486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1720_1450487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1720 ⟨1450487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1720
    ⟨1450487, by decide⟩ (by decide) (![⟨1449507, by decide⟩,⟨1450057, by decide⟩,⟨1450350, by decide⟩,⟨1450486, by decide⟩]) unmarked_context_8_1720_1450487 node_context_8_1720_1450487
  intro a
  fin_cases a
  · exact context_9_6880_1449507
  · exact context_9_6881_1450057
  · exact context_9_6882_1450350
  · exact context_9_6883_1450486

theorem selected_cut_50684 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 110144) = some ⟨11, 1, 0, 434745, 110144, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110144_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110144 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 110144 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 110144, 1, 262144⟩
    (by decide) selected_cut_50684

theorem selected_cut_50685 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 110145) = some ⟨11, 1, 0, 434745, 110145, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110145_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110145 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 110145 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 110145, 1, 262144⟩
    (by decide) selected_cut_50685

theorem selected_cut_50686 : selected 10 ⟨1450523, by decide⟩
    (prefixPartial 11 110146) = some ⟨11, 2, 0, 1450523, 110146, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_110146_1450523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110146 ⟨1450523, by decide⟩ :=
  accepted_of_selected 11 110146 ⟨1450523, by decide⟩ ⟨11, 2, 0, 1450523, 110146, 1049, 262144⟩
    (by decide) selected_cut_50686

theorem selected_cut_50687 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 440588) = some ⟨12, 1, 0, 448748, 440588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440588_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440588 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 440588 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 440588, 1, 65536⟩
    (by decide) selected_cut_50687

theorem selected_cut_50688 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 440589) = some ⟨12, 1, 0, 448748, 440589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440589_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440589 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 440589 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 440589, 1, 65536⟩
    (by decide) selected_cut_50688

theorem selected_cut_50689 : selected 9 ⟨1450599, by decide⟩
    (prefixPartial 12 440590) = some ⟨12, 2, 0, 1450599, 440590, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_440590_1450599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440590 ⟨1450599, by decide⟩ :=
  accepted_of_selected 12 440590 ⟨1450599, by decide⟩ ⟨12, 2, 0, 1450599, 440590, 2401, 65536⟩
    (by decide) selected_cut_50689

theorem selected_cut_50690 : selected 9 ⟨1450654, by decide⟩
    (prefixPartial 12 440591) = some ⟨12, 2, 0, 1450654, 440591, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_440591_1450654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440591 ⟨1450654, by decide⟩ :=
  accepted_of_selected 12 440591 ⟨1450654, by decide⟩ ⟨12, 2, 0, 1450654, 440591, 2037, 65536⟩
    (by decide) selected_cut_50690

theorem unmarked_context_11_110147_1450655 : frontier 10 ⟨1450655, by decide⟩
    (prefixCache 11 110147) (prefixPartial 11 110147) = false := by
  decide +kernel

theorem node_context_11_110147_1450655 : EJMOriginalGlobalDAGData.nodes 10 ⟨1450655, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1450599, by decide⟩,⟨1450654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110147_1450655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110147 ⟨1450655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110147
    ⟨1450655, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1450599, by decide⟩,⟨1450654, by decide⟩]) unmarked_context_11_110147_1450655 node_context_11_110147_1450655
  intro a
  fin_cases a
  · exact context_12_440588_448748
  · exact context_12_440589_448748
  · exact context_12_440590_1450599
  · exact context_12_440591_1450654

theorem unmarked_context_10_27536_1450656 : frontier 11 ⟨1450656, by decide⟩
    (prefixCache 10 27536) (prefixPartial 10 27536) = false := by
  decide +kernel

theorem node_context_10_27536_1450656 : EJMOriginalGlobalDAGData.nodes 11 ⟨1450656, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1450523, by decide⟩,⟨1450655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27536_1450656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27536 ⟨1450656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27536
    ⟨1450656, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1450523, by decide⟩,⟨1450655, by decide⟩]) unmarked_context_10_27536_1450656 node_context_10_27536_1450656
  intro a
  fin_cases a
  · exact context_11_110144_434745
  · exact context_11_110145_434745
  · exact context_11_110146_1450523
  · exact context_11_110147_1450655

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
