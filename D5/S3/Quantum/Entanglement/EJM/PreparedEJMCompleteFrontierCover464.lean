/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover463
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44547 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88602) = some ⟨11, 1, 0, 900587, 88602, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88602_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88602 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88602 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88602, 1, 262144⟩
    (by decide) selected_cut_44547

theorem selected_cut_44548 : selected 10 ⟨1226336, by decide⟩
    (prefixPartial 11 88603) = some ⟨11, 2, 0, 1226336, 88603, 3881, 262144⟩ := by
  decide +kernel

theorem context_11_88603_1226336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88603 ⟨1226336, by decide⟩ :=
  accepted_of_selected 11 88603 ⟨1226336, by decide⟩ ⟨11, 2, 0, 1226336, 88603, 3881, 262144⟩
    (by decide) selected_cut_44548

theorem unmarked_context_10_22150_1226337 : frontier 11 ⟨1226337, by decide⟩
    (prefixCache 10 22150) (prefixPartial 10 22150) = false := by
  decide +kernel

theorem node_context_10_22150_1226337 : EJMOriginalGlobalDAGData.nodes 11 ⟨1226337, by decide⟩ =
    .split (coordinate 10) (![⟨1226210, by decide⟩,⟨1226280, by decide⟩,⟨900587, by decide⟩,⟨1226336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22150_1226337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22150 ⟨1226337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22150
    ⟨1226337, by decide⟩ (by decide) (![⟨1226210, by decide⟩,⟨1226280, by decide⟩,⟨900587, by decide⟩,⟨1226336, by decide⟩]) unmarked_context_10_22150_1226337 node_context_10_22150_1226337
  intro a
  fin_cases a
  · exact context_11_88600_1226210
  · exact context_11_88601_1226280
  · exact context_11_88602_900587
  · exact context_11_88603_1226336

theorem selected_cut_44549 : selected 10 ⟨1226386, by decide⟩
    (prefixPartial 11 88604) = some ⟨11, 2, 0, 1226386, 88604, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_88604_1226386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88604 ⟨1226386, by decide⟩ :=
  accepted_of_selected 11 88604 ⟨1226386, by decide⟩ ⟨11, 2, 0, 1226386, 88604, 2777, 262144⟩
    (by decide) selected_cut_44549

theorem selected_cut_44550 : selected 10 ⟨1226450, by decide⟩
    (prefixPartial 11 88605) = some ⟨11, 2, 0, 1226450, 88605, 3945, 262144⟩ := by
  decide +kernel

theorem context_11_88605_1226450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88605 ⟨1226450, by decide⟩ :=
  accepted_of_selected 11 88605 ⟨1226450, by decide⟩ ⟨11, 2, 0, 1226450, 88605, 3945, 262144⟩
    (by decide) selected_cut_44550

theorem selected_cut_44551 : selected 10 ⟨1226514, by decide⟩
    (prefixPartial 11 88606) = some ⟨11, 2, 0, 1226514, 88606, 3961, 262144⟩ := by
  decide +kernel

theorem context_11_88606_1226514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88606 ⟨1226514, by decide⟩ :=
  accepted_of_selected 11 88606 ⟨1226514, by decide⟩ ⟨11, 2, 0, 1226514, 88606, 3961, 262144⟩
    (by decide) selected_cut_44551

theorem selected_cut_44552 : selected 10 ⟨1226560, by decide⟩
    (prefixPartial 11 88607) = some ⟨11, 2, 0, 1226560, 88607, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_88607_1226560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88607 ⟨1226560, by decide⟩ :=
  accepted_of_selected 11 88607 ⟨1226560, by decide⟩ ⟨11, 2, 0, 1226560, 88607, 2461, 262144⟩
    (by decide) selected_cut_44552

theorem unmarked_context_10_22151_1226561 : frontier 11 ⟨1226561, by decide⟩
    (prefixCache 10 22151) (prefixPartial 10 22151) = false := by
  decide +kernel

theorem node_context_10_22151_1226561 : EJMOriginalGlobalDAGData.nodes 11 ⟨1226561, by decide⟩ =
    .split (coordinate 10) (![⟨1226386, by decide⟩,⟨1226450, by decide⟩,⟨1226514, by decide⟩,⟨1226560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22151_1226561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22151 ⟨1226561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22151
    ⟨1226561, by decide⟩ (by decide) (![⟨1226386, by decide⟩,⟨1226450, by decide⟩,⟨1226514, by decide⟩,⟨1226560, by decide⟩]) unmarked_context_10_22151_1226561 node_context_10_22151_1226561
  intro a
  fin_cases a
  · exact context_11_88604_1226386
  · exact context_11_88605_1226450
  · exact context_11_88606_1226514
  · exact context_11_88607_1226560

theorem unmarked_context_9_5537_1226562 : frontier 12 ⟨1226562, by decide⟩
    (prefixCache 9 5537) (prefixPartial 9 5537) = false := by
  decide +kernel

theorem node_context_9_5537_1226562 : EJMOriginalGlobalDAGData.nodes 12 ⟨1226562, by decide⟩ =
    .split (coordinate 9) (![⟨1226170, by decide⟩,⟨893098, by decide⟩,⟨1226337, by decide⟩,⟨1226561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5537_1226562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5537 ⟨1226562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5537
    ⟨1226562, by decide⟩ (by decide) (![⟨1226170, by decide⟩,⟨893098, by decide⟩,⟨1226337, by decide⟩,⟨1226561, by decide⟩]) unmarked_context_9_5537_1226562 node_context_9_5537_1226562
  intro a
  fin_cases a
  · exact context_10_22148_1226170
  · exact context_10_22149_893098
  · exact context_10_22150_1226337
  · exact context_10_22151_1226561

theorem selected_cut_44553 : selected 10 ⟨1226599, by decide⟩
    (prefixPartial 11 88608) = some ⟨11, 2, 0, 1226599, 88608, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_88608_1226599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88608 ⟨1226599, by decide⟩ :=
  accepted_of_selected 11 88608 ⟨1226599, by decide⟩ ⟨11, 2, 0, 1226599, 88608, 2321, 262144⟩
    (by decide) selected_cut_44553

theorem selected_cut_44554 : selected 9 ⟨1226620, by decide⟩
    (prefixPartial 12 354436) = some ⟨12, 2, 0, 1226620, 354436, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_354436_1226620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354436 ⟨1226620, by decide⟩ :=
  accepted_of_selected 12 354436 ⟨1226620, by decide⟩ ⟨12, 2, 0, 1226620, 354436, 1177, 65536⟩
    (by decide) selected_cut_44554

theorem selected_cut_44555 : selected 9 ⟨1226636, by decide⟩
    (prefixPartial 12 354437) = some ⟨12, 2, 0, 1226636, 354437, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_354437_1226636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354437 ⟨1226636, by decide⟩ :=
  accepted_of_selected 12 354437 ⟨1226636, by decide⟩ ⟨12, 2, 0, 1226636, 354437, 1045, 65536⟩
    (by decide) selected_cut_44555

theorem selected_cut_44556 : selected 9 ⟨1226655, by decide⟩
    (prefixPartial 12 354438) = some ⟨12, 2, 0, 1226655, 354438, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_354438_1226655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354438 ⟨1226655, by decide⟩ :=
  accepted_of_selected 12 354438 ⟨1226655, by decide⟩ ⟨12, 2, 0, 1226655, 354438, 1189, 65536⟩
    (by decide) selected_cut_44556

theorem selected_cut_44557 : selected 9 ⟨1226675, by decide⟩
    (prefixPartial 12 354439) = some ⟨12, 2, 0, 1226675, 354439, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_354439_1226675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354439 ⟨1226675, by decide⟩ :=
  accepted_of_selected 12 354439 ⟨1226675, by decide⟩ ⟨12, 2, 0, 1226675, 354439, 1181, 65536⟩
    (by decide) selected_cut_44557

theorem unmarked_context_11_88609_1226676 : frontier 10 ⟨1226676, by decide⟩
    (prefixCache 11 88609) (prefixPartial 11 88609) = false := by
  decide +kernel

theorem node_context_11_88609_1226676 : EJMOriginalGlobalDAGData.nodes 10 ⟨1226676, by decide⟩ =
    .split (coordinate 11) (![⟨1226620, by decide⟩,⟨1226636, by decide⟩,⟨1226655, by decide⟩,⟨1226675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88609_1226676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88609 ⟨1226676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88609
    ⟨1226676, by decide⟩ (by decide) (![⟨1226620, by decide⟩,⟨1226636, by decide⟩,⟨1226655, by decide⟩,⟨1226675, by decide⟩]) unmarked_context_11_88609_1226676 node_context_11_88609_1226676
  intro a
  fin_cases a
  · exact context_12_354436_1226620
  · exact context_12_354437_1226636
  · exact context_12_354438_1226655
  · exact context_12_354439_1226675

theorem selected_cut_44558 : selected 10 ⟨1226741, by decide⟩
    (prefixPartial 11 88610) = some ⟨11, 2, 0, 1226741, 88610, 3473, 262144⟩ := by
  decide +kernel

theorem context_11_88610_1226741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88610 ⟨1226741, by decide⟩ :=
  accepted_of_selected 11 88610 ⟨1226741, by decide⟩ ⟨11, 2, 0, 1226741, 88610, 3473, 262144⟩
    (by decide) selected_cut_44558

theorem selected_cut_44559 : selected 9 ⟨1226755, by decide⟩
    (prefixPartial 12 354444) = some ⟨12, 2, 0, 1226755, 354444, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_354444_1226755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354444 ⟨1226755, by decide⟩ :=
  accepted_of_selected 12 354444 ⟨1226755, by decide⟩ ⟨12, 2, 0, 1226755, 354444, 1037, 65536⟩
    (by decide) selected_cut_44559

theorem selected_cut_44560 : selected 9 ⟨1226767, by decide⟩
    (prefixPartial 12 354445) = some ⟨12, 2, 0, 1226767, 354445, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_354445_1226767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354445 ⟨1226767, by decide⟩ :=
  accepted_of_selected 12 354445 ⟨1226767, by decide⟩ ⟨12, 2, 0, 1226767, 354445, 1041, 65536⟩
    (by decide) selected_cut_44560

theorem selected_cut_44561 : selected 9 ⟨1226788, by decide⟩
    (prefixPartial 12 354446) = some ⟨12, 2, 0, 1226788, 354446, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_354446_1226788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354446 ⟨1226788, by decide⟩ :=
  accepted_of_selected 12 354446 ⟨1226788, by decide⟩ ⟨12, 2, 0, 1226788, 354446, 1177, 65536⟩
    (by decide) selected_cut_44561

theorem selected_cut_44562 : selected 9 ⟨1226804, by decide⟩
    (prefixPartial 12 354447) = some ⟨12, 2, 0, 1226804, 354447, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_354447_1226804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354447 ⟨1226804, by decide⟩ :=
  accepted_of_selected 12 354447 ⟨1226804, by decide⟩ ⟨12, 2, 0, 1226804, 354447, 1125, 65536⟩
    (by decide) selected_cut_44562

theorem unmarked_context_11_88611_1226805 : frontier 10 ⟨1226805, by decide⟩
    (prefixCache 11 88611) (prefixPartial 11 88611) = false := by
  decide +kernel

theorem node_context_11_88611_1226805 : EJMOriginalGlobalDAGData.nodes 10 ⟨1226805, by decide⟩ =
    .split (coordinate 11) (![⟨1226755, by decide⟩,⟨1226767, by decide⟩,⟨1226788, by decide⟩,⟨1226804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88611_1226805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88611 ⟨1226805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88611
    ⟨1226805, by decide⟩ (by decide) (![⟨1226755, by decide⟩,⟨1226767, by decide⟩,⟨1226788, by decide⟩,⟨1226804, by decide⟩]) unmarked_context_11_88611_1226805 node_context_11_88611_1226805
  intro a
  fin_cases a
  · exact context_12_354444_1226755
  · exact context_12_354445_1226767
  · exact context_12_354446_1226788
  · exact context_12_354447_1226804

theorem unmarked_context_10_22152_1226806 : frontier 11 ⟨1226806, by decide⟩
    (prefixCache 10 22152) (prefixPartial 10 22152) = false := by
  decide +kernel

theorem node_context_10_22152_1226806 : EJMOriginalGlobalDAGData.nodes 11 ⟨1226806, by decide⟩ =
    .split (coordinate 10) (![⟨1226599, by decide⟩,⟨1226676, by decide⟩,⟨1226741, by decide⟩,⟨1226805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22152_1226806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22152 ⟨1226806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22152
    ⟨1226806, by decide⟩ (by decide) (![⟨1226599, by decide⟩,⟨1226676, by decide⟩,⟨1226741, by decide⟩,⟨1226805, by decide⟩]) unmarked_context_10_22152_1226806 node_context_10_22152_1226806
  intro a
  fin_cases a
  · exact context_11_88608_1226599
  · exact context_11_88609_1226676
  · exact context_11_88610_1226741
  · exact context_11_88611_1226805

theorem selected_cut_44563 : selected 10 ⟨1226852, by decide⟩
    (prefixPartial 11 88612) = some ⟨11, 2, 0, 1226852, 88612, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_88612_1226852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88612 ⟨1226852, by decide⟩ :=
  accepted_of_selected 11 88612 ⟨1226852, by decide⟩ ⟨11, 2, 0, 1226852, 88612, 2385, 262144⟩
    (by decide) selected_cut_44563

theorem selected_cut_44564 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 88613) = some ⟨11, 1, 0, 1192826, 88613, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88613_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88613 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 88613 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 88613, 1, 262144⟩
    (by decide) selected_cut_44564

theorem selected_cut_44565 : selected 10 ⟨1226901, by decide⟩
    (prefixPartial 11 88614) = some ⟨11, 2, 0, 1226901, 88614, 2921, 262144⟩ := by
  decide +kernel

theorem context_11_88614_1226901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88614 ⟨1226901, by decide⟩ :=
  accepted_of_selected 11 88614 ⟨1226901, by decide⟩ ⟨11, 2, 0, 1226901, 88614, 2921, 262144⟩
    (by decide) selected_cut_44565

theorem selected_cut_44566 : selected 10 ⟨1226959, by decide⟩
    (prefixPartial 11 88615) = some ⟨11, 2, 0, 1226959, 88615, 3657, 262144⟩ := by
  decide +kernel

theorem context_11_88615_1226959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88615 ⟨1226959, by decide⟩ :=
  accepted_of_selected 11 88615 ⟨1226959, by decide⟩ ⟨11, 2, 0, 1226959, 88615, 3657, 262144⟩
    (by decide) selected_cut_44566

theorem unmarked_context_10_22153_1226960 : frontier 11 ⟨1226960, by decide⟩
    (prefixCache 10 22153) (prefixPartial 10 22153) = false := by
  decide +kernel

theorem node_context_10_22153_1226960 : EJMOriginalGlobalDAGData.nodes 11 ⟨1226960, by decide⟩ =
    .split (coordinate 10) (![⟨1226852, by decide⟩,⟨1192826, by decide⟩,⟨1226901, by decide⟩,⟨1226959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22153_1226960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22153 ⟨1226960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22153
    ⟨1226960, by decide⟩ (by decide) (![⟨1226852, by decide⟩,⟨1192826, by decide⟩,⟨1226901, by decide⟩,⟨1226959, by decide⟩]) unmarked_context_10_22153_1226960 node_context_10_22153_1226960
  intro a
  fin_cases a
  · exact context_11_88612_1226852
  · exact context_11_88613_1192826
  · exact context_11_88614_1226901
  · exact context_11_88615_1226959

theorem selected_cut_44567 : selected 11 ⟨1226999, by decide⟩
    (prefixPartial 10 22154) = some ⟨10, 2, 0, 1226999, 22154, 2533, 1048576⟩ := by
  decide +kernel

theorem context_10_22154_1226999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22154 ⟨1226999, by decide⟩ :=
  accepted_of_selected 10 22154 ⟨1226999, by decide⟩ ⟨10, 2, 0, 1226999, 22154, 2533, 1048576⟩
    (by decide) selected_cut_44567

theorem selected_cut_44568 : selected 10 ⟨1227042, by decide⟩
    (prefixPartial 11 88620) = some ⟨11, 2, 0, 1227042, 88620, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_88620_1227042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88620 ⟨1227042, by decide⟩ :=
  accepted_of_selected 11 88620 ⟨1227042, by decide⟩ ⟨11, 2, 0, 1227042, 88620, 2361, 262144⟩
    (by decide) selected_cut_44568

theorem selected_cut_44569 : selected 10 ⟨1227090, by decide⟩
    (prefixPartial 11 88621) = some ⟨11, 2, 0, 1227090, 88621, 2673, 262144⟩ := by
  decide +kernel

theorem context_11_88621_1227090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88621 ⟨1227090, by decide⟩ :=
  accepted_of_selected 11 88621 ⟨1227090, by decide⟩ ⟨11, 2, 0, 1227090, 88621, 2673, 262144⟩
    (by decide) selected_cut_44569

theorem selected_cut_44570 : selected 10 ⟨1227127, by decide⟩
    (prefixPartial 11 88622) = some ⟨11, 2, 0, 1227127, 88622, 2037, 262144⟩ := by
  decide +kernel

theorem context_11_88622_1227127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88622 ⟨1227127, by decide⟩ :=
  accepted_of_selected 11 88622 ⟨1227127, by decide⟩ ⟨11, 2, 0, 1227127, 88622, 2037, 262144⟩
    (by decide) selected_cut_44570

theorem selected_cut_44571 : selected 10 ⟨1227156, by decide⟩
    (prefixPartial 11 88623) = some ⟨11, 2, 0, 1227156, 88623, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_88623_1227156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88623 ⟨1227156, by decide⟩ :=
  accepted_of_selected 11 88623 ⟨1227156, by decide⟩ ⟨11, 2, 0, 1227156, 88623, 1885, 262144⟩
    (by decide) selected_cut_44571

theorem unmarked_context_10_22155_1227157 : frontier 11 ⟨1227157, by decide⟩
    (prefixCache 10 22155) (prefixPartial 10 22155) = false := by
  decide +kernel

theorem node_context_10_22155_1227157 : EJMOriginalGlobalDAGData.nodes 11 ⟨1227157, by decide⟩ =
    .split (coordinate 10) (![⟨1227042, by decide⟩,⟨1227090, by decide⟩,⟨1227127, by decide⟩,⟨1227156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22155_1227157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22155 ⟨1227157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22155
    ⟨1227157, by decide⟩ (by decide) (![⟨1227042, by decide⟩,⟨1227090, by decide⟩,⟨1227127, by decide⟩,⟨1227156, by decide⟩]) unmarked_context_10_22155_1227157 node_context_10_22155_1227157
  intro a
  fin_cases a
  · exact context_11_88620_1227042
  · exact context_11_88621_1227090
  · exact context_11_88622_1227127
  · exact context_11_88623_1227156

theorem unmarked_context_9_5538_1227158 : frontier 12 ⟨1227158, by decide⟩
    (prefixCache 9 5538) (prefixPartial 9 5538) = false := by
  decide +kernel

theorem node_context_9_5538_1227158 : EJMOriginalGlobalDAGData.nodes 12 ⟨1227158, by decide⟩ =
    .split (coordinate 9) (![⟨1226806, by decide⟩,⟨1226960, by decide⟩,⟨1226999, by decide⟩,⟨1227157, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5538_1227158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5538 ⟨1227158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5538
    ⟨1227158, by decide⟩ (by decide) (![⟨1226806, by decide⟩,⟨1226960, by decide⟩,⟨1226999, by decide⟩,⟨1227157, by decide⟩]) unmarked_context_9_5538_1227158 node_context_9_5538_1227158
  intro a
  fin_cases a
  · exact context_10_22152_1226806
  · exact context_10_22153_1226960
  · exact context_10_22154_1226999
  · exact context_10_22155_1227157

theorem selected_cut_44572 : selected 10 ⟨1227168, by decide⟩
    (prefixPartial 11 88624) = some ⟨11, 2, 0, 1227168, 88624, 961, 262144⟩ := by
  decide +kernel

theorem context_11_88624_1227168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88624 ⟨1227168, by decide⟩ :=
  accepted_of_selected 11 88624 ⟨1227168, by decide⟩ ⟨11, 2, 0, 1227168, 88624, 961, 262144⟩
    (by decide) selected_cut_44572

theorem selected_cut_44573 : selected 10 ⟨1227198, by decide⟩
    (prefixPartial 11 88625) = some ⟨11, 2, 0, 1227198, 88625, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_88625_1227198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88625 ⟨1227198, by decide⟩ :=
  accepted_of_selected 11 88625 ⟨1227198, by decide⟩ ⟨11, 2, 0, 1227198, 88625, 1941, 262144⟩
    (by decide) selected_cut_44573

theorem selected_cut_44574 : selected 10 ⟨1227219, by decide⟩
    (prefixPartial 11 88626) = some ⟨11, 2, 0, 1227219, 88626, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_88626_1227219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88626 ⟨1227219, by decide⟩ :=
  accepted_of_selected 11 88626 ⟨1227219, by decide⟩ ⟨11, 2, 0, 1227219, 88626, 1373, 262144⟩
    (by decide) selected_cut_44574

theorem selected_cut_44575 : selected 10 ⟨1227245, by decide⟩
    (prefixPartial 11 88627) = some ⟨11, 2, 0, 1227245, 88627, 1385, 262144⟩ := by
  decide +kernel

theorem context_11_88627_1227245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88627 ⟨1227245, by decide⟩ :=
  accepted_of_selected 11 88627 ⟨1227245, by decide⟩ ⟨11, 2, 0, 1227245, 88627, 1385, 262144⟩
    (by decide) selected_cut_44575

theorem unmarked_context_10_22156_1227246 : frontier 11 ⟨1227246, by decide⟩
    (prefixCache 10 22156) (prefixPartial 10 22156) = false := by
  decide +kernel

theorem node_context_10_22156_1227246 : EJMOriginalGlobalDAGData.nodes 11 ⟨1227246, by decide⟩ =
    .split (coordinate 10) (![⟨1227168, by decide⟩,⟨1227198, by decide⟩,⟨1227219, by decide⟩,⟨1227245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22156_1227246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22156 ⟨1227246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22156
    ⟨1227246, by decide⟩ (by decide) (![⟨1227168, by decide⟩,⟨1227198, by decide⟩,⟨1227219, by decide⟩,⟨1227245, by decide⟩]) unmarked_context_10_22156_1227246 node_context_10_22156_1227246
  intro a
  fin_cases a
  · exact context_11_88624_1227168
  · exact context_11_88625_1227198
  · exact context_11_88626_1227219
  · exact context_11_88627_1227245

theorem selected_cut_44576 : selected 11 ⟨1227296, by decide⟩
    (prefixPartial 10 22157) = some ⟨10, 2, 0, 1227296, 22157, 3505, 1048576⟩ := by
  decide +kernel

theorem context_10_22157_1227296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22157 ⟨1227296, by decide⟩ :=
  accepted_of_selected 10 22157 ⟨1227296, by decide⟩ ⟨10, 2, 0, 1227296, 22157, 3505, 1048576⟩
    (by decide) selected_cut_44576

theorem selected_cut_44577 : selected 11 ⟨1227325, by decide⟩
    (prefixPartial 10 22158) = some ⟨10, 2, 0, 1227325, 22158, 1417, 1048576⟩ := by
  decide +kernel

theorem context_10_22158_1227325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22158 ⟨1227325, by decide⟩ :=
  accepted_of_selected 10 22158 ⟨1227325, by decide⟩ ⟨10, 2, 0, 1227325, 22158, 1417, 1048576⟩
    (by decide) selected_cut_44577

theorem selected_cut_44578 : selected 11 ⟨1227327, by decide⟩
    (prefixPartial 10 22159) = some ⟨10, 2, 0, 1227327, 22159, 377, 1048576⟩ := by
  decide +kernel

theorem context_10_22159_1227327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22159 ⟨1227327, by decide⟩ :=
  accepted_of_selected 10 22159 ⟨1227327, by decide⟩ ⟨10, 2, 0, 1227327, 22159, 377, 1048576⟩
    (by decide) selected_cut_44578

theorem unmarked_context_9_5539_1227328 : frontier 12 ⟨1227328, by decide⟩
    (prefixCache 9 5539) (prefixPartial 9 5539) = false := by
  decide +kernel

theorem node_context_9_5539_1227328 : EJMOriginalGlobalDAGData.nodes 12 ⟨1227328, by decide⟩ =
    .split (coordinate 9) (![⟨1227246, by decide⟩,⟨1227296, by decide⟩,⟨1227325, by decide⟩,⟨1227327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5539_1227328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5539 ⟨1227328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5539
    ⟨1227328, by decide⟩ (by decide) (![⟨1227246, by decide⟩,⟨1227296, by decide⟩,⟨1227325, by decide⟩,⟨1227327, by decide⟩]) unmarked_context_9_5539_1227328 node_context_9_5539_1227328
  intro a
  fin_cases a
  · exact context_10_22156_1227246
  · exact context_10_22157_1227296
  · exact context_10_22158_1227325
  · exact context_10_22159_1227327

theorem unmarked_context_8_1384_1227329 : frontier 13 ⟨1227329, by decide⟩
    (prefixCache 8 1384) (prefixPartial 8 1384) = false := by
  decide +kernel

theorem node_context_8_1384_1227329 : EJMOriginalGlobalDAGData.nodes 13 ⟨1227329, by decide⟩ =
    .split (coordinate 8) (![⟨1225908, by decide⟩,⟨1226562, by decide⟩,⟨1227158, by decide⟩,⟨1227328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1384_1227329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1384 ⟨1227329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1384
    ⟨1227329, by decide⟩ (by decide) (![⟨1225908, by decide⟩,⟨1226562, by decide⟩,⟨1227158, by decide⟩,⟨1227328, by decide⟩]) unmarked_context_8_1384_1227329 node_context_8_1384_1227329
  intro a
  fin_cases a
  · exact context_9_5536_1225908
  · exact context_9_5537_1226562
  · exact context_9_5538_1227158
  · exact context_9_5539_1227328

theorem selected_cut_44579 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88640) = some ⟨11, 1, 0, 434745, 88640, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88640_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88640 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88640 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88640, 1, 262144⟩
    (by decide) selected_cut_44579

theorem selected_cut_44580 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354564) = some ⟨12, 1, 0, 448748, 354564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354564_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354564 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354564 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354564, 1, 65536⟩
    (by decide) selected_cut_44580

theorem selected_cut_44581 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 354565) = some ⟨12, 1, 0, 34034, 354565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354565_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354565 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 354565 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 354565, 1, 65536⟩
    (by decide) selected_cut_44581

theorem selected_cut_44582 : selected 9 ⟨1227384, by decide⟩
    (prefixPartial 12 354566) = some ⟨12, 2, 0, 1227384, 354566, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_354566_1227384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354566 ⟨1227384, by decide⟩ :=
  accepted_of_selected 12 354566 ⟨1227384, by decide⟩ ⟨12, 2, 0, 1227384, 354566, 2521, 65536⟩
    (by decide) selected_cut_44582

theorem selected_cut_44583 : selected 9 ⟨1227433, by decide⟩
    (prefixPartial 12 354567) = some ⟨12, 2, 0, 1227433, 354567, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_354567_1227433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354567 ⟨1227433, by decide⟩ :=
  accepted_of_selected 12 354567 ⟨1227433, by decide⟩ ⟨12, 2, 0, 1227433, 354567, 2709, 65536⟩
    (by decide) selected_cut_44583

theorem unmarked_context_11_88641_1227434 : frontier 10 ⟨1227434, by decide⟩
    (prefixCache 11 88641) (prefixPartial 11 88641) = false := by
  decide +kernel

theorem node_context_11_88641_1227434 : EJMOriginalGlobalDAGData.nodes 10 ⟨1227434, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1227384, by decide⟩,⟨1227433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88641_1227434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88641 ⟨1227434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88641
    ⟨1227434, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1227384, by decide⟩,⟨1227433, by decide⟩]) unmarked_context_11_88641_1227434 node_context_11_88641_1227434
  intro a
  fin_cases a
  · exact context_12_354564_448748
  · exact context_12_354565_34034
  · exact context_12_354566_1227384
  · exact context_12_354567_1227433

theorem selected_cut_44584 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354568) = some ⟨12, 1, 0, 448748, 354568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354568_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354568 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354568 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354568, 1, 65536⟩
    (by decide) selected_cut_44584

theorem selected_cut_44585 : selected 9 ⟨1227498, by decide⟩
    (prefixPartial 12 354569) = some ⟨12, 2, 0, 1227498, 354569, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_354569_1227498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354569 ⟨1227498, by decide⟩ :=
  accepted_of_selected 12 354569 ⟨1227498, by decide⟩ ⟨12, 2, 0, 1227498, 354569, 2833, 65536⟩
    (by decide) selected_cut_44585

theorem selected_cut_44586 : selected 9 ⟨1227554, by decide⟩
    (prefixPartial 12 354570) = some ⟨12, 2, 0, 1227554, 354570, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_354570_1227554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354570 ⟨1227554, by decide⟩ :=
  accepted_of_selected 12 354570 ⟨1227554, by decide⟩ ⟨12, 2, 0, 1227554, 354570, 2725, 65536⟩
    (by decide) selected_cut_44586

theorem selected_cut_44587 : selected 9 ⟨1227619, by decide⟩
    (prefixPartial 12 354571) = some ⟨12, 2, 0, 1227619, 354571, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_354571_1227619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354571 ⟨1227619, by decide⟩ :=
  accepted_of_selected 12 354571 ⟨1227619, by decide⟩ ⟨12, 2, 0, 1227619, 354571, 2885, 65536⟩
    (by decide) selected_cut_44587

theorem unmarked_context_11_88642_1227620 : frontier 10 ⟨1227620, by decide⟩
    (prefixCache 11 88642) (prefixPartial 11 88642) = false := by
  decide +kernel

theorem node_context_11_88642_1227620 : EJMOriginalGlobalDAGData.nodes 10 ⟨1227620, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1227498, by decide⟩,⟨1227554, by decide⟩,⟨1227619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88642_1227620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88642 ⟨1227620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88642
    ⟨1227620, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1227498, by decide⟩,⟨1227554, by decide⟩,⟨1227619, by decide⟩]) unmarked_context_11_88642_1227620 node_context_11_88642_1227620
  intro a
  fin_cases a
  · exact context_12_354568_448748
  · exact context_12_354569_1227498
  · exact context_12_354570_1227554
  · exact context_12_354571_1227619

theorem selected_cut_44588 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354572) = some ⟨12, 1, 0, 448748, 354572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354572_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354572 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354572 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354572, 1, 65536⟩
    (by decide) selected_cut_44588

theorem selected_cut_44589 : selected 9 ⟨1227665, by decide⟩
    (prefixPartial 12 354573) = some ⟨12, 2, 0, 1227665, 354573, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_354573_1227665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354573 ⟨1227665, by decide⟩ :=
  accepted_of_selected 12 354573 ⟨1227665, by decide⟩ ⟨12, 2, 0, 1227665, 354573, 2509, 65536⟩
    (by decide) selected_cut_44589

theorem selected_cut_44590 : selected 9 ⟨1227709, by decide⟩
    (prefixPartial 12 354574) = some ⟨12, 2, 0, 1227709, 354574, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_354574_1227709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354574 ⟨1227709, by decide⟩ :=
  accepted_of_selected 12 354574 ⟨1227709, by decide⟩ ⟨12, 2, 0, 1227709, 354574, 2633, 65536⟩
    (by decide) selected_cut_44590

theorem selected_cut_44591 : selected 9 ⟨1227761, by decide⟩
    (prefixPartial 12 354575) = some ⟨12, 2, 0, 1227761, 354575, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_354575_1227761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354575 ⟨1227761, by decide⟩ :=
  accepted_of_selected 12 354575 ⟨1227761, by decide⟩ ⟨12, 2, 0, 1227761, 354575, 2929, 65536⟩
    (by decide) selected_cut_44591

theorem unmarked_context_11_88643_1227762 : frontier 10 ⟨1227762, by decide⟩
    (prefixCache 11 88643) (prefixPartial 11 88643) = false := by
  decide +kernel

theorem node_context_11_88643_1227762 : EJMOriginalGlobalDAGData.nodes 10 ⟨1227762, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1227665, by decide⟩,⟨1227709, by decide⟩,⟨1227761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88643_1227762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88643 ⟨1227762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88643
    ⟨1227762, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1227665, by decide⟩,⟨1227709, by decide⟩,⟨1227761, by decide⟩]) unmarked_context_11_88643_1227762 node_context_11_88643_1227762
  intro a
  fin_cases a
  · exact context_12_354572_448748
  · exact context_12_354573_1227665
  · exact context_12_354574_1227709
  · exact context_12_354575_1227761

theorem unmarked_context_10_22160_1227763 : frontier 11 ⟨1227763, by decide⟩
    (prefixCache 10 22160) (prefixPartial 10 22160) = false := by
  decide +kernel

theorem node_context_10_22160_1227763 : EJMOriginalGlobalDAGData.nodes 11 ⟨1227763, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1227434, by decide⟩,⟨1227620, by decide⟩,⟨1227762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22160_1227763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22160 ⟨1227763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22160
    ⟨1227763, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1227434, by decide⟩,⟨1227620, by decide⟩,⟨1227762, by decide⟩]) unmarked_context_10_22160_1227763 node_context_10_22160_1227763
  intro a
  fin_cases a
  · exact context_11_88640_434745
  · exact context_11_88641_1227434
  · exact context_11_88642_1227620
  · exact context_11_88643_1227762

theorem selected_cut_44592 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 354576) = some ⟨12, 1, 0, 435160, 354576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354576_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354576 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 354576 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 354576, 1, 65536⟩
    (by decide) selected_cut_44592

theorem selected_cut_44593 : selected 9 ⟨1227818, by decide⟩
    (prefixPartial 12 354577) = some ⟨12, 2, 0, 1227818, 354577, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_354577_1227818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354577 ⟨1227818, by decide⟩ :=
  accepted_of_selected 12 354577 ⟨1227818, by decide⟩ ⟨12, 2, 0, 1227818, 354577, 2465, 65536⟩
    (by decide) selected_cut_44593

theorem selected_cut_44594 : selected 9 ⟨1227855, by decide⟩
    (prefixPartial 12 354578) = some ⟨12, 2, 0, 1227855, 354578, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_354578_1227855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354578 ⟨1227855, by decide⟩ :=
  accepted_of_selected 12 354578 ⟨1227855, by decide⟩ ⟨12, 2, 0, 1227855, 354578, 2449, 65536⟩
    (by decide) selected_cut_44594

theorem selected_cut_44595 : selected 9 ⟨1227888, by decide⟩
    (prefixPartial 12 354579) = some ⟨12, 2, 0, 1227888, 354579, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_354579_1227888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354579 ⟨1227888, by decide⟩ :=
  accepted_of_selected 12 354579 ⟨1227888, by decide⟩ ⟨12, 2, 0, 1227888, 354579, 2513, 65536⟩
    (by decide) selected_cut_44595

theorem unmarked_context_11_88644_1227889 : frontier 10 ⟨1227889, by decide⟩
    (prefixCache 11 88644) (prefixPartial 11 88644) = false := by
  decide +kernel

theorem node_context_11_88644_1227889 : EJMOriginalGlobalDAGData.nodes 10 ⟨1227889, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1227818, by decide⟩,⟨1227855, by decide⟩,⟨1227888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88644_1227889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88644 ⟨1227889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88644
    ⟨1227889, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1227818, by decide⟩,⟨1227855, by decide⟩,⟨1227888, by decide⟩]) unmarked_context_11_88644_1227889 node_context_11_88644_1227889
  intro a
  fin_cases a
  · exact context_12_354576_435160
  · exact context_12_354577_1227818
  · exact context_12_354578_1227855
  · exact context_12_354579_1227888

theorem selected_cut_44596 : selected 10 ⟨1227924, by decide⟩
    (prefixPartial 11 88645) = some ⟨11, 2, 0, 1227924, 88645, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_88645_1227924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88645 ⟨1227924, by decide⟩ :=
  accepted_of_selected 11 88645 ⟨1227924, by decide⟩ ⟨11, 2, 0, 1227924, 88645, 2341, 262144⟩
    (by decide) selected_cut_44596

theorem selected_cut_44597 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 354584) = some ⟨12, 1, 0, 449505, 354584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354584_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354584 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 354584 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 354584, 1, 65536⟩
    (by decide) selected_cut_44597

theorem selected_cut_44598 : selected 9 ⟨1227964, by decide⟩
    (prefixPartial 12 354585) = some ⟨12, 2, 0, 1227964, 354585, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_354585_1227964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354585 ⟨1227964, by decide⟩ :=
  accepted_of_selected 12 354585 ⟨1227964, by decide⟩ ⟨12, 2, 0, 1227964, 354585, 2357, 65536⟩
    (by decide) selected_cut_44598

theorem selected_cut_44599 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 354586) = some ⟨12, 1, 0, 660636, 354586, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354586_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354586 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 354586 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 354586, 1, 65536⟩
    (by decide) selected_cut_44599

theorem selected_cut_44600 : selected 9 ⟨1228013, by decide⟩
    (prefixPartial 12 354587) = some ⟨12, 2, 0, 1228013, 354587, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_354587_1228013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354587 ⟨1228013, by decide⟩ :=
  accepted_of_selected 12 354587 ⟨1228013, by decide⟩ ⟨12, 2, 0, 1228013, 354587, 2561, 65536⟩
    (by decide) selected_cut_44600

theorem unmarked_context_11_88646_1228014 : frontier 10 ⟨1228014, by decide⟩
    (prefixCache 11 88646) (prefixPartial 11 88646) = false := by
  decide +kernel

theorem node_context_11_88646_1228014 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228014, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨1227964, by decide⟩,⟨660636, by decide⟩,⟨1228013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88646_1228014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88646 ⟨1228014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88646
    ⟨1228014, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨1227964, by decide⟩,⟨660636, by decide⟩,⟨1228013, by decide⟩]) unmarked_context_11_88646_1228014 node_context_11_88646_1228014
  intro a
  fin_cases a
  · exact context_12_354584_449505
  · exact context_12_354585_1227964
  · exact context_12_354586_660636
  · exact context_12_354587_1228013

theorem selected_cut_44601 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 354588) = some ⟨12, 1, 0, 539296, 354588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354588_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354588 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 354588 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 354588, 1, 65536⟩
    (by decide) selected_cut_44601

theorem selected_cut_44602 : selected 9 ⟨1228043, by decide⟩
    (prefixPartial 12 354589) = some ⟨12, 2, 0, 1228043, 354589, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_354589_1228043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354589 ⟨1228043, by decide⟩ :=
  accepted_of_selected 12 354589 ⟨1228043, by decide⟩ ⟨12, 2, 0, 1228043, 354589, 2133, 65536⟩
    (by decide) selected_cut_44602

theorem selected_cut_44603 : selected 9 ⟨1228078, by decide⟩
    (prefixPartial 12 354590) = some ⟨12, 2, 0, 1228078, 354590, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_354590_1228078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354590 ⟨1228078, by decide⟩ :=
  accepted_of_selected 12 354590 ⟨1228078, by decide⟩ ⟨12, 2, 0, 1228078, 354590, 2301, 65536⟩
    (by decide) selected_cut_44603

theorem selected_cut_44604 : selected 9 ⟨1228123, by decide⟩
    (prefixPartial 12 354591) = some ⟨12, 2, 0, 1228123, 354591, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_354591_1228123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354591 ⟨1228123, by decide⟩ :=
  accepted_of_selected 12 354591 ⟨1228123, by decide⟩ ⟨12, 2, 0, 1228123, 354591, 2509, 65536⟩
    (by decide) selected_cut_44604

theorem unmarked_context_11_88647_1228124 : frontier 10 ⟨1228124, by decide⟩
    (prefixCache 11 88647) (prefixPartial 11 88647) = false := by
  decide +kernel

theorem node_context_11_88647_1228124 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228124, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨1228043, by decide⟩,⟨1228078, by decide⟩,⟨1228123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88647_1228124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88647 ⟨1228124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88647
    ⟨1228124, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨1228043, by decide⟩,⟨1228078, by decide⟩,⟨1228123, by decide⟩]) unmarked_context_11_88647_1228124 node_context_11_88647_1228124
  intro a
  fin_cases a
  · exact context_12_354588_539296
  · exact context_12_354589_1228043
  · exact context_12_354590_1228078
  · exact context_12_354591_1228123

theorem unmarked_context_10_22161_1228125 : frontier 11 ⟨1228125, by decide⟩
    (prefixCache 10 22161) (prefixPartial 10 22161) = false := by
  decide +kernel

theorem node_context_10_22161_1228125 : EJMOriginalGlobalDAGData.nodes 11 ⟨1228125, by decide⟩ =
    .split (coordinate 10) (![⟨1227889, by decide⟩,⟨1227924, by decide⟩,⟨1228014, by decide⟩,⟨1228124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22161_1228125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22161 ⟨1228125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22161
    ⟨1228125, by decide⟩ (by decide) (![⟨1227889, by decide⟩,⟨1227924, by decide⟩,⟨1228014, by decide⟩,⟨1228124, by decide⟩]) unmarked_context_10_22161_1228125 node_context_10_22161_1228125
  intro a
  fin_cases a
  · exact context_11_88644_1227889
  · exact context_11_88645_1227924
  · exact context_11_88646_1228014
  · exact context_11_88647_1228124

theorem selected_cut_44605 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 354592) = some ⟨12, 1, 0, 1187656, 354592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354592_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354592 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 354592 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 354592, 1, 65536⟩
    (by decide) selected_cut_44605

theorem selected_cut_44606 : selected 9 ⟨1228165, by decide⟩
    (prefixPartial 12 354593) = some ⟨12, 2, 0, 1228165, 354593, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_354593_1228165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354593 ⟨1228165, by decide⟩ :=
  accepted_of_selected 12 354593 ⟨1228165, by decide⟩ ⟨12, 2, 0, 1228165, 354593, 2377, 65536⟩
    (by decide) selected_cut_44606

theorem selected_cut_44607 : selected 9 ⟨1228199, by decide⟩
    (prefixPartial 12 354594) = some ⟨12, 2, 0, 1228199, 354594, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_354594_1228199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354594 ⟨1228199, by decide⟩ :=
  accepted_of_selected 12 354594 ⟨1228199, by decide⟩ ⟨12, 2, 0, 1228199, 354594, 2173, 65536⟩
    (by decide) selected_cut_44607

theorem selected_cut_44608 : selected 9 ⟨1228236, by decide⟩
    (prefixPartial 12 354595) = some ⟨12, 2, 0, 1228236, 354595, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_354595_1228236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354595 ⟨1228236, by decide⟩ :=
  accepted_of_selected 12 354595 ⟨1228236, by decide⟩ ⟨12, 2, 0, 1228236, 354595, 2389, 65536⟩
    (by decide) selected_cut_44608

theorem unmarked_context_11_88648_1228237 : frontier 10 ⟨1228237, by decide⟩
    (prefixCache 11 88648) (prefixPartial 11 88648) = false := by
  decide +kernel

theorem node_context_11_88648_1228237 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228237, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1228165, by decide⟩,⟨1228199, by decide⟩,⟨1228236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88648_1228237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88648 ⟨1228237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88648
    ⟨1228237, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1228165, by decide⟩,⟨1228199, by decide⟩,⟨1228236, by decide⟩]) unmarked_context_11_88648_1228237 node_context_11_88648_1228237
  intro a
  fin_cases a
  · exact context_12_354592_1187656
  · exact context_12_354593_1228165
  · exact context_12_354594_1228199
  · exact context_12_354595_1228236

theorem selected_cut_44609 : selected 9 ⟨1228238, by decide⟩
    (prefixPartial 12 354596) = some ⟨12, 1, 0, 1228238, 354596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354596_1228238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354596 ⟨1228238, by decide⟩ :=
  accepted_of_selected 12 354596 ⟨1228238, by decide⟩ ⟨12, 1, 0, 1228238, 354596, 1, 65536⟩
    (by decide) selected_cut_44609

theorem selected_cut_44610 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 354597) = some ⟨12, 1, 0, 891951, 354597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354597_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354597 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 354597 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 354597, 1, 65536⟩
    (by decide) selected_cut_44610

theorem selected_cut_44611 : selected 9 ⟨1228268, by decide⟩
    (prefixPartial 12 354598) = some ⟨12, 2, 0, 1228268, 354598, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_354598_1228268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354598 ⟨1228268, by decide⟩ :=
  accepted_of_selected 12 354598 ⟨1228268, by decide⟩ ⟨12, 2, 0, 1228268, 354598, 2001, 65536⟩
    (by decide) selected_cut_44611

theorem selected_cut_44612 : selected 9 ⟨1228303, by decide⟩
    (prefixPartial 12 354599) = some ⟨12, 2, 0, 1228303, 354599, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_354599_1228303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354599 ⟨1228303, by decide⟩ :=
  accepted_of_selected 12 354599 ⟨1228303, by decide⟩ ⟨12, 2, 0, 1228303, 354599, 2237, 65536⟩
    (by decide) selected_cut_44612

theorem unmarked_context_11_88649_1228304 : frontier 10 ⟨1228304, by decide⟩
    (prefixCache 11 88649) (prefixPartial 11 88649) = false := by
  decide +kernel

theorem node_context_11_88649_1228304 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228304, by decide⟩ =
    .split (coordinate 11) (![⟨1228238, by decide⟩,⟨891951, by decide⟩,⟨1228268, by decide⟩,⟨1228303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88649_1228304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88649 ⟨1228304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88649
    ⟨1228304, by decide⟩ (by decide) (![⟨1228238, by decide⟩,⟨891951, by decide⟩,⟨1228268, by decide⟩,⟨1228303, by decide⟩]) unmarked_context_11_88649_1228304 node_context_11_88649_1228304
  intro a
  fin_cases a
  · exact context_12_354596_1228238
  · exact context_12_354597_891951
  · exact context_12_354598_1228268
  · exact context_12_354599_1228303

theorem selected_cut_44613 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88650) = some ⟨11, 1, 0, 900587, 88650, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88650_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88650 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88650 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88650, 1, 262144⟩
    (by decide) selected_cut_44613

theorem selected_cut_44614 : selected 9 ⟨1228332, by decide⟩
    (prefixPartial 12 354604) = some ⟨12, 2, 0, 1228332, 354604, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_354604_1228332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354604 ⟨1228332, by decide⟩ :=
  accepted_of_selected 12 354604 ⟨1228332, by decide⟩ ⟨12, 2, 0, 1228332, 354604, 2325, 65536⟩
    (by decide) selected_cut_44614

theorem selected_cut_44615 : selected 9 ⟨1228362, by decide⟩
    (prefixPartial 12 354605) = some ⟨12, 2, 0, 1228362, 354605, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_354605_1228362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354605 ⟨1228362, by decide⟩ :=
  accepted_of_selected 12 354605 ⟨1228362, by decide⟩ ⟨12, 2, 0, 1228362, 354605, 2097, 65536⟩
    (by decide) selected_cut_44615

theorem selected_cut_44616 : selected 9 ⟨1228395, by decide⟩
    (prefixPartial 12 354606) = some ⟨12, 2, 0, 1228395, 354606, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_354606_1228395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354606 ⟨1228395, by decide⟩ :=
  accepted_of_selected 12 354606 ⟨1228395, by decide⟩ ⟨12, 2, 0, 1228395, 354606, 2149, 65536⟩
    (by decide) selected_cut_44616

theorem selected_cut_44617 : selected 9 ⟨1228439, by decide⟩
    (prefixPartial 12 354607) = some ⟨12, 2, 0, 1228439, 354607, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_354607_1228439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354607 ⟨1228439, by decide⟩ :=
  accepted_of_selected 12 354607 ⟨1228439, by decide⟩ ⟨12, 2, 0, 1228439, 354607, 2445, 65536⟩
    (by decide) selected_cut_44617

theorem unmarked_context_11_88651_1228440 : frontier 10 ⟨1228440, by decide⟩
    (prefixCache 11 88651) (prefixPartial 11 88651) = false := by
  decide +kernel

theorem node_context_11_88651_1228440 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228440, by decide⟩ =
    .split (coordinate 11) (![⟨1228332, by decide⟩,⟨1228362, by decide⟩,⟨1228395, by decide⟩,⟨1228439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88651_1228440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88651 ⟨1228440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88651
    ⟨1228440, by decide⟩ (by decide) (![⟨1228332, by decide⟩,⟨1228362, by decide⟩,⟨1228395, by decide⟩,⟨1228439, by decide⟩]) unmarked_context_11_88651_1228440 node_context_11_88651_1228440
  intro a
  fin_cases a
  · exact context_12_354604_1228332
  · exact context_12_354605_1228362
  · exact context_12_354606_1228395
  · exact context_12_354607_1228439

theorem unmarked_context_10_22162_1228441 : frontier 11 ⟨1228441, by decide⟩
    (prefixCache 10 22162) (prefixPartial 10 22162) = false := by
  decide +kernel

theorem node_context_10_22162_1228441 : EJMOriginalGlobalDAGData.nodes 11 ⟨1228441, by decide⟩ =
    .split (coordinate 10) (![⟨1228237, by decide⟩,⟨1228304, by decide⟩,⟨900587, by decide⟩,⟨1228440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22162_1228441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22162 ⟨1228441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22162
    ⟨1228441, by decide⟩ (by decide) (![⟨1228237, by decide⟩,⟨1228304, by decide⟩,⟨900587, by decide⟩,⟨1228440, by decide⟩]) unmarked_context_10_22162_1228441 node_context_10_22162_1228441
  intro a
  fin_cases a
  · exact context_11_88648_1228237
  · exact context_11_88649_1228304
  · exact context_11_88650_900587
  · exact context_11_88651_1228440

theorem selected_cut_44618 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 354608) = some ⟨12, 1, 0, 1187656, 354608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354608_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354608 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 354608 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 354608, 1, 65536⟩
    (by decide) selected_cut_44618

theorem selected_cut_44619 : selected 9 ⟨1228479, by decide⟩
    (prefixPartial 12 354609) = some ⟨12, 2, 0, 1228479, 354609, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_354609_1228479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354609 ⟨1228479, by decide⟩ :=
  accepted_of_selected 12 354609 ⟨1228479, by decide⟩ ⟨12, 2, 0, 1228479, 354609, 2301, 65536⟩
    (by decide) selected_cut_44619

theorem selected_cut_44620 : selected 9 ⟨1228522, by decide⟩
    (prefixPartial 12 354610) = some ⟨12, 2, 0, 1228522, 354610, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_354610_1228522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354610 ⟨1228522, by decide⟩ :=
  accepted_of_selected 12 354610 ⟨1228522, by decide⟩ ⟨12, 2, 0, 1228522, 354610, 2369, 65536⟩
    (by decide) selected_cut_44620

theorem selected_cut_44621 : selected 9 ⟨1228580, by decide⟩
    (prefixPartial 12 354611) = some ⟨12, 2, 0, 1228580, 354611, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_354611_1228580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354611 ⟨1228580, by decide⟩ :=
  accepted_of_selected 12 354611 ⟨1228580, by decide⟩ ⟨12, 2, 0, 1228580, 354611, 2437, 65536⟩
    (by decide) selected_cut_44621

theorem unmarked_context_11_88652_1228581 : frontier 10 ⟨1228581, by decide⟩
    (prefixCache 11 88652) (prefixPartial 11 88652) = false := by
  decide +kernel

theorem node_context_11_88652_1228581 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228581, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1228479, by decide⟩,⟨1228522, by decide⟩,⟨1228580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88652_1228581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88652 ⟨1228581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88652
    ⟨1228581, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1228479, by decide⟩,⟨1228522, by decide⟩,⟨1228580, by decide⟩]) unmarked_context_11_88652_1228581 node_context_11_88652_1228581
  intro a
  fin_cases a
  · exact context_12_354608_1187656
  · exact context_12_354609_1228479
  · exact context_12_354610_1228522
  · exact context_12_354611_1228580

theorem selected_cut_44622 : selected 9 ⟨1228582, by decide⟩
    (prefixPartial 12 354612) = some ⟨12, 1, 0, 1228582, 354612, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354612_1228582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354612 ⟨1228582, by decide⟩ :=
  accepted_of_selected 12 354612 ⟨1228582, by decide⟩ ⟨12, 1, 0, 1228582, 354612, 1, 65536⟩
    (by decide) selected_cut_44622

theorem selected_cut_44623 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 354613) = some ⟨12, 1, 0, 891951, 354613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354613_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354613 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 354613 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 354613, 1, 65536⟩
    (by decide) selected_cut_44623

theorem selected_cut_44624 : selected 9 ⟨1228628, by decide⟩
    (prefixPartial 12 354614) = some ⟨12, 2, 0, 1228628, 354614, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_354614_1228628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354614 ⟨1228628, by decide⟩ :=
  accepted_of_selected 12 354614 ⟨1228628, by decide⟩ ⟨12, 2, 0, 1228628, 354614, 2237, 65536⟩
    (by decide) selected_cut_44624

theorem selected_cut_44625 : selected 9 ⟨1228667, by decide⟩
    (prefixPartial 12 354615) = some ⟨12, 2, 0, 1228667, 354615, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_354615_1228667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354615 ⟨1228667, by decide⟩ :=
  accepted_of_selected 12 354615 ⟨1228667, by decide⟩ ⟨12, 2, 0, 1228667, 354615, 2193, 65536⟩
    (by decide) selected_cut_44625

theorem unmarked_context_11_88653_1228668 : frontier 10 ⟨1228668, by decide⟩
    (prefixCache 11 88653) (prefixPartial 11 88653) = false := by
  decide +kernel

theorem node_context_11_88653_1228668 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228668, by decide⟩ =
    .split (coordinate 11) (![⟨1228582, by decide⟩,⟨891951, by decide⟩,⟨1228628, by decide⟩,⟨1228667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88653_1228668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88653 ⟨1228668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88653
    ⟨1228668, by decide⟩ (by decide) (![⟨1228582, by decide⟩,⟨891951, by decide⟩,⟨1228628, by decide⟩,⟨1228667, by decide⟩]) unmarked_context_11_88653_1228668 node_context_11_88653_1228668
  intro a
  fin_cases a
  · exact context_12_354612_1228582
  · exact context_12_354613_891951
  · exact context_12_354614_1228628
  · exact context_12_354615_1228667

theorem selected_cut_44626 : selected 9 ⟨1228709, by decide⟩
    (prefixPartial 12 354616) = some ⟨12, 2, 0, 1228709, 354616, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_354616_1228709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354616 ⟨1228709, by decide⟩ :=
  accepted_of_selected 12 354616 ⟨1228709, by decide⟩ ⟨12, 2, 0, 1228709, 354616, 2305, 65536⟩
    (by decide) selected_cut_44626

theorem selected_cut_44627 : selected 9 ⟨1228744, by decide⟩
    (prefixPartial 12 354617) = some ⟨12, 2, 0, 1228744, 354617, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_354617_1228744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354617 ⟨1228744, by decide⟩ :=
  accepted_of_selected 12 354617 ⟨1228744, by decide⟩ ⟨12, 2, 0, 1228744, 354617, 2245, 65536⟩
    (by decide) selected_cut_44627

theorem selected_cut_44628 : selected 9 ⟨1228780, by decide⟩
    (prefixPartial 12 354618) = some ⟨12, 2, 0, 1228780, 354618, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_354618_1228780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354618 ⟨1228780, by decide⟩ :=
  accepted_of_selected 12 354618 ⟨1228780, by decide⟩ ⟨12, 2, 0, 1228780, 354618, 2253, 65536⟩
    (by decide) selected_cut_44628

theorem selected_cut_44629 : selected 9 ⟨1228823, by decide⟩
    (prefixPartial 12 354619) = some ⟨12, 2, 0, 1228823, 354619, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_354619_1228823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354619 ⟨1228823, by decide⟩ :=
  accepted_of_selected 12 354619 ⟨1228823, by decide⟩ ⟨12, 2, 0, 1228823, 354619, 2305, 65536⟩
    (by decide) selected_cut_44629

theorem unmarked_context_11_88654_1228824 : frontier 10 ⟨1228824, by decide⟩
    (prefixCache 11 88654) (prefixPartial 11 88654) = false := by
  decide +kernel

theorem node_context_11_88654_1228824 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228824, by decide⟩ =
    .split (coordinate 11) (![⟨1228709, by decide⟩,⟨1228744, by decide⟩,⟨1228780, by decide⟩,⟨1228823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88654_1228824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88654 ⟨1228824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88654
    ⟨1228824, by decide⟩ (by decide) (![⟨1228709, by decide⟩,⟨1228744, by decide⟩,⟨1228780, by decide⟩,⟨1228823, by decide⟩]) unmarked_context_11_88654_1228824 node_context_11_88654_1228824
  intro a
  fin_cases a
  · exact context_12_354616_1228709
  · exact context_12_354617_1228744
  · exact context_12_354618_1228780
  · exact context_12_354619_1228823

theorem selected_cut_44630 : selected 9 ⟨1228860, by decide⟩
    (prefixPartial 12 354620) = some ⟨12, 2, 0, 1228860, 354620, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_354620_1228860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354620 ⟨1228860, by decide⟩ :=
  accepted_of_selected 12 354620 ⟨1228860, by decide⟩ ⟨12, 2, 0, 1228860, 354620, 2005, 65536⟩
    (by decide) selected_cut_44630

theorem selected_cut_44631 : selected 9 ⟨1228891, by decide⟩
    (prefixPartial 12 354621) = some ⟨12, 2, 0, 1228891, 354621, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_354621_1228891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354621 ⟨1228891, by decide⟩ :=
  accepted_of_selected 12 354621 ⟨1228891, by decide⟩ ⟨12, 2, 0, 1228891, 354621, 1825, 65536⟩
    (by decide) selected_cut_44631

theorem selected_cut_44632 : selected 9 ⟨1228923, by decide⟩
    (prefixPartial 12 354622) = some ⟨12, 2, 0, 1228923, 354622, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_354622_1228923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354622 ⟨1228923, by decide⟩ :=
  accepted_of_selected 12 354622 ⟨1228923, by decide⟩ ⟨12, 2, 0, 1228923, 354622, 1961, 65536⟩
    (by decide) selected_cut_44632

theorem selected_cut_44633 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 354623) = some ⟨12, 1, 0, 1120582, 354623, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354623_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354623 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 354623 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 354623, 1, 65536⟩
    (by decide) selected_cut_44633

theorem unmarked_context_11_88655_1228924 : frontier 10 ⟨1228924, by decide⟩
    (prefixCache 11 88655) (prefixPartial 11 88655) = false := by
  decide +kernel

theorem node_context_11_88655_1228924 : EJMOriginalGlobalDAGData.nodes 10 ⟨1228924, by decide⟩ =
    .split (coordinate 11) (![⟨1228860, by decide⟩,⟨1228891, by decide⟩,⟨1228923, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88655_1228924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88655 ⟨1228924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88655
    ⟨1228924, by decide⟩ (by decide) (![⟨1228860, by decide⟩,⟨1228891, by decide⟩,⟨1228923, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_88655_1228924 node_context_11_88655_1228924
  intro a
  fin_cases a
  · exact context_12_354620_1228860
  · exact context_12_354621_1228891
  · exact context_12_354622_1228923
  · exact context_12_354623_1120582

theorem unmarked_context_10_22163_1228925 : frontier 11 ⟨1228925, by decide⟩
    (prefixCache 10 22163) (prefixPartial 10 22163) = false := by
  decide +kernel

theorem node_context_10_22163_1228925 : EJMOriginalGlobalDAGData.nodes 11 ⟨1228925, by decide⟩ =
    .split (coordinate 10) (![⟨1228581, by decide⟩,⟨1228668, by decide⟩,⟨1228824, by decide⟩,⟨1228924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22163_1228925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22163 ⟨1228925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22163
    ⟨1228925, by decide⟩ (by decide) (![⟨1228581, by decide⟩,⟨1228668, by decide⟩,⟨1228824, by decide⟩,⟨1228924, by decide⟩]) unmarked_context_10_22163_1228925 node_context_10_22163_1228925
  intro a
  fin_cases a
  · exact context_11_88652_1228581
  · exact context_11_88653_1228668
  · exact context_11_88654_1228824
  · exact context_11_88655_1228924

theorem unmarked_context_9_5540_1228926 : frontier 12 ⟨1228926, by decide⟩
    (prefixCache 9 5540) (prefixPartial 9 5540) = false := by
  decide +kernel

theorem node_context_9_5540_1228926 : EJMOriginalGlobalDAGData.nodes 12 ⟨1228926, by decide⟩ =
    .split (coordinate 9) (![⟨1227763, by decide⟩,⟨1228125, by decide⟩,⟨1228441, by decide⟩,⟨1228925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5540_1228926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5540 ⟨1228926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5540
    ⟨1228926, by decide⟩ (by decide) (![⟨1227763, by decide⟩,⟨1228125, by decide⟩,⟨1228441, by decide⟩,⟨1228925, by decide⟩]) unmarked_context_9_5540_1228926 node_context_9_5540_1228926
  intro a
  fin_cases a
  · exact context_10_22160_1227763
  · exact context_10_22161_1228125
  · exact context_10_22162_1228441
  · exact context_10_22163_1228925

theorem selected_cut_44634 : selected 10 ⟨1228972, by decide⟩
    (prefixPartial 11 88656) = some ⟨11, 2, 0, 1228972, 88656, 3053, 262144⟩ := by
  decide +kernel

theorem context_11_88656_1228972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88656 ⟨1228972, by decide⟩ :=
  accepted_of_selected 11 88656 ⟨1228972, by decide⟩ ⟨11, 2, 0, 1228972, 88656, 3053, 262144⟩
    (by decide) selected_cut_44634

theorem selected_cut_44635 : selected 10 ⟨1229026, by decide⟩
    (prefixPartial 11 88657) = some ⟨11, 2, 0, 1229026, 88657, 3989, 262144⟩ := by
  decide +kernel

theorem context_11_88657_1229026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88657 ⟨1229026, by decide⟩ :=
  accepted_of_selected 11 88657 ⟨1229026, by decide⟩ ⟨11, 2, 0, 1229026, 88657, 3989, 262144⟩
    (by decide) selected_cut_44635

theorem selected_cut_44636 : selected 10 ⟨1229069, by decide⟩
    (prefixPartial 11 88658) = some ⟨11, 2, 0, 1229069, 88658, 2881, 262144⟩ := by
  decide +kernel

theorem context_11_88658_1229069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88658 ⟨1229069, by decide⟩ :=
  accepted_of_selected 11 88658 ⟨1229069, by decide⟩ ⟨11, 2, 0, 1229069, 88658, 2881, 262144⟩
    (by decide) selected_cut_44636

theorem selected_cut_44637 : selected 9 ⟨1229083, by decide⟩
    (prefixPartial 12 354636) = some ⟨12, 2, 0, 1229083, 354636, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_354636_1229083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354636 ⟨1229083, by decide⟩ :=
  accepted_of_selected 12 354636 ⟨1229083, by decide⟩ ⟨12, 2, 0, 1229083, 354636, 1333, 65536⟩
    (by decide) selected_cut_44637

theorem selected_cut_44638 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354637) = some ⟨12, 1, 0, 896706, 354637, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354637_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354637 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354637 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354637, 1, 65536⟩
    (by decide) selected_cut_44638

theorem selected_cut_44639 : selected 9 ⟨1229098, by decide⟩
    (prefixPartial 12 354638) = some ⟨12, 2, 0, 1229098, 354638, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_354638_1229098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354638 ⟨1229098, by decide⟩ :=
  accepted_of_selected 12 354638 ⟨1229098, by decide⟩ ⟨12, 2, 0, 1229098, 354638, 1377, 65536⟩
    (by decide) selected_cut_44639

theorem selected_cut_44640 : selected 9 ⟨1229118, by decide⟩
    (prefixPartial 12 354639) = some ⟨12, 2, 0, 1229118, 354639, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_354639_1229118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354639 ⟨1229118, by decide⟩ :=
  accepted_of_selected 12 354639 ⟨1229118, by decide⟩ ⟨12, 2, 0, 1229118, 354639, 1417, 65536⟩
    (by decide) selected_cut_44640

theorem unmarked_context_11_88659_1229119 : frontier 10 ⟨1229119, by decide⟩
    (prefixCache 11 88659) (prefixPartial 11 88659) = false := by
  decide +kernel

theorem node_context_11_88659_1229119 : EJMOriginalGlobalDAGData.nodes 10 ⟨1229119, by decide⟩ =
    .split (coordinate 11) (![⟨1229083, by decide⟩,⟨896706, by decide⟩,⟨1229098, by decide⟩,⟨1229118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88659_1229119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88659 ⟨1229119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88659
    ⟨1229119, by decide⟩ (by decide) (![⟨1229083, by decide⟩,⟨896706, by decide⟩,⟨1229098, by decide⟩,⟨1229118, by decide⟩]) unmarked_context_11_88659_1229119 node_context_11_88659_1229119
  intro a
  fin_cases a
  · exact context_12_354636_1229083
  · exact context_12_354637_896706
  · exact context_12_354638_1229098
  · exact context_12_354639_1229118

theorem unmarked_context_10_22164_1229120 : frontier 11 ⟨1229120, by decide⟩
    (prefixCache 10 22164) (prefixPartial 10 22164) = false := by
  decide +kernel

theorem node_context_10_22164_1229120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1229120, by decide⟩ =
    .split (coordinate 10) (![⟨1228972, by decide⟩,⟨1229026, by decide⟩,⟨1229069, by decide⟩,⟨1229119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22164_1229120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22164 ⟨1229120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22164
    ⟨1229120, by decide⟩ (by decide) (![⟨1228972, by decide⟩,⟨1229026, by decide⟩,⟨1229069, by decide⟩,⟨1229119, by decide⟩]) unmarked_context_10_22164_1229120 node_context_10_22164_1229120
  intro a
  fin_cases a
  · exact context_11_88656_1228972
  · exact context_11_88657_1229026
  · exact context_11_88658_1229069
  · exact context_11_88659_1229119

theorem selected_cut_44641 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22165) = some ⟨10, 1, 0, 893098, 22165, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22165_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22165 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22165 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22165, 1, 1048576⟩
    (by decide) selected_cut_44641

theorem selected_cut_44642 : selected 10 ⟨1229181, by decide⟩
    (prefixPartial 11 88664) = some ⟨11, 2, 0, 1229181, 88664, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_88664_1229181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88664 ⟨1229181, by decide⟩ :=
  accepted_of_selected 11 88664 ⟨1229181, by decide⟩ ⟨11, 2, 0, 1229181, 88664, 2985, 262144⟩
    (by decide) selected_cut_44642

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
