/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover432
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41571 : selected 9 ⟨1136583, by decide⟩
    (prefixPartial 12 336186) = some ⟨12, 2, 0, 1136583, 336186, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_336186_1136583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336186 ⟨1136583, by decide⟩ :=
  accepted_of_selected 12 336186 ⟨1136583, by decide⟩ ⟨12, 2, 0, 1136583, 336186, 1769, 65536⟩
    (by decide) selected_cut_41571

theorem selected_cut_41572 : selected 9 ⟨1136607, by decide⟩
    (prefixPartial 12 336187) = some ⟨12, 2, 0, 1136607, 336187, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_336187_1136607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336187 ⟨1136607, by decide⟩ :=
  accepted_of_selected 12 336187 ⟨1136607, by decide⟩ ⟨12, 2, 0, 1136607, 336187, 1909, 65536⟩
    (by decide) selected_cut_41572

theorem unmarked_context_11_84046_1136608 : frontier 10 ⟨1136608, by decide⟩
    (prefixCache 11 84046) (prefixPartial 11 84046) = false := by
  decide +kernel

theorem node_context_11_84046_1136608 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136608, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1136561, by decide⟩,⟨1136583, by decide⟩,⟨1136607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84046_1136608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84046 ⟨1136608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84046
    ⟨1136608, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1136561, by decide⟩,⟨1136583, by decide⟩,⟨1136607, by decide⟩]) unmarked_context_11_84046_1136608 node_context_11_84046_1136608
  intro a
  fin_cases a
  · exact context_12_336184_1108174
  · exact context_12_336185_1136561
  · exact context_12_336186_1136583
  · exact context_12_336187_1136607

theorem selected_cut_41573 : selected 10 ⟨1136670, by decide⟩
    (prefixPartial 11 84047) = some ⟨11, 2, 0, 1136670, 84047, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_84047_1136670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84047 ⟨1136670, by decide⟩ :=
  accepted_of_selected 11 84047 ⟨1136670, by decide⟩ ⟨11, 2, 0, 1136670, 84047, 3517, 262144⟩
    (by decide) selected_cut_41573

theorem unmarked_context_10_21011_1136671 : frontier 11 ⟨1136671, by decide⟩
    (prefixCache 10 21011) (prefixPartial 10 21011) = false := by
  decide +kernel

theorem node_context_10_21011_1136671 : EJMOriginalGlobalDAGData.nodes 11 ⟨1136671, by decide⟩ =
    .split (coordinate 10) (![⟨1136456, by decide⟩,⟨1136508, by decide⟩,⟨1136608, by decide⟩,⟨1136670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21011_1136671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21011 ⟨1136671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21011
    ⟨1136671, by decide⟩ (by decide) (![⟨1136456, by decide⟩,⟨1136508, by decide⟩,⟨1136608, by decide⟩,⟨1136670, by decide⟩]) unmarked_context_10_21011_1136671 node_context_10_21011_1136671
  intro a
  fin_cases a
  · exact context_11_84044_1136456
  · exact context_11_84045_1136508
  · exact context_11_84046_1136608
  · exact context_11_84047_1136670

theorem unmarked_context_9_5252_1136672 : frontier 12 ⟨1136672, by decide⟩
    (prefixCache 9 5252) (prefixPartial 9 5252) = false := by
  decide +kernel

theorem node_context_9_5252_1136672 : EJMOriginalGlobalDAGData.nodes 12 ⟨1136672, by decide⟩ =
    .split (coordinate 9) (![⟨1135623, by decide⟩,⟨1136010, by decide⟩,⟨1136361, by decide⟩,⟨1136671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5252_1136672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5252 ⟨1136672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5252
    ⟨1136672, by decide⟩ (by decide) (![⟨1135623, by decide⟩,⟨1136010, by decide⟩,⟨1136361, by decide⟩,⟨1136671, by decide⟩]) unmarked_context_9_5252_1136672 node_context_9_5252_1136672
  intro a
  fin_cases a
  · exact context_10_21008_1135623
  · exact context_10_21009_1136010
  · exact context_10_21010_1136361
  · exact context_10_21011_1136671

theorem selected_cut_41574 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84048) = some ⟨11, 1, 0, 907917, 84048, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84048_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84048 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84048 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84048, 1, 262144⟩
    (by decide) selected_cut_41574

theorem selected_cut_41575 : selected 9 ⟨1136699, by decide⟩
    (prefixPartial 12 336196) = some ⟨12, 2, 0, 1136699, 336196, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_336196_1136699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336196 ⟨1136699, by decide⟩ :=
  accepted_of_selected 12 336196 ⟨1136699, by decide⟩ ⟨12, 2, 0, 1136699, 336196, 1425, 65536⟩
    (by decide) selected_cut_41575

theorem selected_cut_41576 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 336197) = some ⟨12, 1, 0, 170504, 336197, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336197_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336197 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 336197 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 336197, 1, 65536⟩
    (by decide) selected_cut_41576

theorem selected_cut_41577 : selected 9 ⟨1136720, by decide⟩
    (prefixPartial 12 336198) = some ⟨12, 2, 0, 1136720, 336198, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_336198_1136720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336198 ⟨1136720, by decide⟩ :=
  accepted_of_selected 12 336198 ⟨1136720, by decide⟩ ⟨12, 2, 0, 1136720, 336198, 1457, 65536⟩
    (by decide) selected_cut_41577

theorem selected_cut_41578 : selected 9 ⟨1136739, by decide⟩
    (prefixPartial 12 336199) = some ⟨12, 2, 0, 1136739, 336199, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_336199_1136739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336199 ⟨1136739, by decide⟩ :=
  accepted_of_selected 12 336199 ⟨1136739, by decide⟩ ⟨12, 2, 0, 1136739, 336199, 1497, 65536⟩
    (by decide) selected_cut_41578

theorem unmarked_context_11_84049_1136740 : frontier 10 ⟨1136740, by decide⟩
    (prefixCache 11 84049) (prefixPartial 11 84049) = false := by
  decide +kernel

theorem node_context_11_84049_1136740 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136740, by decide⟩ =
    .split (coordinate 11) (![⟨1136699, by decide⟩,⟨170504, by decide⟩,⟨1136720, by decide⟩,⟨1136739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84049_1136740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84049 ⟨1136740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84049
    ⟨1136740, by decide⟩ (by decide) (![⟨1136699, by decide⟩,⟨170504, by decide⟩,⟨1136720, by decide⟩,⟨1136739, by decide⟩]) unmarked_context_11_84049_1136740 node_context_11_84049_1136740
  intro a
  fin_cases a
  · exact context_12_336196_1136699
  · exact context_12_336197_170504
  · exact context_12_336198_1136720
  · exact context_12_336199_1136739

theorem selected_cut_41579 : selected 9 ⟨1136766, by decide⟩
    (prefixPartial 12 336200) = some ⟨12, 2, 0, 1136766, 336200, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_336200_1136766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336200 ⟨1136766, by decide⟩ :=
  accepted_of_selected 12 336200 ⟨1136766, by decide⟩ ⟨12, 2, 0, 1136766, 336200, 1445, 65536⟩
    (by decide) selected_cut_41579

theorem selected_cut_41580 : selected 9 ⟨1136797, by decide⟩
    (prefixPartial 12 336201) = some ⟨12, 2, 0, 1136797, 336201, 781, 65536⟩ := by
  decide +kernel

theorem context_12_336201_1136797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336201 ⟨1136797, by decide⟩ :=
  accepted_of_selected 12 336201 ⟨1136797, by decide⟩ ⟨12, 2, 0, 1136797, 336201, 781, 65536⟩
    (by decide) selected_cut_41580

theorem selected_cut_41581 : selected 9 ⟨1136829, by decide⟩
    (prefixPartial 12 336202) = some ⟨12, 2, 0, 1136829, 336202, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_336202_1136829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336202 ⟨1136829, by decide⟩ :=
  accepted_of_selected 12 336202 ⟨1136829, by decide⟩ ⟨12, 2, 0, 1136829, 336202, 1561, 65536⟩
    (by decide) selected_cut_41581

theorem selected_cut_41582 : selected 9 ⟨1136852, by decide⟩
    (prefixPartial 12 336203) = some ⟨12, 2, 0, 1136852, 336203, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_336203_1136852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336203 ⟨1136852, by decide⟩ :=
  accepted_of_selected 12 336203 ⟨1136852, by decide⟩ ⟨12, 2, 0, 1136852, 336203, 1641, 65536⟩
    (by decide) selected_cut_41582

theorem unmarked_context_11_84050_1136853 : frontier 10 ⟨1136853, by decide⟩
    (prefixCache 11 84050) (prefixPartial 11 84050) = false := by
  decide +kernel

theorem node_context_11_84050_1136853 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136853, by decide⟩ =
    .split (coordinate 11) (![⟨1136766, by decide⟩,⟨1136797, by decide⟩,⟨1136829, by decide⟩,⟨1136852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84050_1136853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84050 ⟨1136853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84050
    ⟨1136853, by decide⟩ (by decide) (![⟨1136766, by decide⟩,⟨1136797, by decide⟩,⟨1136829, by decide⟩,⟨1136852, by decide⟩]) unmarked_context_11_84050_1136853 node_context_11_84050_1136853
  intro a
  fin_cases a
  · exact context_12_336200_1136766
  · exact context_12_336201_1136797
  · exact context_12_336202_1136829
  · exact context_12_336203_1136852

theorem selected_cut_41583 : selected 9 ⟨1136877, by decide⟩
    (prefixPartial 12 336204) = some ⟨12, 2, 0, 1136877, 336204, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_336204_1136877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336204 ⟨1136877, by decide⟩ :=
  accepted_of_selected 12 336204 ⟨1136877, by decide⟩ ⟨12, 2, 0, 1136877, 336204, 1345, 65536⟩
    (by decide) selected_cut_41583

theorem selected_cut_41584 : selected 9 ⟨1136886, by decide⟩
    (prefixPartial 12 336205) = some ⟨12, 2, 0, 1136886, 336205, 585, 65536⟩ := by
  decide +kernel

theorem context_12_336205_1136886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336205 ⟨1136886, by decide⟩ :=
  accepted_of_selected 12 336205 ⟨1136886, by decide⟩ ⟨12, 2, 0, 1136886, 336205, 585, 65536⟩
    (by decide) selected_cut_41584

theorem selected_cut_41585 : selected 9 ⟨1136903, by decide⟩
    (prefixPartial 12 336206) = some ⟨12, 2, 0, 1136903, 336206, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_336206_1136903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336206 ⟨1136903, by decide⟩ :=
  accepted_of_selected 12 336206 ⟨1136903, by decide⟩ ⟨12, 2, 0, 1136903, 336206, 1433, 65536⟩
    (by decide) selected_cut_41585

theorem selected_cut_41586 : selected 9 ⟨1136918, by decide⟩
    (prefixPartial 12 336207) = some ⟨12, 2, 0, 1136918, 336207, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_336207_1136918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336207 ⟨1136918, by decide⟩ :=
  accepted_of_selected 12 336207 ⟨1136918, by decide⟩ ⟨12, 2, 0, 1136918, 336207, 1505, 65536⟩
    (by decide) selected_cut_41586

theorem unmarked_context_11_84051_1136919 : frontier 10 ⟨1136919, by decide⟩
    (prefixCache 11 84051) (prefixPartial 11 84051) = false := by
  decide +kernel

theorem node_context_11_84051_1136919 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136919, by decide⟩ =
    .split (coordinate 11) (![⟨1136877, by decide⟩,⟨1136886, by decide⟩,⟨1136903, by decide⟩,⟨1136918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84051_1136919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84051 ⟨1136919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84051
    ⟨1136919, by decide⟩ (by decide) (![⟨1136877, by decide⟩,⟨1136886, by decide⟩,⟨1136903, by decide⟩,⟨1136918, by decide⟩]) unmarked_context_11_84051_1136919 node_context_11_84051_1136919
  intro a
  fin_cases a
  · exact context_12_336204_1136877
  · exact context_12_336205_1136886
  · exact context_12_336206_1136903
  · exact context_12_336207_1136918

theorem unmarked_context_10_21012_1136920 : frontier 11 ⟨1136920, by decide⟩
    (prefixCache 10 21012) (prefixPartial 10 21012) = false := by
  decide +kernel

theorem node_context_10_21012_1136920 : EJMOriginalGlobalDAGData.nodes 11 ⟨1136920, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1136740, by decide⟩,⟨1136853, by decide⟩,⟨1136919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21012_1136920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21012 ⟨1136920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21012
    ⟨1136920, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1136740, by decide⟩,⟨1136853, by decide⟩,⟨1136919, by decide⟩]) unmarked_context_10_21012_1136920 node_context_10_21012_1136920
  intro a
  fin_cases a
  · exact context_11_84048_907917
  · exact context_11_84049_1136740
  · exact context_11_84050_1136853
  · exact context_11_84051_1136919

theorem selected_cut_41587 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21013) = some ⟨10, 1, 0, 893098, 21013, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21013_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21013 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21013 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21013, 1, 1048576⟩
    (by decide) selected_cut_41587

theorem selected_cut_41588 : selected 10 ⟨1136984, by decide⟩
    (prefixPartial 11 84056) = some ⟨11, 2, 0, 1136984, 84056, 3541, 262144⟩ := by
  decide +kernel

theorem context_11_84056_1136984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84056 ⟨1136984, by decide⟩ :=
  accepted_of_selected 11 84056 ⟨1136984, by decide⟩ ⟨11, 2, 0, 1136984, 84056, 3541, 262144⟩
    (by decide) selected_cut_41588

theorem selected_cut_41589 : selected 10 ⟨1137039, by decide⟩
    (prefixPartial 11 84057) = some ⟨11, 2, 0, 1137039, 84057, 4009, 262144⟩ := by
  decide +kernel

theorem context_11_84057_1137039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84057 ⟨1137039, by decide⟩ :=
  accepted_of_selected 11 84057 ⟨1137039, by decide⟩ ⟨11, 2, 0, 1137039, 84057, 4009, 262144⟩
    (by decide) selected_cut_41589

theorem selected_cut_41590 : selected 9 ⟨1137061, by decide⟩
    (prefixPartial 12 336232) = some ⟨12, 2, 0, 1137061, 336232, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_336232_1137061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336232 ⟨1137061, by decide⟩ :=
  accepted_of_selected 12 336232 ⟨1137061, by decide⟩ ⟨12, 2, 0, 1137061, 336232, 1381, 65536⟩
    (by decide) selected_cut_41590

theorem selected_cut_41591 : selected 9 ⟨1137099, by decide⟩
    (prefixPartial 12 336233) = some ⟨12, 2, 0, 1137099, 336233, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_336233_1137099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336233 ⟨1137099, by decide⟩ :=
  accepted_of_selected 12 336233 ⟨1137099, by decide⟩ ⟨12, 2, 0, 1137099, 336233, 1577, 65536⟩
    (by decide) selected_cut_41591

theorem selected_cut_41592 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 336234) = some ⟨12, 1, 0, 474208, 336234, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336234_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336234 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 336234 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 336234, 1, 65536⟩
    (by decide) selected_cut_41592

theorem selected_cut_41593 : selected 9 ⟨1137120, by decide⟩
    (prefixPartial 12 336235) = some ⟨12, 2, 0, 1137120, 336235, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_336235_1137120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336235 ⟨1137120, by decide⟩ :=
  accepted_of_selected 12 336235 ⟨1137120, by decide⟩ ⟨12, 2, 0, 1137120, 336235, 1469, 65536⟩
    (by decide) selected_cut_41593

theorem unmarked_context_11_84058_1137121 : frontier 10 ⟨1137121, by decide⟩
    (prefixCache 11 84058) (prefixPartial 11 84058) = false := by
  decide +kernel

theorem node_context_11_84058_1137121 : EJMOriginalGlobalDAGData.nodes 10 ⟨1137121, by decide⟩ =
    .split (coordinate 11) (![⟨1137061, by decide⟩,⟨1137099, by decide⟩,⟨474208, by decide⟩,⟨1137120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84058_1137121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84058 ⟨1137121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84058
    ⟨1137121, by decide⟩ (by decide) (![⟨1137061, by decide⟩,⟨1137099, by decide⟩,⟨474208, by decide⟩,⟨1137120, by decide⟩]) unmarked_context_11_84058_1137121 node_context_11_84058_1137121
  intro a
  fin_cases a
  · exact context_12_336232_1137061
  · exact context_12_336233_1137099
  · exact context_12_336234_474208
  · exact context_12_336235_1137120

theorem selected_cut_41594 : selected 9 ⟨1137134, by decide⟩
    (prefixPartial 12 336236) = some ⟨12, 2, 0, 1137134, 336236, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_336236_1137134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336236 ⟨1137134, by decide⟩ :=
  accepted_of_selected 12 336236 ⟨1137134, by decide⟩ ⟨12, 2, 0, 1137134, 336236, 1317, 65536⟩
    (by decide) selected_cut_41594

theorem selected_cut_41595 : selected 9 ⟨1137155, by decide⟩
    (prefixPartial 12 336237) = some ⟨12, 2, 0, 1137155, 336237, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_336237_1137155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336237 ⟨1137155, by decide⟩ :=
  accepted_of_selected 12 336237 ⟨1137155, by decide⟩ ⟨12, 2, 0, 1137155, 336237, 1385, 65536⟩
    (by decide) selected_cut_41595

theorem selected_cut_41596 : selected 9 ⟨1137165, by decide⟩
    (prefixPartial 12 336238) = some ⟨12, 2, 0, 1137165, 336238, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_336238_1137165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336238 ⟨1137165, by decide⟩ :=
  accepted_of_selected 12 336238 ⟨1137165, by decide⟩ ⟨12, 2, 0, 1137165, 336238, 1297, 65536⟩
    (by decide) selected_cut_41596

theorem selected_cut_41597 : selected 9 ⟨1137183, by decide⟩
    (prefixPartial 12 336239) = some ⟨12, 2, 0, 1137183, 336239, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_336239_1137183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336239 ⟨1137183, by decide⟩ :=
  accepted_of_selected 12 336239 ⟨1137183, by decide⟩ ⟨12, 2, 0, 1137183, 336239, 1373, 65536⟩
    (by decide) selected_cut_41597

theorem unmarked_context_11_84059_1137184 : frontier 10 ⟨1137184, by decide⟩
    (prefixCache 11 84059) (prefixPartial 11 84059) = false := by
  decide +kernel

theorem node_context_11_84059_1137184 : EJMOriginalGlobalDAGData.nodes 10 ⟨1137184, by decide⟩ =
    .split (coordinate 11) (![⟨1137134, by decide⟩,⟨1137155, by decide⟩,⟨1137165, by decide⟩,⟨1137183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84059_1137184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84059 ⟨1137184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84059
    ⟨1137184, by decide⟩ (by decide) (![⟨1137134, by decide⟩,⟨1137155, by decide⟩,⟨1137165, by decide⟩,⟨1137183, by decide⟩]) unmarked_context_11_84059_1137184 node_context_11_84059_1137184
  intro a
  fin_cases a
  · exact context_12_336236_1137134
  · exact context_12_336237_1137155
  · exact context_12_336238_1137165
  · exact context_12_336239_1137183

theorem unmarked_context_10_21014_1137185 : frontier 11 ⟨1137185, by decide⟩
    (prefixCache 10 21014) (prefixPartial 10 21014) = false := by
  decide +kernel

theorem node_context_10_21014_1137185 : EJMOriginalGlobalDAGData.nodes 11 ⟨1137185, by decide⟩ =
    .split (coordinate 10) (![⟨1136984, by decide⟩,⟨1137039, by decide⟩,⟨1137121, by decide⟩,⟨1137184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21014_1137185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21014 ⟨1137185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21014
    ⟨1137185, by decide⟩ (by decide) (![⟨1136984, by decide⟩,⟨1137039, by decide⟩,⟨1137121, by decide⟩,⟨1137184, by decide⟩]) unmarked_context_10_21014_1137185 node_context_10_21014_1137185
  intro a
  fin_cases a
  · exact context_11_84056_1136984
  · exact context_11_84057_1137039
  · exact context_11_84058_1137121
  · exact context_11_84059_1137184

theorem selected_cut_41598 : selected 10 ⟨1137255, by decide⟩
    (prefixPartial 11 84060) = some ⟨11, 2, 0, 1137255, 84060, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_84060_1137255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84060 ⟨1137255, by decide⟩ :=
  accepted_of_selected 11 84060 ⟨1137255, by decide⟩ ⟨11, 2, 0, 1137255, 84060, 3097, 262144⟩
    (by decide) selected_cut_41598

theorem selected_cut_41599 : selected 10 ⟨1137313, by decide⟩
    (prefixPartial 11 84061) = some ⟨11, 2, 0, 1137313, 84061, 3541, 262144⟩ := by
  decide +kernel

theorem context_11_84061_1137313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84061 ⟨1137313, by decide⟩ :=
  accepted_of_selected 11 84061 ⟨1137313, by decide⟩ ⟨11, 2, 0, 1137313, 84061, 3541, 262144⟩
    (by decide) selected_cut_41599

theorem selected_cut_41600 : selected 9 ⟨1137324, by decide⟩
    (prefixPartial 12 336248) = some ⟨12, 2, 0, 1137324, 336248, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_336248_1137324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336248 ⟨1137324, by decide⟩ :=
  accepted_of_selected 12 336248 ⟨1137324, by decide⟩ ⟨12, 2, 0, 1137324, 336248, 1193, 65536⟩
    (by decide) selected_cut_41600

theorem selected_cut_41601 : selected 9 ⟨1137359, by decide⟩
    (prefixPartial 12 336249) = some ⟨12, 2, 0, 1137359, 336249, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_336249_1137359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336249 ⟨1137359, by decide⟩ :=
  accepted_of_selected 12 336249 ⟨1137359, by decide⟩ ⟨12, 2, 0, 1137359, 336249, 1373, 65536⟩
    (by decide) selected_cut_41601

theorem selected_cut_41602 : selected 9 ⟨1137370, by decide⟩
    (prefixPartial 12 336250) = some ⟨12, 2, 0, 1137370, 336250, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_336250_1137370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336250 ⟨1137370, by decide⟩ :=
  accepted_of_selected 12 336250 ⟨1137370, by decide⟩ ⟨12, 2, 0, 1137370, 336250, 1209, 65536⟩
    (by decide) selected_cut_41602

theorem selected_cut_41603 : selected 9 ⟨1137384, by decide⟩
    (prefixPartial 12 336251) = some ⟨12, 2, 0, 1137384, 336251, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_336251_1137384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336251 ⟨1137384, by decide⟩ :=
  accepted_of_selected 12 336251 ⟨1137384, by decide⟩ ⟨12, 2, 0, 1137384, 336251, 1229, 65536⟩
    (by decide) selected_cut_41603

theorem unmarked_context_11_84062_1137385 : frontier 10 ⟨1137385, by decide⟩
    (prefixCache 11 84062) (prefixPartial 11 84062) = false := by
  decide +kernel

theorem node_context_11_84062_1137385 : EJMOriginalGlobalDAGData.nodes 10 ⟨1137385, by decide⟩ =
    .split (coordinate 11) (![⟨1137324, by decide⟩,⟨1137359, by decide⟩,⟨1137370, by decide⟩,⟨1137384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84062_1137385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84062 ⟨1137385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84062
    ⟨1137385, by decide⟩ (by decide) (![⟨1137324, by decide⟩,⟨1137359, by decide⟩,⟨1137370, by decide⟩,⟨1137384, by decide⟩]) unmarked_context_11_84062_1137385 node_context_11_84062_1137385
  intro a
  fin_cases a
  · exact context_12_336248_1137324
  · exact context_12_336249_1137359
  · exact context_12_336250_1137370
  · exact context_12_336251_1137384

theorem selected_cut_41604 : selected 10 ⟨1137428, by decide⟩
    (prefixPartial 11 84063) = some ⟨11, 2, 0, 1137428, 84063, 3493, 262144⟩ := by
  decide +kernel

theorem context_11_84063_1137428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84063 ⟨1137428, by decide⟩ :=
  accepted_of_selected 11 84063 ⟨1137428, by decide⟩ ⟨11, 2, 0, 1137428, 84063, 3493, 262144⟩
    (by decide) selected_cut_41604

theorem unmarked_context_10_21015_1137429 : frontier 11 ⟨1137429, by decide⟩
    (prefixCache 10 21015) (prefixPartial 10 21015) = false := by
  decide +kernel

theorem node_context_10_21015_1137429 : EJMOriginalGlobalDAGData.nodes 11 ⟨1137429, by decide⟩ =
    .split (coordinate 10) (![⟨1137255, by decide⟩,⟨1137313, by decide⟩,⟨1137385, by decide⟩,⟨1137428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21015_1137429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21015 ⟨1137429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21015
    ⟨1137429, by decide⟩ (by decide) (![⟨1137255, by decide⟩,⟨1137313, by decide⟩,⟨1137385, by decide⟩,⟨1137428, by decide⟩]) unmarked_context_10_21015_1137429 node_context_10_21015_1137429
  intro a
  fin_cases a
  · exact context_11_84060_1137255
  · exact context_11_84061_1137313
  · exact context_11_84062_1137385
  · exact context_11_84063_1137428

theorem unmarked_context_9_5253_1137430 : frontier 12 ⟨1137430, by decide⟩
    (prefixCache 9 5253) (prefixPartial 9 5253) = false := by
  decide +kernel

theorem node_context_9_5253_1137430 : EJMOriginalGlobalDAGData.nodes 12 ⟨1137430, by decide⟩ =
    .split (coordinate 9) (![⟨1136920, by decide⟩,⟨893098, by decide⟩,⟨1137185, by decide⟩,⟨1137429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5253_1137430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5253 ⟨1137430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5253
    ⟨1137430, by decide⟩ (by decide) (![⟨1136920, by decide⟩,⟨893098, by decide⟩,⟨1137185, by decide⟩,⟨1137429, by decide⟩]) unmarked_context_9_5253_1137430 node_context_9_5253_1137430
  intro a
  fin_cases a
  · exact context_10_21012_1136920
  · exact context_10_21013_893098
  · exact context_10_21014_1137185
  · exact context_10_21015_1137429

theorem selected_cut_41605 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84064) = some ⟨11, 1, 0, 907917, 84064, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84064_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84064 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84064 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84064, 1, 262144⟩
    (by decide) selected_cut_41605

theorem selected_cut_41606 : selected 10 ⟨1137476, by decide⟩
    (prefixPartial 11 84065) = some ⟨11, 2, 0, 1137476, 84065, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_84065_1137476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84065 ⟨1137476, by decide⟩ :=
  accepted_of_selected 11 84065 ⟨1137476, by decide⟩ ⟨11, 2, 0, 1137476, 84065, 2953, 262144⟩
    (by decide) selected_cut_41606

theorem selected_cut_41607 : selected 10 ⟨1137535, by decide⟩
    (prefixPartial 11 84066) = some ⟨11, 2, 0, 1137535, 84066, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_84066_1137535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84066 ⟨1137535, by decide⟩ :=
  accepted_of_selected 11 84066 ⟨1137535, by decide⟩ ⟨11, 2, 0, 1137535, 84066, 3545, 262144⟩
    (by decide) selected_cut_41607

theorem selected_cut_41608 : selected 10 ⟨1137598, by decide⟩
    (prefixPartial 11 84067) = some ⟨11, 2, 0, 1137598, 84067, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_84067_1137598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84067 ⟨1137598, by decide⟩ :=
  accepted_of_selected 11 84067 ⟨1137598, by decide⟩ ⟨11, 2, 0, 1137598, 84067, 3957, 262144⟩
    (by decide) selected_cut_41608

theorem unmarked_context_10_21016_1137599 : frontier 11 ⟨1137599, by decide⟩
    (prefixCache 10 21016) (prefixPartial 10 21016) = false := by
  decide +kernel

theorem node_context_10_21016_1137599 : EJMOriginalGlobalDAGData.nodes 11 ⟨1137599, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1137476, by decide⟩,⟨1137535, by decide⟩,⟨1137598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21016_1137599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21016 ⟨1137599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21016
    ⟨1137599, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1137476, by decide⟩,⟨1137535, by decide⟩,⟨1137598, by decide⟩]) unmarked_context_10_21016_1137599 node_context_10_21016_1137599
  intro a
  fin_cases a
  · exact context_11_84064_907917
  · exact context_11_84065_1137476
  · exact context_11_84066_1137535
  · exact context_11_84067_1137598

theorem selected_cut_41609 : selected 10 ⟨1137640, by decide⟩
    (prefixPartial 11 84068) = some ⟨11, 2, 0, 1137640, 84068, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_84068_1137640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84068 ⟨1137640, by decide⟩ :=
  accepted_of_selected 11 84068 ⟨1137640, by decide⟩ ⟨11, 2, 0, 1137640, 84068, 2885, 262144⟩
    (by decide) selected_cut_41609

theorem selected_cut_41610 : selected 10 ⟨1137678, by decide⟩
    (prefixPartial 11 84069) = some ⟨11, 2, 0, 1137678, 84069, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_84069_1137678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84069 ⟨1137678, by decide⟩ :=
  accepted_of_selected 11 84069 ⟨1137678, by decide⟩ ⟨11, 2, 0, 1137678, 84069, 1953, 262144⟩
    (by decide) selected_cut_41610

theorem selected_cut_41611 : selected 10 ⟨1137712, by decide⟩
    (prefixPartial 11 84070) = some ⟨11, 2, 0, 1137712, 84070, 2457, 262144⟩ := by
  decide +kernel

theorem context_11_84070_1137712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84070 ⟨1137712, by decide⟩ :=
  accepted_of_selected 11 84070 ⟨1137712, by decide⟩ ⟨11, 2, 0, 1137712, 84070, 2457, 262144⟩
    (by decide) selected_cut_41611

theorem selected_cut_41612 : selected 10 ⟨1137745, by decide⟩
    (prefixPartial 11 84071) = some ⟨11, 2, 0, 1137745, 84071, 3041, 262144⟩ := by
  decide +kernel

theorem context_11_84071_1137745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84071 ⟨1137745, by decide⟩ :=
  accepted_of_selected 11 84071 ⟨1137745, by decide⟩ ⟨11, 2, 0, 1137745, 84071, 3041, 262144⟩
    (by decide) selected_cut_41612

theorem unmarked_context_10_21017_1137746 : frontier 11 ⟨1137746, by decide⟩
    (prefixCache 10 21017) (prefixPartial 10 21017) = false := by
  decide +kernel

theorem node_context_10_21017_1137746 : EJMOriginalGlobalDAGData.nodes 11 ⟨1137746, by decide⟩ =
    .split (coordinate 10) (![⟨1137640, by decide⟩,⟨1137678, by decide⟩,⟨1137712, by decide⟩,⟨1137745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21017_1137746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21017 ⟨1137746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21017
    ⟨1137746, by decide⟩ (by decide) (![⟨1137640, by decide⟩,⟨1137678, by decide⟩,⟨1137712, by decide⟩,⟨1137745, by decide⟩]) unmarked_context_10_21017_1137746 node_context_10_21017_1137746
  intro a
  fin_cases a
  · exact context_11_84068_1137640
  · exact context_11_84069_1137678
  · exact context_11_84070_1137712
  · exact context_11_84071_1137745

theorem selected_cut_41613 : selected 10 ⟨1137780, by decide⟩
    (prefixPartial 11 84072) = some ⟨11, 2, 0, 1137780, 84072, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_84072_1137780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84072 ⟨1137780, by decide⟩ :=
  accepted_of_selected 11 84072 ⟨1137780, by decide⟩ ⟨11, 2, 0, 1137780, 84072, 2169, 262144⟩
    (by decide) selected_cut_41613

theorem selected_cut_41614 : selected 10 ⟨1137803, by decide⟩
    (prefixPartial 11 84073) = some ⟨11, 2, 0, 1137803, 84073, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_84073_1137803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84073 ⟨1137803, by decide⟩ :=
  accepted_of_selected 11 84073 ⟨1137803, by decide⟩ ⟨11, 2, 0, 1137803, 84073, 1413, 262144⟩
    (by decide) selected_cut_41614

theorem selected_cut_41615 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84074) = some ⟨11, 1, 0, 1109453, 84074, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84074_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84074 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84074 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84074, 1, 262144⟩
    (by decide) selected_cut_41615

theorem selected_cut_41616 : selected 10 ⟨1137830, by decide⟩
    (prefixPartial 11 84075) = some ⟨11, 2, 0, 1137830, 84075, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_84075_1137830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84075 ⟨1137830, by decide⟩ :=
  accepted_of_selected 11 84075 ⟨1137830, by decide⟩ ⟨11, 2, 0, 1137830, 84075, 2093, 262144⟩
    (by decide) selected_cut_41616

theorem unmarked_context_10_21018_1137831 : frontier 11 ⟨1137831, by decide⟩
    (prefixCache 10 21018) (prefixPartial 10 21018) = false := by
  decide +kernel

theorem node_context_10_21018_1137831 : EJMOriginalGlobalDAGData.nodes 11 ⟨1137831, by decide⟩ =
    .split (coordinate 10) (![⟨1137780, by decide⟩,⟨1137803, by decide⟩,⟨1109453, by decide⟩,⟨1137830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21018_1137831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21018 ⟨1137831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21018
    ⟨1137831, by decide⟩ (by decide) (![⟨1137780, by decide⟩,⟨1137803, by decide⟩,⟨1109453, by decide⟩,⟨1137830, by decide⟩]) unmarked_context_10_21018_1137831 node_context_10_21018_1137831
  intro a
  fin_cases a
  · exact context_11_84072_1137780
  · exact context_11_84073_1137803
  · exact context_11_84074_1109453
  · exact context_11_84075_1137830

theorem selected_cut_41617 : selected 10 ⟨1137869, by decide⟩
    (prefixPartial 11 84076) = some ⟨11, 2, 0, 1137869, 84076, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_84076_1137869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84076 ⟨1137869, by decide⟩ :=
  accepted_of_selected 11 84076 ⟨1137869, by decide⟩ ⟨11, 2, 0, 1137869, 84076, 2397, 262144⟩
    (by decide) selected_cut_41617

theorem selected_cut_41618 : selected 10 ⟨1137893, by decide⟩
    (prefixPartial 11 84077) = some ⟨11, 2, 0, 1137893, 84077, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_84077_1137893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84077 ⟨1137893, by decide⟩ :=
  accepted_of_selected 11 84077 ⟨1137893, by decide⟩ ⟨11, 2, 0, 1137893, 84077, 1653, 262144⟩
    (by decide) selected_cut_41618

theorem selected_cut_41619 : selected 10 ⟨1137917, by decide⟩
    (prefixPartial 11 84078) = some ⟨11, 2, 0, 1137917, 84078, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_84078_1137917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84078 ⟨1137917, by decide⟩ :=
  accepted_of_selected 11 84078 ⟨1137917, by decide⟩ ⟨11, 2, 0, 1137917, 84078, 1757, 262144⟩
    (by decide) selected_cut_41619

theorem selected_cut_41620 : selected 10 ⟨1137941, by decide⟩
    (prefixPartial 11 84079) = some ⟨11, 2, 0, 1137941, 84079, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_84079_1137941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84079 ⟨1137941, by decide⟩ :=
  accepted_of_selected 11 84079 ⟨1137941, by decide⟩ ⟨11, 2, 0, 1137941, 84079, 1537, 262144⟩
    (by decide) selected_cut_41620

theorem unmarked_context_10_21019_1137942 : frontier 11 ⟨1137942, by decide⟩
    (prefixCache 10 21019) (prefixPartial 10 21019) = false := by
  decide +kernel

theorem node_context_10_21019_1137942 : EJMOriginalGlobalDAGData.nodes 11 ⟨1137942, by decide⟩ =
    .split (coordinate 10) (![⟨1137869, by decide⟩,⟨1137893, by decide⟩,⟨1137917, by decide⟩,⟨1137941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21019_1137942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21019 ⟨1137942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21019
    ⟨1137942, by decide⟩ (by decide) (![⟨1137869, by decide⟩,⟨1137893, by decide⟩,⟨1137917, by decide⟩,⟨1137941, by decide⟩]) unmarked_context_10_21019_1137942 node_context_10_21019_1137942
  intro a
  fin_cases a
  · exact context_11_84076_1137869
  · exact context_11_84077_1137893
  · exact context_11_84078_1137917
  · exact context_11_84079_1137941

theorem unmarked_context_9_5254_1137943 : frontier 12 ⟨1137943, by decide⟩
    (prefixCache 9 5254) (prefixPartial 9 5254) = false := by
  decide +kernel

theorem node_context_9_5254_1137943 : EJMOriginalGlobalDAGData.nodes 12 ⟨1137943, by decide⟩ =
    .split (coordinate 9) (![⟨1137599, by decide⟩,⟨1137746, by decide⟩,⟨1137831, by decide⟩,⟨1137942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5254_1137943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5254 ⟨1137943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5254
    ⟨1137943, by decide⟩ (by decide) (![⟨1137599, by decide⟩,⟨1137746, by decide⟩,⟨1137831, by decide⟩,⟨1137942, by decide⟩]) unmarked_context_9_5254_1137943 node_context_9_5254_1137943
  intro a
  fin_cases a
  · exact context_10_21016_1137599
  · exact context_10_21017_1137746
  · exact context_10_21018_1137831
  · exact context_10_21019_1137942

theorem selected_cut_41621 : selected 11 ⟨1138006, by decide⟩
    (prefixPartial 10 21020) = some ⟨10, 2, 0, 1138006, 21020, 4065, 1048576⟩ := by
  decide +kernel

theorem context_10_21020_1138006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21020 ⟨1138006, by decide⟩ :=
  accepted_of_selected 10 21020 ⟨1138006, by decide⟩ ⟨10, 2, 0, 1138006, 21020, 4065, 1048576⟩
    (by decide) selected_cut_41621

theorem selected_cut_41622 : selected 11 ⟨1138069, by decide⟩
    (prefixPartial 10 21021) = some ⟨10, 2, 0, 1138069, 21021, 3453, 1048576⟩ := by
  decide +kernel

theorem context_10_21021_1138069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21021 ⟨1138069, by decide⟩ :=
  accepted_of_selected 10 21021 ⟨1138069, by decide⟩ ⟨10, 2, 0, 1138069, 21021, 3453, 1048576⟩
    (by decide) selected_cut_41622

theorem selected_cut_41623 : selected 11 ⟨1138112, by decide⟩
    (prefixPartial 10 21022) = some ⟨10, 2, 0, 1138112, 21022, 2129, 1048576⟩ := by
  decide +kernel

theorem context_10_21022_1138112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21022 ⟨1138112, by decide⟩ :=
  accepted_of_selected 10 21022 ⟨1138112, by decide⟩ ⟨10, 2, 0, 1138112, 21022, 2129, 1048576⟩
    (by decide) selected_cut_41623

theorem selected_cut_41624 : selected 11 ⟨1138129, by decide⟩
    (prefixPartial 10 21023) = some ⟨10, 2, 0, 1138129, 21023, 453, 1048576⟩ := by
  decide +kernel

theorem context_10_21023_1138129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21023 ⟨1138129, by decide⟩ :=
  accepted_of_selected 10 21023 ⟨1138129, by decide⟩ ⟨10, 2, 0, 1138129, 21023, 453, 1048576⟩
    (by decide) selected_cut_41624

theorem unmarked_context_9_5255_1138130 : frontier 12 ⟨1138130, by decide⟩
    (prefixCache 9 5255) (prefixPartial 9 5255) = false := by
  decide +kernel

theorem node_context_9_5255_1138130 : EJMOriginalGlobalDAGData.nodes 12 ⟨1138130, by decide⟩ =
    .split (coordinate 9) (![⟨1138006, by decide⟩,⟨1138069, by decide⟩,⟨1138112, by decide⟩,⟨1138129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5255_1138130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5255 ⟨1138130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5255
    ⟨1138130, by decide⟩ (by decide) (![⟨1138006, by decide⟩,⟨1138069, by decide⟩,⟨1138112, by decide⟩,⟨1138129, by decide⟩]) unmarked_context_9_5255_1138130 node_context_9_5255_1138130
  intro a
  fin_cases a
  · exact context_10_21020_1138006
  · exact context_10_21021_1138069
  · exact context_10_21022_1138112
  · exact context_10_21023_1138129

theorem unmarked_context_8_1313_1138131 : frontier 13 ⟨1138131, by decide⟩
    (prefixCache 8 1313) (prefixPartial 8 1313) = false := by
  decide +kernel

theorem node_context_8_1313_1138131 : EJMOriginalGlobalDAGData.nodes 13 ⟨1138131, by decide⟩ =
    .split (coordinate 8) (![⟨1136672, by decide⟩,⟨1137430, by decide⟩,⟨1137943, by decide⟩,⟨1138130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1313_1138131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1313 ⟨1138131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1313
    ⟨1138131, by decide⟩ (by decide) (![⟨1136672, by decide⟩,⟨1137430, by decide⟩,⟨1137943, by decide⟩,⟨1138130, by decide⟩]) unmarked_context_8_1313_1138131 node_context_8_1313_1138131
  intro a
  fin_cases a
  · exact context_9_5252_1136672
  · exact context_9_5253_1137430
  · exact context_9_5254_1137943
  · exact context_9_5255_1138130

theorem selected_cut_41625 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84096) = some ⟨11, 1, 0, 434745, 84096, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84096_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84096 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84096 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84096, 1, 262144⟩
    (by decide) selected_cut_41625

theorem selected_cut_41626 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336388) = some ⟨12, 1, 0, 448748, 336388, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336388_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336388 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336388 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336388, 1, 65536⟩
    (by decide) selected_cut_41626

theorem selected_cut_41627 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 336389) = some ⟨12, 1, 0, 34034, 336389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336389_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336389 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 336389 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 336389, 1, 65536⟩
    (by decide) selected_cut_41627

theorem selected_cut_41628 : selected 9 ⟨1138187, by decide⟩
    (prefixPartial 12 336390) = some ⟨12, 2, 0, 1138187, 336390, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_336390_1138187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336390 ⟨1138187, by decide⟩ :=
  accepted_of_selected 12 336390 ⟨1138187, by decide⟩ ⟨12, 2, 0, 1138187, 336390, 1461, 65536⟩
    (by decide) selected_cut_41628

theorem selected_cut_41629 : selected 9 ⟨1138236, by decide⟩
    (prefixPartial 12 336391) = some ⟨12, 2, 0, 1138236, 336391, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_336391_1138236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336391 ⟨1138236, by decide⟩ :=
  accepted_of_selected 12 336391 ⟨1138236, by decide⟩ ⟨12, 2, 0, 1138236, 336391, 2857, 65536⟩
    (by decide) selected_cut_41629

theorem unmarked_context_11_84097_1138237 : frontier 10 ⟨1138237, by decide⟩
    (prefixCache 11 84097) (prefixPartial 11 84097) = false := by
  decide +kernel

theorem node_context_11_84097_1138237 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138237, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1138187, by decide⟩,⟨1138236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84097_1138237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84097 ⟨1138237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84097
    ⟨1138237, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1138187, by decide⟩,⟨1138236, by decide⟩]) unmarked_context_11_84097_1138237 node_context_11_84097_1138237
  intro a
  fin_cases a
  · exact context_12_336388_448748
  · exact context_12_336389_34034
  · exact context_12_336390_1138187
  · exact context_12_336391_1138236

theorem selected_cut_41630 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336392) = some ⟨12, 1, 0, 448748, 336392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336392_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336392 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336392 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336392, 1, 65536⟩
    (by decide) selected_cut_41630

theorem selected_cut_41631 : selected 9 ⟨1138304, by decide⟩
    (prefixPartial 12 336393) = some ⟨12, 2, 0, 1138304, 336393, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_336393_1138304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336393 ⟨1138304, by decide⟩ :=
  accepted_of_selected 12 336393 ⟨1138304, by decide⟩ ⟨12, 2, 0, 1138304, 336393, 3017, 65536⟩
    (by decide) selected_cut_41631

theorem selected_cut_41632 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 336394) = some ⟨12, 1, 0, 893903, 336394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336394_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336394 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 336394 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 336394, 1, 65536⟩
    (by decide) selected_cut_41632

theorem selected_cut_41633 : selected 9 ⟨1138356, by decide⟩
    (prefixPartial 12 336395) = some ⟨12, 2, 0, 1138356, 336395, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_336395_1138356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336395 ⟨1138356, by decide⟩ :=
  accepted_of_selected 12 336395 ⟨1138356, by decide⟩ ⟨12, 2, 0, 1138356, 336395, 2885, 65536⟩
    (by decide) selected_cut_41633

theorem unmarked_context_11_84098_1138357 : frontier 10 ⟨1138357, by decide⟩
    (prefixCache 11 84098) (prefixPartial 11 84098) = false := by
  decide +kernel

theorem node_context_11_84098_1138357 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138357, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1138304, by decide⟩,⟨893903, by decide⟩,⟨1138356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84098_1138357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84098 ⟨1138357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84098
    ⟨1138357, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1138304, by decide⟩,⟨893903, by decide⟩,⟨1138356, by decide⟩]) unmarked_context_11_84098_1138357 node_context_11_84098_1138357
  intro a
  fin_cases a
  · exact context_12_336392_448748
  · exact context_12_336393_1138304
  · exact context_12_336394_893903
  · exact context_12_336395_1138356

theorem selected_cut_41634 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336396) = some ⟨12, 1, 0, 448748, 336396, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336396_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336396 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336396 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336396, 1, 65536⟩
    (by decide) selected_cut_41634

theorem selected_cut_41635 : selected 9 ⟨1138394, by decide⟩
    (prefixPartial 12 336397) = some ⟨12, 2, 0, 1138394, 336397, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_336397_1138394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336397 ⟨1138394, by decide⟩ :=
  accepted_of_selected 12 336397 ⟨1138394, by decide⟩ ⟨12, 2, 0, 1138394, 336397, 2697, 65536⟩
    (by decide) selected_cut_41635

theorem selected_cut_41636 : selected 9 ⟨1138431, by decide⟩
    (prefixPartial 12 336398) = some ⟨12, 2, 0, 1138431, 336398, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_336398_1138431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336398 ⟨1138431, by decide⟩ :=
  accepted_of_selected 12 336398 ⟨1138431, by decide⟩ ⟨12, 2, 0, 1138431, 336398, 2225, 65536⟩
    (by decide) selected_cut_41636

theorem selected_cut_41637 : selected 9 ⟨1138463, by decide⟩
    (prefixPartial 12 336399) = some ⟨12, 2, 0, 1138463, 336399, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_336399_1138463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336399 ⟨1138463, by decide⟩ :=
  accepted_of_selected 12 336399 ⟨1138463, by decide⟩ ⟨12, 2, 0, 1138463, 336399, 2309, 65536⟩
    (by decide) selected_cut_41637

theorem unmarked_context_11_84099_1138464 : frontier 10 ⟨1138464, by decide⟩
    (prefixCache 11 84099) (prefixPartial 11 84099) = false := by
  decide +kernel

theorem node_context_11_84099_1138464 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138464, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1138394, by decide⟩,⟨1138431, by decide⟩,⟨1138463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84099_1138464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84099 ⟨1138464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84099
    ⟨1138464, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1138394, by decide⟩,⟨1138431, by decide⟩,⟨1138463, by decide⟩]) unmarked_context_11_84099_1138464 node_context_11_84099_1138464
  intro a
  fin_cases a
  · exact context_12_336396_448748
  · exact context_12_336397_1138394
  · exact context_12_336398_1138431
  · exact context_12_336399_1138463

theorem unmarked_context_10_21024_1138465 : frontier 11 ⟨1138465, by decide⟩
    (prefixCache 10 21024) (prefixPartial 10 21024) = false := by
  decide +kernel

theorem node_context_10_21024_1138465 : EJMOriginalGlobalDAGData.nodes 11 ⟨1138465, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1138237, by decide⟩,⟨1138357, by decide⟩,⟨1138464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21024_1138465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21024 ⟨1138465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21024
    ⟨1138465, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1138237, by decide⟩,⟨1138357, by decide⟩,⟨1138464, by decide⟩]) unmarked_context_10_21024_1138465 node_context_10_21024_1138465
  intro a
  fin_cases a
  · exact context_11_84096_434745
  · exact context_11_84097_1138237
  · exact context_11_84098_1138357
  · exact context_11_84099_1138464

theorem selected_cut_41638 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336400) = some ⟨12, 1, 0, 1108174, 336400, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336400_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336400 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336400 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336400, 1, 65536⟩
    (by decide) selected_cut_41638

theorem selected_cut_41639 : selected 9 ⟨1138506, by decide⟩
    (prefixPartial 12 336401) = some ⟨12, 2, 0, 1138506, 336401, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_336401_1138506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336401 ⟨1138506, by decide⟩ :=
  accepted_of_selected 12 336401 ⟨1138506, by decide⟩ ⟨12, 2, 0, 1138506, 336401, 2685, 65536⟩
    (by decide) selected_cut_41639

theorem selected_cut_41640 : selected 9 ⟨1138537, by decide⟩
    (prefixPartial 12 336402) = some ⟨12, 2, 0, 1138537, 336402, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_336402_1138537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336402 ⟨1138537, by decide⟩ :=
  accepted_of_selected 12 336402 ⟨1138537, by decide⟩ ⟨12, 2, 0, 1138537, 336402, 2313, 65536⟩
    (by decide) selected_cut_41640

theorem selected_cut_41641 : selected 9 ⟨1138573, by decide⟩
    (prefixPartial 12 336403) = some ⟨12, 2, 0, 1138573, 336403, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_336403_1138573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336403 ⟨1138573, by decide⟩ :=
  accepted_of_selected 12 336403 ⟨1138573, by decide⟩ ⟨12, 2, 0, 1138573, 336403, 2805, 65536⟩
    (by decide) selected_cut_41641

theorem unmarked_context_11_84100_1138574 : frontier 10 ⟨1138574, by decide⟩
    (prefixCache 11 84100) (prefixPartial 11 84100) = false := by
  decide +kernel

theorem node_context_11_84100_1138574 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138574, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1138506, by decide⟩,⟨1138537, by decide⟩,⟨1138573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84100_1138574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84100 ⟨1138574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84100
    ⟨1138574, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1138506, by decide⟩,⟨1138537, by decide⟩,⟨1138573, by decide⟩]) unmarked_context_11_84100_1138574 node_context_11_84100_1138574
  intro a
  fin_cases a
  · exact context_12_336400_1108174
  · exact context_12_336401_1138506
  · exact context_12_336402_1138537
  · exact context_12_336403_1138573

theorem selected_cut_41642 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336404) = some ⟨12, 1, 0, 1108174, 336404, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336404_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336404 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336404 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336404, 1, 65536⟩
    (by decide) selected_cut_41642

theorem selected_cut_41643 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 336405) = some ⟨12, 1, 0, 308705, 336405, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336405_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336405 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 336405 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 336405, 1, 65536⟩
    (by decide) selected_cut_41643

theorem selected_cut_41644 : selected 9 ⟨1138613, by decide⟩
    (prefixPartial 12 336406) = some ⟨12, 2, 0, 1138613, 336406, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_336406_1138613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336406 ⟨1138613, by decide⟩ :=
  accepted_of_selected 12 336406 ⟨1138613, by decide⟩ ⟨12, 2, 0, 1138613, 336406, 2501, 65536⟩
    (by decide) selected_cut_41644

theorem selected_cut_41645 : selected 9 ⟨1138676, by decide⟩
    (prefixPartial 12 336407) = some ⟨12, 2, 0, 1138676, 336407, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_336407_1138676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336407 ⟨1138676, by decide⟩ :=
  accepted_of_selected 12 336407 ⟨1138676, by decide⟩ ⟨12, 2, 0, 1138676, 336407, 3221, 65536⟩
    (by decide) selected_cut_41645

theorem unmarked_context_11_84101_1138677 : frontier 10 ⟨1138677, by decide⟩
    (prefixCache 11 84101) (prefixPartial 11 84101) = false := by
  decide +kernel

theorem node_context_11_84101_1138677 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138677, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1138613, by decide⟩,⟨1138676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84101_1138677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84101 ⟨1138677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84101
    ⟨1138677, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1138613, by decide⟩,⟨1138676, by decide⟩]) unmarked_context_11_84101_1138677 node_context_11_84101_1138677
  intro a
  fin_cases a
  · exact context_12_336404_1108174
  · exact context_12_336405_308705
  · exact context_12_336406_1138613
  · exact context_12_336407_1138676

theorem selected_cut_41646 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336408) = some ⟨12, 1, 0, 1108174, 336408, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336408_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336408 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336408 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336408, 1, 65536⟩
    (by decide) selected_cut_41646

theorem selected_cut_41647 : selected 9 ⟨1138723, by decide⟩
    (prefixPartial 12 336409) = some ⟨12, 2, 0, 1138723, 336409, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_336409_1138723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336409 ⟨1138723, by decide⟩ :=
  accepted_of_selected 12 336409 ⟨1138723, by decide⟩ ⟨12, 2, 0, 1138723, 336409, 2585, 65536⟩
    (by decide) selected_cut_41647

theorem selected_cut_41648 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 336410) = some ⟨12, 1, 0, 893903, 336410, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336410_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336410 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 336410 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 336410, 1, 65536⟩
    (by decide) selected_cut_41648

theorem selected_cut_41649 : selected 9 ⟨1138769, by decide⟩
    (prefixPartial 12 336411) = some ⟨12, 2, 0, 1138769, 336411, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_336411_1138769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336411 ⟨1138769, by decide⟩ :=
  accepted_of_selected 12 336411 ⟨1138769, by decide⟩ ⟨12, 2, 0, 1138769, 336411, 2725, 65536⟩
    (by decide) selected_cut_41649

theorem unmarked_context_11_84102_1138770 : frontier 10 ⟨1138770, by decide⟩
    (prefixCache 11 84102) (prefixPartial 11 84102) = false := by
  decide +kernel

theorem node_context_11_84102_1138770 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138770, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1138723, by decide⟩,⟨893903, by decide⟩,⟨1138769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84102_1138770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84102 ⟨1138770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84102
    ⟨1138770, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1138723, by decide⟩,⟨893903, by decide⟩,⟨1138769, by decide⟩]) unmarked_context_11_84102_1138770 node_context_11_84102_1138770
  intro a
  fin_cases a
  · exact context_12_336408_1108174
  · exact context_12_336409_1138723
  · exact context_12_336410_893903
  · exact context_12_336411_1138769

theorem selected_cut_41650 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336412) = some ⟨12, 1, 0, 1108174, 336412, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336412_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336412 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336412 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336412, 1, 65536⟩
    (by decide) selected_cut_41650

theorem selected_cut_41651 : selected 9 ⟨1138802, by decide⟩
    (prefixPartial 12 336413) = some ⟨12, 2, 0, 1138802, 336413, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_336413_1138802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336413 ⟨1138802, by decide⟩ :=
  accepted_of_selected 12 336413 ⟨1138802, by decide⟩ ⟨12, 2, 0, 1138802, 336413, 2365, 65536⟩
    (by decide) selected_cut_41651

theorem selected_cut_41652 : selected 9 ⟨1138830, by decide⟩
    (prefixPartial 12 336414) = some ⟨12, 2, 0, 1138830, 336414, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_336414_1138830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336414 ⟨1138830, by decide⟩ :=
  accepted_of_selected 12 336414 ⟨1138830, by decide⟩ ⟨12, 2, 0, 1138830, 336414, 2157, 65536⟩
    (by decide) selected_cut_41652

theorem selected_cut_41653 : selected 9 ⟨1138854, by decide⟩
    (prefixPartial 12 336415) = some ⟨12, 2, 0, 1138854, 336415, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_336415_1138854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336415 ⟨1138854, by decide⟩ :=
  accepted_of_selected 12 336415 ⟨1138854, by decide⟩ ⟨12, 2, 0, 1138854, 336415, 2289, 65536⟩
    (by decide) selected_cut_41653

theorem unmarked_context_11_84103_1138855 : frontier 10 ⟨1138855, by decide⟩
    (prefixCache 11 84103) (prefixPartial 11 84103) = false := by
  decide +kernel

theorem node_context_11_84103_1138855 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138855, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1138802, by decide⟩,⟨1138830, by decide⟩,⟨1138854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84103_1138855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84103 ⟨1138855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84103
    ⟨1138855, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1138802, by decide⟩,⟨1138830, by decide⟩,⟨1138854, by decide⟩]) unmarked_context_11_84103_1138855 node_context_11_84103_1138855
  intro a
  fin_cases a
  · exact context_12_336412_1108174
  · exact context_12_336413_1138802
  · exact context_12_336414_1138830
  · exact context_12_336415_1138854

theorem unmarked_context_10_21025_1138856 : frontier 11 ⟨1138856, by decide⟩
    (prefixCache 10 21025) (prefixPartial 10 21025) = false := by
  decide +kernel

theorem node_context_10_21025_1138856 : EJMOriginalGlobalDAGData.nodes 11 ⟨1138856, by decide⟩ =
    .split (coordinate 10) (![⟨1138574, by decide⟩,⟨1138677, by decide⟩,⟨1138770, by decide⟩,⟨1138855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21025_1138856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21025 ⟨1138856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21025
    ⟨1138856, by decide⟩ (by decide) (![⟨1138574, by decide⟩,⟨1138677, by decide⟩,⟨1138770, by decide⟩,⟨1138855, by decide⟩]) unmarked_context_10_21025_1138856 node_context_10_21025_1138856
  intro a
  fin_cases a
  · exact context_11_84100_1138574
  · exact context_11_84101_1138677
  · exact context_11_84102_1138770
  · exact context_11_84103_1138855

theorem selected_cut_41654 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336416) = some ⟨12, 1, 0, 1108174, 336416, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336416_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336416 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336416 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336416, 1, 65536⟩
    (by decide) selected_cut_41654

theorem selected_cut_41655 : selected 9 ⟨1138897, by decide⟩
    (prefixPartial 12 336417) = some ⟨12, 2, 0, 1138897, 336417, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_336417_1138897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336417 ⟨1138897, by decide⟩ :=
  accepted_of_selected 12 336417 ⟨1138897, by decide⟩ ⟨12, 2, 0, 1138897, 336417, 2581, 65536⟩
    (by decide) selected_cut_41655

theorem selected_cut_41656 : selected 9 ⟨1138925, by decide⟩
    (prefixPartial 12 336418) = some ⟨12, 2, 0, 1138925, 336418, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_336418_1138925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336418 ⟨1138925, by decide⟩ :=
  accepted_of_selected 12 336418 ⟨1138925, by decide⟩ ⟨12, 2, 0, 1138925, 336418, 2137, 65536⟩
    (by decide) selected_cut_41656

theorem selected_cut_41657 : selected 9 ⟨1138960, by decide⟩
    (prefixPartial 12 336419) = some ⟨12, 2, 0, 1138960, 336419, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_336419_1138960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336419 ⟨1138960, by decide⟩ :=
  accepted_of_selected 12 336419 ⟨1138960, by decide⟩ ⟨12, 2, 0, 1138960, 336419, 2569, 65536⟩
    (by decide) selected_cut_41657

theorem unmarked_context_11_84104_1138961 : frontier 10 ⟨1138961, by decide⟩
    (prefixCache 11 84104) (prefixPartial 11 84104) = false := by
  decide +kernel

theorem node_context_11_84104_1138961 : EJMOriginalGlobalDAGData.nodes 10 ⟨1138961, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1138897, by decide⟩,⟨1138925, by decide⟩,⟨1138960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84104_1138961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84104 ⟨1138961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84104
    ⟨1138961, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1138897, by decide⟩,⟨1138925, by decide⟩,⟨1138960, by decide⟩]) unmarked_context_11_84104_1138961 node_context_11_84104_1138961
  intro a
  fin_cases a
  · exact context_12_336416_1108174
  · exact context_12_336417_1138897
  · exact context_12_336418_1138925
  · exact context_12_336419_1138960

theorem selected_cut_41658 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336420) = some ⟨12, 1, 0, 1108174, 336420, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336420_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336420 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336420 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336420, 1, 65536⟩
    (by decide) selected_cut_41658

theorem selected_cut_41659 : selected 9 ⟨1139009, by decide⟩
    (prefixPartial 12 336421) = some ⟨12, 2, 0, 1139009, 336421, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_336421_1139009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336421 ⟨1139009, by decide⟩ :=
  accepted_of_selected 12 336421 ⟨1139009, by decide⟩ ⟨12, 2, 0, 1139009, 336421, 2825, 65536⟩
    (by decide) selected_cut_41659

theorem selected_cut_41660 : selected 9 ⟨1139043, by decide⟩
    (prefixPartial 12 336422) = some ⟨12, 2, 0, 1139043, 336422, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_336422_1139043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336422 ⟨1139043, by decide⟩ :=
  accepted_of_selected 12 336422 ⟨1139043, by decide⟩ ⟨12, 2, 0, 1139043, 336422, 2189, 65536⟩
    (by decide) selected_cut_41660

theorem selected_cut_41661 : selected 9 ⟨1139090, by decide⟩
    (prefixPartial 12 336423) = some ⟨12, 2, 0, 1139090, 336423, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_336423_1139090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336423 ⟨1139090, by decide⟩ :=
  accepted_of_selected 12 336423 ⟨1139090, by decide⟩ ⟨12, 2, 0, 1139090, 336423, 2737, 65536⟩
    (by decide) selected_cut_41661

theorem unmarked_context_11_84105_1139091 : frontier 10 ⟨1139091, by decide⟩
    (prefixCache 11 84105) (prefixPartial 11 84105) = false := by
  decide +kernel

theorem node_context_11_84105_1139091 : EJMOriginalGlobalDAGData.nodes 10 ⟨1139091, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1139009, by decide⟩,⟨1139043, by decide⟩,⟨1139090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84105_1139091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84105 ⟨1139091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84105
    ⟨1139091, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1139009, by decide⟩,⟨1139043, by decide⟩,⟨1139090, by decide⟩]) unmarked_context_11_84105_1139091 node_context_11_84105_1139091
  intro a
  fin_cases a
  · exact context_12_336420_1108174
  · exact context_12_336421_1139009
  · exact context_12_336422_1139043
  · exact context_12_336423_1139090

theorem selected_cut_41662 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336424) = some ⟨12, 1, 0, 1108174, 336424, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336424_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336424 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336424 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336424, 1, 65536⟩
    (by decide) selected_cut_41662

theorem selected_cut_41663 : selected 9 ⟨1139145, by decide⟩
    (prefixPartial 12 336425) = some ⟨12, 2, 0, 1139145, 336425, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_336425_1139145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336425 ⟨1139145, by decide⟩ :=
  accepted_of_selected 12 336425 ⟨1139145, by decide⟩ ⟨12, 2, 0, 1139145, 336425, 2669, 65536⟩
    (by decide) selected_cut_41663

theorem selected_cut_41664 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 336426) = some ⟨12, 1, 0, 474208, 336426, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336426_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336426 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 336426 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 336426, 1, 65536⟩
    (by decide) selected_cut_41664

theorem selected_cut_41665 : selected 9 ⟨1139186, by decide⟩
    (prefixPartial 12 336427) = some ⟨12, 2, 0, 1139186, 336427, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_336427_1139186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336427 ⟨1139186, by decide⟩ :=
  accepted_of_selected 12 336427 ⟨1139186, by decide⟩ ⟨12, 2, 0, 1139186, 336427, 2533, 65536⟩
    (by decide) selected_cut_41665

theorem unmarked_context_11_84106_1139187 : frontier 10 ⟨1139187, by decide⟩
    (prefixCache 11 84106) (prefixPartial 11 84106) = false := by
  decide +kernel

theorem node_context_11_84106_1139187 : EJMOriginalGlobalDAGData.nodes 10 ⟨1139187, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1139145, by decide⟩,⟨474208, by decide⟩,⟨1139186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84106_1139187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84106 ⟨1139187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84106
    ⟨1139187, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1139145, by decide⟩,⟨474208, by decide⟩,⟨1139186, by decide⟩]) unmarked_context_11_84106_1139187 node_context_11_84106_1139187
  intro a
  fin_cases a
  · exact context_12_336424_1108174
  · exact context_12_336425_1139145
  · exact context_12_336426_474208
  · exact context_12_336427_1139186

theorem selected_cut_41666 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336428) = some ⟨12, 1, 0, 1108174, 336428, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336428_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336428 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336428 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336428, 1, 65536⟩
    (by decide) selected_cut_41666

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
