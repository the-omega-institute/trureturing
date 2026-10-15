/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover465
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_22182_1232789 : frontier 11 ⟨1232789, by decide⟩
    (prefixCache 10 22182) (prefixPartial 10 22182) = false := by
  decide +kernel

theorem node_context_10_22182_1232789 : EJMOriginalGlobalDAGData.nodes 11 ⟨1232789, by decide⟩ =
    .split (coordinate 10) (![⟨1232669, by decide⟩,⟨1232728, by decide⟩,⟨900587, by decide⟩,⟨1232788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22182_1232789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22182 ⟨1232789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22182
    ⟨1232789, by decide⟩ (by decide) (![⟨1232669, by decide⟩,⟨1232728, by decide⟩,⟨900587, by decide⟩,⟨1232788, by decide⟩]) unmarked_context_10_22182_1232789 node_context_10_22182_1232789
  intro a
  fin_cases a
  · exact context_11_88728_1232669
  · exact context_11_88729_1232728
  · exact context_11_88730_900587
  · exact context_11_88731_1232788

theorem selected_cut_44740 : selected 10 ⟨1232863, by decide⟩
    (prefixPartial 11 88732) = some ⟨11, 2, 0, 1232863, 88732, 3753, 262144⟩ := by
  decide +kernel

theorem context_11_88732_1232863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88732 ⟨1232863, by decide⟩ :=
  accepted_of_selected 11 88732 ⟨1232863, by decide⟩ ⟨11, 2, 0, 1232863, 88732, 3753, 262144⟩
    (by decide) selected_cut_44740

theorem selected_cut_44741 : selected 10 ⟨1232918, by decide⟩
    (prefixPartial 11 88733) = some ⟨11, 2, 0, 1232918, 88733, 3253, 262144⟩ := by
  decide +kernel

theorem context_11_88733_1232918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88733 ⟨1232918, by decide⟩ :=
  accepted_of_selected 11 88733 ⟨1232918, by decide⟩ ⟨11, 2, 0, 1232918, 88733, 3253, 262144⟩
    (by decide) selected_cut_44741

theorem selected_cut_44742 : selected 10 ⟨1232957, by decide⟩
    (prefixPartial 11 88734) = some ⟨11, 2, 0, 1232957, 88734, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_88734_1232957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88734 ⟨1232957, by decide⟩ :=
  accepted_of_selected 11 88734 ⟨1232957, by decide⟩ ⟨11, 2, 0, 1232957, 88734, 2145, 262144⟩
    (by decide) selected_cut_44742

theorem selected_cut_44743 : selected 10 ⟨1232994, by decide⟩
    (prefixPartial 11 88735) = some ⟨11, 2, 0, 1232994, 88735, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_88735_1232994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88735 ⟨1232994, by decide⟩ :=
  accepted_of_selected 11 88735 ⟨1232994, by decide⟩ ⟨11, 2, 0, 1232994, 88735, 1353, 262144⟩
    (by decide) selected_cut_44743

theorem unmarked_context_10_22183_1232995 : frontier 11 ⟨1232995, by decide⟩
    (prefixCache 10 22183) (prefixPartial 10 22183) = false := by
  decide +kernel

theorem node_context_10_22183_1232995 : EJMOriginalGlobalDAGData.nodes 11 ⟨1232995, by decide⟩ =
    .split (coordinate 10) (![⟨1232863, by decide⟩,⟨1232918, by decide⟩,⟨1232957, by decide⟩,⟨1232994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22183_1232995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22183 ⟨1232995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22183
    ⟨1232995, by decide⟩ (by decide) (![⟨1232863, by decide⟩,⟨1232918, by decide⟩,⟨1232957, by decide⟩,⟨1232994, by decide⟩]) unmarked_context_10_22183_1232995 node_context_10_22183_1232995
  intro a
  fin_cases a
  · exact context_11_88732_1232863
  · exact context_11_88733_1232918
  · exact context_11_88734_1232957
  · exact context_11_88735_1232994

theorem unmarked_context_9_5545_1232996 : frontier 12 ⟨1232996, by decide⟩
    (prefixCache 9 5545) (prefixPartial 9 5545) = false := by
  decide +kernel

theorem node_context_9_5545_1232996 : EJMOriginalGlobalDAGData.nodes 12 ⟨1232996, by decide⟩ =
    .split (coordinate 9) (![⟨1232565, by decide⟩,⟨893098, by decide⟩,⟨1232789, by decide⟩,⟨1232995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5545_1232996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5545 ⟨1232996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5545
    ⟨1232996, by decide⟩ (by decide) (![⟨1232565, by decide⟩,⟨893098, by decide⟩,⟨1232789, by decide⟩,⟨1232995, by decide⟩]) unmarked_context_9_5545_1232996 node_context_9_5545_1232996
  intro a
  fin_cases a
  · exact context_10_22180_1232565
  · exact context_10_22181_893098
  · exact context_10_22182_1232789
  · exact context_10_22183_1232995

theorem selected_cut_44744 : selected 10 ⟨1233025, by decide⟩
    (prefixPartial 11 88736) = some ⟨11, 2, 0, 1233025, 88736, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_88736_1233025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88736 ⟨1233025, by decide⟩ :=
  accepted_of_selected 11 88736 ⟨1233025, by decide⟩ ⟨11, 2, 0, 1233025, 88736, 1989, 262144⟩
    (by decide) selected_cut_44744

theorem selected_cut_44745 : selected 10 ⟨1233068, by decide⟩
    (prefixPartial 11 88737) = some ⟨11, 2, 0, 1233068, 88737, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_88737_1233068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88737 ⟨1233068, by decide⟩ :=
  accepted_of_selected 11 88737 ⟨1233068, by decide⟩ ⟨11, 2, 0, 1233068, 88737, 2153, 262144⟩
    (by decide) selected_cut_44745

theorem selected_cut_44746 : selected 10 ⟨1233126, by decide⟩
    (prefixPartial 11 88738) = some ⟨11, 2, 0, 1233126, 88738, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_88738_1233126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88738 ⟨1233126, by decide⟩ :=
  accepted_of_selected 11 88738 ⟨1233126, by decide⟩ ⟨11, 2, 0, 1233126, 88738, 2929, 262144⟩
    (by decide) selected_cut_44746

theorem selected_cut_44747 : selected 10 ⟨1233199, by decide⟩
    (prefixPartial 11 88739) = some ⟨11, 2, 0, 1233199, 88739, 4085, 262144⟩ := by
  decide +kernel

theorem context_11_88739_1233199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88739 ⟨1233199, by decide⟩ :=
  accepted_of_selected 11 88739 ⟨1233199, by decide⟩ ⟨11, 2, 0, 1233199, 88739, 4085, 262144⟩
    (by decide) selected_cut_44747

theorem unmarked_context_10_22184_1233200 : frontier 11 ⟨1233200, by decide⟩
    (prefixCache 10 22184) (prefixPartial 10 22184) = false := by
  decide +kernel

theorem node_context_10_22184_1233200 : EJMOriginalGlobalDAGData.nodes 11 ⟨1233200, by decide⟩ =
    .split (coordinate 10) (![⟨1233025, by decide⟩,⟨1233068, by decide⟩,⟨1233126, by decide⟩,⟨1233199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22184_1233200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22184 ⟨1233200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22184
    ⟨1233200, by decide⟩ (by decide) (![⟨1233025, by decide⟩,⟨1233068, by decide⟩,⟨1233126, by decide⟩,⟨1233199, by decide⟩]) unmarked_context_10_22184_1233200 node_context_10_22184_1233200
  intro a
  fin_cases a
  · exact context_11_88736_1233025
  · exact context_11_88737_1233068
  · exact context_11_88738_1233126
  · exact context_11_88739_1233199

theorem selected_cut_44748 : selected 10 ⟨1233244, by decide⟩
    (prefixPartial 11 88740) = some ⟨11, 2, 0, 1233244, 88740, 2553, 262144⟩ := by
  decide +kernel

theorem context_11_88740_1233244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88740 ⟨1233244, by decide⟩ :=
  accepted_of_selected 11 88740 ⟨1233244, by decide⟩ ⟨11, 2, 0, 1233244, 88740, 2553, 262144⟩
    (by decide) selected_cut_44748

theorem selected_cut_44749 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 88741) = some ⟨11, 1, 0, 1192826, 88741, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88741_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88741 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 88741 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 88741, 1, 262144⟩
    (by decide) selected_cut_44749

theorem selected_cut_44750 : selected 10 ⟨1233286, by decide⟩
    (prefixPartial 11 88742) = some ⟨11, 2, 0, 1233286, 88742, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_88742_1233286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88742 ⟨1233286, by decide⟩ :=
  accepted_of_selected 11 88742 ⟨1233286, by decide⟩ ⟨11, 2, 0, 1233286, 88742, 2405, 262144⟩
    (by decide) selected_cut_44750

theorem selected_cut_44751 : selected 10 ⟨1233322, by decide⟩
    (prefixPartial 11 88743) = some ⟨11, 2, 0, 1233322, 88743, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_88743_1233322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88743 ⟨1233322, by decide⟩ :=
  accepted_of_selected 11 88743 ⟨1233322, by decide⟩ ⟨11, 2, 0, 1233322, 88743, 2385, 262144⟩
    (by decide) selected_cut_44751

theorem unmarked_context_10_22185_1233323 : frontier 11 ⟨1233323, by decide⟩
    (prefixCache 10 22185) (prefixPartial 10 22185) = false := by
  decide +kernel

theorem node_context_10_22185_1233323 : EJMOriginalGlobalDAGData.nodes 11 ⟨1233323, by decide⟩ =
    .split (coordinate 10) (![⟨1233244, by decide⟩,⟨1192826, by decide⟩,⟨1233286, by decide⟩,⟨1233322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22185_1233323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22185 ⟨1233323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22185
    ⟨1233323, by decide⟩ (by decide) (![⟨1233244, by decide⟩,⟨1192826, by decide⟩,⟨1233286, by decide⟩,⟨1233322, by decide⟩]) unmarked_context_10_22185_1233323 node_context_10_22185_1233323
  intro a
  fin_cases a
  · exact context_11_88740_1233244
  · exact context_11_88741_1192826
  · exact context_11_88742_1233286
  · exact context_11_88743_1233322

theorem selected_cut_44752 : selected 11 ⟨1233356, by decide⟩
    (prefixPartial 10 22186) = some ⟨10, 2, 0, 1233356, 22186, 1513, 1048576⟩ := by
  decide +kernel

theorem context_10_22186_1233356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22186 ⟨1233356, by decide⟩ :=
  accepted_of_selected 10 22186 ⟨1233356, by decide⟩ ⟨10, 2, 0, 1233356, 22186, 1513, 1048576⟩
    (by decide) selected_cut_44752

theorem selected_cut_44753 : selected 10 ⟨1233396, by decide⟩
    (prefixPartial 11 88748) = some ⟨11, 2, 0, 1233396, 88748, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_88748_1233396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88748 ⟨1233396, by decide⟩ :=
  accepted_of_selected 11 88748 ⟨1233396, by decide⟩ ⟨11, 2, 0, 1233396, 88748, 2521, 262144⟩
    (by decide) selected_cut_44753

theorem selected_cut_44754 : selected 10 ⟨1233416, by decide⟩
    (prefixPartial 11 88749) = some ⟨11, 2, 0, 1233416, 88749, 1209, 262144⟩ := by
  decide +kernel

theorem context_11_88749_1233416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88749 ⟨1233416, by decide⟩ :=
  accepted_of_selected 11 88749 ⟨1233416, by decide⟩ ⟨11, 2, 0, 1233416, 88749, 1209, 262144⟩
    (by decide) selected_cut_44754

theorem selected_cut_44755 : selected 10 ⟨1233444, by decide⟩
    (prefixPartial 11 88750) = some ⟨11, 2, 0, 1233444, 88750, 1637, 262144⟩ := by
  decide +kernel

theorem context_11_88750_1233444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88750 ⟨1233444, by decide⟩ :=
  accepted_of_selected 11 88750 ⟨1233444, by decide⟩ ⟨11, 2, 0, 1233444, 88750, 1637, 262144⟩
    (by decide) selected_cut_44755

theorem selected_cut_44756 : selected 10 ⟨1233470, by decide⟩
    (prefixPartial 11 88751) = some ⟨11, 2, 0, 1233470, 88751, 1153, 262144⟩ := by
  decide +kernel

theorem context_11_88751_1233470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88751 ⟨1233470, by decide⟩ :=
  accepted_of_selected 11 88751 ⟨1233470, by decide⟩ ⟨11, 2, 0, 1233470, 88751, 1153, 262144⟩
    (by decide) selected_cut_44756

theorem unmarked_context_10_22187_1233471 : frontier 11 ⟨1233471, by decide⟩
    (prefixCache 10 22187) (prefixPartial 10 22187) = false := by
  decide +kernel

theorem node_context_10_22187_1233471 : EJMOriginalGlobalDAGData.nodes 11 ⟨1233471, by decide⟩ =
    .split (coordinate 10) (![⟨1233396, by decide⟩,⟨1233416, by decide⟩,⟨1233444, by decide⟩,⟨1233470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22187_1233471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22187 ⟨1233471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22187
    ⟨1233471, by decide⟩ (by decide) (![⟨1233396, by decide⟩,⟨1233416, by decide⟩,⟨1233444, by decide⟩,⟨1233470, by decide⟩]) unmarked_context_10_22187_1233471 node_context_10_22187_1233471
  intro a
  fin_cases a
  · exact context_11_88748_1233396
  · exact context_11_88749_1233416
  · exact context_11_88750_1233444
  · exact context_11_88751_1233470

theorem unmarked_context_9_5546_1233472 : frontier 12 ⟨1233472, by decide⟩
    (prefixCache 9 5546) (prefixPartial 9 5546) = false := by
  decide +kernel

theorem node_context_9_5546_1233472 : EJMOriginalGlobalDAGData.nodes 12 ⟨1233472, by decide⟩ =
    .split (coordinate 9) (![⟨1233200, by decide⟩,⟨1233323, by decide⟩,⟨1233356, by decide⟩,⟨1233471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5546_1233472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5546 ⟨1233472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5546
    ⟨1233472, by decide⟩ (by decide) (![⟨1233200, by decide⟩,⟨1233323, by decide⟩,⟨1233356, by decide⟩,⟨1233471, by decide⟩]) unmarked_context_9_5546_1233472 node_context_9_5546_1233472
  intro a
  fin_cases a
  · exact context_10_22184_1233200
  · exact context_10_22185_1233323
  · exact context_10_22186_1233356
  · exact context_10_22187_1233471

theorem selected_cut_44757 : selected 10 ⟨1233506, by decide⟩
    (prefixPartial 11 88752) = some ⟨11, 2, 0, 1233506, 88752, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_88752_1233506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88752 ⟨1233506, by decide⟩ :=
  accepted_of_selected 11 88752 ⟨1233506, by decide⟩ ⟨11, 2, 0, 1233506, 88752, 1705, 262144⟩
    (by decide) selected_cut_44757

theorem selected_cut_44758 : selected 10 ⟨1233541, by decide⟩
    (prefixPartial 11 88753) = some ⟨11, 2, 0, 1233541, 88753, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_88753_1233541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88753 ⟨1233541, by decide⟩ :=
  accepted_of_selected 11 88753 ⟨1233541, by decide⟩ ⟨11, 2, 0, 1233541, 88753, 2101, 262144⟩
    (by decide) selected_cut_44758

theorem selected_cut_44759 : selected 10 ⟨1233570, by decide⟩
    (prefixPartial 11 88754) = some ⟨11, 2, 0, 1233570, 88754, 1337, 262144⟩ := by
  decide +kernel

theorem context_11_88754_1233570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88754 ⟨1233570, by decide⟩ :=
  accepted_of_selected 11 88754 ⟨1233570, by decide⟩ ⟨11, 2, 0, 1233570, 88754, 1337, 262144⟩
    (by decide) selected_cut_44759

theorem selected_cut_44760 : selected 10 ⟨1233595, by decide⟩
    (prefixPartial 11 88755) = some ⟨11, 2, 0, 1233595, 88755, 1349, 262144⟩ := by
  decide +kernel

theorem context_11_88755_1233595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88755 ⟨1233595, by decide⟩ :=
  accepted_of_selected 11 88755 ⟨1233595, by decide⟩ ⟨11, 2, 0, 1233595, 88755, 1349, 262144⟩
    (by decide) selected_cut_44760

theorem unmarked_context_10_22188_1233596 : frontier 11 ⟨1233596, by decide⟩
    (prefixCache 10 22188) (prefixPartial 10 22188) = false := by
  decide +kernel

theorem node_context_10_22188_1233596 : EJMOriginalGlobalDAGData.nodes 11 ⟨1233596, by decide⟩ =
    .split (coordinate 10) (![⟨1233506, by decide⟩,⟨1233541, by decide⟩,⟨1233570, by decide⟩,⟨1233595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22188_1233596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22188 ⟨1233596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22188
    ⟨1233596, by decide⟩ (by decide) (![⟨1233506, by decide⟩,⟨1233541, by decide⟩,⟨1233570, by decide⟩,⟨1233595, by decide⟩]) unmarked_context_10_22188_1233596 node_context_10_22188_1233596
  intro a
  fin_cases a
  · exact context_11_88752_1233506
  · exact context_11_88753_1233541
  · exact context_11_88754_1233570
  · exact context_11_88755_1233595

theorem selected_cut_44761 : selected 11 ⟨1233644, by decide⟩
    (prefixPartial 10 22189) = some ⟨10, 2, 0, 1233644, 22189, 2877, 1048576⟩ := by
  decide +kernel

theorem context_10_22189_1233644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22189 ⟨1233644, by decide⟩ :=
  accepted_of_selected 10 22189 ⟨1233644, by decide⟩ ⟨10, 2, 0, 1233644, 22189, 2877, 1048576⟩
    (by decide) selected_cut_44761

theorem selected_cut_44762 : selected 11 ⟨1233681, by decide⟩
    (prefixPartial 10 22190) = some ⟨10, 2, 0, 1233681, 22190, 1417, 1048576⟩ := by
  decide +kernel

theorem context_10_22190_1233681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22190 ⟨1233681, by decide⟩ :=
  accepted_of_selected 10 22190 ⟨1233681, by decide⟩ ⟨10, 2, 0, 1233681, 22190, 1417, 1048576⟩
    (by decide) selected_cut_44762

theorem selected_cut_44763 : selected 11 ⟨1233698, by decide⟩
    (prefixPartial 10 22191) = some ⟨10, 2, 0, 1233698, 22191, 365, 1048576⟩ := by
  decide +kernel

theorem context_10_22191_1233698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22191 ⟨1233698, by decide⟩ :=
  accepted_of_selected 10 22191 ⟨1233698, by decide⟩ ⟨10, 2, 0, 1233698, 22191, 365, 1048576⟩
    (by decide) selected_cut_44763

theorem unmarked_context_9_5547_1233699 : frontier 12 ⟨1233699, by decide⟩
    (prefixCache 9 5547) (prefixPartial 9 5547) = false := by
  decide +kernel

theorem node_context_9_5547_1233699 : EJMOriginalGlobalDAGData.nodes 12 ⟨1233699, by decide⟩ =
    .split (coordinate 9) (![⟨1233596, by decide⟩,⟨1233644, by decide⟩,⟨1233681, by decide⟩,⟨1233698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5547_1233699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5547 ⟨1233699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5547
    ⟨1233699, by decide⟩ (by decide) (![⟨1233596, by decide⟩,⟨1233644, by decide⟩,⟨1233681, by decide⟩,⟨1233698, by decide⟩]) unmarked_context_9_5547_1233699 node_context_9_5547_1233699
  intro a
  fin_cases a
  · exact context_10_22188_1233596
  · exact context_10_22189_1233644
  · exact context_10_22190_1233681
  · exact context_10_22191_1233698

theorem unmarked_context_8_1386_1233700 : frontier 13 ⟨1233700, by decide⟩
    (prefixCache 8 1386) (prefixPartial 8 1386) = false := by
  decide +kernel

theorem node_context_8_1386_1233700 : EJMOriginalGlobalDAGData.nodes 13 ⟨1233700, by decide⟩ =
    .split (coordinate 8) (![⟨1232212, by decide⟩,⟨1232996, by decide⟩,⟨1233472, by decide⟩,⟨1233699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1386_1233700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1386 ⟨1233700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1386
    ⟨1233700, by decide⟩ (by decide) (![⟨1232212, by decide⟩,⟨1232996, by decide⟩,⟨1233472, by decide⟩,⟨1233699, by decide⟩]) unmarked_context_8_1386_1233700 node_context_8_1386_1233700
  intro a
  fin_cases a
  · exact context_9_5544_1232212
  · exact context_9_5545_1232996
  · exact context_9_5546_1233472
  · exact context_9_5547_1233699

theorem selected_cut_44764 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88768) = some ⟨11, 1, 0, 434745, 88768, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88768_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88768 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88768 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88768, 1, 262144⟩
    (by decide) selected_cut_44764

theorem selected_cut_44765 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355076) = some ⟨12, 1, 0, 448748, 355076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355076_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355076 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355076 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355076, 1, 65536⟩
    (by decide) selected_cut_44765

theorem selected_cut_44766 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 355077) = some ⟨12, 1, 0, 34034, 355077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355077_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355077 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 355077 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 355077, 1, 65536⟩
    (by decide) selected_cut_44766

theorem selected_cut_44767 : selected 9 ⟨1233755, by decide⟩
    (prefixPartial 12 355078) = some ⟨12, 2, 0, 1233755, 355078, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_355078_1233755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355078 ⟨1233755, by decide⟩ :=
  accepted_of_selected 12 355078 ⟨1233755, by decide⟩ ⟨12, 2, 0, 1233755, 355078, 3001, 65536⟩
    (by decide) selected_cut_44767

theorem selected_cut_44768 : selected 9 ⟨1233811, by decide⟩
    (prefixPartial 12 355079) = some ⟨12, 2, 0, 1233811, 355079, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_355079_1233811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355079 ⟨1233811, by decide⟩ :=
  accepted_of_selected 12 355079 ⟨1233811, by decide⟩ ⟨12, 2, 0, 1233811, 355079, 3141, 65536⟩
    (by decide) selected_cut_44768

theorem unmarked_context_11_88769_1233812 : frontier 10 ⟨1233812, by decide⟩
    (prefixCache 11 88769) (prefixPartial 11 88769) = false := by
  decide +kernel

theorem node_context_11_88769_1233812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1233812, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1233755, by decide⟩,⟨1233811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88769_1233812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88769 ⟨1233812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88769
    ⟨1233812, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1233755, by decide⟩,⟨1233811, by decide⟩]) unmarked_context_11_88769_1233812 node_context_11_88769_1233812
  intro a
  fin_cases a
  · exact context_12_355076_448748
  · exact context_12_355077_34034
  · exact context_12_355078_1233755
  · exact context_12_355079_1233811

theorem selected_cut_44769 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355080) = some ⟨12, 1, 0, 448748, 355080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355080_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355080 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355080 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355080, 1, 65536⟩
    (by decide) selected_cut_44769

theorem selected_cut_44770 : selected 9 ⟨1233878, by decide⟩
    (prefixPartial 12 355081) = some ⟨12, 2, 0, 1233878, 355081, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_355081_1233878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355081 ⟨1233878, by decide⟩ :=
  accepted_of_selected 12 355081 ⟨1233878, by decide⟩ ⟨12, 2, 0, 1233878, 355081, 3269, 65536⟩
    (by decide) selected_cut_44770

theorem selected_cut_44771 : selected 9 ⟨1233938, by decide⟩
    (prefixPartial 12 355082) = some ⟨12, 2, 0, 1233938, 355082, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_355082_1233938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355082 ⟨1233938, by decide⟩ :=
  accepted_of_selected 12 355082 ⟨1233938, by decide⟩ ⟨12, 2, 0, 1233938, 355082, 3113, 65536⟩
    (by decide) selected_cut_44771

theorem selected_cut_44772 : selected 9 ⟨1234002, by decide⟩
    (prefixPartial 12 355083) = some ⟨12, 2, 0, 1234002, 355083, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_355083_1234002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355083 ⟨1234002, by decide⟩ :=
  accepted_of_selected 12 355083 ⟨1234002, by decide⟩ ⟨12, 2, 0, 1234002, 355083, 3365, 65536⟩
    (by decide) selected_cut_44772

theorem unmarked_context_11_88770_1234003 : frontier 10 ⟨1234003, by decide⟩
    (prefixCache 11 88770) (prefixPartial 11 88770) = false := by
  decide +kernel

theorem node_context_11_88770_1234003 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234003, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1233878, by decide⟩,⟨1233938, by decide⟩,⟨1234002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88770_1234003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88770 ⟨1234003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88770
    ⟨1234003, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1233878, by decide⟩,⟨1233938, by decide⟩,⟨1234002, by decide⟩]) unmarked_context_11_88770_1234003 node_context_11_88770_1234003
  intro a
  fin_cases a
  · exact context_12_355080_448748
  · exact context_12_355081_1233878
  · exact context_12_355082_1233938
  · exact context_12_355083_1234002

theorem selected_cut_44773 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355084) = some ⟨12, 1, 0, 448748, 355084, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355084_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355084 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355084 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355084, 1, 65536⟩
    (by decide) selected_cut_44773

theorem selected_cut_44774 : selected 9 ⟨1234044, by decide⟩
    (prefixPartial 12 355085) = some ⟨12, 2, 0, 1234044, 355085, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_355085_1234044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355085 ⟨1234044, by decide⟩ :=
  accepted_of_selected 12 355085 ⟨1234044, by decide⟩ ⟨12, 2, 0, 1234044, 355085, 2769, 65536⟩
    (by decide) selected_cut_44774

theorem selected_cut_44775 : selected 9 ⟨1234097, by decide⟩
    (prefixPartial 12 355086) = some ⟨12, 2, 0, 1234097, 355086, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_355086_1234097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355086 ⟨1234097, by decide⟩ :=
  accepted_of_selected 12 355086 ⟨1234097, by decide⟩ ⟨12, 2, 0, 1234097, 355086, 3089, 65536⟩
    (by decide) selected_cut_44775

theorem selected_cut_44776 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 355087) = some ⟨12, 1, 0, 903806, 355087, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355087_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355087 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 355087 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 355087, 1, 65536⟩
    (by decide) selected_cut_44776

theorem unmarked_context_11_88771_1234098 : frontier 10 ⟨1234098, by decide⟩
    (prefixCache 11 88771) (prefixPartial 11 88771) = false := by
  decide +kernel

theorem node_context_11_88771_1234098 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234098, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1234044, by decide⟩,⟨1234097, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88771_1234098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88771 ⟨1234098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88771
    ⟨1234098, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1234044, by decide⟩,⟨1234097, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88771_1234098 node_context_11_88771_1234098
  intro a
  fin_cases a
  · exact context_12_355084_448748
  · exact context_12_355085_1234044
  · exact context_12_355086_1234097
  · exact context_12_355087_903806

theorem unmarked_context_10_22192_1234099 : frontier 11 ⟨1234099, by decide⟩
    (prefixCache 10 22192) (prefixPartial 10 22192) = false := by
  decide +kernel

theorem node_context_10_22192_1234099 : EJMOriginalGlobalDAGData.nodes 11 ⟨1234099, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1233812, by decide⟩,⟨1234003, by decide⟩,⟨1234098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22192_1234099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22192 ⟨1234099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22192
    ⟨1234099, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1233812, by decide⟩,⟨1234003, by decide⟩,⟨1234098, by decide⟩]) unmarked_context_10_22192_1234099 node_context_10_22192_1234099
  intro a
  fin_cases a
  · exact context_11_88768_434745
  · exact context_11_88769_1233812
  · exact context_11_88770_1234003
  · exact context_11_88771_1234098

theorem selected_cut_44777 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355088) = some ⟨12, 1, 0, 435160, 355088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355088_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355088 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355088 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355088, 1, 65536⟩
    (by decide) selected_cut_44777

theorem selected_cut_44778 : selected 9 ⟨1234152, by decide⟩
    (prefixPartial 12 355089) = some ⟨12, 2, 0, 1234152, 355089, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_355089_1234152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355089 ⟨1234152, by decide⟩ :=
  accepted_of_selected 12 355089 ⟨1234152, by decide⟩ ⟨12, 2, 0, 1234152, 355089, 3165, 65536⟩
    (by decide) selected_cut_44778

theorem selected_cut_44779 : selected 9 ⟨1234216, by decide⟩
    (prefixPartial 12 355090) = some ⟨12, 2, 0, 1234216, 355090, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_355090_1234216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355090 ⟨1234216, by decide⟩ :=
  accepted_of_selected 12 355090 ⟨1234216, by decide⟩ ⟨12, 2, 0, 1234216, 355090, 3465, 65536⟩
    (by decide) selected_cut_44779

theorem selected_cut_44780 : selected 9 ⟨1234279, by decide⟩
    (prefixPartial 12 355091) = some ⟨12, 2, 0, 1234279, 355091, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_355091_1234279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355091 ⟨1234279, by decide⟩ :=
  accepted_of_selected 12 355091 ⟨1234279, by decide⟩ ⟨12, 2, 0, 1234279, 355091, 3517, 65536⟩
    (by decide) selected_cut_44780

theorem unmarked_context_11_88772_1234280 : frontier 10 ⟨1234280, by decide⟩
    (prefixCache 11 88772) (prefixPartial 11 88772) = false := by
  decide +kernel

theorem node_context_11_88772_1234280 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234280, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1234152, by decide⟩,⟨1234216, by decide⟩,⟨1234279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88772_1234280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88772 ⟨1234280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88772
    ⟨1234280, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1234152, by decide⟩,⟨1234216, by decide⟩,⟨1234279, by decide⟩]) unmarked_context_11_88772_1234280 node_context_11_88772_1234280
  intro a
  fin_cases a
  · exact context_12_355088_435160
  · exact context_12_355089_1234152
  · exact context_12_355090_1234216
  · exact context_12_355091_1234279

theorem selected_cut_44781 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355092) = some ⟨12, 1, 0, 435160, 355092, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355092_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355092 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355092 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355092, 1, 65536⟩
    (by decide) selected_cut_44781

theorem selected_cut_44782 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 355093) = some ⟨12, 1, 0, 1118965, 355093, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355093_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355093 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 355093 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 355093, 1, 65536⟩
    (by decide) selected_cut_44782

theorem selected_cut_44783 : selected 9 ⟨1234330, by decide⟩
    (prefixPartial 12 355094) = some ⟨12, 2, 0, 1234330, 355094, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_355094_1234330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355094 ⟨1234330, by decide⟩ :=
  accepted_of_selected 12 355094 ⟨1234330, by decide⟩ ⟨12, 2, 0, 1234330, 355094, 2981, 65536⟩
    (by decide) selected_cut_44783

theorem selected_cut_44784 : selected 9 ⟨1234389, by decide⟩
    (prefixPartial 12 355095) = some ⟨12, 2, 0, 1234389, 355095, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_355095_1234389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355095 ⟨1234389, by decide⟩ :=
  accepted_of_selected 12 355095 ⟨1234389, by decide⟩ ⟨12, 2, 0, 1234389, 355095, 3217, 65536⟩
    (by decide) selected_cut_44784

theorem unmarked_context_11_88773_1234390 : frontier 10 ⟨1234390, by decide⟩
    (prefixCache 11 88773) (prefixPartial 11 88773) = false := by
  decide +kernel

theorem node_context_11_88773_1234390 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234390, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1118965, by decide⟩,⟨1234330, by decide⟩,⟨1234389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88773_1234390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88773 ⟨1234390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88773
    ⟨1234390, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1118965, by decide⟩,⟨1234330, by decide⟩,⟨1234389, by decide⟩]) unmarked_context_11_88773_1234390 node_context_11_88773_1234390
  intro a
  fin_cases a
  · exact context_12_355092_435160
  · exact context_12_355093_1118965
  · exact context_12_355094_1234330
  · exact context_12_355095_1234389

theorem selected_cut_44785 : selected 9 ⟨1234442, by decide⟩
    (prefixPartial 12 355096) = some ⟨12, 2, 0, 1234442, 355096, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_355096_1234442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355096 ⟨1234442, by decide⟩ :=
  accepted_of_selected 12 355096 ⟨1234442, by decide⟩ ⟨12, 2, 0, 1234442, 355096, 3013, 65536⟩
    (by decide) selected_cut_44785

theorem selected_cut_44786 : selected 9 ⟨1234492, by decide⟩
    (prefixPartial 12 355097) = some ⟨12, 2, 0, 1234492, 355097, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_355097_1234492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355097 ⟨1234492, by decide⟩ :=
  accepted_of_selected 12 355097 ⟨1234492, by decide⟩ ⟨12, 2, 0, 1234492, 355097, 3001, 65536⟩
    (by decide) selected_cut_44786

theorem selected_cut_44787 : selected 9 ⟨1234545, by decide⟩
    (prefixPartial 12 355098) = some ⟨12, 2, 0, 1234545, 355098, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_355098_1234545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355098 ⟨1234545, by decide⟩ :=
  accepted_of_selected 12 355098 ⟨1234545, by decide⟩ ⟨12, 2, 0, 1234545, 355098, 2925, 65536⟩
    (by decide) selected_cut_44787

theorem selected_cut_44788 : selected 9 ⟨1234601, by decide⟩
    (prefixPartial 12 355099) = some ⟨12, 2, 0, 1234601, 355099, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_355099_1234601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355099 ⟨1234601, by decide⟩ :=
  accepted_of_selected 12 355099 ⟨1234601, by decide⟩ ⟨12, 2, 0, 1234601, 355099, 3329, 65536⟩
    (by decide) selected_cut_44788

theorem unmarked_context_11_88774_1234602 : frontier 10 ⟨1234602, by decide⟩
    (prefixCache 11 88774) (prefixPartial 11 88774) = false := by
  decide +kernel

theorem node_context_11_88774_1234602 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234602, by decide⟩ =
    .split (coordinate 11) (![⟨1234442, by decide⟩,⟨1234492, by decide⟩,⟨1234545, by decide⟩,⟨1234601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88774_1234602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88774 ⟨1234602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88774
    ⟨1234602, by decide⟩ (by decide) (![⟨1234442, by decide⟩,⟨1234492, by decide⟩,⟨1234545, by decide⟩,⟨1234601, by decide⟩]) unmarked_context_11_88774_1234602 node_context_11_88774_1234602
  intro a
  fin_cases a
  · exact context_12_355096_1234442
  · exact context_12_355097_1234492
  · exact context_12_355098_1234545
  · exact context_12_355099_1234601

theorem selected_cut_44789 : selected 9 ⟨1234639, by decide⟩
    (prefixPartial 12 355100) = some ⟨12, 2, 0, 1234639, 355100, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_355100_1234639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355100 ⟨1234639, by decide⟩ :=
  accepted_of_selected 12 355100 ⟨1234639, by decide⟩ ⟨12, 2, 0, 1234639, 355100, 1385, 65536⟩
    (by decide) selected_cut_44789

theorem selected_cut_44790 : selected 9 ⟨1234669, by decide⟩
    (prefixPartial 12 355101) = some ⟨12, 2, 0, 1234669, 355101, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_355101_1234669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355101 ⟨1234669, by decide⟩ :=
  accepted_of_selected 12 355101 ⟨1234669, by decide⟩ ⟨12, 2, 0, 1234669, 355101, 2581, 65536⟩
    (by decide) selected_cut_44790

theorem selected_cut_44791 : selected 9 ⟨1234710, by decide⟩
    (prefixPartial 12 355102) = some ⟨12, 2, 0, 1234710, 355102, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_355102_1234710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355102 ⟨1234710, by decide⟩ :=
  accepted_of_selected 12 355102 ⟨1234710, by decide⟩ ⟨12, 2, 0, 1234710, 355102, 2869, 65536⟩
    (by decide) selected_cut_44791

theorem selected_cut_44792 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 355103) = some ⟨12, 1, 0, 903806, 355103, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355103_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355103 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 355103 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 355103, 1, 65536⟩
    (by decide) selected_cut_44792

theorem unmarked_context_11_88775_1234711 : frontier 10 ⟨1234711, by decide⟩
    (prefixCache 11 88775) (prefixPartial 11 88775) = false := by
  decide +kernel

theorem node_context_11_88775_1234711 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234711, by decide⟩ =
    .split (coordinate 11) (![⟨1234639, by decide⟩,⟨1234669, by decide⟩,⟨1234710, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88775_1234711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88775 ⟨1234711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88775
    ⟨1234711, by decide⟩ (by decide) (![⟨1234639, by decide⟩,⟨1234669, by decide⟩,⟨1234710, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88775_1234711 node_context_11_88775_1234711
  intro a
  fin_cases a
  · exact context_12_355100_1234639
  · exact context_12_355101_1234669
  · exact context_12_355102_1234710
  · exact context_12_355103_903806

theorem unmarked_context_10_22193_1234712 : frontier 11 ⟨1234712, by decide⟩
    (prefixCache 10 22193) (prefixPartial 10 22193) = false := by
  decide +kernel

theorem node_context_10_22193_1234712 : EJMOriginalGlobalDAGData.nodes 11 ⟨1234712, by decide⟩ =
    .split (coordinate 10) (![⟨1234280, by decide⟩,⟨1234390, by decide⟩,⟨1234602, by decide⟩,⟨1234711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22193_1234712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22193 ⟨1234712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22193
    ⟨1234712, by decide⟩ (by decide) (![⟨1234280, by decide⟩,⟨1234390, by decide⟩,⟨1234602, by decide⟩,⟨1234711, by decide⟩]) unmarked_context_10_22193_1234712 node_context_10_22193_1234712
  intro a
  fin_cases a
  · exact context_11_88772_1234280
  · exact context_11_88773_1234390
  · exact context_11_88774_1234602
  · exact context_11_88775_1234711

theorem selected_cut_44793 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 355104) = some ⟨12, 1, 0, 1187656, 355104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355104_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355104 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 355104 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 355104, 1, 65536⟩
    (by decide) selected_cut_44793

theorem selected_cut_44794 : selected 9 ⟨1234748, by decide⟩
    (prefixPartial 12 355105) = some ⟨12, 2, 0, 1234748, 355105, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_355105_1234748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355105 ⟨1234748, by decide⟩ :=
  accepted_of_selected 12 355105 ⟨1234748, by decide⟩ ⟨12, 2, 0, 1234748, 355105, 2513, 65536⟩
    (by decide) selected_cut_44794

theorem selected_cut_44795 : selected 9 ⟨1234788, by decide⟩
    (prefixPartial 12 355106) = some ⟨12, 2, 0, 1234788, 355106, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_355106_1234788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355106 ⟨1234788, by decide⟩ :=
  accepted_of_selected 12 355106 ⟨1234788, by decide⟩ ⟨12, 2, 0, 1234788, 355106, 2513, 65536⟩
    (by decide) selected_cut_44795

theorem selected_cut_44796 : selected 9 ⟨1234838, by decide⟩
    (prefixPartial 12 355107) = some ⟨12, 2, 0, 1234838, 355107, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_355107_1234838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355107 ⟨1234838, by decide⟩ :=
  accepted_of_selected 12 355107 ⟨1234838, by decide⟩ ⟨12, 2, 0, 1234838, 355107, 2705, 65536⟩
    (by decide) selected_cut_44796

theorem unmarked_context_11_88776_1234839 : frontier 10 ⟨1234839, by decide⟩
    (prefixCache 11 88776) (prefixPartial 11 88776) = false := by
  decide +kernel

theorem node_context_11_88776_1234839 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234839, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1234748, by decide⟩,⟨1234788, by decide⟩,⟨1234838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88776_1234839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88776 ⟨1234839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88776
    ⟨1234839, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1234748, by decide⟩,⟨1234788, by decide⟩,⟨1234838, by decide⟩]) unmarked_context_11_88776_1234839 node_context_11_88776_1234839
  intro a
  fin_cases a
  · exact context_12_355104_1187656
  · exact context_12_355105_1234748
  · exact context_12_355106_1234788
  · exact context_12_355107_1234838

theorem selected_cut_44797 : selected 9 ⟨1234874, by decide⟩
    (prefixPartial 12 355108) = some ⟨12, 2, 0, 1234874, 355108, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_355108_1234874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355108 ⟨1234874, by decide⟩ :=
  accepted_of_selected 12 355108 ⟨1234874, by decide⟩ ⟨12, 2, 0, 1234874, 355108, 2549, 65536⟩
    (by decide) selected_cut_44797

theorem selected_cut_44798 : selected 9 ⟨1234909, by decide⟩
    (prefixPartial 12 355109) = some ⟨12, 2, 0, 1234909, 355109, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_355109_1234909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355109 ⟨1234909, by decide⟩ :=
  accepted_of_selected 12 355109 ⟨1234909, by decide⟩ ⟨12, 2, 0, 1234909, 355109, 2229, 65536⟩
    (by decide) selected_cut_44798

theorem selected_cut_44799 : selected 9 ⟨1234940, by decide⟩
    (prefixPartial 12 355110) = some ⟨12, 2, 0, 1234940, 355110, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_355110_1234940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355110 ⟨1234940, by decide⟩ :=
  accepted_of_selected 12 355110 ⟨1234940, by decide⟩ ⟨12, 2, 0, 1234940, 355110, 2205, 65536⟩
    (by decide) selected_cut_44799

theorem selected_cut_44800 : selected 9 ⟨1234979, by decide⟩
    (prefixPartial 12 355111) = some ⟨12, 2, 0, 1234979, 355111, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_355111_1234979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355111 ⟨1234979, by decide⟩ :=
  accepted_of_selected 12 355111 ⟨1234979, by decide⟩ ⟨12, 2, 0, 1234979, 355111, 2433, 65536⟩
    (by decide) selected_cut_44800

theorem unmarked_context_11_88777_1234980 : frontier 10 ⟨1234980, by decide⟩
    (prefixCache 11 88777) (prefixPartial 11 88777) = false := by
  decide +kernel

theorem node_context_11_88777_1234980 : EJMOriginalGlobalDAGData.nodes 10 ⟨1234980, by decide⟩ =
    .split (coordinate 11) (![⟨1234874, by decide⟩,⟨1234909, by decide⟩,⟨1234940, by decide⟩,⟨1234979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88777_1234980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88777 ⟨1234980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88777
    ⟨1234980, by decide⟩ (by decide) (![⟨1234874, by decide⟩,⟨1234909, by decide⟩,⟨1234940, by decide⟩,⟨1234979, by decide⟩]) unmarked_context_11_88777_1234980 node_context_11_88777_1234980
  intro a
  fin_cases a
  · exact context_12_355108_1234874
  · exact context_12_355109_1234909
  · exact context_12_355110_1234940
  · exact context_12_355111_1234979

theorem selected_cut_44801 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88778) = some ⟨11, 1, 0, 900587, 88778, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88778_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88778 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88778 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88778, 1, 262144⟩
    (by decide) selected_cut_44801

theorem selected_cut_44802 : selected 9 ⟨1235020, by decide⟩
    (prefixPartial 12 355116) = some ⟨12, 2, 0, 1235020, 355116, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_355116_1235020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355116 ⟨1235020, by decide⟩ :=
  accepted_of_selected 12 355116 ⟨1235020, by decide⟩ ⟨12, 2, 0, 1235020, 355116, 2481, 65536⟩
    (by decide) selected_cut_44802

theorem selected_cut_44803 : selected 9 ⟨1235047, by decide⟩
    (prefixPartial 12 355117) = some ⟨12, 2, 0, 1235047, 355117, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_355117_1235047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355117 ⟨1235047, by decide⟩ :=
  accepted_of_selected 12 355117 ⟨1235047, by decide⟩ ⟨12, 2, 0, 1235047, 355117, 2157, 65536⟩
    (by decide) selected_cut_44803

theorem selected_cut_44804 : selected 9 ⟨1235085, by decide⟩
    (prefixPartial 12 355118) = some ⟨12, 2, 0, 1235085, 355118, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_355118_1235085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355118 ⟨1235085, by decide⟩ :=
  accepted_of_selected 12 355118 ⟨1235085, by decide⟩ ⟨12, 2, 0, 1235085, 355118, 2405, 65536⟩
    (by decide) selected_cut_44804

theorem selected_cut_44805 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 355119) = some ⟨12, 1, 0, 903806, 355119, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355119_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355119 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 355119 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 355119, 1, 65536⟩
    (by decide) selected_cut_44805

theorem unmarked_context_11_88779_1235086 : frontier 10 ⟨1235086, by decide⟩
    (prefixCache 11 88779) (prefixPartial 11 88779) = false := by
  decide +kernel

theorem node_context_11_88779_1235086 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235086, by decide⟩ =
    .split (coordinate 11) (![⟨1235020, by decide⟩,⟨1235047, by decide⟩,⟨1235085, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88779_1235086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88779 ⟨1235086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88779
    ⟨1235086, by decide⟩ (by decide) (![⟨1235020, by decide⟩,⟨1235047, by decide⟩,⟨1235085, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88779_1235086 node_context_11_88779_1235086
  intro a
  fin_cases a
  · exact context_12_355116_1235020
  · exact context_12_355117_1235047
  · exact context_12_355118_1235085
  · exact context_12_355119_903806

theorem unmarked_context_10_22194_1235087 : frontier 11 ⟨1235087, by decide⟩
    (prefixCache 10 22194) (prefixPartial 10 22194) = false := by
  decide +kernel

theorem node_context_10_22194_1235087 : EJMOriginalGlobalDAGData.nodes 11 ⟨1235087, by decide⟩ =
    .split (coordinate 10) (![⟨1234839, by decide⟩,⟨1234980, by decide⟩,⟨900587, by decide⟩,⟨1235086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22194_1235087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22194 ⟨1235087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22194
    ⟨1235087, by decide⟩ (by decide) (![⟨1234839, by decide⟩,⟨1234980, by decide⟩,⟨900587, by decide⟩,⟨1235086, by decide⟩]) unmarked_context_10_22194_1235087 node_context_10_22194_1235087
  intro a
  fin_cases a
  · exact context_11_88776_1234839
  · exact context_11_88777_1234980
  · exact context_11_88778_900587
  · exact context_11_88779_1235086

theorem selected_cut_44806 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 355120) = some ⟨12, 1, 0, 1187656, 355120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355120_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355120 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 355120 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 355120, 1, 65536⟩
    (by decide) selected_cut_44806

theorem selected_cut_44807 : selected 9 ⟨1235126, by decide⟩
    (prefixPartial 12 355121) = some ⟨12, 2, 0, 1235126, 355121, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_355121_1235126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355121 ⟨1235126, by decide⟩ :=
  accepted_of_selected 12 355121 ⟨1235126, by decide⟩ ⟨12, 2, 0, 1235126, 355121, 2481, 65536⟩
    (by decide) selected_cut_44807

theorem selected_cut_44808 : selected 9 ⟨1235173, by decide⟩
    (prefixPartial 12 355122) = some ⟨12, 2, 0, 1235173, 355122, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_355122_1235173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355122 ⟨1235173, by decide⟩ :=
  accepted_of_selected 12 355122 ⟨1235173, by decide⟩ ⟨12, 2, 0, 1235173, 355122, 2705, 65536⟩
    (by decide) selected_cut_44808

theorem selected_cut_44809 : selected 9 ⟨1235214, by decide⟩
    (prefixPartial 12 355123) = some ⟨12, 2, 0, 1235214, 355123, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_355123_1235214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355123 ⟨1235214, by decide⟩ :=
  accepted_of_selected 12 355123 ⟨1235214, by decide⟩ ⟨12, 2, 0, 1235214, 355123, 2601, 65536⟩
    (by decide) selected_cut_44809

theorem unmarked_context_11_88780_1235215 : frontier 10 ⟨1235215, by decide⟩
    (prefixCache 11 88780) (prefixPartial 11 88780) = false := by
  decide +kernel

theorem node_context_11_88780_1235215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235215, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1235126, by decide⟩,⟨1235173, by decide⟩,⟨1235214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88780_1235215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88780 ⟨1235215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88780
    ⟨1235215, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1235126, by decide⟩,⟨1235173, by decide⟩,⟨1235214, by decide⟩]) unmarked_context_11_88780_1235215 node_context_11_88780_1235215
  intro a
  fin_cases a
  · exact context_12_355120_1187656
  · exact context_12_355121_1235126
  · exact context_12_355122_1235173
  · exact context_12_355123_1235214

theorem selected_cut_44810 : selected 9 ⟨1235264, by decide⟩
    (prefixPartial 12 355124) = some ⟨12, 2, 0, 1235264, 355124, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_355124_1235264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355124 ⟨1235264, by decide⟩ :=
  accepted_of_selected 12 355124 ⟨1235264, by decide⟩ ⟨12, 2, 0, 1235264, 355124, 2525, 65536⟩
    (by decide) selected_cut_44810

theorem selected_cut_44811 : selected 9 ⟨1235301, by decide⟩
    (prefixPartial 12 355125) = some ⟨12, 2, 0, 1235301, 355125, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_355125_1235301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355125 ⟨1235301, by decide⟩ :=
  accepted_of_selected 12 355125 ⟨1235301, by decide⟩ ⟨12, 2, 0, 1235301, 355125, 2281, 65536⟩
    (by decide) selected_cut_44811

theorem selected_cut_44812 : selected 9 ⟨1235337, by decide⟩
    (prefixPartial 12 355126) = some ⟨12, 2, 0, 1235337, 355126, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_355126_1235337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355126 ⟨1235337, by decide⟩ :=
  accepted_of_selected 12 355126 ⟨1235337, by decide⟩ ⟨12, 2, 0, 1235337, 355126, 2353, 65536⟩
    (by decide) selected_cut_44812

theorem selected_cut_44813 : selected 9 ⟨1235377, by decide⟩
    (prefixPartial 12 355127) = some ⟨12, 2, 0, 1235377, 355127, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_355127_1235377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355127 ⟨1235377, by decide⟩ :=
  accepted_of_selected 12 355127 ⟨1235377, by decide⟩ ⟨12, 2, 0, 1235377, 355127, 2337, 65536⟩
    (by decide) selected_cut_44813

theorem unmarked_context_11_88781_1235378 : frontier 10 ⟨1235378, by decide⟩
    (prefixCache 11 88781) (prefixPartial 11 88781) = false := by
  decide +kernel

theorem node_context_11_88781_1235378 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235378, by decide⟩ =
    .split (coordinate 11) (![⟨1235264, by decide⟩,⟨1235301, by decide⟩,⟨1235337, by decide⟩,⟨1235377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88781_1235378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88781 ⟨1235378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88781
    ⟨1235378, by decide⟩ (by decide) (![⟨1235264, by decide⟩,⟨1235301, by decide⟩,⟨1235337, by decide⟩,⟨1235377, by decide⟩]) unmarked_context_11_88781_1235378 node_context_11_88781_1235378
  intro a
  fin_cases a
  · exact context_12_355124_1235264
  · exact context_12_355125_1235301
  · exact context_12_355126_1235337
  · exact context_12_355127_1235377

theorem selected_cut_44814 : selected 9 ⟨1235426, by decide⟩
    (prefixPartial 12 355128) = some ⟨12, 2, 0, 1235426, 355128, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_355128_1235426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355128 ⟨1235426, by decide⟩ :=
  accepted_of_selected 12 355128 ⟨1235426, by decide⟩ ⟨12, 2, 0, 1235426, 355128, 2617, 65536⟩
    (by decide) selected_cut_44814

theorem selected_cut_44815 : selected 9 ⟨1235467, by decide⟩
    (prefixPartial 12 355129) = some ⟨12, 2, 0, 1235467, 355129, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_355129_1235467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355129 ⟨1235467, by decide⟩ :=
  accepted_of_selected 12 355129 ⟨1235467, by decide⟩ ⟨12, 2, 0, 1235467, 355129, 2425, 65536⟩
    (by decide) selected_cut_44815

theorem selected_cut_44816 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 355130) = some ⟨12, 1, 0, 662655, 355130, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355130_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355130 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 355130 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 355130, 1, 65536⟩
    (by decide) selected_cut_44816

theorem selected_cut_44817 : selected 9 ⟨1235512, by decide⟩
    (prefixPartial 12 355131) = some ⟨12, 2, 0, 1235512, 355131, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_355131_1235512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355131 ⟨1235512, by decide⟩ :=
  accepted_of_selected 12 355131 ⟨1235512, by decide⟩ ⟨12, 2, 0, 1235512, 355131, 2389, 65536⟩
    (by decide) selected_cut_44817

theorem unmarked_context_11_88782_1235513 : frontier 10 ⟨1235513, by decide⟩
    (prefixCache 11 88782) (prefixPartial 11 88782) = false := by
  decide +kernel

theorem node_context_11_88782_1235513 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235513, by decide⟩ =
    .split (coordinate 11) (![⟨1235426, by decide⟩,⟨1235467, by decide⟩,⟨662655, by decide⟩,⟨1235512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88782_1235513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88782 ⟨1235513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88782
    ⟨1235513, by decide⟩ (by decide) (![⟨1235426, by decide⟩,⟨1235467, by decide⟩,⟨662655, by decide⟩,⟨1235512, by decide⟩]) unmarked_context_11_88782_1235513 node_context_11_88782_1235513
  intro a
  fin_cases a
  · exact context_12_355128_1235426
  · exact context_12_355129_1235467
  · exact context_12_355130_662655
  · exact context_12_355131_1235512

theorem selected_cut_44818 : selected 9 ⟨1235551, by decide⟩
    (prefixPartial 12 355132) = some ⟨12, 2, 0, 1235551, 355132, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_355132_1235551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355132 ⟨1235551, by decide⟩ :=
  accepted_of_selected 12 355132 ⟨1235551, by decide⟩ ⟨12, 2, 0, 1235551, 355132, 2289, 65536⟩
    (by decide) selected_cut_44818

theorem selected_cut_44819 : selected 9 ⟨1235592, by decide⟩
    (prefixPartial 12 355133) = some ⟨12, 2, 0, 1235592, 355133, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_355133_1235592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355133 ⟨1235592, by decide⟩ :=
  accepted_of_selected 12 355133 ⟨1235592, by decide⟩ ⟨12, 2, 0, 1235592, 355133, 2085, 65536⟩
    (by decide) selected_cut_44819

theorem selected_cut_44820 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 355134) = some ⟨12, 1, 0, 762109, 355134, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355134_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355134 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 355134 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 355134, 1, 65536⟩
    (by decide) selected_cut_44820

theorem selected_cut_44821 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 355135) = some ⟨12, 1, 0, 1120582, 355135, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355135_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355135 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 355135 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 355135, 1, 65536⟩
    (by decide) selected_cut_44821

theorem unmarked_context_11_88783_1235593 : frontier 10 ⟨1235593, by decide⟩
    (prefixCache 11 88783) (prefixPartial 11 88783) = false := by
  decide +kernel

theorem node_context_11_88783_1235593 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235593, by decide⟩ =
    .split (coordinate 11) (![⟨1235551, by decide⟩,⟨1235592, by decide⟩,⟨762109, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88783_1235593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88783 ⟨1235593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88783
    ⟨1235593, by decide⟩ (by decide) (![⟨1235551, by decide⟩,⟨1235592, by decide⟩,⟨762109, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_88783_1235593 node_context_11_88783_1235593
  intro a
  fin_cases a
  · exact context_12_355132_1235551
  · exact context_12_355133_1235592
  · exact context_12_355134_762109
  · exact context_12_355135_1120582

theorem unmarked_context_10_22195_1235594 : frontier 11 ⟨1235594, by decide⟩
    (prefixCache 10 22195) (prefixPartial 10 22195) = false := by
  decide +kernel

theorem node_context_10_22195_1235594 : EJMOriginalGlobalDAGData.nodes 11 ⟨1235594, by decide⟩ =
    .split (coordinate 10) (![⟨1235215, by decide⟩,⟨1235378, by decide⟩,⟨1235513, by decide⟩,⟨1235593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22195_1235594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22195 ⟨1235594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22195
    ⟨1235594, by decide⟩ (by decide) (![⟨1235215, by decide⟩,⟨1235378, by decide⟩,⟨1235513, by decide⟩,⟨1235593, by decide⟩]) unmarked_context_10_22195_1235594 node_context_10_22195_1235594
  intro a
  fin_cases a
  · exact context_11_88780_1235215
  · exact context_11_88781_1235378
  · exact context_11_88782_1235513
  · exact context_11_88783_1235593

theorem unmarked_context_9_5548_1235595 : frontier 12 ⟨1235595, by decide⟩
    (prefixCache 9 5548) (prefixPartial 9 5548) = false := by
  decide +kernel

theorem node_context_9_5548_1235595 : EJMOriginalGlobalDAGData.nodes 12 ⟨1235595, by decide⟩ =
    .split (coordinate 9) (![⟨1234099, by decide⟩,⟨1234712, by decide⟩,⟨1235087, by decide⟩,⟨1235594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5548_1235595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5548 ⟨1235595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5548
    ⟨1235595, by decide⟩ (by decide) (![⟨1234099, by decide⟩,⟨1234712, by decide⟩,⟨1235087, by decide⟩,⟨1235594, by decide⟩]) unmarked_context_9_5548_1235595 node_context_9_5548_1235595
  intro a
  fin_cases a
  · exact context_10_22192_1234099
  · exact context_10_22193_1234712
  · exact context_10_22194_1235087
  · exact context_10_22195_1235594

theorem selected_cut_44822 : selected 10 ⟨1235651, by decide⟩
    (prefixPartial 11 88784) = some ⟨11, 2, 0, 1235651, 88784, 3549, 262144⟩ := by
  decide +kernel

theorem context_11_88784_1235651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88784 ⟨1235651, by decide⟩ :=
  accepted_of_selected 11 88784 ⟨1235651, by decide⟩ ⟨11, 2, 0, 1235651, 88784, 3549, 262144⟩
    (by decide) selected_cut_44822

theorem selected_cut_44823 : selected 9 ⟨1235674, by decide⟩
    (prefixPartial 12 355140) = some ⟨12, 2, 0, 1235674, 355140, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_355140_1235674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355140 ⟨1235674, by decide⟩ :=
  accepted_of_selected 12 355140 ⟨1235674, by decide⟩ ⟨12, 2, 0, 1235674, 355140, 1605, 65536⟩
    (by decide) selected_cut_44823

theorem selected_cut_44824 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355141) = some ⟨12, 1, 0, 896706, 355141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355141_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355141 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355141 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355141, 1, 65536⟩
    (by decide) selected_cut_44824

theorem selected_cut_44825 : selected 9 ⟨1235695, by decide⟩
    (prefixPartial 12 355142) = some ⟨12, 2, 0, 1235695, 355142, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_355142_1235695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355142 ⟨1235695, by decide⟩ :=
  accepted_of_selected 12 355142 ⟨1235695, by decide⟩ ⟨12, 2, 0, 1235695, 355142, 1457, 65536⟩
    (by decide) selected_cut_44825

theorem selected_cut_44826 : selected 9 ⟨1235719, by decide⟩
    (prefixPartial 12 355143) = some ⟨12, 2, 0, 1235719, 355143, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_355143_1235719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355143 ⟨1235719, by decide⟩ :=
  accepted_of_selected 12 355143 ⟨1235719, by decide⟩ ⟨12, 2, 0, 1235719, 355143, 1565, 65536⟩
    (by decide) selected_cut_44826

theorem unmarked_context_11_88785_1235720 : frontier 10 ⟨1235720, by decide⟩
    (prefixCache 11 88785) (prefixPartial 11 88785) = false := by
  decide +kernel

theorem node_context_11_88785_1235720 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235720, by decide⟩ =
    .split (coordinate 11) (![⟨1235674, by decide⟩,⟨896706, by decide⟩,⟨1235695, by decide⟩,⟨1235719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88785_1235720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88785 ⟨1235720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88785
    ⟨1235720, by decide⟩ (by decide) (![⟨1235674, by decide⟩,⟨896706, by decide⟩,⟨1235695, by decide⟩,⟨1235719, by decide⟩]) unmarked_context_11_88785_1235720 node_context_11_88785_1235720
  intro a
  fin_cases a
  · exact context_12_355140_1235674
  · exact context_12_355141_896706
  · exact context_12_355142_1235695
  · exact context_12_355143_1235719

theorem selected_cut_44827 : selected 9 ⟨1235744, by decide⟩
    (prefixPartial 12 355144) = some ⟨12, 2, 0, 1235744, 355144, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_355144_1235744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355144 ⟨1235744, by decide⟩ :=
  accepted_of_selected 12 355144 ⟨1235744, by decide⟩ ⟨12, 2, 0, 1235744, 355144, 1709, 65536⟩
    (by decide) selected_cut_44827

theorem selected_cut_44828 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355145) = some ⟨12, 1, 0, 896706, 355145, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355145_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355145 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355145 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355145, 1, 65536⟩
    (by decide) selected_cut_44828

theorem selected_cut_44829 : selected 9 ⟨1235770, by decide⟩
    (prefixPartial 12 355146) = some ⟨12, 2, 0, 1235770, 355146, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_355146_1235770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355146 ⟨1235770, by decide⟩ :=
  accepted_of_selected 12 355146 ⟨1235770, by decide⟩ ⟨12, 2, 0, 1235770, 355146, 1589, 65536⟩
    (by decide) selected_cut_44829

theorem selected_cut_44830 : selected 9 ⟨1235797, by decide⟩
    (prefixPartial 12 355147) = some ⟨12, 2, 0, 1235797, 355147, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_355147_1235797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355147 ⟨1235797, by decide⟩ :=
  accepted_of_selected 12 355147 ⟨1235797, by decide⟩ ⟨12, 2, 0, 1235797, 355147, 1641, 65536⟩
    (by decide) selected_cut_44830

theorem unmarked_context_11_88786_1235798 : frontier 10 ⟨1235798, by decide⟩
    (prefixCache 11 88786) (prefixPartial 11 88786) = false := by
  decide +kernel

theorem node_context_11_88786_1235798 : EJMOriginalGlobalDAGData.nodes 10 ⟨1235798, by decide⟩ =
    .split (coordinate 11) (![⟨1235744, by decide⟩,⟨896706, by decide⟩,⟨1235770, by decide⟩,⟨1235797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88786_1235798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88786 ⟨1235798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88786
    ⟨1235798, by decide⟩ (by decide) (![⟨1235744, by decide⟩,⟨896706, by decide⟩,⟨1235770, by decide⟩,⟨1235797, by decide⟩]) unmarked_context_11_88786_1235798 node_context_11_88786_1235798
  intro a
  fin_cases a
  · exact context_12_355144_1235744
  · exact context_12_355145_896706
  · exact context_12_355146_1235770
  · exact context_12_355147_1235797

theorem selected_cut_44831 : selected 10 ⟨1235844, by decide⟩
    (prefixPartial 11 88787) = some ⟨11, 2, 0, 1235844, 88787, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_88787_1235844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88787 ⟨1235844, by decide⟩ :=
  accepted_of_selected 11 88787 ⟨1235844, by decide⟩ ⟨11, 2, 0, 1235844, 88787, 2781, 262144⟩
    (by decide) selected_cut_44831

theorem unmarked_context_10_22196_1235845 : frontier 11 ⟨1235845, by decide⟩
    (prefixCache 10 22196) (prefixPartial 10 22196) = false := by
  decide +kernel

theorem node_context_10_22196_1235845 : EJMOriginalGlobalDAGData.nodes 11 ⟨1235845, by decide⟩ =
    .split (coordinate 10) (![⟨1235651, by decide⟩,⟨1235720, by decide⟩,⟨1235798, by decide⟩,⟨1235844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22196_1235845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22196 ⟨1235845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22196
    ⟨1235845, by decide⟩ (by decide) (![⟨1235651, by decide⟩,⟨1235720, by decide⟩,⟨1235798, by decide⟩,⟨1235844, by decide⟩]) unmarked_context_10_22196_1235845 node_context_10_22196_1235845
  intro a
  fin_cases a
  · exact context_11_88784_1235651
  · exact context_11_88785_1235720
  · exact context_11_88786_1235798
  · exact context_11_88787_1235844

theorem selected_cut_44832 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22197) = some ⟨10, 1, 0, 893098, 22197, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22197_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22197 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22197 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22197, 1, 1048576⟩
    (by decide) selected_cut_44832

theorem selected_cut_44833 : selected 10 ⟨1235898, by decide⟩
    (prefixPartial 11 88792) = some ⟨11, 2, 0, 1235898, 88792, 3709, 262144⟩ := by
  decide +kernel

theorem context_11_88792_1235898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88792 ⟨1235898, by decide⟩ :=
  accepted_of_selected 11 88792 ⟨1235898, by decide⟩ ⟨11, 2, 0, 1235898, 88792, 3709, 262144⟩
    (by decide) selected_cut_44833

theorem selected_cut_44834 : selected 10 ⟨1235948, by decide⟩
    (prefixPartial 11 88793) = some ⟨11, 2, 0, 1235948, 88793, 3621, 262144⟩ := by
  decide +kernel

theorem context_11_88793_1235948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88793 ⟨1235948, by decide⟩ :=
  accepted_of_selected 11 88793 ⟨1235948, by decide⟩ ⟨11, 2, 0, 1235948, 88793, 3621, 262144⟩
    (by decide) selected_cut_44834

theorem selected_cut_44835 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88794) = some ⟨11, 1, 0, 900587, 88794, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88794_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88794 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88794 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88794, 1, 262144⟩
    (by decide) selected_cut_44835

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
