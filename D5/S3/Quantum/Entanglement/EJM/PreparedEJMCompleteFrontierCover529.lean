/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover528
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50788 : selected 9 ⟨1454788, by decide⟩
    (prefixPartial 12 441106) = some ⟨12, 2, 0, 1454788, 441106, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_441106_1454788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441106 ⟨1454788, by decide⟩ :=
  accepted_of_selected 12 441106 ⟨1454788, by decide⟩ ⟨12, 2, 0, 1454788, 441106, 2013, 65536⟩
    (by decide) selected_cut_50788

theorem selected_cut_50789 : selected 9 ⟨1454827, by decide⟩
    (prefixPartial 12 441107) = some ⟨12, 2, 0, 1454827, 441107, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_441107_1454827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441107 ⟨1454827, by decide⟩ :=
  accepted_of_selected 12 441107 ⟨1454827, by decide⟩ ⟨12, 2, 0, 1454827, 441107, 1745, 65536⟩
    (by decide) selected_cut_50789

theorem unmarked_context_11_110276_1454828 : frontier 10 ⟨1454828, by decide⟩
    (prefixCache 11 110276) (prefixPartial 11 110276) = false := by
  decide +kernel

theorem node_context_11_110276_1454828 : EJMOriginalGlobalDAGData.nodes 10 ⟨1454828, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1454742, by decide⟩,⟨1454788, by decide⟩,⟨1454827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110276_1454828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110276 ⟨1454828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110276
    ⟨1454828, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1454742, by decide⟩,⟨1454788, by decide⟩,⟨1454827, by decide⟩]) unmarked_context_11_110276_1454828 node_context_11_110276_1454828
  intro a
  fin_cases a
  · exact context_12_441104_435790
  · exact context_12_441105_1454742
  · exact context_12_441106_1454788
  · exact context_12_441107_1454827

theorem selected_cut_50790 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 110277) = some ⟨11, 1, 0, 1192826, 110277, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110277_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110277 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 110277 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 110277, 1, 262144⟩
    (by decide) selected_cut_50790

theorem selected_cut_50791 : selected 10 ⟨1454899, by decide⟩
    (prefixPartial 11 110278) = some ⟨11, 2, 0, 1454899, 110278, 3381, 262144⟩ := by
  decide +kernel

theorem context_11_110278_1454899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110278 ⟨1454899, by decide⟩ :=
  accepted_of_selected 11 110278 ⟨1454899, by decide⟩ ⟨11, 2, 0, 1454899, 110278, 3381, 262144⟩
    (by decide) selected_cut_50791

theorem selected_cut_50792 : selected 9 ⟨1454951, by decide⟩
    (prefixPartial 12 441116) = some ⟨12, 2, 0, 1454951, 441116, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_441116_1454951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441116 ⟨1454951, by decide⟩ :=
  accepted_of_selected 12 441116 ⟨1454951, by decide⟩ ⟨12, 2, 0, 1454951, 441116, 1785, 65536⟩
    (by decide) selected_cut_50792

theorem selected_cut_50793 : selected 9 ⟨1455000, by decide⟩
    (prefixPartial 12 441117) = some ⟨12, 2, 0, 1455000, 441117, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_441117_1455000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441117 ⟨1455000, by decide⟩ :=
  accepted_of_selected 12 441117 ⟨1455000, by decide⟩ ⟨12, 2, 0, 1455000, 441117, 2001, 65536⟩
    (by decide) selected_cut_50793

theorem selected_cut_50794 : selected 9 ⟨1455041, by decide⟩
    (prefixPartial 12 441118) = some ⟨12, 2, 0, 1455041, 441118, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_441118_1455041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441118 ⟨1455041, by decide⟩ :=
  accepted_of_selected 12 441118 ⟨1455041, by decide⟩ ⟨12, 2, 0, 1455041, 441118, 1873, 65536⟩
    (by decide) selected_cut_50794

theorem selected_cut_50795 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 441119) = some ⟨12, 1, 0, 903806, 441119, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441119_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441119 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 441119 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 441119, 1, 65536⟩
    (by decide) selected_cut_50795

theorem unmarked_context_11_110279_1455042 : frontier 10 ⟨1455042, by decide⟩
    (prefixCache 11 110279) (prefixPartial 11 110279) = false := by
  decide +kernel

theorem node_context_11_110279_1455042 : EJMOriginalGlobalDAGData.nodes 10 ⟨1455042, by decide⟩ =
    .split (coordinate 11) (![⟨1454951, by decide⟩,⟨1455000, by decide⟩,⟨1455041, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110279_1455042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110279 ⟨1455042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110279
    ⟨1455042, by decide⟩ (by decide) (![⟨1454951, by decide⟩,⟨1455000, by decide⟩,⟨1455041, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_110279_1455042 node_context_11_110279_1455042
  intro a
  fin_cases a
  · exact context_12_441116_1454951
  · exact context_12_441117_1455000
  · exact context_12_441118_1455041
  · exact context_12_441119_903806

theorem unmarked_context_10_27569_1455043 : frontier 11 ⟨1455043, by decide⟩
    (prefixCache 10 27569) (prefixPartial 10 27569) = false := by
  decide +kernel

theorem node_context_10_27569_1455043 : EJMOriginalGlobalDAGData.nodes 11 ⟨1455043, by decide⟩ =
    .split (coordinate 10) (![⟨1454828, by decide⟩,⟨1192826, by decide⟩,⟨1454899, by decide⟩,⟨1455042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27569_1455043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27569 ⟨1455043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27569
    ⟨1455043, by decide⟩ (by decide) (![⟨1454828, by decide⟩,⟨1192826, by decide⟩,⟨1454899, by decide⟩,⟨1455042, by decide⟩]) unmarked_context_10_27569_1455043 node_context_10_27569_1455043
  intro a
  fin_cases a
  · exact context_11_110276_1454828
  · exact context_11_110277_1192826
  · exact context_11_110278_1454899
  · exact context_11_110279_1455042

theorem selected_cut_50796 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 441120) = some ⟨12, 1, 0, 1448897, 441120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441120_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441120 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 441120 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 441120, 1, 65536⟩
    (by decide) selected_cut_50796

theorem selected_cut_50797 : selected 9 ⟨1455079, by decide⟩
    (prefixPartial 12 441121) = some ⟨12, 2, 0, 1455079, 441121, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_441121_1455079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441121 ⟨1455079, by decide⟩ :=
  accepted_of_selected 12 441121 ⟨1455079, by decide⟩ ⟨12, 2, 0, 1455079, 441121, 1777, 65536⟩
    (by decide) selected_cut_50797

theorem selected_cut_50798 : selected 9 ⟨1455112, by decide⟩
    (prefixPartial 12 441122) = some ⟨12, 2, 0, 1455112, 441122, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_441122_1455112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441122 ⟨1455112, by decide⟩ :=
  accepted_of_selected 12 441122 ⟨1455112, by decide⟩ ⟨12, 2, 0, 1455112, 441122, 1713, 65536⟩
    (by decide) selected_cut_50798

theorem selected_cut_50799 : selected 9 ⟨1455140, by decide⟩
    (prefixPartial 12 441123) = some ⟨12, 2, 0, 1455140, 441123, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_441123_1455140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441123 ⟨1455140, by decide⟩ :=
  accepted_of_selected 12 441123 ⟨1455140, by decide⟩ ⟨12, 2, 0, 1455140, 441123, 1437, 65536⟩
    (by decide) selected_cut_50799

theorem unmarked_context_11_110280_1455141 : frontier 10 ⟨1455141, by decide⟩
    (prefixCache 11 110280) (prefixPartial 11 110280) = false := by
  decide +kernel

theorem node_context_11_110280_1455141 : EJMOriginalGlobalDAGData.nodes 10 ⟨1455141, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1455079, by decide⟩,⟨1455112, by decide⟩,⟨1455140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110280_1455141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110280 ⟨1455141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110280
    ⟨1455141, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1455079, by decide⟩,⟨1455112, by decide⟩,⟨1455140, by decide⟩]) unmarked_context_11_110280_1455141 node_context_11_110280_1455141
  intro a
  fin_cases a
  · exact context_12_441120_1448897
  · exact context_12_441121_1455079
  · exact context_12_441122_1455112
  · exact context_12_441123_1455140

theorem selected_cut_50800 : selected 10 ⟨1455196, by decide⟩
    (prefixPartial 11 110281) = some ⟨11, 2, 0, 1455196, 110281, 2945, 262144⟩ := by
  decide +kernel

theorem context_11_110281_1455196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110281 ⟨1455196, by decide⟩ :=
  accepted_of_selected 11 110281 ⟨1455196, by decide⟩ ⟨11, 2, 0, 1455196, 110281, 2945, 262144⟩
    (by decide) selected_cut_50800

theorem selected_cut_50801 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110282) = some ⟨11, 1, 0, 900587, 110282, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110282_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110282 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110282 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110282, 1, 262144⟩
    (by decide) selected_cut_50801

theorem selected_cut_50802 : selected 10 ⟨1455272, by decide⟩
    (prefixPartial 11 110283) = some ⟨11, 2, 0, 1455272, 110283, 3425, 262144⟩ := by
  decide +kernel

theorem context_11_110283_1455272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110283 ⟨1455272, by decide⟩ :=
  accepted_of_selected 11 110283 ⟨1455272, by decide⟩ ⟨11, 2, 0, 1455272, 110283, 3425, 262144⟩
    (by decide) selected_cut_50802

theorem unmarked_context_10_27570_1455273 : frontier 11 ⟨1455273, by decide⟩
    (prefixCache 10 27570) (prefixPartial 10 27570) = false := by
  decide +kernel

theorem node_context_10_27570_1455273 : EJMOriginalGlobalDAGData.nodes 11 ⟨1455273, by decide⟩ =
    .split (coordinate 10) (![⟨1455141, by decide⟩,⟨1455196, by decide⟩,⟨900587, by decide⟩,⟨1455272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27570_1455273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27570 ⟨1455273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27570
    ⟨1455273, by decide⟩ (by decide) (![⟨1455141, by decide⟩,⟨1455196, by decide⟩,⟨900587, by decide⟩,⟨1455272, by decide⟩]) unmarked_context_10_27570_1455273 node_context_10_27570_1455273
  intro a
  fin_cases a
  · exact context_11_110280_1455141
  · exact context_11_110281_1455196
  · exact context_11_110282_900587
  · exact context_11_110283_1455272

theorem selected_cut_50803 : selected 9 ⟨1367531, by decide⟩
    (prefixPartial 12 441136) = some ⟨12, 1, 0, 1367531, 441136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441136_1367531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441136 ⟨1367531, by decide⟩ :=
  accepted_of_selected 12 441136 ⟨1367531, by decide⟩ ⟨12, 1, 0, 1367531, 441136, 1, 65536⟩
    (by decide) selected_cut_50803

theorem selected_cut_50804 : selected 9 ⟨1455310, by decide⟩
    (prefixPartial 12 441137) = some ⟨12, 2, 0, 1455310, 441137, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_441137_1455310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441137 ⟨1455310, by decide⟩ :=
  accepted_of_selected 12 441137 ⟨1455310, by decide⟩ ⟨12, 2, 0, 1455310, 441137, 1669, 65536⟩
    (by decide) selected_cut_50804

theorem selected_cut_50805 : selected 9 ⟨1455342, by decide⟩
    (prefixPartial 12 441138) = some ⟨12, 2, 0, 1455342, 441138, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_441138_1455342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441138 ⟨1455342, by decide⟩ :=
  accepted_of_selected 12 441138 ⟨1455342, by decide⟩ ⟨12, 2, 0, 1455342, 441138, 1537, 65536⟩
    (by decide) selected_cut_50805

theorem selected_cut_50806 : selected 9 ⟨1455368, by decide⟩
    (prefixPartial 12 441139) = some ⟨12, 2, 0, 1455368, 441139, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_441139_1455368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441139 ⟨1455368, by decide⟩ :=
  accepted_of_selected 12 441139 ⟨1455368, by decide⟩ ⟨12, 2, 0, 1455368, 441139, 1325, 65536⟩
    (by decide) selected_cut_50806

theorem unmarked_context_11_110284_1455369 : frontier 10 ⟨1455369, by decide⟩
    (prefixCache 11 110284) (prefixPartial 11 110284) = false := by
  decide +kernel

theorem node_context_11_110284_1455369 : EJMOriginalGlobalDAGData.nodes 10 ⟨1455369, by decide⟩ =
    .split (coordinate 11) (![⟨1367531, by decide⟩,⟨1455310, by decide⟩,⟨1455342, by decide⟩,⟨1455368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110284_1455369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110284 ⟨1455369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110284
    ⟨1455369, by decide⟩ (by decide) (![⟨1367531, by decide⟩,⟨1455310, by decide⟩,⟨1455342, by decide⟩,⟨1455368, by decide⟩]) unmarked_context_11_110284_1455369 node_context_11_110284_1455369
  intro a
  fin_cases a
  · exact context_12_441136_1367531
  · exact context_12_441137_1455310
  · exact context_12_441138_1455342
  · exact context_12_441139_1455368

theorem selected_cut_50807 : selected 9 ⟨1455419, by decide⟩
    (prefixPartial 12 441140) = some ⟨12, 2, 0, 1455419, 441140, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_441140_1455419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441140 ⟨1455419, by decide⟩ :=
  accepted_of_selected 12 441140 ⟨1455419, by decide⟩ ⟨12, 2, 0, 1455419, 441140, 1605, 65536⟩
    (by decide) selected_cut_50807

theorem selected_cut_50808 : selected 9 ⟨1367070, by decide⟩
    (prefixPartial 12 441141) = some ⟨12, 1, 0, 1367070, 441141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441141_1367070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441141 ⟨1367070, by decide⟩ :=
  accepted_of_selected 12 441141 ⟨1367070, by decide⟩ ⟨12, 1, 0, 1367070, 441141, 1, 65536⟩
    (by decide) selected_cut_50808

theorem selected_cut_50809 : selected 9 ⟨1455454, by decide⟩
    (prefixPartial 12 441142) = some ⟨12, 2, 0, 1455454, 441142, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_441142_1455454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441142 ⟨1455454, by decide⟩ :=
  accepted_of_selected 12 441142 ⟨1455454, by decide⟩ ⟨12, 2, 0, 1455454, 441142, 1465, 65536⟩
    (by decide) selected_cut_50809

theorem selected_cut_50810 : selected 9 ⟨1455482, by decide⟩
    (prefixPartial 12 441143) = some ⟨12, 2, 0, 1455482, 441143, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_441143_1455482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441143 ⟨1455482, by decide⟩ :=
  accepted_of_selected 12 441143 ⟨1455482, by decide⟩ ⟨12, 2, 0, 1455482, 441143, 1333, 65536⟩
    (by decide) selected_cut_50810

theorem unmarked_context_11_110285_1455483 : frontier 10 ⟨1455483, by decide⟩
    (prefixCache 11 110285) (prefixPartial 11 110285) = false := by
  decide +kernel

theorem node_context_11_110285_1455483 : EJMOriginalGlobalDAGData.nodes 10 ⟨1455483, by decide⟩ =
    .split (coordinate 11) (![⟨1455419, by decide⟩,⟨1367070, by decide⟩,⟨1455454, by decide⟩,⟨1455482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110285_1455483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110285 ⟨1455483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110285
    ⟨1455483, by decide⟩ (by decide) (![⟨1455419, by decide⟩,⟨1367070, by decide⟩,⟨1455454, by decide⟩,⟨1455482, by decide⟩]) unmarked_context_11_110285_1455483 node_context_11_110285_1455483
  intro a
  fin_cases a
  · exact context_12_441140_1455419
  · exact context_12_441141_1367070
  · exact context_12_441142_1455454
  · exact context_12_441143_1455482

theorem selected_cut_50811 : selected 10 ⟨1455533, by decide⟩
    (prefixPartial 11 110286) = some ⟨11, 2, 0, 1455533, 110286, 2317, 262144⟩ := by
  decide +kernel

theorem context_11_110286_1455533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110286 ⟨1455533, by decide⟩ :=
  accepted_of_selected 11 110286 ⟨1455533, by decide⟩ ⟨11, 2, 0, 1455533, 110286, 2317, 262144⟩
    (by decide) selected_cut_50811

theorem selected_cut_50812 : selected 10 ⟨1453758, by decide⟩
    (prefixPartial 11 110287) = some ⟨11, 2, 0, 1453758, 110287, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110287_1453758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110287 ⟨1453758, by decide⟩ :=
  accepted_of_selected 11 110287 ⟨1453758, by decide⟩ ⟨11, 2, 0, 1453758, 110287, 5, 262144⟩
    (by decide) selected_cut_50812

theorem unmarked_context_10_27571_1455534 : frontier 11 ⟨1455534, by decide⟩
    (prefixCache 10 27571) (prefixPartial 10 27571) = false := by
  decide +kernel

theorem node_context_10_27571_1455534 : EJMOriginalGlobalDAGData.nodes 11 ⟨1455534, by decide⟩ =
    .split (coordinate 10) (![⟨1455369, by decide⟩,⟨1455483, by decide⟩,⟨1455533, by decide⟩,⟨1453758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27571_1455534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27571 ⟨1455534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27571
    ⟨1455534, by decide⟩ (by decide) (![⟨1455369, by decide⟩,⟨1455483, by decide⟩,⟨1455533, by decide⟩,⟨1453758, by decide⟩]) unmarked_context_10_27571_1455534 node_context_10_27571_1455534
  intro a
  fin_cases a
  · exact context_11_110284_1455369
  · exact context_11_110285_1455483
  · exact context_11_110286_1455533
  · exact context_11_110287_1453758

theorem unmarked_context_9_6892_1455535 : frontier 12 ⟨1455535, by decide⟩
    (prefixCache 9 6892) (prefixPartial 9 6892) = false := by
  decide +kernel

theorem node_context_9_6892_1455535 : EJMOriginalGlobalDAGData.nodes 12 ⟨1455535, by decide⟩ =
    .split (coordinate 9) (![⟨1454691, by decide⟩,⟨1455043, by decide⟩,⟨1455273, by decide⟩,⟨1455534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6892_1455535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6892 ⟨1455535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6892
    ⟨1455535, by decide⟩ (by decide) (![⟨1454691, by decide⟩,⟨1455043, by decide⟩,⟨1455273, by decide⟩,⟨1455534, by decide⟩]) unmarked_context_9_6892_1455535 node_context_9_6892_1455535
  intro a
  fin_cases a
  · exact context_10_27568_1454691
  · exact context_10_27569_1455043
  · exact context_10_27570_1455273
  · exact context_10_27571_1455534

theorem selected_cut_50813 : selected 10 ⟨1455563, by decide⟩
    (prefixPartial 11 110288) = some ⟨11, 2, 0, 1455563, 110288, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_110288_1455563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110288 ⟨1455563, by decide⟩ :=
  accepted_of_selected 11 110288 ⟨1455563, by decide⟩ ⟨11, 2, 0, 1455563, 110288, 1169, 262144⟩
    (by decide) selected_cut_50813

theorem selected_cut_50814 : selected 10 ⟨1455657, by decide⟩
    (prefixPartial 11 110289) = some ⟨11, 2, 0, 1455657, 110289, 3857, 262144⟩ := by
  decide +kernel

theorem context_11_110289_1455657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110289 ⟨1455657, by decide⟩ :=
  accepted_of_selected 11 110289 ⟨1455657, by decide⟩ ⟨11, 2, 0, 1455657, 110289, 3857, 262144⟩
    (by decide) selected_cut_50814

theorem selected_cut_50815 : selected 10 ⟨1455694, by decide⟩
    (prefixPartial 11 110290) = some ⟨11, 2, 0, 1455694, 110290, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_110290_1455694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110290 ⟨1455694, by decide⟩ :=
  accepted_of_selected 11 110290 ⟨1455694, by decide⟩ ⟨11, 2, 0, 1455694, 110290, 1989, 262144⟩
    (by decide) selected_cut_50815

theorem selected_cut_50816 : selected 10 ⟨1455765, by decide⟩
    (prefixPartial 11 110291) = some ⟨11, 2, 0, 1455765, 110291, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_110291_1455765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110291 ⟨1455765, by decide⟩ :=
  accepted_of_selected 11 110291 ⟨1455765, by decide⟩ ⟨11, 2, 0, 1455765, 110291, 2425, 262144⟩
    (by decide) selected_cut_50816

theorem unmarked_context_10_27572_1455766 : frontier 11 ⟨1455766, by decide⟩
    (prefixCache 10 27572) (prefixPartial 10 27572) = false := by
  decide +kernel

theorem node_context_10_27572_1455766 : EJMOriginalGlobalDAGData.nodes 11 ⟨1455766, by decide⟩ =
    .split (coordinate 10) (![⟨1455563, by decide⟩,⟨1455657, by decide⟩,⟨1455694, by decide⟩,⟨1455765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27572_1455766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27572 ⟨1455766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27572
    ⟨1455766, by decide⟩ (by decide) (![⟨1455563, by decide⟩,⟨1455657, by decide⟩,⟨1455694, by decide⟩,⟨1455765, by decide⟩]) unmarked_context_10_27572_1455766 node_context_10_27572_1455766
  intro a
  fin_cases a
  · exact context_11_110288_1455563
  · exact context_11_110289_1455657
  · exact context_11_110290_1455694
  · exact context_11_110291_1455765

theorem selected_cut_50817 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 27573) = some ⟨10, 1, 0, 893098, 27573, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27573_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27573 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 27573 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 27573, 1, 1048576⟩
    (by decide) selected_cut_50817

theorem selected_cut_50818 : selected 10 ⟨1455833, by decide⟩
    (prefixPartial 11 110296) = some ⟨11, 2, 0, 1455833, 110296, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_110296_1455833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110296 ⟨1455833, by decide⟩ :=
  accepted_of_selected 11 110296 ⟨1455833, by decide⟩ ⟨11, 2, 0, 1455833, 110296, 2189, 262144⟩
    (by decide) selected_cut_50818

theorem selected_cut_50819 : selected 10 ⟨1455877, by decide⟩
    (prefixPartial 11 110297) = some ⟨11, 2, 0, 1455877, 110297, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_110297_1455877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110297 ⟨1455877, by decide⟩ :=
  accepted_of_selected 11 110297 ⟨1455877, by decide⟩ ⟨11, 2, 0, 1455877, 110297, 2493, 262144⟩
    (by decide) selected_cut_50819

theorem selected_cut_50820 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110298) = some ⟨11, 1, 0, 900587, 110298, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110298_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110298 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110298 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110298, 1, 262144⟩
    (by decide) selected_cut_50820

theorem selected_cut_50821 : selected 10 ⟨1455911, by decide⟩
    (prefixPartial 11 110299) = some ⟨11, 2, 0, 1455911, 110299, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_110299_1455911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110299 ⟨1455911, by decide⟩ :=
  accepted_of_selected 11 110299 ⟨1455911, by decide⟩ ⟨11, 2, 0, 1455911, 110299, 1541, 262144⟩
    (by decide) selected_cut_50821

theorem unmarked_context_10_27574_1455912 : frontier 11 ⟨1455912, by decide⟩
    (prefixCache 10 27574) (prefixPartial 10 27574) = false := by
  decide +kernel

theorem node_context_10_27574_1455912 : EJMOriginalGlobalDAGData.nodes 11 ⟨1455912, by decide⟩ =
    .split (coordinate 10) (![⟨1455833, by decide⟩,⟨1455877, by decide⟩,⟨900587, by decide⟩,⟨1455911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27574_1455912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27574 ⟨1455912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27574
    ⟨1455912, by decide⟩ (by decide) (![⟨1455833, by decide⟩,⟨1455877, by decide⟩,⟨900587, by decide⟩,⟨1455911, by decide⟩]) unmarked_context_10_27574_1455912 node_context_10_27574_1455912
  intro a
  fin_cases a
  · exact context_11_110296_1455833
  · exact context_11_110297_1455877
  · exact context_11_110298_900587
  · exact context_11_110299_1455911

theorem selected_cut_50822 : selected 10 ⟨1455941, by decide⟩
    (prefixPartial 11 110300) = some ⟨11, 2, 0, 1455941, 110300, 1557, 262144⟩ := by
  decide +kernel

theorem context_11_110300_1455941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110300 ⟨1455941, by decide⟩ :=
  accepted_of_selected 11 110300 ⟨1455941, by decide⟩ ⟨11, 2, 0, 1455941, 110300, 1557, 262144⟩
    (by decide) selected_cut_50822

theorem selected_cut_50823 : selected 10 ⟨1455986, by decide⟩
    (prefixPartial 11 110301) = some ⟨11, 2, 0, 1455986, 110301, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_110301_1455986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110301 ⟨1455986, by decide⟩ :=
  accepted_of_selected 11 110301 ⟨1455986, by decide⟩ ⟨11, 2, 0, 1455986, 110301, 2341, 262144⟩
    (by decide) selected_cut_50823

theorem selected_cut_50824 : selected 10 ⟨1456013, by decide⟩
    (prefixPartial 11 110302) = some ⟨11, 2, 0, 1456013, 110302, 1197, 262144⟩ := by
  decide +kernel

theorem context_11_110302_1456013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110302 ⟨1456013, by decide⟩ :=
  accepted_of_selected 11 110302 ⟨1456013, by decide⟩ ⟨11, 2, 0, 1456013, 110302, 1197, 262144⟩
    (by decide) selected_cut_50824

theorem selected_cut_50825 : selected 10 ⟨1454188, by decide⟩
    (prefixPartial 11 110303) = some ⟨11, 2, 0, 1454188, 110303, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110303_1454188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110303 ⟨1454188, by decide⟩ :=
  accepted_of_selected 11 110303 ⟨1454188, by decide⟩ ⟨11, 2, 0, 1454188, 110303, 5, 262144⟩
    (by decide) selected_cut_50825

theorem unmarked_context_10_27575_1456014 : frontier 11 ⟨1456014, by decide⟩
    (prefixCache 10 27575) (prefixPartial 10 27575) = false := by
  decide +kernel

theorem node_context_10_27575_1456014 : EJMOriginalGlobalDAGData.nodes 11 ⟨1456014, by decide⟩ =
    .split (coordinate 10) (![⟨1455941, by decide⟩,⟨1455986, by decide⟩,⟨1456013, by decide⟩,⟨1454188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27575_1456014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27575 ⟨1456014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27575
    ⟨1456014, by decide⟩ (by decide) (![⟨1455941, by decide⟩,⟨1455986, by decide⟩,⟨1456013, by decide⟩,⟨1454188, by decide⟩]) unmarked_context_10_27575_1456014 node_context_10_27575_1456014
  intro a
  fin_cases a
  · exact context_11_110300_1455941
  · exact context_11_110301_1455986
  · exact context_11_110302_1456013
  · exact context_11_110303_1454188

theorem unmarked_context_9_6893_1456015 : frontier 12 ⟨1456015, by decide⟩
    (prefixCache 9 6893) (prefixPartial 9 6893) = false := by
  decide +kernel

theorem node_context_9_6893_1456015 : EJMOriginalGlobalDAGData.nodes 12 ⟨1456015, by decide⟩ =
    .split (coordinate 9) (![⟨1455766, by decide⟩,⟨893098, by decide⟩,⟨1455912, by decide⟩,⟨1456014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6893_1456015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6893 ⟨1456015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6893
    ⟨1456015, by decide⟩ (by decide) (![⟨1455766, by decide⟩,⟨893098, by decide⟩,⟨1455912, by decide⟩,⟨1456014, by decide⟩]) unmarked_context_9_6893_1456015 node_context_9_6893_1456015
  intro a
  fin_cases a
  · exact context_10_27572_1455766
  · exact context_10_27573_893098
  · exact context_10_27574_1455912
  · exact context_10_27575_1456014

theorem selected_cut_50826 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 110304) = some ⟨11, 1, 0, 1375697, 110304, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110304_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110304 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 110304 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 110304, 1, 262144⟩
    (by decide) selected_cut_50826

theorem selected_cut_50827 : selected 10 ⟨1456048, by decide⟩
    (prefixPartial 11 110305) = some ⟨11, 2, 0, 1456048, 110305, 1393, 262144⟩ := by
  decide +kernel

theorem context_11_110305_1456048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110305 ⟨1456048, by decide⟩ :=
  accepted_of_selected 11 110305 ⟨1456048, by decide⟩ ⟨11, 2, 0, 1456048, 110305, 1393, 262144⟩
    (by decide) selected_cut_50827

theorem selected_cut_50828 : selected 10 ⟨1456092, by decide⟩
    (prefixPartial 11 110306) = some ⟨11, 2, 0, 1456092, 110306, 1725, 262144⟩ := by
  decide +kernel

theorem context_11_110306_1456092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110306 ⟨1456092, by decide⟩ :=
  accepted_of_selected 11 110306 ⟨1456092, by decide⟩ ⟨11, 2, 0, 1456092, 110306, 1725, 262144⟩
    (by decide) selected_cut_50828

theorem selected_cut_50829 : selected 10 ⟨1456119, by decide⟩
    (prefixPartial 11 110307) = some ⟨11, 2, 0, 1456119, 110307, 1265, 262144⟩ := by
  decide +kernel

theorem context_11_110307_1456119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110307 ⟨1456119, by decide⟩ :=
  accepted_of_selected 11 110307 ⟨1456119, by decide⟩ ⟨11, 2, 0, 1456119, 110307, 1265, 262144⟩
    (by decide) selected_cut_50829

theorem unmarked_context_10_27576_1456120 : frontier 11 ⟨1456120, by decide⟩
    (prefixCache 10 27576) (prefixPartial 10 27576) = false := by
  decide +kernel

theorem node_context_10_27576_1456120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1456120, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1456048, by decide⟩,⟨1456092, by decide⟩,⟨1456119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27576_1456120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27576 ⟨1456120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27576
    ⟨1456120, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1456048, by decide⟩,⟨1456092, by decide⟩,⟨1456119, by decide⟩]) unmarked_context_10_27576_1456120 node_context_10_27576_1456120
  intro a
  fin_cases a
  · exact context_11_110304_1375697
  · exact context_11_110305_1456048
  · exact context_11_110306_1456092
  · exact context_11_110307_1456119

theorem selected_cut_50830 : selected 11 ⟨1456198, by decide⟩
    (prefixPartial 10 27577) = some ⟨10, 2, 0, 1456198, 27577, 3369, 1048576⟩ := by
  decide +kernel

theorem context_10_27577_1456198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27577 ⟨1456198, by decide⟩ :=
  accepted_of_selected 10 27577 ⟨1456198, by decide⟩ ⟨10, 2, 0, 1456198, 27577, 3369, 1048576⟩
    (by decide) selected_cut_50830

theorem selected_cut_50831 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 27578) = some ⟨10, 2, 0, 1432895, 27578, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_27578_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27578 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 27578 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 27578, 5, 1048576⟩
    (by decide) selected_cut_50831

theorem selected_cut_50832 : selected 11 ⟨1456257, by decide⟩
    (prefixPartial 10 27579) = some ⟨10, 2, 0, 1456257, 27579, 2645, 1048576⟩ := by
  decide +kernel

theorem context_10_27579_1456257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27579 ⟨1456257, by decide⟩ :=
  accepted_of_selected 10 27579 ⟨1456257, by decide⟩ ⟨10, 2, 0, 1456257, 27579, 2645, 1048576⟩
    (by decide) selected_cut_50832

theorem unmarked_context_9_6894_1456258 : frontier 12 ⟨1456258, by decide⟩
    (prefixCache 9 6894) (prefixPartial 9 6894) = false := by
  decide +kernel

theorem node_context_9_6894_1456258 : EJMOriginalGlobalDAGData.nodes 12 ⟨1456258, by decide⟩ =
    .split (coordinate 9) (![⟨1456120, by decide⟩,⟨1456198, by decide⟩,⟨1432895, by decide⟩,⟨1456257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6894_1456258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6894 ⟨1456258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6894
    ⟨1456258, by decide⟩ (by decide) (![⟨1456120, by decide⟩,⟨1456198, by decide⟩,⟨1432895, by decide⟩,⟨1456257, by decide⟩]) unmarked_context_9_6894_1456258 node_context_9_6894_1456258
  intro a
  fin_cases a
  · exact context_10_27576_1456120
  · exact context_10_27577_1456198
  · exact context_10_27578_1432895
  · exact context_10_27579_1456257

theorem selected_cut_50833 : selected 12 ⟨1456364, by decide⟩
    (prefixPartial 9 6895) = some ⟨9, 2, 0, 1456364, 6895, 3433, 4194304⟩ := by
  decide +kernel

theorem context_9_6895_1456364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6895 ⟨1456364, by decide⟩ :=
  accepted_of_selected 9 6895 ⟨1456364, by decide⟩ ⟨9, 2, 0, 1456364, 6895, 3433, 4194304⟩
    (by decide) selected_cut_50833

theorem unmarked_context_8_1723_1456365 : frontier 13 ⟨1456365, by decide⟩
    (prefixCache 8 1723) (prefixPartial 8 1723) = false := by
  decide +kernel

theorem node_context_8_1723_1456365 : EJMOriginalGlobalDAGData.nodes 13 ⟨1456365, by decide⟩ =
    .split (coordinate 8) (![⟨1455535, by decide⟩,⟨1456015, by decide⟩,⟨1456258, by decide⟩,⟨1456364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1723_1456365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1723 ⟨1456365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1723
    ⟨1456365, by decide⟩ (by decide) (![⟨1455535, by decide⟩,⟨1456015, by decide⟩,⟨1456258, by decide⟩,⟨1456364, by decide⟩]) unmarked_context_8_1723_1456365 node_context_8_1723_1456365
  intro a
  fin_cases a
  · exact context_9_6892_1455535
  · exact context_9_6893_1456015
  · exact context_9_6894_1456258
  · exact context_9_6895_1456364

theorem unmarked_context_7_430_1456366 : frontier 14 ⟨1456366, by decide⟩
    (prefixCache 7 430) (prefixPartial 7 430) = false := by
  decide +kernel

theorem node_context_7_430_1456366 : EJMOriginalGlobalDAGData.nodes 14 ⟨1456366, by decide⟩ =
    .split (coordinate 7) (![⟨1450487, by decide⟩,⟨1452755, by decide⟩,⟨1454555, by decide⟩,⟨1456365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_430_1456366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 430 ⟨1456366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 430
    ⟨1456366, by decide⟩ (by decide) (![⟨1450487, by decide⟩,⟨1452755, by decide⟩,⟨1454555, by decide⟩,⟨1456365, by decide⟩]) unmarked_context_7_430_1456366 node_context_7_430_1456366
  intro a
  fin_cases a
  · exact context_8_1720_1450487
  · exact context_8_1721_1452755
  · exact context_8_1722_1454555
  · exact context_8_1723_1456365

theorem selected_cut_50834 : selected 11 ⟨1456499, by decide⟩
    (prefixPartial 10 27584) = some ⟨10, 2, 0, 1456499, 27584, 2933, 1048576⟩ := by
  decide +kernel

theorem context_10_27584_1456499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27584 ⟨1456499, by decide⟩ :=
  accepted_of_selected 10 27584 ⟨1456499, by decide⟩ ⟨10, 2, 0, 1456499, 27584, 2933, 1048576⟩
    (by decide) selected_cut_50834

theorem selected_cut_50835 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 441360) = some ⟨12, 1, 0, 435790, 441360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441360_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441360 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 441360 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 441360, 1, 65536⟩
    (by decide) selected_cut_50835

theorem selected_cut_50836 : selected 9 ⟨1456565, by decide⟩
    (prefixPartial 12 441361) = some ⟨12, 2, 0, 1456565, 441361, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_441361_1456565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441361 ⟨1456565, by decide⟩ :=
  accepted_of_selected 12 441361 ⟨1456565, by decide⟩ ⟨12, 2, 0, 1456565, 441361, 2285, 65536⟩
    (by decide) selected_cut_50836

theorem selected_cut_50837 : selected 9 ⟨1456619, by decide⟩
    (prefixPartial 12 441362) = some ⟨12, 2, 0, 1456619, 441362, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_441362_1456619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441362 ⟨1456619, by decide⟩ :=
  accepted_of_selected 12 441362 ⟨1456619, by decide⟩ ⟨12, 2, 0, 1456619, 441362, 1989, 65536⟩
    (by decide) selected_cut_50837

theorem selected_cut_50838 : selected 9 ⟨1456669, by decide⟩
    (prefixPartial 12 441363) = some ⟨12, 2, 0, 1456669, 441363, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_441363_1456669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441363 ⟨1456669, by decide⟩ :=
  accepted_of_selected 12 441363 ⟨1456669, by decide⟩ ⟨12, 2, 0, 1456669, 441363, 1981, 65536⟩
    (by decide) selected_cut_50838

theorem unmarked_context_11_110340_1456670 : frontier 10 ⟨1456670, by decide⟩
    (prefixCache 11 110340) (prefixPartial 11 110340) = false := by
  decide +kernel

theorem node_context_11_110340_1456670 : EJMOriginalGlobalDAGData.nodes 10 ⟨1456670, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1456565, by decide⟩,⟨1456619, by decide⟩,⟨1456669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110340_1456670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110340 ⟨1456670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110340
    ⟨1456670, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1456565, by decide⟩,⟨1456619, by decide⟩,⟨1456669, by decide⟩]) unmarked_context_11_110340_1456670 node_context_11_110340_1456670
  intro a
  fin_cases a
  · exact context_12_441360_435790
  · exact context_12_441361_1456565
  · exact context_12_441362_1456619
  · exact context_12_441363_1456669

theorem selected_cut_50839 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 110341) = some ⟨11, 1, 0, 1241271, 110341, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110341_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110341 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 110341 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 110341, 1, 262144⟩
    (by decide) selected_cut_50839

theorem selected_cut_50840 : selected 10 ⟨1456789, by decide⟩
    (prefixPartial 11 110342) = some ⟨11, 2, 0, 1456789, 110342, 4033, 262144⟩ := by
  decide +kernel

theorem context_11_110342_1456789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110342 ⟨1456789, by decide⟩ :=
  accepted_of_selected 11 110342 ⟨1456789, by decide⟩ ⟨11, 2, 0, 1456789, 110342, 4033, 262144⟩
    (by decide) selected_cut_50840

theorem selected_cut_50841 : selected 10 ⟨1456882, by decide⟩
    (prefixPartial 11 110343) = some ⟨11, 2, 0, 1456882, 110343, 3677, 262144⟩ := by
  decide +kernel

theorem context_11_110343_1456882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110343 ⟨1456882, by decide⟩ :=
  accepted_of_selected 11 110343 ⟨1456882, by decide⟩ ⟨11, 2, 0, 1456882, 110343, 3677, 262144⟩
    (by decide) selected_cut_50841

theorem unmarked_context_10_27585_1456883 : frontier 11 ⟨1456883, by decide⟩
    (prefixCache 10 27585) (prefixPartial 10 27585) = false := by
  decide +kernel

theorem node_context_10_27585_1456883 : EJMOriginalGlobalDAGData.nodes 11 ⟨1456883, by decide⟩ =
    .split (coordinate 10) (![⟨1456670, by decide⟩,⟨1241271, by decide⟩,⟨1456789, by decide⟩,⟨1456882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27585_1456883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27585 ⟨1456883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27585
    ⟨1456883, by decide⟩ (by decide) (![⟨1456670, by decide⟩,⟨1241271, by decide⟩,⟨1456789, by decide⟩,⟨1456882, by decide⟩]) unmarked_context_10_27585_1456883 node_context_10_27585_1456883
  intro a
  fin_cases a
  · exact context_11_110340_1456670
  · exact context_11_110341_1241271
  · exact context_11_110342_1456789
  · exact context_11_110343_1456882

theorem selected_cut_50842 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 441376) = some ⟨12, 1, 0, 1448897, 441376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441376_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441376 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 441376 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 441376, 1, 65536⟩
    (by decide) selected_cut_50842

theorem selected_cut_50843 : selected 9 ⟨1456942, by decide⟩
    (prefixPartial 12 441377) = some ⟨12, 2, 0, 1456942, 441377, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_441377_1456942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441377 ⟨1456942, by decide⟩ :=
  accepted_of_selected 12 441377 ⟨1456942, by decide⟩ ⟨12, 2, 0, 1456942, 441377, 1837, 65536⟩
    (by decide) selected_cut_50843

theorem selected_cut_50844 : selected 9 ⟨1456995, by decide⟩
    (prefixPartial 12 441378) = some ⟨12, 2, 0, 1456995, 441378, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_441378_1456995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441378 ⟨1456995, by decide⟩ :=
  accepted_of_selected 12 441378 ⟨1456995, by decide⟩ ⟨12, 2, 0, 1456995, 441378, 1737, 65536⟩
    (by decide) selected_cut_50844

theorem selected_cut_50845 : selected 9 ⟨1457046, by decide⟩
    (prefixPartial 12 441379) = some ⟨12, 2, 0, 1457046, 441379, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_441379_1457046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441379 ⟨1457046, by decide⟩ :=
  accepted_of_selected 12 441379 ⟨1457046, by decide⟩ ⟨12, 2, 0, 1457046, 441379, 1593, 65536⟩
    (by decide) selected_cut_50845

theorem unmarked_context_11_110344_1457047 : frontier 10 ⟨1457047, by decide⟩
    (prefixCache 11 110344) (prefixPartial 11 110344) = false := by
  decide +kernel

theorem node_context_11_110344_1457047 : EJMOriginalGlobalDAGData.nodes 10 ⟨1457047, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1456942, by decide⟩,⟨1456995, by decide⟩,⟨1457046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110344_1457047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110344 ⟨1457047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110344
    ⟨1457047, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1456942, by decide⟩,⟨1456995, by decide⟩,⟨1457046, by decide⟩]) unmarked_context_11_110344_1457047 node_context_11_110344_1457047
  intro a
  fin_cases a
  · exact context_12_441376_1448897
  · exact context_12_441377_1456942
  · exact context_12_441378_1456995
  · exact context_12_441379_1457046

theorem selected_cut_50846 : selected 10 ⟨1457158, by decide⟩
    (prefixPartial 11 110345) = some ⟨11, 2, 0, 1457158, 110345, 3305, 262144⟩ := by
  decide +kernel

theorem context_11_110345_1457158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110345 ⟨1457158, by decide⟩ :=
  accepted_of_selected 11 110345 ⟨1457158, by decide⟩ ⟨11, 2, 0, 1457158, 110345, 3305, 262144⟩
    (by decide) selected_cut_50846

theorem selected_cut_50847 : selected 10 ⟨1457203, by decide⟩
    (prefixPartial 11 110346) = some ⟨11, 2, 0, 1457203, 110346, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_110346_1457203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110346 ⟨1457203, by decide⟩ :=
  accepted_of_selected 11 110346 ⟨1457203, by decide⟩ ⟨11, 2, 0, 1457203, 110346, 1413, 262144⟩
    (by decide) selected_cut_50847

theorem selected_cut_50848 : selected 10 ⟨1457278, by decide⟩
    (prefixPartial 11 110347) = some ⟨11, 2, 0, 1457278, 110347, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_110347_1457278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110347 ⟨1457278, by decide⟩ :=
  accepted_of_selected 11 110347 ⟨1457278, by decide⟩ ⟨11, 2, 0, 1457278, 110347, 2717, 262144⟩
    (by decide) selected_cut_50848

theorem unmarked_context_10_27586_1457279 : frontier 11 ⟨1457279, by decide⟩
    (prefixCache 10 27586) (prefixPartial 10 27586) = false := by
  decide +kernel

theorem node_context_10_27586_1457279 : EJMOriginalGlobalDAGData.nodes 11 ⟨1457279, by decide⟩ =
    .split (coordinate 10) (![⟨1457047, by decide⟩,⟨1457158, by decide⟩,⟨1457203, by decide⟩,⟨1457278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27586_1457279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27586 ⟨1457279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27586
    ⟨1457279, by decide⟩ (by decide) (![⟨1457047, by decide⟩,⟨1457158, by decide⟩,⟨1457203, by decide⟩,⟨1457278, by decide⟩]) unmarked_context_10_27586_1457279 node_context_10_27586_1457279
  intro a
  fin_cases a
  · exact context_11_110344_1457047
  · exact context_11_110345_1457158
  · exact context_11_110346_1457203
  · exact context_11_110347_1457278

theorem selected_cut_50849 : selected 10 ⟨1457427, by decide⟩
    (prefixPartial 11 110348) = some ⟨11, 2, 0, 1457427, 110348, 3633, 262144⟩ := by
  decide +kernel

theorem context_11_110348_1457427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110348 ⟨1457427, by decide⟩ :=
  accepted_of_selected 11 110348 ⟨1457427, by decide⟩ ⟨11, 2, 0, 1457427, 110348, 3633, 262144⟩
    (by decide) selected_cut_50849

theorem selected_cut_50850 : selected 10 ⟨1457523, by decide⟩
    (prefixPartial 11 110349) = some ⟨11, 2, 0, 1457523, 110349, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_110349_1457523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110349 ⟨1457523, by decide⟩ :=
  accepted_of_selected 11 110349 ⟨1457523, by decide⟩ ⟨11, 2, 0, 1457523, 110349, 2329, 262144⟩
    (by decide) selected_cut_50850

theorem selected_cut_50851 : selected 10 ⟨1457584, by decide⟩
    (prefixPartial 11 110350) = some ⟨11, 2, 0, 1457584, 110350, 1837, 262144⟩ := by
  decide +kernel

theorem context_11_110350_1457584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110350 ⟨1457584, by decide⟩ :=
  accepted_of_selected 11 110350 ⟨1457584, by decide⟩ ⟨11, 2, 0, 1457584, 110350, 1837, 262144⟩
    (by decide) selected_cut_50851

theorem selected_cut_50852 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 110351) = some ⟨11, 1, 0, 977886, 110351, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110351_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110351 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 110351 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 110351, 1, 262144⟩
    (by decide) selected_cut_50852

theorem unmarked_context_10_27587_1457585 : frontier 11 ⟨1457585, by decide⟩
    (prefixCache 10 27587) (prefixPartial 10 27587) = false := by
  decide +kernel

theorem node_context_10_27587_1457585 : EJMOriginalGlobalDAGData.nodes 11 ⟨1457585, by decide⟩ =
    .split (coordinate 10) (![⟨1457427, by decide⟩,⟨1457523, by decide⟩,⟨1457584, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27587_1457585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27587 ⟨1457585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27587
    ⟨1457585, by decide⟩ (by decide) (![⟨1457427, by decide⟩,⟨1457523, by decide⟩,⟨1457584, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_27587_1457585 node_context_10_27587_1457585
  intro a
  fin_cases a
  · exact context_11_110348_1457427
  · exact context_11_110349_1457523
  · exact context_11_110350_1457584
  · exact context_11_110351_977886

theorem unmarked_context_9_6896_1457586 : frontier 12 ⟨1457586, by decide⟩
    (prefixCache 9 6896) (prefixPartial 9 6896) = false := by
  decide +kernel

theorem node_context_9_6896_1457586 : EJMOriginalGlobalDAGData.nodes 12 ⟨1457586, by decide⟩ =
    .split (coordinate 9) (![⟨1456499, by decide⟩,⟨1456883, by decide⟩,⟨1457279, by decide⟩,⟨1457585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6896_1457586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6896 ⟨1457586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6896
    ⟨1457586, by decide⟩ (by decide) (![⟨1456499, by decide⟩,⟨1456883, by decide⟩,⟨1457279, by decide⟩,⟨1457585, by decide⟩]) unmarked_context_9_6896_1457586 node_context_9_6896_1457586
  intro a
  fin_cases a
  · exact context_10_27584_1456499
  · exact context_10_27585_1456883
  · exact context_10_27586_1457279
  · exact context_10_27587_1457585

theorem selected_cut_50853 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 27588) = some ⟨10, 1, 0, 793297, 27588, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27588_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27588 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 27588 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 27588, 1, 1048576⟩
    (by decide) selected_cut_50853

theorem selected_cut_50854 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 27589) = some ⟨10, 1, 0, 893098, 27589, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27589_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27589 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 27589 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 27589, 1, 1048576⟩
    (by decide) selected_cut_50854

theorem selected_cut_50855 : selected 10 ⟨1457654, by decide⟩
    (prefixPartial 11 110360) = some ⟨11, 2, 0, 1457654, 110360, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_110360_1457654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110360 ⟨1457654, by decide⟩ :=
  accepted_of_selected 11 110360 ⟨1457654, by decide⟩ ⟨11, 2, 0, 1457654, 110360, 1525, 262144⟩
    (by decide) selected_cut_50855

theorem selected_cut_50856 : selected 10 ⟨1457738, by decide⟩
    (prefixPartial 11 110361) = some ⟨11, 2, 0, 1457738, 110361, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_110361_1457738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110361 ⟨1457738, by decide⟩ :=
  accepted_of_selected 11 110361 ⟨1457738, by decide⟩ ⟨11, 2, 0, 1457738, 110361, 2109, 262144⟩
    (by decide) selected_cut_50856

theorem selected_cut_50857 : selected 10 ⟨1457766, by decide⟩
    (prefixPartial 11 110362) = some ⟨11, 2, 0, 1457766, 110362, 165, 262144⟩ := by
  decide +kernel

theorem context_11_110362_1457766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110362 ⟨1457766, by decide⟩ :=
  accepted_of_selected 11 110362 ⟨1457766, by decide⟩ ⟨11, 2, 0, 1457766, 110362, 165, 262144⟩
    (by decide) selected_cut_50857

theorem selected_cut_50858 : selected 10 ⟨1457795, by decide⟩
    (prefixPartial 11 110363) = some ⟨11, 2, 0, 1457795, 110363, 1085, 262144⟩ := by
  decide +kernel

theorem context_11_110363_1457795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110363 ⟨1457795, by decide⟩ :=
  accepted_of_selected 11 110363 ⟨1457795, by decide⟩ ⟨11, 2, 0, 1457795, 110363, 1085, 262144⟩
    (by decide) selected_cut_50858

theorem unmarked_context_10_27590_1457796 : frontier 11 ⟨1457796, by decide⟩
    (prefixCache 10 27590) (prefixPartial 10 27590) = false := by
  decide +kernel

theorem node_context_10_27590_1457796 : EJMOriginalGlobalDAGData.nodes 11 ⟨1457796, by decide⟩ =
    .split (coordinate 10) (![⟨1457654, by decide⟩,⟨1457738, by decide⟩,⟨1457766, by decide⟩,⟨1457795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27590_1457796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27590 ⟨1457796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27590
    ⟨1457796, by decide⟩ (by decide) (![⟨1457654, by decide⟩,⟨1457738, by decide⟩,⟨1457766, by decide⟩,⟨1457795, by decide⟩]) unmarked_context_10_27590_1457796 node_context_10_27590_1457796
  intro a
  fin_cases a
  · exact context_11_110360_1457654
  · exact context_11_110361_1457738
  · exact context_11_110362_1457766
  · exact context_11_110363_1457795

theorem selected_cut_50859 : selected 11 ⟨1457904, by decide⟩
    (prefixPartial 10 27591) = some ⟨10, 2, 0, 1457904, 27591, 2701, 1048576⟩ := by
  decide +kernel

theorem context_10_27591_1457904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27591 ⟨1457904, by decide⟩ :=
  accepted_of_selected 10 27591 ⟨1457904, by decide⟩ ⟨10, 2, 0, 1457904, 27591, 2701, 1048576⟩
    (by decide) selected_cut_50859

theorem unmarked_context_9_6897_1457905 : frontier 12 ⟨1457905, by decide⟩
    (prefixCache 9 6897) (prefixPartial 9 6897) = false := by
  decide +kernel

theorem node_context_9_6897_1457905 : EJMOriginalGlobalDAGData.nodes 12 ⟨1457905, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1457796, by decide⟩,⟨1457904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6897_1457905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6897 ⟨1457905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6897
    ⟨1457905, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1457796, by decide⟩,⟨1457904, by decide⟩]) unmarked_context_9_6897_1457905 node_context_9_6897_1457905
  intro a
  fin_cases a
  · exact context_10_27588_793297
  · exact context_10_27589_893098
  · exact context_10_27590_1457796
  · exact context_10_27591_1457904

theorem selected_cut_50860 : selected 12 ⟨1457941, by decide⟩
    (prefixPartial 9 6898) = some ⟨9, 2, 0, 1457941, 6898, 613, 4194304⟩ := by
  decide +kernel

theorem context_9_6898_1457941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6898 ⟨1457941, by decide⟩ :=
  accepted_of_selected 9 6898 ⟨1457941, by decide⟩ ⟨9, 2, 0, 1457941, 6898, 613, 4194304⟩
    (by decide) selected_cut_50860

theorem selected_cut_50861 : selected 12 ⟨1457970, by decide⟩
    (prefixPartial 9 6899) = some ⟨9, 2, 0, 1457970, 6899, 289, 4194304⟩ := by
  decide +kernel

theorem context_9_6899_1457970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6899 ⟨1457970, by decide⟩ :=
  accepted_of_selected 9 6899 ⟨1457970, by decide⟩ ⟨9, 2, 0, 1457970, 6899, 289, 4194304⟩
    (by decide) selected_cut_50861

theorem unmarked_context_8_1724_1457971 : frontier 13 ⟨1457971, by decide⟩
    (prefixCache 8 1724) (prefixPartial 8 1724) = false := by
  decide +kernel

theorem node_context_8_1724_1457971 : EJMOriginalGlobalDAGData.nodes 13 ⟨1457971, by decide⟩ =
    .split (coordinate 8) (![⟨1457586, by decide⟩,⟨1457905, by decide⟩,⟨1457941, by decide⟩,⟨1457970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1724_1457971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1724 ⟨1457971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1724
    ⟨1457971, by decide⟩ (by decide) (![⟨1457586, by decide⟩,⟨1457905, by decide⟩,⟨1457941, by decide⟩,⟨1457970, by decide⟩]) unmarked_context_8_1724_1457971 node_context_8_1724_1457971
  intro a
  fin_cases a
  · exact context_9_6896_1457586
  · exact context_9_6897_1457905
  · exact context_9_6898_1457941
  · exact context_9_6899_1457970

theorem selected_cut_50862 : selected 11 ⟨1458072, by decide⟩
    (prefixPartial 10 27600) = some ⟨10, 2, 0, 1458072, 27600, 2209, 1048576⟩ := by
  decide +kernel

theorem context_10_27600_1458072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27600 ⟨1458072, by decide⟩ :=
  accepted_of_selected 10 27600 ⟨1458072, by decide⟩ ⟨10, 2, 0, 1458072, 27600, 2209, 1048576⟩
    (by decide) selected_cut_50862

theorem selected_cut_50863 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 441616) = some ⟨12, 1, 0, 435790, 441616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441616_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441616 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 441616 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 441616, 1, 65536⟩
    (by decide) selected_cut_50863

theorem selected_cut_50864 : selected 9 ⟨1458135, by decide⟩
    (prefixPartial 12 441617) = some ⟨12, 2, 0, 1458135, 441617, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_441617_1458135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441617 ⟨1458135, by decide⟩ :=
  accepted_of_selected 12 441617 ⟨1458135, by decide⟩ ⟨12, 2, 0, 1458135, 441617, 1877, 65536⟩
    (by decide) selected_cut_50864

theorem selected_cut_50865 : selected 9 ⟨1458181, by decide⟩
    (prefixPartial 12 441618) = some ⟨12, 2, 0, 1458181, 441618, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_441618_1458181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441618 ⟨1458181, by decide⟩ :=
  accepted_of_selected 12 441618 ⟨1458181, by decide⟩ ⟨12, 2, 0, 1458181, 441618, 1773, 65536⟩
    (by decide) selected_cut_50865

theorem selected_cut_50866 : selected 9 ⟨1458225, by decide⟩
    (prefixPartial 12 441619) = some ⟨12, 2, 0, 1458225, 441619, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_441619_1458225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441619 ⟨1458225, by decide⟩ :=
  accepted_of_selected 12 441619 ⟨1458225, by decide⟩ ⟨12, 2, 0, 1458225, 441619, 1709, 65536⟩
    (by decide) selected_cut_50866

theorem unmarked_context_11_110404_1458226 : frontier 10 ⟨1458226, by decide⟩
    (prefixCache 11 110404) (prefixPartial 11 110404) = false := by
  decide +kernel

theorem node_context_11_110404_1458226 : EJMOriginalGlobalDAGData.nodes 10 ⟨1458226, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1458135, by decide⟩,⟨1458181, by decide⟩,⟨1458225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110404_1458226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110404 ⟨1458226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110404
    ⟨1458226, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1458135, by decide⟩,⟨1458181, by decide⟩,⟨1458225, by decide⟩]) unmarked_context_11_110404_1458226 node_context_11_110404_1458226
  intro a
  fin_cases a
  · exact context_12_441616_435790
  · exact context_12_441617_1458135
  · exact context_12_441618_1458181
  · exact context_12_441619_1458225

theorem selected_cut_50867 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 110405) = some ⟨11, 1, 0, 1241271, 110405, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110405_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110405 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 110405 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 110405, 1, 262144⟩
    (by decide) selected_cut_50867

theorem selected_cut_50868 : selected 10 ⟨1458307, by decide⟩
    (prefixPartial 11 110406) = some ⟨11, 2, 0, 1458307, 110406, 3089, 262144⟩ := by
  decide +kernel

theorem context_11_110406_1458307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110406 ⟨1458307, by decide⟩ :=
  accepted_of_selected 11 110406 ⟨1458307, by decide⟩ ⟨11, 2, 0, 1458307, 110406, 3089, 262144⟩
    (by decide) selected_cut_50868

theorem selected_cut_50869 : selected 10 ⟨1458372, by decide⟩
    (prefixPartial 11 110407) = some ⟨11, 2, 0, 1458372, 110407, 2925, 262144⟩ := by
  decide +kernel

theorem context_11_110407_1458372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110407 ⟨1458372, by decide⟩ :=
  accepted_of_selected 11 110407 ⟨1458372, by decide⟩ ⟨11, 2, 0, 1458372, 110407, 2925, 262144⟩
    (by decide) selected_cut_50869

theorem unmarked_context_10_27601_1458373 : frontier 11 ⟨1458373, by decide⟩
    (prefixCache 10 27601) (prefixPartial 10 27601) = false := by
  decide +kernel

theorem node_context_10_27601_1458373 : EJMOriginalGlobalDAGData.nodes 11 ⟨1458373, by decide⟩ =
    .split (coordinate 10) (![⟨1458226, by decide⟩,⟨1241271, by decide⟩,⟨1458307, by decide⟩,⟨1458372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27601_1458373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27601 ⟨1458373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27601
    ⟨1458373, by decide⟩ (by decide) (![⟨1458226, by decide⟩,⟨1241271, by decide⟩,⟨1458307, by decide⟩,⟨1458372, by decide⟩]) unmarked_context_10_27601_1458373 node_context_10_27601_1458373
  intro a
  fin_cases a
  · exact context_11_110404_1458226
  · exact context_11_110405_1241271
  · exact context_11_110406_1458307
  · exact context_11_110407_1458372

theorem selected_cut_50870 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 441632) = some ⟨12, 1, 0, 1448897, 441632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441632_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441632 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 441632 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 441632, 1, 65536⟩
    (by decide) selected_cut_50870

theorem selected_cut_50871 : selected 9 ⟨1458423, by decide⟩
    (prefixPartial 12 441633) = some ⟨12, 2, 0, 1458423, 441633, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_441633_1458423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441633 ⟨1458423, by decide⟩ :=
  accepted_of_selected 12 441633 ⟨1458423, by decide⟩ ⟨12, 2, 0, 1458423, 441633, 1617, 65536⟩
    (by decide) selected_cut_50871

theorem selected_cut_50872 : selected 9 ⟨1458466, by decide⟩
    (prefixPartial 12 441634) = some ⟨12, 2, 0, 1458466, 441634, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_441634_1458466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441634 ⟨1458466, by decide⟩ :=
  accepted_of_selected 12 441634 ⟨1458466, by decide⟩ ⟨12, 2, 0, 1458466, 441634, 1605, 65536⟩
    (by decide) selected_cut_50872

theorem selected_cut_50873 : selected 9 ⟨1458509, by decide⟩
    (prefixPartial 12 441635) = some ⟨12, 2, 0, 1458509, 441635, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_441635_1458509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441635 ⟨1458509, by decide⟩ :=
  accepted_of_selected 12 441635 ⟨1458509, by decide⟩ ⟨12, 2, 0, 1458509, 441635, 1481, 65536⟩
    (by decide) selected_cut_50873

theorem unmarked_context_11_110408_1458510 : frontier 10 ⟨1458510, by decide⟩
    (prefixCache 11 110408) (prefixPartial 11 110408) = false := by
  decide +kernel

theorem node_context_11_110408_1458510 : EJMOriginalGlobalDAGData.nodes 10 ⟨1458510, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1458423, by decide⟩,⟨1458466, by decide⟩,⟨1458509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110408_1458510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110408 ⟨1458510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110408
    ⟨1458510, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1458423, by decide⟩,⟨1458466, by decide⟩,⟨1458509, by decide⟩]) unmarked_context_11_110408_1458510 node_context_11_110408_1458510
  intro a
  fin_cases a
  · exact context_12_441632_1448897
  · exact context_12_441633_1458423
  · exact context_12_441634_1458466
  · exact context_12_441635_1458509

theorem selected_cut_50874 : selected 10 ⟨1458595, by decide⟩
    (prefixPartial 11 110409) = some ⟨11, 2, 0, 1458595, 110409, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_110409_1458595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110409 ⟨1458595, by decide⟩ :=
  accepted_of_selected 11 110409 ⟨1458595, by decide⟩ ⟨11, 2, 0, 1458595, 110409, 2833, 262144⟩
    (by decide) selected_cut_50874

theorem selected_cut_50875 : selected 10 ⟨1458596, by decide⟩
    (prefixPartial 11 110410) = some ⟨11, 2, 0, 1458596, 110410, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110410_1458596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110410 ⟨1458596, by decide⟩ :=
  accepted_of_selected 11 110410 ⟨1458596, by decide⟩ ⟨11, 2, 0, 1458596, 110410, 5, 262144⟩
    (by decide) selected_cut_50875

theorem selected_cut_50876 : selected 10 ⟨1458664, by decide⟩
    (prefixPartial 11 110411) = some ⟨11, 2, 0, 1458664, 110411, 2381, 262144⟩ := by
  decide +kernel

theorem context_11_110411_1458664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110411 ⟨1458664, by decide⟩ :=
  accepted_of_selected 11 110411 ⟨1458664, by decide⟩ ⟨11, 2, 0, 1458664, 110411, 2381, 262144⟩
    (by decide) selected_cut_50876

theorem unmarked_context_10_27602_1458665 : frontier 11 ⟨1458665, by decide⟩
    (prefixCache 10 27602) (prefixPartial 10 27602) = false := by
  decide +kernel

theorem node_context_10_27602_1458665 : EJMOriginalGlobalDAGData.nodes 11 ⟨1458665, by decide⟩ =
    .split (coordinate 10) (![⟨1458510, by decide⟩,⟨1458595, by decide⟩,⟨1458596, by decide⟩,⟨1458664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27602_1458665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27602 ⟨1458665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27602
    ⟨1458665, by decide⟩ (by decide) (![⟨1458510, by decide⟩,⟨1458595, by decide⟩,⟨1458596, by decide⟩,⟨1458664, by decide⟩]) unmarked_context_10_27602_1458665 node_context_10_27602_1458665
  intro a
  fin_cases a
  · exact context_11_110408_1458510
  · exact context_11_110409_1458595
  · exact context_11_110410_1458596
  · exact context_11_110411_1458664

theorem selected_cut_50877 : selected 10 ⟨1458776, by decide⟩
    (prefixPartial 11 110412) = some ⟨11, 2, 0, 1458776, 110412, 3173, 262144⟩ := by
  decide +kernel

theorem context_11_110412_1458776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110412 ⟨1458776, by decide⟩ :=
  accepted_of_selected 11 110412 ⟨1458776, by decide⟩ ⟨11, 2, 0, 1458776, 110412, 3173, 262144⟩
    (by decide) selected_cut_50877

theorem selected_cut_50878 : selected 10 ⟨1458847, by decide⟩
    (prefixPartial 11 110413) = some ⟨11, 2, 0, 1458847, 110413, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_110413_1458847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110413 ⟨1458847, by decide⟩ :=
  accepted_of_selected 11 110413 ⟨1458847, by decide⟩ ⟨11, 2, 0, 1458847, 110413, 1997, 262144⟩
    (by decide) selected_cut_50878

theorem selected_cut_50879 : selected 10 ⟨1458891, by decide⟩
    (prefixPartial 11 110414) = some ⟨11, 2, 0, 1458891, 110414, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_110414_1458891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110414 ⟨1458891, by decide⟩ :=
  accepted_of_selected 11 110414 ⟨1458891, by decide⟩ ⟨11, 2, 0, 1458891, 110414, 1581, 262144⟩
    (by decide) selected_cut_50879

theorem selected_cut_50880 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 110415) = some ⟨11, 1, 0, 977886, 110415, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110415_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110415 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 110415 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 110415, 1, 262144⟩
    (by decide) selected_cut_50880

theorem unmarked_context_10_27603_1458892 : frontier 11 ⟨1458892, by decide⟩
    (prefixCache 10 27603) (prefixPartial 10 27603) = false := by
  decide +kernel

theorem node_context_10_27603_1458892 : EJMOriginalGlobalDAGData.nodes 11 ⟨1458892, by decide⟩ =
    .split (coordinate 10) (![⟨1458776, by decide⟩,⟨1458847, by decide⟩,⟨1458891, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27603_1458892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27603 ⟨1458892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27603
    ⟨1458892, by decide⟩ (by decide) (![⟨1458776, by decide⟩,⟨1458847, by decide⟩,⟨1458891, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_27603_1458892 node_context_10_27603_1458892
  intro a
  fin_cases a
  · exact context_11_110412_1458776
  · exact context_11_110413_1458847
  · exact context_11_110414_1458891
  · exact context_11_110415_977886

theorem unmarked_context_9_6900_1458893 : frontier 12 ⟨1458893, by decide⟩
    (prefixCache 9 6900) (prefixPartial 9 6900) = false := by
  decide +kernel

theorem node_context_9_6900_1458893 : EJMOriginalGlobalDAGData.nodes 12 ⟨1458893, by decide⟩ =
    .split (coordinate 9) (![⟨1458072, by decide⟩,⟨1458373, by decide⟩,⟨1458665, by decide⟩,⟨1458892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6900_1458893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6900 ⟨1458893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6900
    ⟨1458893, by decide⟩ (by decide) (![⟨1458072, by decide⟩,⟨1458373, by decide⟩,⟨1458665, by decide⟩,⟨1458892, by decide⟩]) unmarked_context_9_6900_1458893 node_context_9_6900_1458893
  intro a
  fin_cases a
  · exact context_10_27600_1458072
  · exact context_10_27601_1458373
  · exact context_10_27602_1458665
  · exact context_10_27603_1458892

theorem selected_cut_50881 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 27604) = some ⟨10, 1, 0, 793297, 27604, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27604_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27604 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 27604 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 27604, 1, 1048576⟩
    (by decide) selected_cut_50881

theorem selected_cut_50882 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 27605) = some ⟨10, 1, 0, 893098, 27605, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27605_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27605 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 27605 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 27605, 1, 1048576⟩
    (by decide) selected_cut_50882

theorem selected_cut_50883 : selected 10 ⟨1458943, by decide⟩
    (prefixPartial 11 110424) = some ⟨11, 2, 0, 1458943, 110424, 1469, 262144⟩ := by
  decide +kernel

theorem context_11_110424_1458943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110424 ⟨1458943, by decide⟩ :=
  accepted_of_selected 11 110424 ⟨1458943, by decide⟩ ⟨11, 2, 0, 1458943, 110424, 1469, 262144⟩
    (by decide) selected_cut_50883

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
