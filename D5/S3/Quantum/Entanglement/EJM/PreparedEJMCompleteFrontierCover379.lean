/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover378
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36388 : selected 9 ⟨963784, by decide⟩
    (prefixPartial 12 288619) = some ⟨12, 2, 0, 963784, 288619, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_288619_963784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288619 ⟨963784, by decide⟩ :=
  accepted_of_selected 12 288619 ⟨963784, by decide⟩ ⟨12, 2, 0, 963784, 288619, 2045, 65536⟩
    (by decide) selected_cut_36388

theorem unmarked_context_11_72154_963785 : frontier 10 ⟨963785, by decide⟩
    (prefixCache 11 72154) (prefixPartial 11 72154) = false := by
  decide +kernel

theorem node_context_11_72154_963785 : EJMOriginalGlobalDAGData.nodes 10 ⟨963785, by decide⟩ =
    .split (coordinate 11) (![⟨963715, by decide⟩,⟨896706, by decide⟩,⟨963745, by decide⟩,⟨963784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72154_963785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72154 ⟨963785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72154
    ⟨963785, by decide⟩ (by decide) (![⟨963715, by decide⟩,⟨896706, by decide⟩,⟨963745, by decide⟩,⟨963784, by decide⟩]) unmarked_context_11_72154_963785 node_context_11_72154_963785
  intro a
  fin_cases a
  · exact context_12_288616_963715
  · exact context_12_288617_896706
  · exact context_12_288618_963745
  · exact context_12_288619_963784

theorem selected_cut_36389 : selected 10 ⟨963855, by decide⟩
    (prefixPartial 11 72155) = some ⟨11, 2, 0, 963855, 72155, 3869, 262144⟩ := by
  decide +kernel

theorem context_11_72155_963855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72155 ⟨963855, by decide⟩ :=
  accepted_of_selected 11 72155 ⟨963855, by decide⟩ ⟨11, 2, 0, 963855, 72155, 3869, 262144⟩
    (by decide) selected_cut_36389

theorem unmarked_context_10_18038_963856 : frontier 11 ⟨963856, by decide⟩
    (prefixCache 10 18038) (prefixPartial 10 18038) = false := by
  decide +kernel

theorem node_context_10_18038_963856 : EJMOriginalGlobalDAGData.nodes 11 ⟨963856, by decide⟩ =
    .split (coordinate 10) (![⟨963609, by decide⟩,⟨963681, by decide⟩,⟨963785, by decide⟩,⟨963855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18038_963856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18038 ⟨963856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18038
    ⟨963856, by decide⟩ (by decide) (![⟨963609, by decide⟩,⟨963681, by decide⟩,⟨963785, by decide⟩,⟨963855, by decide⟩]) unmarked_context_10_18038_963856 node_context_10_18038_963856
  intro a
  fin_cases a
  · exact context_11_72152_963609
  · exact context_11_72153_963681
  · exact context_11_72154_963785
  · exact context_11_72155_963855

theorem selected_cut_36390 : selected 9 ⟨963900, by decide⟩
    (prefixPartial 12 288624) = some ⟨12, 2, 0, 963900, 288624, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_288624_963900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288624 ⟨963900, by decide⟩ :=
  accepted_of_selected 12 288624 ⟨963900, by decide⟩ ⟨12, 2, 0, 963900, 288624, 2181, 65536⟩
    (by decide) selected_cut_36390

theorem selected_cut_36391 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288625) = some ⟨12, 1, 0, 896706, 288625, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288625_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288625 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288625 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288625, 1, 65536⟩
    (by decide) selected_cut_36391

theorem selected_cut_36392 : selected 9 ⟨963962, by decide⟩
    (prefixPartial 12 288626) = some ⟨12, 2, 0, 963962, 288626, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_288626_963962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288626 ⟨963962, by decide⟩ :=
  accepted_of_selected 12 288626 ⟨963962, by decide⟩ ⟨12, 2, 0, 963962, 288626, 2557, 65536⟩
    (by decide) selected_cut_36392

theorem selected_cut_36393 : selected 9 ⟨963997, by decide⟩
    (prefixPartial 12 288627) = some ⟨12, 2, 0, 963997, 288627, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_288627_963997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288627 ⟨963997, by decide⟩ :=
  accepted_of_selected 12 288627 ⟨963997, by decide⟩ ⟨12, 2, 0, 963997, 288627, 2217, 65536⟩
    (by decide) selected_cut_36393

theorem unmarked_context_11_72156_963998 : frontier 10 ⟨963998, by decide⟩
    (prefixCache 11 72156) (prefixPartial 11 72156) = false := by
  decide +kernel

theorem node_context_11_72156_963998 : EJMOriginalGlobalDAGData.nodes 10 ⟨963998, by decide⟩ =
    .split (coordinate 11) (![⟨963900, by decide⟩,⟨896706, by decide⟩,⟨963962, by decide⟩,⟨963997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72156_963998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72156 ⟨963998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72156
    ⟨963998, by decide⟩ (by decide) (![⟨963900, by decide⟩,⟨896706, by decide⟩,⟨963962, by decide⟩,⟨963997, by decide⟩]) unmarked_context_11_72156_963998 node_context_11_72156_963998
  intro a
  fin_cases a
  · exact context_12_288624_963900
  · exact context_12_288625_896706
  · exact context_12_288626_963962
  · exact context_12_288627_963997

theorem selected_cut_36394 : selected 9 ⟨964020, by decide⟩
    (prefixPartial 12 288628) = some ⟨12, 2, 0, 964020, 288628, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_288628_964020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288628 ⟨964020, by decide⟩ :=
  accepted_of_selected 12 288628 ⟨964020, by decide⟩ ⟨12, 2, 0, 964020, 288628, 1617, 65536⟩
    (by decide) selected_cut_36394

theorem selected_cut_36395 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288629) = some ⟨12, 1, 0, 896706, 288629, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288629_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288629 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288629 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288629, 1, 65536⟩
    (by decide) selected_cut_36395

theorem selected_cut_36396 : selected 9 ⟨964047, by decide⟩
    (prefixPartial 12 288630) = some ⟨12, 2, 0, 964047, 288630, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_288630_964047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288630 ⟨964047, by decide⟩ :=
  accepted_of_selected 12 288630 ⟨964047, by decide⟩ ⟨12, 2, 0, 964047, 288630, 1781, 65536⟩
    (by decide) selected_cut_36396

theorem selected_cut_36397 : selected 9 ⟨964077, by decide⟩
    (prefixPartial 12 288631) = some ⟨12, 2, 0, 964077, 288631, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_288631_964077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288631 ⟨964077, by decide⟩ :=
  accepted_of_selected 12 288631 ⟨964077, by decide⟩ ⟨12, 2, 0, 964077, 288631, 1649, 65536⟩
    (by decide) selected_cut_36397

theorem unmarked_context_11_72157_964078 : frontier 10 ⟨964078, by decide⟩
    (prefixCache 11 72157) (prefixPartial 11 72157) = false := by
  decide +kernel

theorem node_context_11_72157_964078 : EJMOriginalGlobalDAGData.nodes 10 ⟨964078, by decide⟩ =
    .split (coordinate 11) (![⟨964020, by decide⟩,⟨896706, by decide⟩,⟨964047, by decide⟩,⟨964077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72157_964078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72157 ⟨964078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72157
    ⟨964078, by decide⟩ (by decide) (![⟨964020, by decide⟩,⟨896706, by decide⟩,⟨964047, by decide⟩,⟨964077, by decide⟩]) unmarked_context_11_72157_964078 node_context_11_72157_964078
  intro a
  fin_cases a
  · exact context_12_288628_964020
  · exact context_12_288629_896706
  · exact context_12_288630_964047
  · exact context_12_288631_964077

theorem selected_cut_36398 : selected 9 ⟨964117, by decide⟩
    (prefixPartial 12 288632) = some ⟨12, 2, 0, 964117, 288632, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_288632_964117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288632 ⟨964117, by decide⟩ :=
  accepted_of_selected 12 288632 ⟨964117, by decide⟩ ⟨12, 2, 0, 964117, 288632, 2121, 65536⟩
    (by decide) selected_cut_36398

theorem selected_cut_36399 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288633) = some ⟨12, 1, 0, 896706, 288633, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288633_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288633 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288633 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288633, 1, 65536⟩
    (by decide) selected_cut_36399

theorem selected_cut_36400 : selected 9 ⟨964150, by decide⟩
    (prefixPartial 12 288634) = some ⟨12, 2, 0, 964150, 288634, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_288634_964150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288634 ⟨964150, by decide⟩ :=
  accepted_of_selected 12 288634 ⟨964150, by decide⟩ ⟨12, 2, 0, 964150, 288634, 1997, 65536⟩
    (by decide) selected_cut_36400

theorem selected_cut_36401 : selected 9 ⟨964182, by decide⟩
    (prefixPartial 12 288635) = some ⟨12, 2, 0, 964182, 288635, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_288635_964182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288635 ⟨964182, by decide⟩ :=
  accepted_of_selected 12 288635 ⟨964182, by decide⟩ ⟨12, 2, 0, 964182, 288635, 1945, 65536⟩
    (by decide) selected_cut_36401

theorem unmarked_context_11_72158_964183 : frontier 10 ⟨964183, by decide⟩
    (prefixCache 11 72158) (prefixPartial 11 72158) = false := by
  decide +kernel

theorem node_context_11_72158_964183 : EJMOriginalGlobalDAGData.nodes 10 ⟨964183, by decide⟩ =
    .split (coordinate 11) (![⟨964117, by decide⟩,⟨896706, by decide⟩,⟨964150, by decide⟩,⟨964182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72158_964183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72158 ⟨964183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72158
    ⟨964183, by decide⟩ (by decide) (![⟨964117, by decide⟩,⟨896706, by decide⟩,⟨964150, by decide⟩,⟨964182, by decide⟩]) unmarked_context_11_72158_964183 node_context_11_72158_964183
  intro a
  fin_cases a
  · exact context_12_288632_964117
  · exact context_12_288633_896706
  · exact context_12_288634_964150
  · exact context_12_288635_964182

theorem selected_cut_36402 : selected 10 ⟨964245, by decide⟩
    (prefixPartial 11 72159) = some ⟨11, 2, 0, 964245, 72159, 3645, 262144⟩ := by
  decide +kernel

theorem context_11_72159_964245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72159 ⟨964245, by decide⟩ :=
  accepted_of_selected 11 72159 ⟨964245, by decide⟩ ⟨11, 2, 0, 964245, 72159, 3645, 262144⟩
    (by decide) selected_cut_36402

theorem unmarked_context_10_18039_964246 : frontier 11 ⟨964246, by decide⟩
    (prefixCache 10 18039) (prefixPartial 10 18039) = false := by
  decide +kernel

theorem node_context_10_18039_964246 : EJMOriginalGlobalDAGData.nodes 11 ⟨964246, by decide⟩ =
    .split (coordinate 10) (![⟨963998, by decide⟩,⟨964078, by decide⟩,⟨964183, by decide⟩,⟨964245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18039_964246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18039 ⟨964246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18039
    ⟨964246, by decide⟩ (by decide) (![⟨963998, by decide⟩,⟨964078, by decide⟩,⟨964183, by decide⟩,⟨964245, by decide⟩]) unmarked_context_10_18039_964246 node_context_10_18039_964246
  intro a
  fin_cases a
  · exact context_11_72156_963998
  · exact context_11_72157_964078
  · exact context_11_72158_964183
  · exact context_11_72159_964245

theorem unmarked_context_9_4509_964247 : frontier 12 ⟨964247, by decide⟩
    (prefixCache 9 4509) (prefixPartial 9 4509) = false := by
  decide +kernel

theorem node_context_9_4509_964247 : EJMOriginalGlobalDAGData.nodes 12 ⟨964247, by decide⟩ =
    .split (coordinate 9) (![⟨963478, by decide⟩,⟨893098, by decide⟩,⟨963856, by decide⟩,⟨964246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4509_964247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4509 ⟨964247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4509
    ⟨964247, by decide⟩ (by decide) (![⟨963478, by decide⟩,⟨893098, by decide⟩,⟨963856, by decide⟩,⟨964246, by decide⟩]) unmarked_context_9_4509_964247 node_context_9_4509_964247
  intro a
  fin_cases a
  · exact context_10_18036_963478
  · exact context_10_18037_893098
  · exact context_10_18038_963856
  · exact context_10_18039_964246

theorem selected_cut_36403 : selected 9 ⟨964286, by decide⟩
    (prefixPartial 12 288640) = some ⟨12, 2, 0, 964286, 288640, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_288640_964286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288640 ⟨964286, by decide⟩ :=
  accepted_of_selected 12 288640 ⟨964286, by decide⟩ ⟨12, 2, 0, 964286, 288640, 1993, 65536⟩
    (by decide) selected_cut_36403

theorem selected_cut_36404 : selected 9 ⟨964311, by decide⟩
    (prefixPartial 12 288641) = some ⟨12, 2, 0, 964311, 288641, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_288641_964311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288641 ⟨964311, by decide⟩ :=
  accepted_of_selected 12 288641 ⟨964311, by decide⟩ ⟨12, 2, 0, 964311, 288641, 1561, 65536⟩
    (by decide) selected_cut_36404

theorem selected_cut_36405 : selected 9 ⟨964342, by decide⟩
    (prefixPartial 12 288642) = some ⟨12, 2, 0, 964342, 288642, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_288642_964342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288642 ⟨964342, by decide⟩ :=
  accepted_of_selected 12 288642 ⟨964342, by decide⟩ ⟨12, 2, 0, 964342, 288642, 1649, 65536⟩
    (by decide) selected_cut_36405

theorem selected_cut_36406 : selected 9 ⟨964369, by decide⟩
    (prefixPartial 12 288643) = some ⟨12, 2, 0, 964369, 288643, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_288643_964369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288643 ⟨964369, by decide⟩ :=
  accepted_of_selected 12 288643 ⟨964369, by decide⟩ ⟨12, 2, 0, 964369, 288643, 1701, 65536⟩
    (by decide) selected_cut_36406

theorem unmarked_context_11_72160_964370 : frontier 10 ⟨964370, by decide⟩
    (prefixCache 11 72160) (prefixPartial 11 72160) = false := by
  decide +kernel

theorem node_context_11_72160_964370 : EJMOriginalGlobalDAGData.nodes 10 ⟨964370, by decide⟩ =
    .split (coordinate 11) (![⟨964286, by decide⟩,⟨964311, by decide⟩,⟨964342, by decide⟩,⟨964369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72160_964370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72160 ⟨964370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72160
    ⟨964370, by decide⟩ (by decide) (![⟨964286, by decide⟩,⟨964311, by decide⟩,⟨964342, by decide⟩,⟨964369, by decide⟩]) unmarked_context_11_72160_964370 node_context_11_72160_964370
  intro a
  fin_cases a
  · exact context_12_288640_964286
  · exact context_12_288641_964311
  · exact context_12_288642_964342
  · exact context_12_288643_964369

theorem selected_cut_36407 : selected 9 ⟨964405, by decide⟩
    (prefixPartial 12 288644) = some ⟨12, 2, 0, 964405, 288644, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_288644_964405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288644 ⟨964405, by decide⟩ :=
  accepted_of_selected 12 288644 ⟨964405, by decide⟩ ⟨12, 2, 0, 964405, 288644, 1829, 65536⟩
    (by decide) selected_cut_36407

theorem selected_cut_36408 : selected 9 ⟨964427, by decide⟩
    (prefixPartial 12 288645) = some ⟨12, 2, 0, 964427, 288645, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_288645_964427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288645 ⟨964427, by decide⟩ :=
  accepted_of_selected 12 288645 ⟨964427, by decide⟩ ⟨12, 2, 0, 964427, 288645, 1417, 65536⟩
    (by decide) selected_cut_36408

theorem selected_cut_36409 : selected 9 ⟨964447, by decide⟩
    (prefixPartial 12 288646) = some ⟨12, 2, 0, 964447, 288646, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_288646_964447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288646 ⟨964447, by decide⟩ :=
  accepted_of_selected 12 288646 ⟨964447, by decide⟩ ⟨12, 2, 0, 964447, 288646, 1457, 65536⟩
    (by decide) selected_cut_36409

theorem selected_cut_36410 : selected 9 ⟨964472, by decide⟩
    (prefixPartial 12 288647) = some ⟨12, 2, 0, 964472, 288647, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_288647_964472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288647 ⟨964472, by decide⟩ :=
  accepted_of_selected 12 288647 ⟨964472, by decide⟩ ⟨12, 2, 0, 964472, 288647, 1657, 65536⟩
    (by decide) selected_cut_36410

theorem unmarked_context_11_72161_964473 : frontier 10 ⟨964473, by decide⟩
    (prefixCache 11 72161) (prefixPartial 11 72161) = false := by
  decide +kernel

theorem node_context_11_72161_964473 : EJMOriginalGlobalDAGData.nodes 10 ⟨964473, by decide⟩ =
    .split (coordinate 11) (![⟨964405, by decide⟩,⟨964427, by decide⟩,⟨964447, by decide⟩,⟨964472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72161_964473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72161 ⟨964473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72161
    ⟨964473, by decide⟩ (by decide) (![⟨964405, by decide⟩,⟨964427, by decide⟩,⟨964447, by decide⟩,⟨964472, by decide⟩]) unmarked_context_11_72161_964473 node_context_11_72161_964473
  intro a
  fin_cases a
  · exact context_12_288644_964405
  · exact context_12_288645_964427
  · exact context_12_288646_964447
  · exact context_12_288647_964472

theorem selected_cut_36411 : selected 9 ⟨964527, by decide⟩
    (prefixPartial 12 288648) = some ⟨12, 2, 0, 964527, 288648, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_288648_964527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288648 ⟨964527, by decide⟩ :=
  accepted_of_selected 12 288648 ⟨964527, by decide⟩ ⟨12, 2, 0, 964527, 288648, 2053, 65536⟩
    (by decide) selected_cut_36411

theorem selected_cut_36412 : selected 9 ⟨964547, by decide⟩
    (prefixPartial 12 288649) = some ⟨12, 2, 0, 964547, 288649, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_288649_964547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288649 ⟨964547, by decide⟩ :=
  accepted_of_selected 12 288649 ⟨964547, by decide⟩ ⟨12, 2, 0, 964547, 288649, 1373, 65536⟩
    (by decide) selected_cut_36412

theorem selected_cut_36413 : selected 9 ⟨964566, by decide⟩
    (prefixPartial 12 288650) = some ⟨12, 2, 0, 964566, 288650, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_288650_964566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288650 ⟨964566, by decide⟩ :=
  accepted_of_selected 12 288650 ⟨964566, by decide⟩ ⟨12, 2, 0, 964566, 288650, 1421, 65536⟩
    (by decide) selected_cut_36413

theorem selected_cut_36414 : selected 9 ⟨964594, by decide⟩
    (prefixPartial 12 288651) = some ⟨12, 2, 0, 964594, 288651, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_288651_964594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288651 ⟨964594, by decide⟩ :=
  accepted_of_selected 12 288651 ⟨964594, by decide⟩ ⟨12, 2, 0, 964594, 288651, 1573, 65536⟩
    (by decide) selected_cut_36414

theorem unmarked_context_11_72162_964595 : frontier 10 ⟨964595, by decide⟩
    (prefixCache 11 72162) (prefixPartial 11 72162) = false := by
  decide +kernel

theorem node_context_11_72162_964595 : EJMOriginalGlobalDAGData.nodes 10 ⟨964595, by decide⟩ =
    .split (coordinate 11) (![⟨964527, by decide⟩,⟨964547, by decide⟩,⟨964566, by decide⟩,⟨964594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72162_964595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72162 ⟨964595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72162
    ⟨964595, by decide⟩ (by decide) (![⟨964527, by decide⟩,⟨964547, by decide⟩,⟨964566, by decide⟩,⟨964594, by decide⟩]) unmarked_context_11_72162_964595 node_context_11_72162_964595
  intro a
  fin_cases a
  · exact context_12_288648_964527
  · exact context_12_288649_964547
  · exact context_12_288650_964566
  · exact context_12_288651_964594

theorem selected_cut_36415 : selected 10 ⟨964663, by decide⟩
    (prefixPartial 11 72163) = some ⟨11, 2, 0, 964663, 72163, 3885, 262144⟩ := by
  decide +kernel

theorem context_11_72163_964663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72163 ⟨964663, by decide⟩ :=
  accepted_of_selected 11 72163 ⟨964663, by decide⟩ ⟨11, 2, 0, 964663, 72163, 3885, 262144⟩
    (by decide) selected_cut_36415

theorem unmarked_context_10_18040_964664 : frontier 11 ⟨964664, by decide⟩
    (prefixCache 10 18040) (prefixPartial 10 18040) = false := by
  decide +kernel

theorem node_context_10_18040_964664 : EJMOriginalGlobalDAGData.nodes 11 ⟨964664, by decide⟩ =
    .split (coordinate 10) (![⟨964370, by decide⟩,⟨964473, by decide⟩,⟨964595, by decide⟩,⟨964663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18040_964664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18040 ⟨964664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18040
    ⟨964664, by decide⟩ (by decide) (![⟨964370, by decide⟩,⟨964473, by decide⟩,⟨964595, by decide⟩,⟨964663, by decide⟩]) unmarked_context_10_18040_964664 node_context_10_18040_964664
  intro a
  fin_cases a
  · exact context_11_72160_964370
  · exact context_11_72161_964473
  · exact context_11_72162_964595
  · exact context_11_72163_964663

theorem selected_cut_36416 : selected 9 ⟨964680, by decide⟩
    (prefixPartial 12 288656) = some ⟨12, 2, 0, 964680, 288656, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_288656_964680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288656 ⟨964680, by decide⟩ :=
  accepted_of_selected 12 288656 ⟨964680, by decide⟩ ⟨12, 2, 0, 964680, 288656, 1217, 65536⟩
    (by decide) selected_cut_36416

theorem selected_cut_36417 : selected 9 ⟨964697, by decide⟩
    (prefixPartial 12 288657) = some ⟨12, 2, 0, 964697, 288657, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_288657_964697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288657 ⟨964697, by decide⟩ :=
  accepted_of_selected 12 288657 ⟨964697, by decide⟩ ⟨12, 2, 0, 964697, 288657, 1157, 65536⟩
    (by decide) selected_cut_36417

theorem selected_cut_36418 : selected 9 ⟨964715, by decide⟩
    (prefixPartial 12 288658) = some ⟨12, 2, 0, 964715, 288658, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_288658_964715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288658 ⟨964715, by decide⟩ :=
  accepted_of_selected 12 288658 ⟨964715, by decide⟩ ⟨12, 2, 0, 964715, 288658, 1313, 65536⟩
    (by decide) selected_cut_36418

theorem selected_cut_36419 : selected 9 ⟨964730, by decide⟩
    (prefixPartial 12 288659) = some ⟨12, 2, 0, 964730, 288659, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_288659_964730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288659 ⟨964730, by decide⟩ :=
  accepted_of_selected 12 288659 ⟨964730, by decide⟩ ⟨12, 2, 0, 964730, 288659, 1169, 65536⟩
    (by decide) selected_cut_36419

theorem unmarked_context_11_72164_964731 : frontier 10 ⟨964731, by decide⟩
    (prefixCache 11 72164) (prefixPartial 11 72164) = false := by
  decide +kernel

theorem node_context_11_72164_964731 : EJMOriginalGlobalDAGData.nodes 10 ⟨964731, by decide⟩ =
    .split (coordinate 11) (![⟨964680, by decide⟩,⟨964697, by decide⟩,⟨964715, by decide⟩,⟨964730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72164_964731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72164 ⟨964731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72164
    ⟨964731, by decide⟩ (by decide) (![⟨964680, by decide⟩,⟨964697, by decide⟩,⟨964715, by decide⟩,⟨964730, by decide⟩]) unmarked_context_11_72164_964731 node_context_11_72164_964731
  intro a
  fin_cases a
  · exact context_12_288656_964680
  · exact context_12_288657_964697
  · exact context_12_288658_964715
  · exact context_12_288659_964730

theorem selected_cut_36420 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 72165) = some ⟨11, 1, 0, 892405, 72165, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72165_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72165 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 72165 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 72165, 1, 262144⟩
    (by decide) selected_cut_36420

theorem selected_cut_36421 : selected 9 ⟨964755, by decide⟩
    (prefixPartial 12 288664) = some ⟨12, 2, 0, 964755, 288664, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_288664_964755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288664 ⟨964755, by decide⟩ :=
  accepted_of_selected 12 288664 ⟨964755, by decide⟩ ⟨12, 2, 0, 964755, 288664, 1317, 65536⟩
    (by decide) selected_cut_36421

theorem selected_cut_36422 : selected 9 ⟨964768, by decide⟩
    (prefixPartial 12 288665) = some ⟨12, 2, 0, 964768, 288665, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_288665_964768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288665 ⟨964768, by decide⟩ :=
  accepted_of_selected 12 288665 ⟨964768, by decide⟩ ⟨12, 2, 0, 964768, 288665, 1013, 65536⟩
    (by decide) selected_cut_36422

theorem selected_cut_36423 : selected 9 ⟨964782, by decide⟩
    (prefixPartial 12 288666) = some ⟨12, 2, 0, 964782, 288666, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_288666_964782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288666 ⟨964782, by decide⟩ :=
  accepted_of_selected 12 288666 ⟨964782, by decide⟩ ⟨12, 2, 0, 964782, 288666, 1069, 65536⟩
    (by decide) selected_cut_36423

theorem selected_cut_36424 : selected 9 ⟨964804, by decide⟩
    (prefixPartial 12 288667) = some ⟨12, 2, 0, 964804, 288667, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_288667_964804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288667 ⟨964804, by decide⟩ :=
  accepted_of_selected 12 288667 ⟨964804, by decide⟩ ⟨12, 2, 0, 964804, 288667, 1197, 65536⟩
    (by decide) selected_cut_36424

theorem unmarked_context_11_72166_964805 : frontier 10 ⟨964805, by decide⟩
    (prefixCache 11 72166) (prefixPartial 11 72166) = false := by
  decide +kernel

theorem node_context_11_72166_964805 : EJMOriginalGlobalDAGData.nodes 10 ⟨964805, by decide⟩ =
    .split (coordinate 11) (![⟨964755, by decide⟩,⟨964768, by decide⟩,⟨964782, by decide⟩,⟨964804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72166_964805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72166 ⟨964805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72166
    ⟨964805, by decide⟩ (by decide) (![⟨964755, by decide⟩,⟨964768, by decide⟩,⟨964782, by decide⟩,⟨964804, by decide⟩]) unmarked_context_11_72166_964805 node_context_11_72166_964805
  intro a
  fin_cases a
  · exact context_12_288664_964755
  · exact context_12_288665_964768
  · exact context_12_288666_964782
  · exact context_12_288667_964804

theorem selected_cut_36425 : selected 10 ⟨964846, by decide⟩
    (prefixPartial 11 72167) = some ⟨11, 2, 0, 964846, 72167, 2969, 262144⟩ := by
  decide +kernel

theorem context_11_72167_964846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72167 ⟨964846, by decide⟩ :=
  accepted_of_selected 11 72167 ⟨964846, by decide⟩ ⟨11, 2, 0, 964846, 72167, 2969, 262144⟩
    (by decide) selected_cut_36425

theorem unmarked_context_10_18041_964847 : frontier 11 ⟨964847, by decide⟩
    (prefixCache 10 18041) (prefixPartial 10 18041) = false := by
  decide +kernel

theorem node_context_10_18041_964847 : EJMOriginalGlobalDAGData.nodes 11 ⟨964847, by decide⟩ =
    .split (coordinate 10) (![⟨964731, by decide⟩,⟨892405, by decide⟩,⟨964805, by decide⟩,⟨964846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18041_964847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18041 ⟨964847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18041
    ⟨964847, by decide⟩ (by decide) (![⟨964731, by decide⟩,⟨892405, by decide⟩,⟨964805, by decide⟩,⟨964846, by decide⟩]) unmarked_context_10_18041_964847 node_context_10_18041_964847
  intro a
  fin_cases a
  · exact context_11_72164_964731
  · exact context_11_72165_892405
  · exact context_11_72166_964805
  · exact context_11_72167_964846

theorem selected_cut_36426 : selected 10 ⟨964908, by decide⟩
    (prefixPartial 11 72168) = some ⟨11, 2, 0, 964908, 72168, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_72168_964908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72168 ⟨964908, by decide⟩ :=
  accepted_of_selected 11 72168 ⟨964908, by decide⟩ ⟨11, 2, 0, 964908, 72168, 3273, 262144⟩
    (by decide) selected_cut_36426

theorem selected_cut_36427 : selected 10 ⟨964939, by decide⟩
    (prefixPartial 11 72169) = some ⟨11, 2, 0, 964939, 72169, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_72169_964939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72169 ⟨964939, by decide⟩ :=
  accepted_of_selected 11 72169 ⟨964939, by decide⟩ ⟨11, 2, 0, 964939, 72169, 2565, 262144⟩
    (by decide) selected_cut_36427

theorem selected_cut_36428 : selected 10 ⟨964966, by decide⟩
    (prefixPartial 11 72170) = some ⟨11, 2, 0, 964966, 72170, 381, 262144⟩ := by
  decide +kernel

theorem context_11_72170_964966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72170 ⟨964966, by decide⟩ :=
  accepted_of_selected 11 72170 ⟨964966, by decide⟩ ⟨11, 2, 0, 964966, 72170, 381, 262144⟩
    (by decide) selected_cut_36428

theorem selected_cut_36429 : selected 10 ⟨964992, by decide⟩
    (prefixPartial 11 72171) = some ⟨11, 2, 0, 964992, 72171, 1765, 262144⟩ := by
  decide +kernel

theorem context_11_72171_964992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72171 ⟨964992, by decide⟩ :=
  accepted_of_selected 11 72171 ⟨964992, by decide⟩ ⟨11, 2, 0, 964992, 72171, 1765, 262144⟩
    (by decide) selected_cut_36429

theorem unmarked_context_10_18042_964993 : frontier 11 ⟨964993, by decide⟩
    (prefixCache 10 18042) (prefixPartial 10 18042) = false := by
  decide +kernel

theorem node_context_10_18042_964993 : EJMOriginalGlobalDAGData.nodes 11 ⟨964993, by decide⟩ =
    .split (coordinate 10) (![⟨964908, by decide⟩,⟨964939, by decide⟩,⟨964966, by decide⟩,⟨964992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18042_964993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18042 ⟨964993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18042
    ⟨964993, by decide⟩ (by decide) (![⟨964908, by decide⟩,⟨964939, by decide⟩,⟨964966, by decide⟩,⟨964992, by decide⟩]) unmarked_context_10_18042_964993 node_context_10_18042_964993
  intro a
  fin_cases a
  · exact context_11_72168_964908
  · exact context_11_72169_964939
  · exact context_11_72170_964966
  · exact context_11_72171_964992

theorem selected_cut_36430 : selected 9 ⟨965007, by decide⟩
    (prefixPartial 12 288688) = some ⟨12, 2, 0, 965007, 288688, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_288688_965007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288688 ⟨965007, by decide⟩ :=
  accepted_of_selected 12 288688 ⟨965007, by decide⟩ ⟨12, 2, 0, 965007, 288688, 1033, 65536⟩
    (by decide) selected_cut_36430

theorem selected_cut_36431 : selected 9 ⟨965027, by decide⟩
    (prefixPartial 12 288689) = some ⟨12, 2, 0, 965027, 288689, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_288689_965027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288689 ⟨965027, by decide⟩ :=
  accepted_of_selected 12 288689 ⟨965027, by decide⟩ ⟨12, 2, 0, 965027, 288689, 1037, 65536⟩
    (by decide) selected_cut_36431

theorem selected_cut_36432 : selected 9 ⟨965061, by decide⟩
    (prefixPartial 12 288690) = some ⟨12, 2, 0, 965061, 288690, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_288690_965061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288690 ⟨965061, by decide⟩ :=
  accepted_of_selected 12 288690 ⟨965061, by decide⟩ ⟨12, 2, 0, 965061, 288690, 1237, 65536⟩
    (by decide) selected_cut_36432

theorem selected_cut_36433 : selected 9 ⟨965081, by decide⟩
    (prefixPartial 12 288691) = some ⟨12, 2, 0, 965081, 288691, 929, 65536⟩ := by
  decide +kernel

theorem context_12_288691_965081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288691 ⟨965081, by decide⟩ :=
  accepted_of_selected 12 288691 ⟨965081, by decide⟩ ⟨12, 2, 0, 965081, 288691, 929, 65536⟩
    (by decide) selected_cut_36433

theorem unmarked_context_11_72172_965082 : frontier 10 ⟨965082, by decide⟩
    (prefixCache 11 72172) (prefixPartial 11 72172) = false := by
  decide +kernel

theorem node_context_11_72172_965082 : EJMOriginalGlobalDAGData.nodes 10 ⟨965082, by decide⟩ =
    .split (coordinate 11) (![⟨965007, by decide⟩,⟨965027, by decide⟩,⟨965061, by decide⟩,⟨965081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72172_965082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72172 ⟨965082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72172
    ⟨965082, by decide⟩ (by decide) (![⟨965007, by decide⟩,⟨965027, by decide⟩,⟨965061, by decide⟩,⟨965081, by decide⟩]) unmarked_context_11_72172_965082 node_context_11_72172_965082
  intro a
  fin_cases a
  · exact context_12_288688_965007
  · exact context_12_288689_965027
  · exact context_12_288690_965061
  · exact context_12_288691_965081

theorem selected_cut_36434 : selected 10 ⟨965138, by decide⟩
    (prefixPartial 11 72173) = some ⟨11, 2, 0, 965138, 72173, 3441, 262144⟩ := by
  decide +kernel

theorem context_11_72173_965138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72173 ⟨965138, by decide⟩ :=
  accepted_of_selected 11 72173 ⟨965138, by decide⟩ ⟨11, 2, 0, 965138, 72173, 3441, 262144⟩
    (by decide) selected_cut_36434

theorem selected_cut_36435 : selected 10 ⟨965194, by decide⟩
    (prefixPartial 11 72174) = some ⟨11, 2, 0, 965194, 72174, 3345, 262144⟩ := by
  decide +kernel

theorem context_11_72174_965194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72174 ⟨965194, by decide⟩ :=
  accepted_of_selected 11 72174 ⟨965194, by decide⟩ ⟨11, 2, 0, 965194, 72174, 3345, 262144⟩
    (by decide) selected_cut_36435

theorem selected_cut_36436 : selected 10 ⟨965232, by decide⟩
    (prefixPartial 11 72175) = some ⟨11, 2, 0, 965232, 72175, 2217, 262144⟩ := by
  decide +kernel

theorem context_11_72175_965232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72175 ⟨965232, by decide⟩ :=
  accepted_of_selected 11 72175 ⟨965232, by decide⟩ ⟨11, 2, 0, 965232, 72175, 2217, 262144⟩
    (by decide) selected_cut_36436

theorem unmarked_context_10_18043_965233 : frontier 11 ⟨965233, by decide⟩
    (prefixCache 10 18043) (prefixPartial 10 18043) = false := by
  decide +kernel

theorem node_context_10_18043_965233 : EJMOriginalGlobalDAGData.nodes 11 ⟨965233, by decide⟩ =
    .split (coordinate 10) (![⟨965082, by decide⟩,⟨965138, by decide⟩,⟨965194, by decide⟩,⟨965232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18043_965233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18043 ⟨965233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18043
    ⟨965233, by decide⟩ (by decide) (![⟨965082, by decide⟩,⟨965138, by decide⟩,⟨965194, by decide⟩,⟨965232, by decide⟩]) unmarked_context_10_18043_965233 node_context_10_18043_965233
  intro a
  fin_cases a
  · exact context_11_72172_965082
  · exact context_11_72173_965138
  · exact context_11_72174_965194
  · exact context_11_72175_965232

theorem unmarked_context_9_4510_965234 : frontier 12 ⟨965234, by decide⟩
    (prefixCache 9 4510) (prefixPartial 9 4510) = false := by
  decide +kernel

theorem node_context_9_4510_965234 : EJMOriginalGlobalDAGData.nodes 12 ⟨965234, by decide⟩ =
    .split (coordinate 9) (![⟨964664, by decide⟩,⟨964847, by decide⟩,⟨964993, by decide⟩,⟨965233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4510_965234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4510 ⟨965234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4510
    ⟨965234, by decide⟩ (by decide) (![⟨964664, by decide⟩,⟨964847, by decide⟩,⟨964993, by decide⟩,⟨965233, by decide⟩]) unmarked_context_9_4510_965234 node_context_9_4510_965234
  intro a
  fin_cases a
  · exact context_10_18040_964664
  · exact context_10_18041_964847
  · exact context_10_18042_964993
  · exact context_10_18043_965233

theorem selected_cut_36437 : selected 10 ⟨965265, by decide⟩
    (prefixPartial 11 72176) = some ⟨11, 2, 0, 965265, 72176, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_72176_965265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72176 ⟨965265, by decide⟩ :=
  accepted_of_selected 11 72176 ⟨965265, by decide⟩ ⟨11, 2, 0, 965265, 72176, 2165, 262144⟩
    (by decide) selected_cut_36437

theorem selected_cut_36438 : selected 10 ⟨965297, by decide⟩
    (prefixPartial 11 72177) = some ⟨11, 2, 0, 965297, 72177, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_72177_965297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72177 ⟨965297, by decide⟩ :=
  accepted_of_selected 11 72177 ⟨965297, by decide⟩ ⟨11, 2, 0, 965297, 72177, 2057, 262144⟩
    (by decide) selected_cut_36438

theorem selected_cut_36439 : selected 10 ⟨965333, by decide⟩
    (prefixPartial 11 72178) = some ⟨11, 2, 0, 965333, 72178, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_72178_965333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72178 ⟨965333, by decide⟩ :=
  accepted_of_selected 11 72178 ⟨965333, by decide⟩ ⟨11, 2, 0, 965333, 72178, 2149, 262144⟩
    (by decide) selected_cut_36439

theorem selected_cut_36440 : selected 10 ⟨965368, by decide⟩
    (prefixPartial 11 72179) = some ⟨11, 2, 0, 965368, 72179, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_72179_965368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72179 ⟨965368, by decide⟩ :=
  accepted_of_selected 11 72179 ⟨965368, by decide⟩ ⟨11, 2, 0, 965368, 72179, 1461, 262144⟩
    (by decide) selected_cut_36440

theorem unmarked_context_10_18044_965369 : frontier 11 ⟨965369, by decide⟩
    (prefixCache 10 18044) (prefixPartial 10 18044) = false := by
  decide +kernel

theorem node_context_10_18044_965369 : EJMOriginalGlobalDAGData.nodes 11 ⟨965369, by decide⟩ =
    .split (coordinate 10) (![⟨965265, by decide⟩,⟨965297, by decide⟩,⟨965333, by decide⟩,⟨965368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18044_965369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18044 ⟨965369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18044
    ⟨965369, by decide⟩ (by decide) (![⟨965265, by decide⟩,⟨965297, by decide⟩,⟨965333, by decide⟩,⟨965368, by decide⟩]) unmarked_context_10_18044_965369 node_context_10_18044_965369
  intro a
  fin_cases a
  · exact context_11_72176_965265
  · exact context_11_72177_965297
  · exact context_11_72178_965333
  · exact context_11_72179_965368

theorem selected_cut_36441 : selected 11 ⟨965428, by decide⟩
    (prefixPartial 10 18045) = some ⟨10, 2, 0, 965428, 18045, 3925, 1048576⟩ := by
  decide +kernel

theorem context_10_18045_965428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18045 ⟨965428, by decide⟩ :=
  accepted_of_selected 10 18045 ⟨965428, by decide⟩ ⟨10, 2, 0, 965428, 18045, 3925, 1048576⟩
    (by decide) selected_cut_36441

theorem selected_cut_36442 : selected 11 ⟨965493, by decide⟩
    (prefixPartial 10 18046) = some ⟨10, 2, 0, 965493, 18046, 3333, 1048576⟩ := by
  decide +kernel

theorem context_10_18046_965493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18046 ⟨965493, by decide⟩ :=
  accepted_of_selected 10 18046 ⟨965493, by decide⟩ ⟨10, 2, 0, 965493, 18046, 3333, 1048576⟩
    (by decide) selected_cut_36442

theorem selected_cut_36443 : selected 11 ⟨965534, by decide⟩
    (prefixPartial 10 18047) = some ⟨10, 2, 0, 965534, 18047, 677, 1048576⟩ := by
  decide +kernel

theorem context_10_18047_965534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18047 ⟨965534, by decide⟩ :=
  accepted_of_selected 10 18047 ⟨965534, by decide⟩ ⟨10, 2, 0, 965534, 18047, 677, 1048576⟩
    (by decide) selected_cut_36443

theorem unmarked_context_9_4511_965535 : frontier 12 ⟨965535, by decide⟩
    (prefixCache 9 4511) (prefixPartial 9 4511) = false := by
  decide +kernel

theorem node_context_9_4511_965535 : EJMOriginalGlobalDAGData.nodes 12 ⟨965535, by decide⟩ =
    .split (coordinate 9) (![⟨965369, by decide⟩,⟨965428, by decide⟩,⟨965493, by decide⟩,⟨965534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4511_965535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4511 ⟨965535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4511
    ⟨965535, by decide⟩ (by decide) (![⟨965369, by decide⟩,⟨965428, by decide⟩,⟨965493, by decide⟩,⟨965534, by decide⟩]) unmarked_context_9_4511_965535 node_context_9_4511_965535
  intro a
  fin_cases a
  · exact context_10_18044_965369
  · exact context_10_18045_965428
  · exact context_10_18046_965493
  · exact context_10_18047_965534

theorem unmarked_context_8_1127_965536 : frontier 13 ⟨965536, by decide⟩
    (prefixCache 8 1127) (prefixPartial 8 1127) = false := by
  decide +kernel

theorem node_context_8_1127_965536 : EJMOriginalGlobalDAGData.nodes 13 ⟨965536, by decide⟩ =
    .split (coordinate 8) (![⟨962899, by decide⟩,⟨964247, by decide⟩,⟨965234, by decide⟩,⟨965535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1127_965536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1127 ⟨965536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1127
    ⟨965536, by decide⟩ (by decide) (![⟨962899, by decide⟩,⟨964247, by decide⟩,⟨965234, by decide⟩,⟨965535, by decide⟩]) unmarked_context_8_1127_965536 node_context_8_1127_965536
  intro a
  fin_cases a
  · exact context_9_4508_962899
  · exact context_9_4509_964247
  · exact context_9_4510_965234
  · exact context_9_4511_965535

theorem unmarked_context_7_281_965537 : frontier 14 ⟨965537, by decide⟩
    (prefixCache 7 281) (prefixPartial 7 281) = false := by
  decide +kernel

theorem node_context_7_281_965537 : EJMOriginalGlobalDAGData.nodes 14 ⟨965537, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨954489, by decide⟩,⟨959985, by decide⟩,⟨965536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_281_965537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 281 ⟨965537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 281
    ⟨965537, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨954489, by decide⟩,⟨959985, by decide⟩,⟨965536, by decide⟩]) unmarked_context_7_281_965537 node_context_7_281_965537
  intro a
  fin_cases a
  · exact context_8_1124_14300
  · exact context_8_1125_954489
  · exact context_8_1126_959985
  · exact context_8_1127_965536

theorem selected_cut_36444 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1128) = some ⟨8, 1, 0, 14300, 1128, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1128_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1128 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1128 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1128, 1, 16777216⟩
    (by decide) selected_cut_36444

theorem selected_cut_36445 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1129) = some ⟨8, 1, 0, 14300, 1129, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1129_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1129 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1129 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1129, 1, 16777216⟩
    (by decide) selected_cut_36445

theorem selected_cut_36446 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 289280) = some ⟨12, 1, 0, 34034, 289280, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289280_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289280 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 289280 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 289280, 1, 65536⟩
    (by decide) selected_cut_36446

theorem selected_cut_36447 : selected 9 ⟨965599, by decide⟩
    (prefixPartial 12 289281) = some ⟨12, 2, 0, 965599, 289281, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_289281_965599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289281 ⟨965599, by decide⟩ :=
  accepted_of_selected 12 289281 ⟨965599, by decide⟩ ⟨12, 2, 0, 965599, 289281, 3749, 65536⟩
    (by decide) selected_cut_36447

theorem selected_cut_36448 : selected 9 ⟨965660, by decide⟩
    (prefixPartial 12 289282) = some ⟨12, 2, 0, 965660, 289282, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_289282_965660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289282 ⟨965660, by decide⟩ :=
  accepted_of_selected 12 289282 ⟨965660, by decide⟩ ⟨12, 2, 0, 965660, 289282, 3621, 65536⟩
    (by decide) selected_cut_36448

theorem selected_cut_36449 : selected 8 ⟨965691, by decide⟩
    (prefixPartial 13 1157132) = some ⟨13, 2, 0, 965691, 1157132, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_1157132_965691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157132 ⟨965691, by decide⟩ :=
  accepted_of_selected 13 1157132 ⟨965691, by decide⟩ ⟨13, 2, 0, 965691, 1157132, 1601, 16384⟩
    (by decide) selected_cut_36449

theorem selected_cut_36450 : selected 8 ⟨965709, by decide⟩
    (prefixPartial 13 1157133) = some ⟨13, 2, 0, 965709, 1157133, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1157133_965709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157133 ⟨965709, by decide⟩ :=
  accepted_of_selected 13 1157133 ⟨965709, by decide⟩ ⟨13, 2, 0, 965709, 1157133, 853, 16384⟩
    (by decide) selected_cut_36450

theorem selected_cut_36451 : selected 8 ⟨965725, by decide⟩
    (prefixPartial 13 1157134) = some ⟨13, 2, 0, 965725, 1157134, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_1157134_965725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157134 ⟨965725, by decide⟩ :=
  accepted_of_selected 13 1157134 ⟨965725, by decide⟩ ⟨13, 2, 0, 965725, 1157134, 1145, 16384⟩
    (by decide) selected_cut_36451

theorem selected_cut_36452 : selected 8 ⟨965734, by decide⟩
    (prefixPartial 13 1157135) = some ⟨13, 2, 0, 965734, 1157135, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1157135_965734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157135 ⟨965734, by decide⟩ :=
  accepted_of_selected 13 1157135 ⟨965734, by decide⟩ ⟨13, 2, 0, 965734, 1157135, 725, 16384⟩
    (by decide) selected_cut_36452

theorem unmarked_context_12_289283_965735 : frontier 9 ⟨965735, by decide⟩
    (prefixCache 12 289283) (prefixPartial 12 289283) = false := by
  decide +kernel

theorem node_context_12_289283_965735 : EJMOriginalGlobalDAGData.nodes 9 ⟨965735, by decide⟩ =
    .split (coordinate 12) (![⟨965691, by decide⟩,⟨965709, by decide⟩,⟨965725, by decide⟩,⟨965734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_289283_965735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289283 ⟨965735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 289283
    ⟨965735, by decide⟩ (by decide) (![⟨965691, by decide⟩,⟨965709, by decide⟩,⟨965725, by decide⟩,⟨965734, by decide⟩]) unmarked_context_12_289283_965735 node_context_12_289283_965735
  intro a
  fin_cases a
  · exact context_13_1157132_965691
  · exact context_13_1157133_965709
  · exact context_13_1157134_965725
  · exact context_13_1157135_965734

theorem unmarked_context_11_72320_965736 : frontier 10 ⟨965736, by decide⟩
    (prefixCache 11 72320) (prefixPartial 11 72320) = false := by
  decide +kernel

theorem node_context_11_72320_965736 : EJMOriginalGlobalDAGData.nodes 10 ⟨965736, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨965599, by decide⟩,⟨965660, by decide⟩,⟨965735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72320_965736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72320 ⟨965736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72320
    ⟨965736, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨965599, by decide⟩,⟨965660, by decide⟩,⟨965735, by decide⟩]) unmarked_context_11_72320_965736 node_context_11_72320_965736
  intro a
  fin_cases a
  · exact context_12_289280_34034
  · exact context_12_289281_965599
  · exact context_12_289282_965660
  · exact context_12_289283_965735

theorem selected_cut_36453 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 289284) = some ⟨12, 1, 0, 34034, 289284, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289284_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289284 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 289284 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 289284, 1, 65536⟩
    (by decide) selected_cut_36453

theorem selected_cut_36454 : selected 9 ⟨965806, by decide⟩
    (prefixPartial 12 289285) = some ⟨12, 2, 0, 965806, 289285, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_289285_965806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289285 ⟨965806, by decide⟩ :=
  accepted_of_selected 12 289285 ⟨965806, by decide⟩ ⟨12, 2, 0, 965806, 289285, 3761, 65536⟩
    (by decide) selected_cut_36454

theorem selected_cut_36455 : selected 9 ⟨965860, by decide⟩
    (prefixPartial 12 289286) = some ⟨12, 2, 0, 965860, 289286, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_289286_965860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289286 ⟨965860, by decide⟩ :=
  accepted_of_selected 12 289286 ⟨965860, by decide⟩ ⟨12, 2, 0, 965860, 289286, 3633, 65536⟩
    (by decide) selected_cut_36455

theorem selected_cut_36456 : selected 8 ⟨965892, by decide⟩
    (prefixPartial 13 1157148) = some ⟨13, 2, 0, 965892, 1157148, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_1157148_965892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157148 ⟨965892, by decide⟩ :=
  accepted_of_selected 13 1157148 ⟨965892, by decide⟩ ⟨13, 2, 0, 965892, 1157148, 1585, 16384⟩
    (by decide) selected_cut_36456

theorem selected_cut_36457 : selected 8 ⟨965904, by decide⟩
    (prefixPartial 13 1157149) = some ⟨13, 2, 0, 965904, 1157149, 785, 16384⟩ := by
  decide +kernel

theorem context_13_1157149_965904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157149 ⟨965904, by decide⟩ :=
  accepted_of_selected 13 1157149 ⟨965904, by decide⟩ ⟨13, 2, 0, 965904, 1157149, 785, 16384⟩
    (by decide) selected_cut_36457

theorem selected_cut_36458 : selected 8 ⟨965927, by decide⟩
    (prefixPartial 13 1157150) = some ⟨13, 2, 0, 965927, 1157150, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_1157150_965927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157150 ⟨965927, by decide⟩ :=
  accepted_of_selected 13 1157150 ⟨965927, by decide⟩ ⟨13, 2, 0, 965927, 1157150, 1169, 16384⟩
    (by decide) selected_cut_36458

theorem selected_cut_36459 : selected 8 ⟨965938, by decide⟩
    (prefixPartial 13 1157151) = some ⟨13, 2, 0, 965938, 1157151, 737, 16384⟩ := by
  decide +kernel

theorem context_13_1157151_965938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157151 ⟨965938, by decide⟩ :=
  accepted_of_selected 13 1157151 ⟨965938, by decide⟩ ⟨13, 2, 0, 965938, 1157151, 737, 16384⟩
    (by decide) selected_cut_36459

theorem unmarked_context_12_289287_965939 : frontier 9 ⟨965939, by decide⟩
    (prefixCache 12 289287) (prefixPartial 12 289287) = false := by
  decide +kernel

theorem node_context_12_289287_965939 : EJMOriginalGlobalDAGData.nodes 9 ⟨965939, by decide⟩ =
    .split (coordinate 12) (![⟨965892, by decide⟩,⟨965904, by decide⟩,⟨965927, by decide⟩,⟨965938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_289287_965939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289287 ⟨965939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 289287
    ⟨965939, by decide⟩ (by decide) (![⟨965892, by decide⟩,⟨965904, by decide⟩,⟨965927, by decide⟩,⟨965938, by decide⟩]) unmarked_context_12_289287_965939 node_context_12_289287_965939
  intro a
  fin_cases a
  · exact context_13_1157148_965892
  · exact context_13_1157149_965904
  · exact context_13_1157150_965927
  · exact context_13_1157151_965938

theorem unmarked_context_11_72321_965940 : frontier 10 ⟨965940, by decide⟩
    (prefixCache 11 72321) (prefixPartial 11 72321) = false := by
  decide +kernel

theorem node_context_11_72321_965940 : EJMOriginalGlobalDAGData.nodes 10 ⟨965940, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨965806, by decide⟩,⟨965860, by decide⟩,⟨965939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72321_965940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72321 ⟨965940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72321
    ⟨965940, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨965806, by decide⟩,⟨965860, by decide⟩,⟨965939, by decide⟩]) unmarked_context_11_72321_965940 node_context_11_72321_965940
  intro a
  fin_cases a
  · exact context_12_289284_34034
  · exact context_12_289285_965806
  · exact context_12_289286_965860
  · exact context_12_289287_965939

theorem selected_cut_36460 : selected 9 ⟨966039, by decide⟩
    (prefixPartial 12 289288) = some ⟨12, 2, 0, 966039, 289288, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_289288_966039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289288 ⟨966039, by decide⟩ :=
  accepted_of_selected 12 289288 ⟨966039, by decide⟩ ⟨12, 2, 0, 966039, 289288, 3197, 65536⟩
    (by decide) selected_cut_36460

theorem selected_cut_36461 : selected 9 ⟨966113, by decide⟩
    (prefixPartial 12 289289) = some ⟨12, 2, 0, 966113, 289289, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_289289_966113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289289 ⟨966113, by decide⟩ :=
  accepted_of_selected 12 289289 ⟨966113, by decide⟩ ⟨12, 2, 0, 966113, 289289, 3749, 65536⟩
    (by decide) selected_cut_36461

theorem selected_cut_36462 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 289290) = some ⟨12, 1, 0, 893903, 289290, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289290_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289290 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 289290 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 289290, 1, 65536⟩
    (by decide) selected_cut_36462

theorem selected_cut_36463 : selected 8 ⟨966137, by decide⟩
    (prefixPartial 13 1157164) = some ⟨13, 2, 0, 966137, 1157164, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_1157164_966137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157164 ⟨966137, by decide⟩ :=
  accepted_of_selected 13 1157164 ⟨966137, by decide⟩ ⟨13, 2, 0, 966137, 1157164, 1157, 16384⟩
    (by decide) selected_cut_36463

theorem selected_cut_36464 : selected 8 ⟨966159, by decide⟩
    (prefixPartial 13 1157165) = some ⟨13, 2, 0, 966159, 1157165, 949, 16384⟩ := by
  decide +kernel

theorem context_13_1157165_966159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157165 ⟨966159, by decide⟩ :=
  accepted_of_selected 13 1157165 ⟨966159, by decide⟩ ⟨13, 2, 0, 966159, 1157165, 949, 16384⟩
    (by decide) selected_cut_36464

theorem selected_cut_36465 : selected 8 ⟨966179, by decide⟩
    (prefixPartial 13 1157166) = some ⟨13, 2, 0, 966179, 1157166, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_1157166_966179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157166 ⟨966179, by decide⟩ :=
  accepted_of_selected 13 1157166 ⟨966179, by decide⟩ ⟨13, 2, 0, 966179, 1157166, 1189, 16384⟩
    (by decide) selected_cut_36465

theorem selected_cut_36466 : selected 8 ⟨966191, by decide⟩
    (prefixPartial 13 1157167) = some ⟨13, 2, 0, 966191, 1157167, 837, 16384⟩ := by
  decide +kernel

theorem context_13_1157167_966191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1157167 ⟨966191, by decide⟩ :=
  accepted_of_selected 13 1157167 ⟨966191, by decide⟩ ⟨13, 2, 0, 966191, 1157167, 837, 16384⟩
    (by decide) selected_cut_36466

theorem unmarked_context_12_289291_966192 : frontier 9 ⟨966192, by decide⟩
    (prefixCache 12 289291) (prefixPartial 12 289291) = false := by
  decide +kernel

theorem node_context_12_289291_966192 : EJMOriginalGlobalDAGData.nodes 9 ⟨966192, by decide⟩ =
    .split (coordinate 12) (![⟨966137, by decide⟩,⟨966159, by decide⟩,⟨966179, by decide⟩,⟨966191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_289291_966192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289291 ⟨966192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 289291
    ⟨966192, by decide⟩ (by decide) (![⟨966137, by decide⟩,⟨966159, by decide⟩,⟨966179, by decide⟩,⟨966191, by decide⟩]) unmarked_context_12_289291_966192 node_context_12_289291_966192
  intro a
  fin_cases a
  · exact context_13_1157164_966137
  · exact context_13_1157165_966159
  · exact context_13_1157166_966179
  · exact context_13_1157167_966191

theorem unmarked_context_11_72322_966193 : frontier 10 ⟨966193, by decide⟩
    (prefixCache 11 72322) (prefixPartial 11 72322) = false := by
  decide +kernel

theorem node_context_11_72322_966193 : EJMOriginalGlobalDAGData.nodes 10 ⟨966193, by decide⟩ =
    .split (coordinate 11) (![⟨966039, by decide⟩,⟨966113, by decide⟩,⟨893903, by decide⟩,⟨966192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72322_966193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72322 ⟨966193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72322
    ⟨966193, by decide⟩ (by decide) (![⟨966039, by decide⟩,⟨966113, by decide⟩,⟨893903, by decide⟩,⟨966192, by decide⟩]) unmarked_context_11_72322_966193 node_context_11_72322_966193
  intro a
  fin_cases a
  · exact context_12_289288_966039
  · exact context_12_289289_966113
  · exact context_12_289290_893903
  · exact context_12_289291_966192

theorem selected_cut_36467 : selected 9 ⟨966255, by decide⟩
    (prefixPartial 12 289292) = some ⟨12, 2, 0, 966255, 289292, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_289292_966255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289292 ⟨966255, by decide⟩ :=
  accepted_of_selected 12 289292 ⟨966255, by decide⟩ ⟨12, 2, 0, 966255, 289292, 2853, 65536⟩
    (by decide) selected_cut_36467

theorem selected_cut_36468 : selected 9 ⟨966319, by decide⟩
    (prefixPartial 12 289293) = some ⟨12, 2, 0, 966319, 289293, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_289293_966319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289293 ⟨966319, by decide⟩ :=
  accepted_of_selected 12 289293 ⟨966319, by decide⟩ ⟨12, 2, 0, 966319, 289293, 3673, 65536⟩
    (by decide) selected_cut_36468

theorem selected_cut_36469 : selected 9 ⟨966378, by decide⟩
    (prefixPartial 12 289294) = some ⟨12, 2, 0, 966378, 289294, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_289294_966378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289294 ⟨966378, by decide⟩ :=
  accepted_of_selected 12 289294 ⟨966378, by decide⟩ ⟨12, 2, 0, 966378, 289294, 3761, 65536⟩
    (by decide) selected_cut_36469

theorem selected_cut_36470 : selected 9 ⟨966448, by decide⟩
    (prefixPartial 12 289295) = some ⟨12, 2, 0, 966448, 289295, 3985, 65536⟩ := by
  decide +kernel

theorem context_12_289295_966448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289295 ⟨966448, by decide⟩ :=
  accepted_of_selected 12 289295 ⟨966448, by decide⟩ ⟨12, 2, 0, 966448, 289295, 3985, 65536⟩
    (by decide) selected_cut_36470

theorem unmarked_context_11_72323_966449 : frontier 10 ⟨966449, by decide⟩
    (prefixCache 11 72323) (prefixPartial 11 72323) = false := by
  decide +kernel

theorem node_context_11_72323_966449 : EJMOriginalGlobalDAGData.nodes 10 ⟨966449, by decide⟩ =
    .split (coordinate 11) (![⟨966255, by decide⟩,⟨966319, by decide⟩,⟨966378, by decide⟩,⟨966448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72323_966449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72323 ⟨966449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72323
    ⟨966449, by decide⟩ (by decide) (![⟨966255, by decide⟩,⟨966319, by decide⟩,⟨966378, by decide⟩,⟨966448, by decide⟩]) unmarked_context_11_72323_966449 node_context_11_72323_966449
  intro a
  fin_cases a
  · exact context_12_289292_966255
  · exact context_12_289293_966319
  · exact context_12_289294_966378
  · exact context_12_289295_966448

theorem unmarked_context_10_18080_966450 : frontier 11 ⟨966450, by decide⟩
    (prefixCache 10 18080) (prefixPartial 10 18080) = false := by
  decide +kernel

theorem node_context_10_18080_966450 : EJMOriginalGlobalDAGData.nodes 11 ⟨966450, by decide⟩ =
    .split (coordinate 10) (![⟨965736, by decide⟩,⟨965940, by decide⟩,⟨966193, by decide⟩,⟨966449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18080_966450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18080 ⟨966450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18080
    ⟨966450, by decide⟩ (by decide) (![⟨965736, by decide⟩,⟨965940, by decide⟩,⟨966193, by decide⟩,⟨966449, by decide⟩]) unmarked_context_10_18080_966450 node_context_10_18080_966450
  intro a
  fin_cases a
  · exact context_11_72320_965736
  · exact context_11_72321_965940
  · exact context_11_72322_966193
  · exact context_11_72323_966449

theorem selected_cut_36471 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289296) = some ⟨12, 1, 0, 1738, 289296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289296_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289296 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289296 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289296, 1, 65536⟩
    (by decide) selected_cut_36471

theorem selected_cut_36472 : selected 9 ⟨966505, by decide⟩
    (prefixPartial 12 289297) = some ⟨12, 2, 0, 966505, 289297, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_289297_966505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289297 ⟨966505, by decide⟩ :=
  accepted_of_selected 12 289297 ⟨966505, by decide⟩ ⟨12, 2, 0, 966505, 289297, 2337, 65536⟩
    (by decide) selected_cut_36472

theorem selected_cut_36473 : selected 9 ⟨966570, by decide⟩
    (prefixPartial 12 289298) = some ⟨12, 2, 0, 966570, 289298, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_289298_966570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289298 ⟨966570, by decide⟩ :=
  accepted_of_selected 12 289298 ⟨966570, by decide⟩ ⟨12, 2, 0, 966570, 289298, 3225, 65536⟩
    (by decide) selected_cut_36473

theorem selected_cut_36474 : selected 9 ⟨966643, by decide⟩
    (prefixPartial 12 289299) = some ⟨12, 2, 0, 966643, 289299, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_289299_966643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289299 ⟨966643, by decide⟩ :=
  accepted_of_selected 12 289299 ⟨966643, by decide⟩ ⟨12, 2, 0, 966643, 289299, 3957, 65536⟩
    (by decide) selected_cut_36474

theorem unmarked_context_11_72324_966644 : frontier 10 ⟨966644, by decide⟩
    (prefixCache 11 72324) (prefixPartial 11 72324) = false := by
  decide +kernel

theorem node_context_11_72324_966644 : EJMOriginalGlobalDAGData.nodes 10 ⟨966644, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨966505, by decide⟩,⟨966570, by decide⟩,⟨966643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72324_966644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72324 ⟨966644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72324
    ⟨966644, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨966505, by decide⟩,⟨966570, by decide⟩,⟨966643, by decide⟩]) unmarked_context_11_72324_966644 node_context_11_72324_966644
  intro a
  fin_cases a
  · exact context_12_289296_1738
  · exact context_12_289297_966505
  · exact context_12_289298_966570
  · exact context_12_289299_966643

theorem selected_cut_36475 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289300) = some ⟨12, 1, 0, 1738, 289300, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289300_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289300 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289300 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289300, 1, 65536⟩
    (by decide) selected_cut_36475

theorem selected_cut_36476 : selected 9 ⟨928104, by decide⟩
    (prefixPartial 12 289301) = some ⟨12, 1, 0, 928104, 289301, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289301_928104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289301 ⟨928104, by decide⟩ :=
  accepted_of_selected 12 289301 ⟨928104, by decide⟩ ⟨12, 1, 0, 928104, 289301, 1, 65536⟩
    (by decide) selected_cut_36476

theorem selected_cut_36477 : selected 9 ⟨966701, by decide⟩
    (prefixPartial 12 289302) = some ⟨12, 2, 0, 966701, 289302, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_289302_966701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289302 ⟨966701, by decide⟩ :=
  accepted_of_selected 12 289302 ⟨966701, by decide⟩ ⟨12, 2, 0, 966701, 289302, 3081, 65536⟩
    (by decide) selected_cut_36477

theorem selected_cut_36478 : selected 9 ⟨966768, by decide⟩
    (prefixPartial 12 289303) = some ⟨12, 2, 0, 966768, 289303, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_289303_966768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289303 ⟨966768, by decide⟩ :=
  accepted_of_selected 12 289303 ⟨966768, by decide⟩ ⟨12, 2, 0, 966768, 289303, 3649, 65536⟩
    (by decide) selected_cut_36478

theorem unmarked_context_11_72325_966769 : frontier 10 ⟨966769, by decide⟩
    (prefixCache 11 72325) (prefixPartial 11 72325) = false := by
  decide +kernel

theorem node_context_11_72325_966769 : EJMOriginalGlobalDAGData.nodes 10 ⟨966769, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨928104, by decide⟩,⟨966701, by decide⟩,⟨966768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72325_966769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72325 ⟨966769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72325
    ⟨966769, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨928104, by decide⟩,⟨966701, by decide⟩,⟨966768, by decide⟩]) unmarked_context_11_72325_966769 node_context_11_72325_966769
  intro a
  fin_cases a
  · exact context_12_289300_1738
  · exact context_12_289301_928104
  · exact context_12_289302_966701
  · exact context_12_289303_966768

theorem selected_cut_36479 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 289304) = some ⟨12, 1, 0, 1738, 289304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289304_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289304 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 289304 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 289304, 1, 65536⟩
    (by decide) selected_cut_36479

theorem selected_cut_36480 : selected 9 ⟨966820, by decide⟩
    (prefixPartial 12 289305) = some ⟨12, 2, 0, 966820, 289305, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_289305_966820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289305 ⟨966820, by decide⟩ :=
  accepted_of_selected 12 289305 ⟨966820, by decide⟩ ⟨12, 2, 0, 966820, 289305, 2033, 65536⟩
    (by decide) selected_cut_36480

theorem selected_cut_36481 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 289306) = some ⟨12, 1, 0, 893903, 289306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289306_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289306 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 289306 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 289306, 1, 65536⟩
    (by decide) selected_cut_36481

theorem selected_cut_36482 : selected 9 ⟨966887, by decide⟩
    (prefixPartial 12 289307) = some ⟨12, 2, 0, 966887, 289307, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_289307_966887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289307 ⟨966887, by decide⟩ :=
  accepted_of_selected 12 289307 ⟨966887, by decide⟩ ⟨12, 2, 0, 966887, 289307, 3265, 65536⟩
    (by decide) selected_cut_36482

theorem unmarked_context_11_72326_966888 : frontier 10 ⟨966888, by decide⟩
    (prefixCache 11 72326) (prefixPartial 11 72326) = false := by
  decide +kernel

theorem node_context_11_72326_966888 : EJMOriginalGlobalDAGData.nodes 10 ⟨966888, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨966820, by decide⟩,⟨893903, by decide⟩,⟨966887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72326_966888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72326 ⟨966888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72326
    ⟨966888, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨966820, by decide⟩,⟨893903, by decide⟩,⟨966887, by decide⟩]) unmarked_context_11_72326_966888 node_context_11_72326_966888
  intro a
  fin_cases a
  · exact context_12_289304_1738
  · exact context_12_289305_966820
  · exact context_12_289306_893903
  · exact context_12_289307_966887

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
