/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover133
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12867 : selected 8 ⟨339266, by decide⟩
    (prefixPartial 13 105633) = some ⟨13, 2, 0, 339266, 105633, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_105633_339266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105633 ⟨339266, by decide⟩ :=
  accepted_of_selected 13 105633 ⟨339266, by decide⟩ ⟨13, 2, 0, 339266, 105633, 2005, 16384⟩
    (by decide) selected_cut_12867

theorem selected_cut_12868 : selected 8 ⟨339284, by decide⟩
    (prefixPartial 13 105634) = some ⟨13, 2, 0, 339284, 105634, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_105634_339284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105634 ⟨339284, by decide⟩ :=
  accepted_of_selected 13 105634 ⟨339284, by decide⟩ ⟨13, 2, 0, 339284, 105634, 1405, 16384⟩
    (by decide) selected_cut_12868

theorem selected_cut_12869 : selected 8 ⟨339294, by decide⟩
    (prefixPartial 13 105635) = some ⟨13, 2, 0, 339294, 105635, 777, 16384⟩ := by
  decide +kernel

theorem context_13_105635_339294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105635 ⟨339294, by decide⟩ :=
  accepted_of_selected 13 105635 ⟨339294, by decide⟩ ⟨13, 2, 0, 339294, 105635, 777, 16384⟩
    (by decide) selected_cut_12869

theorem unmarked_context_12_26408_339295 : frontier 9 ⟨339295, by decide⟩
    (prefixCache 12 26408) (prefixPartial 12 26408) = false := by
  decide +kernel

theorem node_context_12_26408_339295 : EJMOriginalGlobalDAGData.nodes 9 ⟨339295, by decide⟩ =
    .split (coordinate 12) (![⟨339237, by decide⟩,⟨339266, by decide⟩,⟨339284, by decide⟩,⟨339294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26408_339295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26408 ⟨339295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26408
    ⟨339295, by decide⟩ (by decide) (![⟨339237, by decide⟩,⟨339266, by decide⟩,⟨339284, by decide⟩,⟨339294, by decide⟩]) unmarked_context_12_26408_339295 node_context_12_26408_339295
  intro a
  fin_cases a
  · exact context_13_105632_339237
  · exact context_13_105633_339266
  · exact context_13_105634_339284
  · exact context_13_105635_339294

theorem selected_cut_12870 : selected 8 ⟨339304, by decide⟩
    (prefixPartial 13 105636) = some ⟨13, 2, 0, 339304, 105636, 793, 16384⟩ := by
  decide +kernel

theorem context_13_105636_339304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105636 ⟨339304, by decide⟩ :=
  accepted_of_selected 13 105636 ⟨339304, by decide⟩ ⟨13, 2, 0, 339304, 105636, 793, 16384⟩
    (by decide) selected_cut_12870

theorem selected_cut_12871 : selected 8 ⟨339341, by decide⟩
    (prefixPartial 13 105637) = some ⟨13, 2, 0, 339341, 105637, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_105637_339341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105637 ⟨339341, by decide⟩ :=
  accepted_of_selected 13 105637 ⟨339341, by decide⟩ ⟨13, 2, 0, 339341, 105637, 2561, 16384⟩
    (by decide) selected_cut_12871

theorem selected_cut_12872 : selected 8 ⟨339360, by decide⟩
    (prefixPartial 13 105638) = some ⟨13, 2, 0, 339360, 105638, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_105638_339360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105638 ⟨339360, by decide⟩ :=
  accepted_of_selected 13 105638 ⟨339360, by decide⟩ ⟨13, 2, 0, 339360, 105638, 1477, 16384⟩
    (by decide) selected_cut_12872

theorem selected_cut_12873 : selected 8 ⟨339374, by decide⟩
    (prefixPartial 13 105639) = some ⟨13, 2, 0, 339374, 105639, 785, 16384⟩ := by
  decide +kernel

theorem context_13_105639_339374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105639 ⟨339374, by decide⟩ :=
  accepted_of_selected 13 105639 ⟨339374, by decide⟩ ⟨13, 2, 0, 339374, 105639, 785, 16384⟩
    (by decide) selected_cut_12873

theorem unmarked_context_12_26409_339375 : frontier 9 ⟨339375, by decide⟩
    (prefixCache 12 26409) (prefixPartial 12 26409) = false := by
  decide +kernel

theorem node_context_12_26409_339375 : EJMOriginalGlobalDAGData.nodes 9 ⟨339375, by decide⟩ =
    .split (coordinate 12) (![⟨339304, by decide⟩,⟨339341, by decide⟩,⟨339360, by decide⟩,⟨339374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26409_339375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26409 ⟨339375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26409
    ⟨339375, by decide⟩ (by decide) (![⟨339304, by decide⟩,⟨339341, by decide⟩,⟨339360, by decide⟩,⟨339374, by decide⟩]) unmarked_context_12_26409_339375 node_context_12_26409_339375
  intro a
  fin_cases a
  · exact context_13_105636_339304
  · exact context_13_105637_339341
  · exact context_13_105638_339360
  · exact context_13_105639_339374

theorem selected_cut_12874 : selected 8 ⟨339384, by decide⟩
    (prefixPartial 13 105640) = some ⟨13, 2, 0, 339384, 105640, 689, 16384⟩ := by
  decide +kernel

theorem context_13_105640_339384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105640 ⟨339384, by decide⟩ :=
  accepted_of_selected 13 105640 ⟨339384, by decide⟩ ⟨13, 2, 0, 339384, 105640, 689, 16384⟩
    (by decide) selected_cut_12874

theorem selected_cut_12875 : selected 8 ⟨339418, by decide⟩
    (prefixPartial 13 105641) = some ⟨13, 2, 0, 339418, 105641, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_105641_339418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105641 ⟨339418, by decide⟩ :=
  accepted_of_selected 13 105641 ⟨339418, by decide⟩ ⟨13, 2, 0, 339418, 105641, 2193, 16384⟩
    (by decide) selected_cut_12875

theorem selected_cut_12876 : selected 8 ⟨339436, by decide⟩
    (prefixPartial 13 105642) = some ⟨13, 2, 0, 339436, 105642, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_105642_339436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105642 ⟨339436, by decide⟩ :=
  accepted_of_selected 13 105642 ⟨339436, by decide⟩ ⟨13, 2, 0, 339436, 105642, 1325, 16384⟩
    (by decide) selected_cut_12876

theorem selected_cut_12877 : selected 8 ⟨339441, by decide⟩
    (prefixPartial 13 105643) = some ⟨13, 2, 0, 339441, 105643, 797, 16384⟩ := by
  decide +kernel

theorem context_13_105643_339441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105643 ⟨339441, by decide⟩ :=
  accepted_of_selected 13 105643 ⟨339441, by decide⟩ ⟨13, 2, 0, 339441, 105643, 797, 16384⟩
    (by decide) selected_cut_12877

theorem unmarked_context_12_26410_339442 : frontier 9 ⟨339442, by decide⟩
    (prefixCache 12 26410) (prefixPartial 12 26410) = false := by
  decide +kernel

theorem node_context_12_26410_339442 : EJMOriginalGlobalDAGData.nodes 9 ⟨339442, by decide⟩ =
    .split (coordinate 12) (![⟨339384, by decide⟩,⟨339418, by decide⟩,⟨339436, by decide⟩,⟨339441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26410_339442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26410 ⟨339442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26410
    ⟨339442, by decide⟩ (by decide) (![⟨339384, by decide⟩,⟨339418, by decide⟩,⟨339436, by decide⟩,⟨339441, by decide⟩]) unmarked_context_12_26410_339442 node_context_12_26410_339442
  intro a
  fin_cases a
  · exact context_13_105640_339384
  · exact context_13_105641_339418
  · exact context_13_105642_339436
  · exact context_13_105643_339441

theorem selected_cut_12878 : selected 8 ⟨339451, by decide⟩
    (prefixPartial 13 105644) = some ⟨13, 2, 0, 339451, 105644, 677, 16384⟩ := by
  decide +kernel

theorem context_13_105644_339451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105644 ⟨339451, by decide⟩ :=
  accepted_of_selected 13 105644 ⟨339451, by decide⟩ ⟨13, 2, 0, 339451, 105644, 677, 16384⟩
    (by decide) selected_cut_12878

theorem selected_cut_12879 : selected 8 ⟨339491, by decide⟩
    (prefixPartial 13 105645) = some ⟨13, 2, 0, 339491, 105645, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_105645_339491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105645 ⟨339491, by decide⟩ :=
  accepted_of_selected 13 105645 ⟨339491, by decide⟩ ⟨13, 2, 0, 339491, 105645, 2517, 16384⟩
    (by decide) selected_cut_12879

theorem selected_cut_12880 : selected 8 ⟨339507, by decide⟩
    (prefixPartial 13 105646) = some ⟨13, 2, 0, 339507, 105646, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_105646_339507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105646 ⟨339507, by decide⟩ :=
  accepted_of_selected 13 105646 ⟨339507, by decide⟩ ⟨13, 2, 0, 339507, 105646, 1249, 16384⟩
    (by decide) selected_cut_12880

theorem selected_cut_12881 : selected 8 ⟨339512, by decide⟩
    (prefixPartial 13 105647) = some ⟨13, 2, 0, 339512, 105647, 689, 16384⟩ := by
  decide +kernel

theorem context_13_105647_339512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105647 ⟨339512, by decide⟩ :=
  accepted_of_selected 13 105647 ⟨339512, by decide⟩ ⟨13, 2, 0, 339512, 105647, 689, 16384⟩
    (by decide) selected_cut_12881

theorem unmarked_context_12_26411_339513 : frontier 9 ⟨339513, by decide⟩
    (prefixCache 12 26411) (prefixPartial 12 26411) = false := by
  decide +kernel

theorem node_context_12_26411_339513 : EJMOriginalGlobalDAGData.nodes 9 ⟨339513, by decide⟩ =
    .split (coordinate 12) (![⟨339451, by decide⟩,⟨339491, by decide⟩,⟨339507, by decide⟩,⟨339512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26411_339513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26411 ⟨339513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26411
    ⟨339513, by decide⟩ (by decide) (![⟨339451, by decide⟩,⟨339491, by decide⟩,⟨339507, by decide⟩,⟨339512, by decide⟩]) unmarked_context_12_26411_339513 node_context_12_26411_339513
  intro a
  fin_cases a
  · exact context_13_105644_339451
  · exact context_13_105645_339491
  · exact context_13_105646_339507
  · exact context_13_105647_339512

theorem unmarked_context_11_6602_339514 : frontier 10 ⟨339514, by decide⟩
    (prefixCache 11 6602) (prefixPartial 11 6602) = false := by
  decide +kernel

theorem node_context_11_6602_339514 : EJMOriginalGlobalDAGData.nodes 10 ⟨339514, by decide⟩ =
    .split (coordinate 11) (![⟨339295, by decide⟩,⟨339375, by decide⟩,⟨339442, by decide⟩,⟨339513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6602_339514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6602 ⟨339514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6602
    ⟨339514, by decide⟩ (by decide) (![⟨339295, by decide⟩,⟨339375, by decide⟩,⟨339442, by decide⟩,⟨339513, by decide⟩]) unmarked_context_11_6602_339514 node_context_11_6602_339514
  intro a
  fin_cases a
  · exact context_12_26408_339295
  · exact context_12_26409_339375
  · exact context_12_26410_339442
  · exact context_12_26411_339513

theorem selected_cut_12882 : selected 9 ⟨339569, by decide⟩
    (prefixPartial 12 26412) = some ⟨12, 2, 0, 339569, 26412, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_26412_339569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26412 ⟨339569, by decide⟩ :=
  accepted_of_selected 12 26412 ⟨339569, by decide⟩ ⟨12, 2, 0, 339569, 26412, 3965, 65536⟩
    (by decide) selected_cut_12882

theorem selected_cut_12883 : selected 8 ⟨339578, by decide⟩
    (prefixPartial 13 105652) = some ⟨13, 2, 0, 339578, 105652, 737, 16384⟩ := by
  decide +kernel

theorem context_13_105652_339578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105652 ⟨339578, by decide⟩ :=
  accepted_of_selected 13 105652 ⟨339578, by decide⟩ ⟨13, 2, 0, 339578, 105652, 737, 16384⟩
    (by decide) selected_cut_12883

theorem selected_cut_12884 : selected 8 ⟨339622, by decide⟩
    (prefixPartial 13 105653) = some ⟨13, 2, 0, 339622, 105653, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_105653_339622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105653 ⟨339622, by decide⟩ :=
  accepted_of_selected 13 105653 ⟨339622, by decide⟩ ⟨13, 2, 0, 339622, 105653, 2197, 16384⟩
    (by decide) selected_cut_12884

theorem selected_cut_12885 : selected 8 ⟨339644, by decide⟩
    (prefixPartial 13 105654) = some ⟨13, 2, 0, 339644, 105654, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_105654_339644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105654 ⟨339644, by decide⟩ :=
  accepted_of_selected 13 105654 ⟨339644, by decide⟩ ⟨13, 2, 0, 339644, 105654, 1273, 16384⟩
    (by decide) selected_cut_12885

theorem selected_cut_12886 : selected 8 ⟨339654, by decide⟩
    (prefixPartial 13 105655) = some ⟨13, 2, 0, 339654, 105655, 653, 16384⟩ := by
  decide +kernel

theorem context_13_105655_339654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105655 ⟨339654, by decide⟩ :=
  accepted_of_selected 13 105655 ⟨339654, by decide⟩ ⟨13, 2, 0, 339654, 105655, 653, 16384⟩
    (by decide) selected_cut_12886

theorem unmarked_context_12_26413_339655 : frontier 9 ⟨339655, by decide⟩
    (prefixCache 12 26413) (prefixPartial 12 26413) = false := by
  decide +kernel

theorem node_context_12_26413_339655 : EJMOriginalGlobalDAGData.nodes 9 ⟨339655, by decide⟩ =
    .split (coordinate 12) (![⟨339578, by decide⟩,⟨339622, by decide⟩,⟨339644, by decide⟩,⟨339654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26413_339655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26413 ⟨339655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26413
    ⟨339655, by decide⟩ (by decide) (![⟨339578, by decide⟩,⟨339622, by decide⟩,⟨339644, by decide⟩,⟨339654, by decide⟩]) unmarked_context_12_26413_339655 node_context_12_26413_339655
  intro a
  fin_cases a
  · exact context_13_105652_339578
  · exact context_13_105653_339622
  · exact context_13_105654_339644
  · exact context_13_105655_339654

theorem selected_cut_12887 : selected 8 ⟨339666, by decide⟩
    (prefixPartial 13 105656) = some ⟨13, 2, 0, 339666, 105656, 677, 16384⟩ := by
  decide +kernel

theorem context_13_105656_339666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105656 ⟨339666, by decide⟩ :=
  accepted_of_selected 13 105656 ⟨339666, by decide⟩ ⟨13, 2, 0, 339666, 105656, 677, 16384⟩
    (by decide) selected_cut_12887

theorem selected_cut_12888 : selected 8 ⟨339703, by decide⟩
    (prefixPartial 13 105657) = some ⟨13, 2, 0, 339703, 105657, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_105657_339703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105657 ⟨339703, by decide⟩ :=
  accepted_of_selected 13 105657 ⟨339703, by decide⟩ ⟨13, 2, 0, 339703, 105657, 2101, 16384⟩
    (by decide) selected_cut_12888

theorem selected_cut_12889 : selected 8 ⟨339718, by decide⟩
    (prefixPartial 13 105658) = some ⟨13, 2, 0, 339718, 105658, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_105658_339718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105658 ⟨339718, by decide⟩ :=
  accepted_of_selected 13 105658 ⟨339718, by decide⟩ ⟨13, 2, 0, 339718, 105658, 1085, 16384⟩
    (by decide) selected_cut_12889

theorem selected_cut_12890 : selected 8 ⟨339726, by decide⟩
    (prefixPartial 13 105659) = some ⟨13, 2, 0, 339726, 105659, 721, 16384⟩ := by
  decide +kernel

theorem context_13_105659_339726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105659 ⟨339726, by decide⟩ :=
  accepted_of_selected 13 105659 ⟨339726, by decide⟩ ⟨13, 2, 0, 339726, 105659, 721, 16384⟩
    (by decide) selected_cut_12890

theorem unmarked_context_12_26414_339727 : frontier 9 ⟨339727, by decide⟩
    (prefixCache 12 26414) (prefixPartial 12 26414) = false := by
  decide +kernel

theorem node_context_12_26414_339727 : EJMOriginalGlobalDAGData.nodes 9 ⟨339727, by decide⟩ =
    .split (coordinate 12) (![⟨339666, by decide⟩,⟨339703, by decide⟩,⟨339718, by decide⟩,⟨339726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26414_339727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26414 ⟨339727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26414
    ⟨339727, by decide⟩ (by decide) (![⟨339666, by decide⟩,⟨339703, by decide⟩,⟨339718, by decide⟩,⟨339726, by decide⟩]) unmarked_context_12_26414_339727 node_context_12_26414_339727
  intro a
  fin_cases a
  · exact context_13_105656_339666
  · exact context_13_105657_339703
  · exact context_13_105658_339718
  · exact context_13_105659_339726

theorem selected_cut_12891 : selected 8 ⟨339742, by decide⟩
    (prefixPartial 13 105660) = some ⟨13, 2, 0, 339742, 105660, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_105660_339742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105660 ⟨339742, by decide⟩ :=
  accepted_of_selected 13 105660 ⟨339742, by decide⟩ ⟨13, 2, 0, 339742, 105660, 1009, 16384⟩
    (by decide) selected_cut_12891

theorem selected_cut_12892 : selected 8 ⟨339823, by decide⟩
    (prefixPartial 13 105661) = some ⟨13, 2, 0, 339823, 105661, 3849, 16384⟩ := by
  decide +kernel

theorem context_13_105661_339823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105661 ⟨339823, by decide⟩ :=
  accepted_of_selected 13 105661 ⟨339823, by decide⟩ ⟨13, 2, 0, 339823, 105661, 3849, 16384⟩
    (by decide) selected_cut_12892

theorem selected_cut_12893 : selected 8 ⟨339861, by decide⟩
    (prefixPartial 13 105662) = some ⟨13, 2, 0, 339861, 105662, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_105662_339861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105662 ⟨339861, by decide⟩ :=
  accepted_of_selected 13 105662 ⟨339861, by decide⟩ ⟨13, 2, 0, 339861, 105662, 2057, 16384⟩
    (by decide) selected_cut_12893

theorem selected_cut_12894 : selected 8 ⟨339892, by decide⟩
    (prefixPartial 13 105663) = some ⟨13, 2, 0, 339892, 105663, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_105663_339892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105663 ⟨339892, by decide⟩ :=
  accepted_of_selected 13 105663 ⟨339892, by decide⟩ ⟨13, 2, 0, 339892, 105663, 1053, 16384⟩
    (by decide) selected_cut_12894

theorem unmarked_context_12_26415_339893 : frontier 9 ⟨339893, by decide⟩
    (prefixCache 12 26415) (prefixPartial 12 26415) = false := by
  decide +kernel

theorem node_context_12_26415_339893 : EJMOriginalGlobalDAGData.nodes 9 ⟨339893, by decide⟩ =
    .split (coordinate 12) (![⟨339742, by decide⟩,⟨339823, by decide⟩,⟨339861, by decide⟩,⟨339892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26415_339893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26415 ⟨339893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26415
    ⟨339893, by decide⟩ (by decide) (![⟨339742, by decide⟩,⟨339823, by decide⟩,⟨339861, by decide⟩,⟨339892, by decide⟩]) unmarked_context_12_26415_339893 node_context_12_26415_339893
  intro a
  fin_cases a
  · exact context_13_105660_339742
  · exact context_13_105661_339823
  · exact context_13_105662_339861
  · exact context_13_105663_339892

theorem unmarked_context_11_6603_339894 : frontier 10 ⟨339894, by decide⟩
    (prefixCache 11 6603) (prefixPartial 11 6603) = false := by
  decide +kernel

theorem node_context_11_6603_339894 : EJMOriginalGlobalDAGData.nodes 10 ⟨339894, by decide⟩ =
    .split (coordinate 11) (![⟨339569, by decide⟩,⟨339655, by decide⟩,⟨339727, by decide⟩,⟨339893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6603_339894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6603 ⟨339894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6603
    ⟨339894, by decide⟩ (by decide) (![⟨339569, by decide⟩,⟨339655, by decide⟩,⟨339727, by decide⟩,⟨339893, by decide⟩]) unmarked_context_11_6603_339894 node_context_11_6603_339894
  intro a
  fin_cases a
  · exact context_12_26412_339569
  · exact context_12_26413_339655
  · exact context_12_26414_339727
  · exact context_12_26415_339893

theorem unmarked_context_10_1650_339895 : frontier 11 ⟨339895, by decide⟩
    (prefixCache 10 1650) (prefixPartial 10 1650) = false := by
  decide +kernel

theorem node_context_10_1650_339895 : EJMOriginalGlobalDAGData.nodes 11 ⟨339895, by decide⟩ =
    .split (coordinate 10) (![⟨338959, by decide⟩,⟨339228, by decide⟩,⟨339514, by decide⟩,⟨339894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1650_339895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1650 ⟨339895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1650
    ⟨339895, by decide⟩ (by decide) (![⟨338959, by decide⟩,⟨339228, by decide⟩,⟨339514, by decide⟩,⟨339894, by decide⟩]) unmarked_context_10_1650_339895 node_context_10_1650_339895
  intro a
  fin_cases a
  · exact context_11_6600_338959
  · exact context_11_6601_339228
  · exact context_11_6602_339514
  · exact context_11_6603_339894

theorem selected_cut_12895 : selected 8 ⟨339901, by decide⟩
    (prefixPartial 13 105664) = some ⟨13, 2, 0, 339901, 105664, 469, 16384⟩ := by
  decide +kernel

theorem context_13_105664_339901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105664 ⟨339901, by decide⟩ :=
  accepted_of_selected 13 105664 ⟨339901, by decide⟩ ⟨13, 2, 0, 339901, 105664, 469, 16384⟩
    (by decide) selected_cut_12895

theorem selected_cut_12896 : selected 8 ⟨339923, by decide⟩
    (prefixPartial 13 105665) = some ⟨13, 2, 0, 339923, 105665, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_105665_339923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105665 ⟨339923, by decide⟩ :=
  accepted_of_selected 13 105665 ⟨339923, by decide⟩ ⟨13, 2, 0, 339923, 105665, 1721, 16384⟩
    (by decide) selected_cut_12896

theorem selected_cut_12897 : selected 8 ⟨339937, by decide⟩
    (prefixPartial 13 105666) = some ⟨13, 2, 0, 339937, 105666, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_105666_339937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105666 ⟨339937, by decide⟩ :=
  accepted_of_selected 13 105666 ⟨339937, by decide⟩ ⟨13, 2, 0, 339937, 105666, 1233, 16384⟩
    (by decide) selected_cut_12897

theorem selected_cut_12898 : selected 8 ⟨339943, by decide⟩
    (prefixPartial 13 105667) = some ⟨13, 2, 0, 339943, 105667, 781, 16384⟩ := by
  decide +kernel

theorem context_13_105667_339943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105667 ⟨339943, by decide⟩ :=
  accepted_of_selected 13 105667 ⟨339943, by decide⟩ ⟨13, 2, 0, 339943, 105667, 781, 16384⟩
    (by decide) selected_cut_12898

theorem unmarked_context_12_26416_339944 : frontier 9 ⟨339944, by decide⟩
    (prefixCache 12 26416) (prefixPartial 12 26416) = false := by
  decide +kernel

theorem node_context_12_26416_339944 : EJMOriginalGlobalDAGData.nodes 9 ⟨339944, by decide⟩ =
    .split (coordinate 12) (![⟨339901, by decide⟩,⟨339923, by decide⟩,⟨339937, by decide⟩,⟨339943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26416_339944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26416 ⟨339944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26416
    ⟨339944, by decide⟩ (by decide) (![⟨339901, by decide⟩,⟨339923, by decide⟩,⟨339937, by decide⟩,⟨339943, by decide⟩]) unmarked_context_12_26416_339944 node_context_12_26416_339944
  intro a
  fin_cases a
  · exact context_13_105664_339901
  · exact context_13_105665_339923
  · exact context_13_105666_339937
  · exact context_13_105667_339943

theorem selected_cut_12899 : selected 8 ⟨339951, by decide⟩
    (prefixPartial 13 105668) = some ⟨13, 2, 0, 339951, 105668, 605, 16384⟩ := by
  decide +kernel

theorem context_13_105668_339951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105668 ⟨339951, by decide⟩ :=
  accepted_of_selected 13 105668 ⟨339951, by decide⟩ ⟨13, 2, 0, 339951, 105668, 605, 16384⟩
    (by decide) selected_cut_12899

theorem selected_cut_12900 : selected 8 ⟨339980, by decide⟩
    (prefixPartial 13 105669) = some ⟨13, 2, 0, 339980, 105669, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_105669_339980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105669 ⟨339980, by decide⟩ :=
  accepted_of_selected 13 105669 ⟨339980, by decide⟩ ⟨13, 2, 0, 339980, 105669, 2429, 16384⟩
    (by decide) selected_cut_12900

theorem selected_cut_12901 : selected 8 ⟨340003, by decide⟩
    (prefixPartial 13 105670) = some ⟨13, 2, 0, 340003, 105670, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_105670_340003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105670 ⟨340003, by decide⟩ :=
  accepted_of_selected 13 105670 ⟨340003, by decide⟩ ⟨13, 2, 0, 340003, 105670, 1641, 16384⟩
    (by decide) selected_cut_12901

theorem selected_cut_12902 : selected 8 ⟨340009, by decide⟩
    (prefixPartial 13 105671) = some ⟨13, 2, 0, 340009, 105671, 661, 16384⟩ := by
  decide +kernel

theorem context_13_105671_340009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105671 ⟨340009, by decide⟩ :=
  accepted_of_selected 13 105671 ⟨340009, by decide⟩ ⟨13, 2, 0, 340009, 105671, 661, 16384⟩
    (by decide) selected_cut_12902

theorem unmarked_context_12_26417_340010 : frontier 9 ⟨340010, by decide⟩
    (prefixCache 12 26417) (prefixPartial 12 26417) = false := by
  decide +kernel

theorem node_context_12_26417_340010 : EJMOriginalGlobalDAGData.nodes 9 ⟨340010, by decide⟩ =
    .split (coordinate 12) (![⟨339951, by decide⟩,⟨339980, by decide⟩,⟨340003, by decide⟩,⟨340009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26417_340010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26417 ⟨340010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26417
    ⟨340010, by decide⟩ (by decide) (![⟨339951, by decide⟩,⟨339980, by decide⟩,⟨340003, by decide⟩,⟨340009, by decide⟩]) unmarked_context_12_26417_340010 node_context_12_26417_340010
  intro a
  fin_cases a
  · exact context_13_105668_339951
  · exact context_13_105669_339980
  · exact context_13_105670_340003
  · exact context_13_105671_340009

theorem selected_cut_12903 : selected 8 ⟨340018, by decide⟩
    (prefixPartial 13 105672) = some ⟨13, 2, 0, 340018, 105672, 541, 16384⟩ := by
  decide +kernel

theorem context_13_105672_340018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105672 ⟨340018, by decide⟩ :=
  accepted_of_selected 13 105672 ⟨340018, by decide⟩ ⟨13, 2, 0, 340018, 105672, 541, 16384⟩
    (by decide) selected_cut_12903

theorem selected_cut_12904 : selected 8 ⟨340050, by decide⟩
    (prefixPartial 13 105673) = some ⟨13, 2, 0, 340050, 105673, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_105673_340050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105673 ⟨340050, by decide⟩ :=
  accepted_of_selected 13 105673 ⟨340050, by decide⟩ ⟨13, 2, 0, 340050, 105673, 2257, 16384⟩
    (by decide) selected_cut_12904

theorem selected_cut_12905 : selected 8 ⟨340071, by decide⟩
    (prefixPartial 13 105674) = some ⟨13, 2, 0, 340071, 105674, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_105674_340071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105674 ⟨340071, by decide⟩ :=
  accepted_of_selected 13 105674 ⟨340071, by decide⟩ ⟨13, 2, 0, 340071, 105674, 1509, 16384⟩
    (by decide) selected_cut_12905

theorem selected_cut_12906 : selected 8 ⟨340079, by decide⟩
    (prefixPartial 13 105675) = some ⟨13, 2, 0, 340079, 105675, 729, 16384⟩ := by
  decide +kernel

theorem context_13_105675_340079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105675 ⟨340079, by decide⟩ :=
  accepted_of_selected 13 105675 ⟨340079, by decide⟩ ⟨13, 2, 0, 340079, 105675, 729, 16384⟩
    (by decide) selected_cut_12906

theorem unmarked_context_12_26418_340080 : frontier 9 ⟨340080, by decide⟩
    (prefixCache 12 26418) (prefixPartial 12 26418) = false := by
  decide +kernel

theorem node_context_12_26418_340080 : EJMOriginalGlobalDAGData.nodes 9 ⟨340080, by decide⟩ =
    .split (coordinate 12) (![⟨340018, by decide⟩,⟨340050, by decide⟩,⟨340071, by decide⟩,⟨340079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26418_340080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26418 ⟨340080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26418
    ⟨340080, by decide⟩ (by decide) (![⟨340018, by decide⟩,⟨340050, by decide⟩,⟨340071, by decide⟩,⟨340079, by decide⟩]) unmarked_context_12_26418_340080 node_context_12_26418_340080
  intro a
  fin_cases a
  · exact context_13_105672_340018
  · exact context_13_105673_340050
  · exact context_13_105674_340071
  · exact context_13_105675_340079

theorem selected_cut_12907 : selected 8 ⟨340086, by decide⟩
    (prefixPartial 13 105676) = some ⟨13, 2, 0, 340086, 105676, 525, 16384⟩ := by
  decide +kernel

theorem context_13_105676_340086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105676 ⟨340086, by decide⟩ :=
  accepted_of_selected 13 105676 ⟨340086, by decide⟩ ⟨13, 2, 0, 340086, 105676, 525, 16384⟩
    (by decide) selected_cut_12907

theorem selected_cut_12908 : selected 8 ⟨340113, by decide⟩
    (prefixPartial 13 105677) = some ⟨13, 2, 0, 340113, 105677, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_105677_340113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105677 ⟨340113, by decide⟩ :=
  accepted_of_selected 13 105677 ⟨340113, by decide⟩ ⟨13, 2, 0, 340113, 105677, 2529, 16384⟩
    (by decide) selected_cut_12908

theorem selected_cut_12909 : selected 8 ⟨340134, by decide⟩
    (prefixPartial 13 105678) = some ⟨13, 2, 0, 340134, 105678, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_105678_340134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105678 ⟨340134, by decide⟩ :=
  accepted_of_selected 13 105678 ⟨340134, by decide⟩ ⟨13, 2, 0, 340134, 105678, 1429, 16384⟩
    (by decide) selected_cut_12909

theorem selected_cut_12910 : selected 8 ⟨340139, by decide⟩
    (prefixPartial 13 105679) = some ⟨13, 2, 0, 340139, 105679, 653, 16384⟩ := by
  decide +kernel

theorem context_13_105679_340139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105679 ⟨340139, by decide⟩ :=
  accepted_of_selected 13 105679 ⟨340139, by decide⟩ ⟨13, 2, 0, 340139, 105679, 653, 16384⟩
    (by decide) selected_cut_12910

theorem unmarked_context_12_26419_340140 : frontier 9 ⟨340140, by decide⟩
    (prefixCache 12 26419) (prefixPartial 12 26419) = false := by
  decide +kernel

theorem node_context_12_26419_340140 : EJMOriginalGlobalDAGData.nodes 9 ⟨340140, by decide⟩ =
    .split (coordinate 12) (![⟨340086, by decide⟩,⟨340113, by decide⟩,⟨340134, by decide⟩,⟨340139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26419_340140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26419 ⟨340140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26419
    ⟨340140, by decide⟩ (by decide) (![⟨340086, by decide⟩,⟨340113, by decide⟩,⟨340134, by decide⟩,⟨340139, by decide⟩]) unmarked_context_12_26419_340140 node_context_12_26419_340140
  intro a
  fin_cases a
  · exact context_13_105676_340086
  · exact context_13_105677_340113
  · exact context_13_105678_340134
  · exact context_13_105679_340139

theorem unmarked_context_11_6604_340141 : frontier 10 ⟨340141, by decide⟩
    (prefixCache 11 6604) (prefixPartial 11 6604) = false := by
  decide +kernel

theorem node_context_11_6604_340141 : EJMOriginalGlobalDAGData.nodes 10 ⟨340141, by decide⟩ =
    .split (coordinate 11) (![⟨339944, by decide⟩,⟨340010, by decide⟩,⟨340080, by decide⟩,⟨340140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6604_340141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6604 ⟨340141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6604
    ⟨340141, by decide⟩ (by decide) (![⟨339944, by decide⟩,⟨340010, by decide⟩,⟨340080, by decide⟩,⟨340140, by decide⟩]) unmarked_context_11_6604_340141 node_context_11_6604_340141
  intro a
  fin_cases a
  · exact context_12_26416_339944
  · exact context_12_26417_340010
  · exact context_12_26418_340080
  · exact context_12_26419_340140

theorem selected_cut_12911 : selected 8 ⟨340146, by decide⟩
    (prefixPartial 13 105680) = some ⟨13, 2, 0, 340146, 105680, 313, 16384⟩ := by
  decide +kernel

theorem context_13_105680_340146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105680 ⟨340146, by decide⟩ :=
  accepted_of_selected 13 105680 ⟨340146, by decide⟩ ⟨13, 2, 0, 340146, 105680, 313, 16384⟩
    (by decide) selected_cut_12911

theorem selected_cut_12912 : selected 8 ⟨340182, by decide⟩
    (prefixPartial 13 105681) = some ⟨13, 2, 0, 340182, 105681, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_105681_340182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105681 ⟨340182, by decide⟩ :=
  accepted_of_selected 13 105681 ⟨340182, by decide⟩ ⟨13, 2, 0, 340182, 105681, 2265, 16384⟩
    (by decide) selected_cut_12912

theorem selected_cut_12913 : selected 8 ⟨340197, by decide⟩
    (prefixPartial 13 105682) = some ⟨13, 2, 0, 340197, 105682, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_105682_340197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105682 ⟨340197, by decide⟩ :=
  accepted_of_selected 13 105682 ⟨340197, by decide⟩ ⟨13, 2, 0, 340197, 105682, 1329, 16384⟩
    (by decide) selected_cut_12913

theorem selected_cut_12914 : selected 8 ⟨340202, by decide⟩
    (prefixPartial 13 105683) = some ⟨13, 2, 0, 340202, 105683, 789, 16384⟩ := by
  decide +kernel

theorem context_13_105683_340202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105683 ⟨340202, by decide⟩ :=
  accepted_of_selected 13 105683 ⟨340202, by decide⟩ ⟨13, 2, 0, 340202, 105683, 789, 16384⟩
    (by decide) selected_cut_12914

theorem unmarked_context_12_26420_340203 : frontier 9 ⟨340203, by decide⟩
    (prefixCache 12 26420) (prefixPartial 12 26420) = false := by
  decide +kernel

theorem node_context_12_26420_340203 : EJMOriginalGlobalDAGData.nodes 9 ⟨340203, by decide⟩ =
    .split (coordinate 12) (![⟨340146, by decide⟩,⟨340182, by decide⟩,⟨340197, by decide⟩,⟨340202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26420_340203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26420 ⟨340203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26420
    ⟨340203, by decide⟩ (by decide) (![⟨340146, by decide⟩,⟨340182, by decide⟩,⟨340197, by decide⟩,⟨340202, by decide⟩]) unmarked_context_12_26420_340203 node_context_12_26420_340203
  intro a
  fin_cases a
  · exact context_13_105680_340146
  · exact context_13_105681_340182
  · exact context_13_105682_340197
  · exact context_13_105683_340202

theorem selected_cut_12915 : selected 8 ⟨340208, by decide⟩
    (prefixPartial 13 105684) = some ⟨13, 2, 0, 340208, 105684, 373, 16384⟩ := by
  decide +kernel

theorem context_13_105684_340208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105684 ⟨340208, by decide⟩ :=
  accepted_of_selected 13 105684 ⟨340208, by decide⟩ ⟨13, 2, 0, 340208, 105684, 373, 16384⟩
    (by decide) selected_cut_12915

theorem selected_cut_12916 : selected 8 ⟨340236, by decide⟩
    (prefixPartial 13 105685) = some ⟨13, 2, 0, 340236, 105685, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_105685_340236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105685 ⟨340236, by decide⟩ :=
  accepted_of_selected 13 105685 ⟨340236, by decide⟩ ⟨13, 2, 0, 340236, 105685, 2613, 16384⟩
    (by decide) selected_cut_12916

theorem selected_cut_12917 : selected 8 ⟨340256, by decide⟩
    (prefixPartial 13 105686) = some ⟨13, 2, 0, 340256, 105686, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_105686_340256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105686 ⟨340256, by decide⟩ :=
  accepted_of_selected 13 105686 ⟨340256, by decide⟩ ⟨13, 2, 0, 340256, 105686, 1473, 16384⟩
    (by decide) selected_cut_12917

theorem selected_cut_12918 : selected 8 ⟨340260, by decide⟩
    (prefixPartial 13 105687) = some ⟨13, 2, 0, 340260, 105687, 725, 16384⟩ := by
  decide +kernel

theorem context_13_105687_340260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105687 ⟨340260, by decide⟩ :=
  accepted_of_selected 13 105687 ⟨340260, by decide⟩ ⟨13, 2, 0, 340260, 105687, 725, 16384⟩
    (by decide) selected_cut_12918

theorem unmarked_context_12_26421_340261 : frontier 9 ⟨340261, by decide⟩
    (prefixCache 12 26421) (prefixPartial 12 26421) = false := by
  decide +kernel

theorem node_context_12_26421_340261 : EJMOriginalGlobalDAGData.nodes 9 ⟨340261, by decide⟩ =
    .split (coordinate 12) (![⟨340208, by decide⟩,⟨340236, by decide⟩,⟨340256, by decide⟩,⟨340260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26421_340261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26421 ⟨340261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26421
    ⟨340261, by decide⟩ (by decide) (![⟨340208, by decide⟩,⟨340236, by decide⟩,⟨340256, by decide⟩,⟨340260, by decide⟩]) unmarked_context_12_26421_340261 node_context_12_26421_340261
  intro a
  fin_cases a
  · exact context_13_105684_340208
  · exact context_13_105685_340236
  · exact context_13_105686_340256
  · exact context_13_105687_340260

theorem selected_cut_12919 : selected 8 ⟨340266, by decide⟩
    (prefixPartial 13 105688) = some ⟨13, 2, 0, 340266, 105688, 341, 16384⟩ := by
  decide +kernel

theorem context_13_105688_340266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105688 ⟨340266, by decide⟩ :=
  accepted_of_selected 13 105688 ⟨340266, by decide⟩ ⟨13, 2, 0, 340266, 105688, 341, 16384⟩
    (by decide) selected_cut_12919

theorem selected_cut_12920 : selected 8 ⟨340300, by decide⟩
    (prefixPartial 13 105689) = some ⟨13, 2, 0, 340300, 105689, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_105689_340300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105689 ⟨340300, by decide⟩ :=
  accepted_of_selected 13 105689 ⟨340300, by decide⟩ ⟨13, 2, 0, 340300, 105689, 2529, 16384⟩
    (by decide) selected_cut_12920

theorem selected_cut_12921 : selected 8 ⟨340322, by decide⟩
    (prefixPartial 13 105690) = some ⟨13, 2, 0, 340322, 105690, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_105690_340322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105690 ⟨340322, by decide⟩ :=
  accepted_of_selected 13 105690 ⟨340322, by decide⟩ ⟨13, 2, 0, 340322, 105690, 1441, 16384⟩
    (by decide) selected_cut_12921

theorem selected_cut_12922 : selected 8 ⟨340330, by decide⟩
    (prefixPartial 13 105691) = some ⟨13, 2, 0, 340330, 105691, 849, 16384⟩ := by
  decide +kernel

theorem context_13_105691_340330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105691 ⟨340330, by decide⟩ :=
  accepted_of_selected 13 105691 ⟨340330, by decide⟩ ⟨13, 2, 0, 340330, 105691, 849, 16384⟩
    (by decide) selected_cut_12922

theorem unmarked_context_12_26422_340331 : frontier 9 ⟨340331, by decide⟩
    (prefixCache 12 26422) (prefixPartial 12 26422) = false := by
  decide +kernel

theorem node_context_12_26422_340331 : EJMOriginalGlobalDAGData.nodes 9 ⟨340331, by decide⟩ =
    .split (coordinate 12) (![⟨340266, by decide⟩,⟨340300, by decide⟩,⟨340322, by decide⟩,⟨340330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26422_340331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26422 ⟨340331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26422
    ⟨340331, by decide⟩ (by decide) (![⟨340266, by decide⟩,⟨340300, by decide⟩,⟨340322, by decide⟩,⟨340330, by decide⟩]) unmarked_context_12_26422_340331 node_context_12_26422_340331
  intro a
  fin_cases a
  · exact context_13_105688_340266
  · exact context_13_105689_340300
  · exact context_13_105690_340322
  · exact context_13_105691_340330

theorem selected_cut_12923 : selected 8 ⟨340336, by decide⟩
    (prefixPartial 13 105692) = some ⟨13, 2, 0, 340336, 105692, 297, 16384⟩ := by
  decide +kernel

theorem context_13_105692_340336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105692 ⟨340336, by decide⟩ :=
  accepted_of_selected 13 105692 ⟨340336, by decide⟩ ⟨13, 2, 0, 340336, 105692, 297, 16384⟩
    (by decide) selected_cut_12923

theorem selected_cut_12924 : selected 8 ⟨340365, by decide⟩
    (prefixPartial 13 105693) = some ⟨13, 2, 0, 340365, 105693, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_105693_340365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105693 ⟨340365, by decide⟩ :=
  accepted_of_selected 13 105693 ⟨340365, by decide⟩ ⟨13, 2, 0, 340365, 105693, 2569, 16384⟩
    (by decide) selected_cut_12924

theorem selected_cut_12925 : selected 8 ⟨340384, by decide⟩
    (prefixPartial 13 105694) = some ⟨13, 2, 0, 340384, 105694, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_105694_340384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105694 ⟨340384, by decide⟩ :=
  accepted_of_selected 13 105694 ⟨340384, by decide⟩ ⟨13, 2, 0, 340384, 105694, 1377, 16384⟩
    (by decide) selected_cut_12925

theorem selected_cut_12926 : selected 8 ⟨340391, by decide⟩
    (prefixPartial 13 105695) = some ⟨13, 2, 0, 340391, 105695, 749, 16384⟩ := by
  decide +kernel

theorem context_13_105695_340391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105695 ⟨340391, by decide⟩ :=
  accepted_of_selected 13 105695 ⟨340391, by decide⟩ ⟨13, 2, 0, 340391, 105695, 749, 16384⟩
    (by decide) selected_cut_12926

theorem unmarked_context_12_26423_340392 : frontier 9 ⟨340392, by decide⟩
    (prefixCache 12 26423) (prefixPartial 12 26423) = false := by
  decide +kernel

theorem node_context_12_26423_340392 : EJMOriginalGlobalDAGData.nodes 9 ⟨340392, by decide⟩ =
    .split (coordinate 12) (![⟨340336, by decide⟩,⟨340365, by decide⟩,⟨340384, by decide⟩,⟨340391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26423_340392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26423 ⟨340392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26423
    ⟨340392, by decide⟩ (by decide) (![⟨340336, by decide⟩,⟨340365, by decide⟩,⟨340384, by decide⟩,⟨340391, by decide⟩]) unmarked_context_12_26423_340392 node_context_12_26423_340392
  intro a
  fin_cases a
  · exact context_13_105692_340336
  · exact context_13_105693_340365
  · exact context_13_105694_340384
  · exact context_13_105695_340391

theorem unmarked_context_11_6605_340393 : frontier 10 ⟨340393, by decide⟩
    (prefixCache 11 6605) (prefixPartial 11 6605) = false := by
  decide +kernel

theorem node_context_11_6605_340393 : EJMOriginalGlobalDAGData.nodes 10 ⟨340393, by decide⟩ =
    .split (coordinate 11) (![⟨340203, by decide⟩,⟨340261, by decide⟩,⟨340331, by decide⟩,⟨340392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6605_340393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6605 ⟨340393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6605
    ⟨340393, by decide⟩ (by decide) (![⟨340203, by decide⟩,⟨340261, by decide⟩,⟨340331, by decide⟩,⟨340392, by decide⟩]) unmarked_context_11_6605_340393 node_context_11_6605_340393
  intro a
  fin_cases a
  · exact context_12_26420_340203
  · exact context_12_26421_340261
  · exact context_12_26422_340331
  · exact context_12_26423_340392

theorem selected_cut_12927 : selected 8 ⟨340397, by decide⟩
    (prefixPartial 13 105696) = some ⟨13, 2, 0, 340397, 105696, 225, 16384⟩ := by
  decide +kernel

theorem context_13_105696_340397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105696 ⟨340397, by decide⟩ :=
  accepted_of_selected 13 105696 ⟨340397, by decide⟩ ⟨13, 2, 0, 340397, 105696, 225, 16384⟩
    (by decide) selected_cut_12927

theorem selected_cut_12928 : selected 8 ⟨340427, by decide⟩
    (prefixPartial 13 105697) = some ⟨13, 2, 0, 340427, 105697, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_105697_340427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105697 ⟨340427, by decide⟩ :=
  accepted_of_selected 13 105697 ⟨340427, by decide⟩ ⟨13, 2, 0, 340427, 105697, 2285, 16384⟩
    (by decide) selected_cut_12928

theorem selected_cut_12929 : selected 8 ⟨340444, by decide⟩
    (prefixPartial 13 105698) = some ⟨13, 2, 0, 340444, 105698, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_105698_340444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105698 ⟨340444, by decide⟩ :=
  accepted_of_selected 13 105698 ⟨340444, by decide⟩ ⟨13, 2, 0, 340444, 105698, 1561, 16384⟩
    (by decide) selected_cut_12929

theorem selected_cut_12930 : selected 8 ⟨340452, by decide⟩
    (prefixPartial 13 105699) = some ⟨13, 2, 0, 340452, 105699, 825, 16384⟩ := by
  decide +kernel

theorem context_13_105699_340452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105699 ⟨340452, by decide⟩ :=
  accepted_of_selected 13 105699 ⟨340452, by decide⟩ ⟨13, 2, 0, 340452, 105699, 825, 16384⟩
    (by decide) selected_cut_12930

theorem unmarked_context_12_26424_340453 : frontier 9 ⟨340453, by decide⟩
    (prefixCache 12 26424) (prefixPartial 12 26424) = false := by
  decide +kernel

theorem node_context_12_26424_340453 : EJMOriginalGlobalDAGData.nodes 9 ⟨340453, by decide⟩ =
    .split (coordinate 12) (![⟨340397, by decide⟩,⟨340427, by decide⟩,⟨340444, by decide⟩,⟨340452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26424_340453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26424 ⟨340453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26424
    ⟨340453, by decide⟩ (by decide) (![⟨340397, by decide⟩,⟨340427, by decide⟩,⟨340444, by decide⟩,⟨340452, by decide⟩]) unmarked_context_12_26424_340453 node_context_12_26424_340453
  intro a
  fin_cases a
  · exact context_13_105696_340397
  · exact context_13_105697_340427
  · exact context_13_105698_340444
  · exact context_13_105699_340452

theorem selected_cut_12931 : selected 8 ⟨340457, by decide⟩
    (prefixPartial 13 105700) = some ⟨13, 2, 0, 340457, 105700, 261, 16384⟩ := by
  decide +kernel

theorem context_13_105700_340457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105700 ⟨340457, by decide⟩ :=
  accepted_of_selected 13 105700 ⟨340457, by decide⟩ ⟨13, 2, 0, 340457, 105700, 261, 16384⟩
    (by decide) selected_cut_12931

theorem selected_cut_12932 : selected 8 ⟨340499, by decide⟩
    (prefixPartial 13 105701) = some ⟨13, 2, 0, 340499, 105701, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_105701_340499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105701 ⟨340499, by decide⟩ :=
  accepted_of_selected 13 105701 ⟨340499, by decide⟩ ⟨13, 2, 0, 340499, 105701, 2749, 16384⟩
    (by decide) selected_cut_12932

theorem selected_cut_12933 : selected 8 ⟨340519, by decide⟩
    (prefixPartial 13 105702) = some ⟨13, 2, 0, 340519, 105702, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_105702_340519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105702 ⟨340519, by decide⟩ :=
  accepted_of_selected 13 105702 ⟨340519, by decide⟩ ⟨13, 2, 0, 340519, 105702, 1649, 16384⟩
    (by decide) selected_cut_12933

theorem selected_cut_12934 : selected 8 ⟨340528, by decide⟩
    (prefixPartial 13 105703) = some ⟨13, 2, 0, 340528, 105703, 829, 16384⟩ := by
  decide +kernel

theorem context_13_105703_340528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105703 ⟨340528, by decide⟩ :=
  accepted_of_selected 13 105703 ⟨340528, by decide⟩ ⟨13, 2, 0, 340528, 105703, 829, 16384⟩
    (by decide) selected_cut_12934

theorem unmarked_context_12_26425_340529 : frontier 9 ⟨340529, by decide⟩
    (prefixCache 12 26425) (prefixPartial 12 26425) = false := by
  decide +kernel

theorem node_context_12_26425_340529 : EJMOriginalGlobalDAGData.nodes 9 ⟨340529, by decide⟩ =
    .split (coordinate 12) (![⟨340457, by decide⟩,⟨340499, by decide⟩,⟨340519, by decide⟩,⟨340528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26425_340529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26425 ⟨340529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26425
    ⟨340529, by decide⟩ (by decide) (![⟨340457, by decide⟩,⟨340499, by decide⟩,⟨340519, by decide⟩,⟨340528, by decide⟩]) unmarked_context_12_26425_340529 node_context_12_26425_340529
  intro a
  fin_cases a
  · exact context_13_105700_340457
  · exact context_13_105701_340499
  · exact context_13_105702_340519
  · exact context_13_105703_340528

theorem selected_cut_12935 : selected 8 ⟨340532, by decide⟩
    (prefixPartial 13 105704) = some ⟨13, 2, 0, 340532, 105704, 181, 16384⟩ := by
  decide +kernel

theorem context_13_105704_340532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105704 ⟨340532, by decide⟩ :=
  accepted_of_selected 13 105704 ⟨340532, by decide⟩ ⟨13, 2, 0, 340532, 105704, 181, 16384⟩
    (by decide) selected_cut_12935

theorem selected_cut_12936 : selected 8 ⟨340560, by decide⟩
    (prefixPartial 13 105705) = some ⟨13, 2, 0, 340560, 105705, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_105705_340560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105705 ⟨340560, by decide⟩ :=
  accepted_of_selected 13 105705 ⟨340560, by decide⟩ ⟨13, 2, 0, 340560, 105705, 2437, 16384⟩
    (by decide) selected_cut_12936

theorem selected_cut_12937 : selected 8 ⟨340583, by decide⟩
    (prefixPartial 13 105706) = some ⟨13, 2, 0, 340583, 105706, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_105706_340583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105706 ⟨340583, by decide⟩ :=
  accepted_of_selected 13 105706 ⟨340583, by decide⟩ ⟨13, 2, 0, 340583, 105706, 1561, 16384⟩
    (by decide) selected_cut_12937

theorem selected_cut_12938 : selected 8 ⟨340589, by decide⟩
    (prefixPartial 13 105707) = some ⟨13, 2, 0, 340589, 105707, 829, 16384⟩ := by
  decide +kernel

theorem context_13_105707_340589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105707 ⟨340589, by decide⟩ :=
  accepted_of_selected 13 105707 ⟨340589, by decide⟩ ⟨13, 2, 0, 340589, 105707, 829, 16384⟩
    (by decide) selected_cut_12938

theorem unmarked_context_12_26426_340590 : frontier 9 ⟨340590, by decide⟩
    (prefixCache 12 26426) (prefixPartial 12 26426) = false := by
  decide +kernel

theorem node_context_12_26426_340590 : EJMOriginalGlobalDAGData.nodes 9 ⟨340590, by decide⟩ =
    .split (coordinate 12) (![⟨340532, by decide⟩,⟨340560, by decide⟩,⟨340583, by decide⟩,⟨340589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26426_340590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26426 ⟨340590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26426
    ⟨340590, by decide⟩ (by decide) (![⟨340532, by decide⟩,⟨340560, by decide⟩,⟨340583, by decide⟩,⟨340589, by decide⟩]) unmarked_context_12_26426_340590 node_context_12_26426_340590
  intro a
  fin_cases a
  · exact context_13_105704_340532
  · exact context_13_105705_340560
  · exact context_13_105706_340583
  · exact context_13_105707_340589

theorem selected_cut_12939 : selected 8 ⟨340594, by decide⟩
    (prefixPartial 13 105708) = some ⟨13, 2, 0, 340594, 105708, 157, 16384⟩ := by
  decide +kernel

theorem context_13_105708_340594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105708 ⟨340594, by decide⟩ :=
  accepted_of_selected 13 105708 ⟨340594, by decide⟩ ⟨13, 2, 0, 340594, 105708, 157, 16384⟩
    (by decide) selected_cut_12939

theorem selected_cut_12940 : selected 8 ⟨340638, by decide⟩
    (prefixPartial 13 105709) = some ⟨13, 2, 0, 340638, 105709, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_105709_340638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105709 ⟨340638, by decide⟩ :=
  accepted_of_selected 13 105709 ⟨340638, by decide⟩ ⟨13, 2, 0, 340638, 105709, 2813, 16384⟩
    (by decide) selected_cut_12940

theorem selected_cut_12941 : selected 8 ⟨340659, by decide⟩
    (prefixPartial 13 105710) = some ⟨13, 2, 0, 340659, 105710, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_105710_340659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105710 ⟨340659, by decide⟩ :=
  accepted_of_selected 13 105710 ⟨340659, by decide⟩ ⟨13, 2, 0, 340659, 105710, 1337, 16384⟩
    (by decide) selected_cut_12941

theorem selected_cut_12942 : selected 8 ⟨340666, by decide⟩
    (prefixPartial 13 105711) = some ⟨13, 2, 0, 340666, 105711, 689, 16384⟩ := by
  decide +kernel

theorem context_13_105711_340666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105711 ⟨340666, by decide⟩ :=
  accepted_of_selected 13 105711 ⟨340666, by decide⟩ ⟨13, 2, 0, 340666, 105711, 689, 16384⟩
    (by decide) selected_cut_12942

theorem unmarked_context_12_26427_340667 : frontier 9 ⟨340667, by decide⟩
    (prefixCache 12 26427) (prefixPartial 12 26427) = false := by
  decide +kernel

theorem node_context_12_26427_340667 : EJMOriginalGlobalDAGData.nodes 9 ⟨340667, by decide⟩ =
    .split (coordinate 12) (![⟨340594, by decide⟩,⟨340638, by decide⟩,⟨340659, by decide⟩,⟨340666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26427_340667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26427 ⟨340667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26427
    ⟨340667, by decide⟩ (by decide) (![⟨340594, by decide⟩,⟨340638, by decide⟩,⟨340659, by decide⟩,⟨340666, by decide⟩]) unmarked_context_12_26427_340667 node_context_12_26427_340667
  intro a
  fin_cases a
  · exact context_13_105708_340594
  · exact context_13_105709_340638
  · exact context_13_105710_340659
  · exact context_13_105711_340666

theorem unmarked_context_11_6606_340668 : frontier 10 ⟨340668, by decide⟩
    (prefixCache 11 6606) (prefixPartial 11 6606) = false := by
  decide +kernel

theorem node_context_11_6606_340668 : EJMOriginalGlobalDAGData.nodes 10 ⟨340668, by decide⟩ =
    .split (coordinate 11) (![⟨340453, by decide⟩,⟨340529, by decide⟩,⟨340590, by decide⟩,⟨340667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6606_340668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6606 ⟨340668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6606
    ⟨340668, by decide⟩ (by decide) (![⟨340453, by decide⟩,⟨340529, by decide⟩,⟨340590, by decide⟩,⟨340667, by decide⟩]) unmarked_context_11_6606_340668 node_context_11_6606_340668
  intro a
  fin_cases a
  · exact context_12_26424_340453
  · exact context_12_26425_340529
  · exact context_12_26426_340590
  · exact context_12_26427_340667

theorem selected_cut_12943 : selected 9 ⟨340720, by decide⟩
    (prefixPartial 12 26428) = some ⟨12, 2, 0, 340720, 26428, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_26428_340720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26428 ⟨340720, by decide⟩ :=
  accepted_of_selected 12 26428 ⟨340720, by decide⟩ ⟨12, 2, 0, 340720, 26428, 3669, 65536⟩
    (by decide) selected_cut_12943

theorem selected_cut_12944 : selected 8 ⟨340723, by decide⟩
    (prefixPartial 13 105716) = some ⟨13, 2, 0, 340723, 105716, 81, 16384⟩ := by
  decide +kernel

theorem context_13_105716_340723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105716 ⟨340723, by decide⟩ :=
  accepted_of_selected 13 105716 ⟨340723, by decide⟩ ⟨13, 2, 0, 340723, 105716, 81, 16384⟩
    (by decide) selected_cut_12944

theorem selected_cut_12945 : selected 8 ⟨340753, by decide⟩
    (prefixPartial 13 105717) = some ⟨13, 2, 0, 340753, 105717, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_105717_340753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105717 ⟨340753, by decide⟩ :=
  accepted_of_selected 13 105717 ⟨340753, by decide⟩ ⟨13, 2, 0, 340753, 105717, 2065, 16384⟩
    (by decide) selected_cut_12945

theorem selected_cut_12946 : selected 8 ⟨340774, by decide⟩
    (prefixPartial 13 105718) = some ⟨13, 2, 0, 340774, 105718, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_105718_340774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105718 ⟨340774, by decide⟩ :=
  accepted_of_selected 13 105718 ⟨340774, by decide⟩ ⟨13, 2, 0, 340774, 105718, 1441, 16384⟩
    (by decide) selected_cut_12946

theorem selected_cut_12947 : selected 8 ⟨340779, by decide⟩
    (prefixPartial 13 105719) = some ⟨13, 2, 0, 340779, 105719, 705, 16384⟩ := by
  decide +kernel

theorem context_13_105719_340779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105719 ⟨340779, by decide⟩ :=
  accepted_of_selected 13 105719 ⟨340779, by decide⟩ ⟨13, 2, 0, 340779, 105719, 705, 16384⟩
    (by decide) selected_cut_12947

theorem unmarked_context_12_26429_340780 : frontier 9 ⟨340780, by decide⟩
    (prefixCache 12 26429) (prefixPartial 12 26429) = false := by
  decide +kernel

theorem node_context_12_26429_340780 : EJMOriginalGlobalDAGData.nodes 9 ⟨340780, by decide⟩ =
    .split (coordinate 12) (![⟨340723, by decide⟩,⟨340753, by decide⟩,⟨340774, by decide⟩,⟨340779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26429_340780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26429 ⟨340780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26429
    ⟨340780, by decide⟩ (by decide) (![⟨340723, by decide⟩,⟨340753, by decide⟩,⟨340774, by decide⟩,⟨340779, by decide⟩]) unmarked_context_12_26429_340780 node_context_12_26429_340780
  intro a
  fin_cases a
  · exact context_13_105716_340723
  · exact context_13_105717_340753
  · exact context_13_105718_340774
  · exact context_13_105719_340779

theorem selected_cut_12948 : selected 8 ⟨340783, by decide⟩
    (prefixPartial 13 105720) = some ⟨13, 2, 0, 340783, 105720, 41, 16384⟩ := by
  decide +kernel

theorem context_13_105720_340783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105720 ⟨340783, by decide⟩ :=
  accepted_of_selected 13 105720 ⟨340783, by decide⟩ ⟨13, 2, 0, 340783, 105720, 41, 16384⟩
    (by decide) selected_cut_12948

theorem selected_cut_12949 : selected 8 ⟨340808, by decide⟩
    (prefixPartial 13 105721) = some ⟨13, 2, 0, 340808, 105721, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_105721_340808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105721 ⟨340808, by decide⟩ :=
  accepted_of_selected 13 105721 ⟨340808, by decide⟩ ⟨13, 2, 0, 340808, 105721, 2037, 16384⟩
    (by decide) selected_cut_12949

theorem selected_cut_12950 : selected 8 ⟨340824, by decide⟩
    (prefixPartial 13 105722) = some ⟨13, 2, 0, 340824, 105722, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_105722_340824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105722 ⟨340824, by decide⟩ :=
  accepted_of_selected 13 105722 ⟨340824, by decide⟩ ⟨13, 2, 0, 340824, 105722, 1333, 16384⟩
    (by decide) selected_cut_12950

theorem selected_cut_12951 : selected 8 ⟨340829, by decide⟩
    (prefixPartial 13 105723) = some ⟨13, 2, 0, 340829, 105723, 761, 16384⟩ := by
  decide +kernel

theorem context_13_105723_340829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105723 ⟨340829, by decide⟩ :=
  accepted_of_selected 13 105723 ⟨340829, by decide⟩ ⟨13, 2, 0, 340829, 105723, 761, 16384⟩
    (by decide) selected_cut_12951

theorem unmarked_context_12_26430_340830 : frontier 9 ⟨340830, by decide⟩
    (prefixCache 12 26430) (prefixPartial 12 26430) = false := by
  decide +kernel

theorem node_context_12_26430_340830 : EJMOriginalGlobalDAGData.nodes 9 ⟨340830, by decide⟩ =
    .split (coordinate 12) (![⟨340783, by decide⟩,⟨340808, by decide⟩,⟨340824, by decide⟩,⟨340829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26430_340830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26430 ⟨340830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26430
    ⟨340830, by decide⟩ (by decide) (![⟨340783, by decide⟩,⟨340808, by decide⟩,⟨340824, by decide⟩,⟨340829, by decide⟩]) unmarked_context_12_26430_340830 node_context_12_26430_340830
  intro a
  fin_cases a
  · exact context_13_105720_340783
  · exact context_13_105721_340808
  · exact context_13_105722_340824
  · exact context_13_105723_340829

theorem selected_cut_12952 : selected 9 ⟨340831, by decide⟩
    (prefixPartial 12 26431) = some ⟨12, 1, 0, 340831, 26431, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26431_340831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26431 ⟨340831, by decide⟩ :=
  accepted_of_selected 12 26431 ⟨340831, by decide⟩ ⟨12, 1, 0, 340831, 26431, 1, 65536⟩
    (by decide) selected_cut_12952

theorem unmarked_context_11_6607_340832 : frontier 10 ⟨340832, by decide⟩
    (prefixCache 11 6607) (prefixPartial 11 6607) = false := by
  decide +kernel

theorem node_context_11_6607_340832 : EJMOriginalGlobalDAGData.nodes 10 ⟨340832, by decide⟩ =
    .split (coordinate 11) (![⟨340720, by decide⟩,⟨340780, by decide⟩,⟨340830, by decide⟩,⟨340831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6607_340832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6607 ⟨340832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6607
    ⟨340832, by decide⟩ (by decide) (![⟨340720, by decide⟩,⟨340780, by decide⟩,⟨340830, by decide⟩,⟨340831, by decide⟩]) unmarked_context_11_6607_340832 node_context_11_6607_340832
  intro a
  fin_cases a
  · exact context_12_26428_340720
  · exact context_12_26429_340780
  · exact context_12_26430_340830
  · exact context_12_26431_340831

theorem unmarked_context_10_1651_340833 : frontier 11 ⟨340833, by decide⟩
    (prefixCache 10 1651) (prefixPartial 10 1651) = false := by
  decide +kernel

theorem node_context_10_1651_340833 : EJMOriginalGlobalDAGData.nodes 11 ⟨340833, by decide⟩ =
    .split (coordinate 10) (![⟨340141, by decide⟩,⟨340393, by decide⟩,⟨340668, by decide⟩,⟨340832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1651_340833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1651 ⟨340833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1651
    ⟨340833, by decide⟩ (by decide) (![⟨340141, by decide⟩,⟨340393, by decide⟩,⟨340668, by decide⟩,⟨340832, by decide⟩]) unmarked_context_10_1651_340833 node_context_10_1651_340833
  intro a
  fin_cases a
  · exact context_11_6604_340141
  · exact context_11_6605_340393
  · exact context_11_6606_340668
  · exact context_11_6607_340832

theorem unmarked_context_9_412_340834 : frontier 12 ⟨340834, by decide⟩
    (prefixCache 9 412) (prefixPartial 9 412) = false := by
  decide +kernel

theorem node_context_9_412_340834 : EJMOriginalGlobalDAGData.nodes 12 ⟨340834, by decide⟩ =
    .split (coordinate 9) (![⟨337056, by decide⟩,⟨338673, by decide⟩,⟨339895, by decide⟩,⟨340833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_412_340834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 412 ⟨340834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 412
    ⟨340834, by decide⟩ (by decide) (![⟨337056, by decide⟩,⟨338673, by decide⟩,⟨339895, by decide⟩,⟨340833, by decide⟩]) unmarked_context_9_412_340834 node_context_9_412_340834
  intro a
  fin_cases a
  · exact context_10_1648_337056
  · exact context_10_1649_338673
  · exact context_10_1650_339895
  · exact context_10_1651_340833

theorem selected_cut_12953 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105728) = some ⟨13, 1, 0, 3444, 105728, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105728_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105728 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105728 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105728, 1, 16384⟩
    (by decide) selected_cut_12953

theorem selected_cut_12954 : selected 8 ⟨340863, by decide⟩
    (prefixPartial 13 105729) = some ⟨13, 2, 0, 340863, 105729, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_105729_340863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105729 ⟨340863, by decide⟩ :=
  accepted_of_selected 13 105729 ⟨340863, by decide⟩ ⟨13, 2, 0, 340863, 105729, 2729, 16384⟩
    (by decide) selected_cut_12954

theorem selected_cut_12955 : selected 8 ⟨340893, by decide⟩
    (prefixPartial 13 105730) = some ⟨13, 2, 0, 340893, 105730, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_105730_340893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105730 ⟨340893, by decide⟩ :=
  accepted_of_selected 13 105730 ⟨340893, by decide⟩ ⟨13, 2, 0, 340893, 105730, 1729, 16384⟩
    (by decide) selected_cut_12955

theorem selected_cut_12956 : selected 8 ⟨340901, by decide⟩
    (prefixPartial 13 105731) = some ⟨13, 2, 0, 340901, 105731, 777, 16384⟩ := by
  decide +kernel

theorem context_13_105731_340901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105731 ⟨340901, by decide⟩ :=
  accepted_of_selected 13 105731 ⟨340901, by decide⟩ ⟨13, 2, 0, 340901, 105731, 777, 16384⟩
    (by decide) selected_cut_12956

theorem unmarked_context_12_26432_340902 : frontier 9 ⟨340902, by decide⟩
    (prefixCache 12 26432) (prefixPartial 12 26432) = false := by
  decide +kernel

theorem node_context_12_26432_340902 : EJMOriginalGlobalDAGData.nodes 9 ⟨340902, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨340863, by decide⟩,⟨340893, by decide⟩,⟨340901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26432_340902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26432 ⟨340902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26432
    ⟨340902, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨340863, by decide⟩,⟨340893, by decide⟩,⟨340901, by decide⟩]) unmarked_context_12_26432_340902 node_context_12_26432_340902
  intro a
  fin_cases a
  · exact context_13_105728_3444
  · exact context_13_105729_340863
  · exact context_13_105730_340893
  · exact context_13_105731_340901

theorem selected_cut_12957 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105732) = some ⟨13, 1, 0, 3444, 105732, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105732_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105732 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105732 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105732, 1, 16384⟩
    (by decide) selected_cut_12957

theorem selected_cut_12958 : selected 8 ⟨340976, by decide⟩
    (prefixPartial 13 105733) = some ⟨13, 2, 0, 340976, 105733, 4089, 16384⟩ := by
  decide +kernel

theorem context_13_105733_340976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105733 ⟨340976, by decide⟩ :=
  accepted_of_selected 13 105733 ⟨340976, by decide⟩ ⟨13, 2, 0, 340976, 105733, 4089, 16384⟩
    (by decide) selected_cut_12958

theorem selected_cut_12959 : selected 8 ⟨341028, by decide⟩
    (prefixPartial 13 105734) = some ⟨13, 2, 0, 341028, 105734, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_105734_341028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105734 ⟨341028, by decide⟩ :=
  accepted_of_selected 13 105734 ⟨341028, by decide⟩ ⟨13, 2, 0, 341028, 105734, 2781, 16384⟩
    (by decide) selected_cut_12959

theorem selected_cut_12960 : selected 8 ⟨341041, by decide⟩
    (prefixPartial 13 105735) = some ⟨13, 2, 0, 341041, 105735, 889, 16384⟩ := by
  decide +kernel

theorem context_13_105735_341041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105735 ⟨341041, by decide⟩ :=
  accepted_of_selected 13 105735 ⟨341041, by decide⟩ ⟨13, 2, 0, 341041, 105735, 889, 16384⟩
    (by decide) selected_cut_12960

theorem unmarked_context_12_26433_341042 : frontier 9 ⟨341042, by decide⟩
    (prefixCache 12 26433) (prefixPartial 12 26433) = false := by
  decide +kernel

theorem node_context_12_26433_341042 : EJMOriginalGlobalDAGData.nodes 9 ⟨341042, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨340976, by decide⟩,⟨341028, by decide⟩,⟨341041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26433_341042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26433 ⟨341042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26433
    ⟨341042, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨340976, by decide⟩,⟨341028, by decide⟩,⟨341041, by decide⟩]) unmarked_context_12_26433_341042 node_context_12_26433_341042
  intro a
  fin_cases a
  · exact context_13_105732_3444
  · exact context_13_105733_340976
  · exact context_13_105734_341028
  · exact context_13_105735_341041

theorem selected_cut_12961 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105736) = some ⟨13, 1, 0, 3444, 105736, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105736_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105736 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105736 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105736, 1, 16384⟩
    (by decide) selected_cut_12961

theorem selected_cut_12962 : selected 8 ⟨341088, by decide⟩
    (prefixPartial 13 105737) = some ⟨13, 2, 0, 341088, 105737, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_105737_341088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105737 ⟨341088, by decide⟩ :=
  accepted_of_selected 13 105737 ⟨341088, by decide⟩ ⟨13, 2, 0, 341088, 105737, 3013, 16384⟩
    (by decide) selected_cut_12962

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
