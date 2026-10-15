/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover140
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13540 : selected 8 ⟨354798, by decide⟩
    (prefixPartial 13 106927) = some ⟨13, 2, 0, 354798, 106927, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_106927_354798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106927 ⟨354798, by decide⟩ :=
  accepted_of_selected 13 106927 ⟨354798, by decide⟩ ⟨13, 2, 0, 354798, 106927, 1297, 16384⟩
    (by decide) selected_cut_13540

theorem unmarked_context_12_26731_354799 : frontier 9 ⟨354799, by decide⟩
    (prefixCache 12 26731) (prefixPartial 12 26731) = false := by
  decide +kernel

theorem node_context_12_26731_354799 : EJMOriginalGlobalDAGData.nodes 9 ⟨354799, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354763, by decide⟩,⟨354784, by decide⟩,⟨354798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26731_354799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26731 ⟨354799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26731
    ⟨354799, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354763, by decide⟩,⟨354784, by decide⟩,⟨354798, by decide⟩]) unmarked_context_12_26731_354799 node_context_12_26731_354799
  intro a
  fin_cases a
  · exact context_13_106924_3444
  · exact context_13_106925_354763
  · exact context_13_106926_354784
  · exact context_13_106927_354798

theorem unmarked_context_11_6682_354800 : frontier 10 ⟨354800, by decide⟩
    (prefixCache 11 6682) (prefixPartial 11 6682) = false := by
  decide +kernel

theorem node_context_11_6682_354800 : EJMOriginalGlobalDAGData.nodes 10 ⟨354800, by decide⟩ =
    .split (coordinate 11) (![⟨354586, by decide⟩,⟨354745, by decide⟩,⟨93922, by decide⟩,⟨354799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6682_354800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6682 ⟨354800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6682
    ⟨354800, by decide⟩ (by decide) (![⟨354586, by decide⟩,⟨354745, by decide⟩,⟨93922, by decide⟩,⟨354799, by decide⟩]) unmarked_context_11_6682_354800 node_context_11_6682_354800
  intro a
  fin_cases a
  · exact context_12_26728_354586
  · exact context_12_26729_354745
  · exact context_12_26730_93922
  · exact context_12_26731_354799

theorem selected_cut_13541 : selected 9 ⟨354835, by decide⟩
    (prefixPartial 12 26732) = some ⟨12, 2, 0, 354835, 26732, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_26732_354835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26732 ⟨354835, by decide⟩ :=
  accepted_of_selected 12 26732 ⟨354835, by decide⟩ ⟨12, 2, 0, 354835, 26732, 3361, 65536⟩
    (by decide) selected_cut_13541

theorem selected_cut_13542 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106932) = some ⟨13, 1, 0, 3444, 106932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106932, 1, 16384⟩
    (by decide) selected_cut_13542

theorem selected_cut_13543 : selected 8 ⟨354850, by decide⟩
    (prefixPartial 13 106933) = some ⟨13, 2, 0, 354850, 106933, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_106933_354850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106933 ⟨354850, by decide⟩ :=
  accepted_of_selected 13 106933 ⟨354850, by decide⟩ ⟨13, 2, 0, 354850, 106933, 1097, 16384⟩
    (by decide) selected_cut_13543

theorem selected_cut_13544 : selected 8 ⟨354883, by decide⟩
    (prefixPartial 13 106934) = some ⟨13, 2, 0, 354883, 106934, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_106934_354883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106934 ⟨354883, by decide⟩ :=
  accepted_of_selected 13 106934 ⟨354883, by decide⟩ ⟨13, 2, 0, 354883, 106934, 2081, 16384⟩
    (by decide) selected_cut_13544

theorem selected_cut_13545 : selected 8 ⟨354904, by decide⟩
    (prefixPartial 13 106935) = some ⟨13, 2, 0, 354904, 106935, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_106935_354904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106935 ⟨354904, by decide⟩ :=
  accepted_of_selected 13 106935 ⟨354904, by decide⟩ ⟨13, 2, 0, 354904, 106935, 1221, 16384⟩
    (by decide) selected_cut_13545

theorem unmarked_context_12_26733_354905 : frontier 9 ⟨354905, by decide⟩
    (prefixCache 12 26733) (prefixPartial 12 26733) = false := by
  decide +kernel

theorem node_context_12_26733_354905 : EJMOriginalGlobalDAGData.nodes 9 ⟨354905, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354850, by decide⟩,⟨354883, by decide⟩,⟨354904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26733_354905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26733 ⟨354905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26733
    ⟨354905, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354850, by decide⟩,⟨354883, by decide⟩,⟨354904, by decide⟩]) unmarked_context_12_26733_354905 node_context_12_26733_354905
  intro a
  fin_cases a
  · exact context_13_106932_3444
  · exact context_13_106933_354850
  · exact context_13_106934_354883
  · exact context_13_106935_354904

theorem selected_cut_13546 : selected 9 ⟨354945, by decide⟩
    (prefixPartial 12 26734) = some ⟨12, 2, 0, 354945, 26734, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_26734_354945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26734 ⟨354945, by decide⟩ :=
  accepted_of_selected 12 26734 ⟨354945, by decide⟩ ⟨12, 2, 0, 354945, 26734, 3373, 65536⟩
    (by decide) selected_cut_13546

theorem selected_cut_13547 : selected 9 ⟨354987, by decide⟩
    (prefixPartial 12 26735) = some ⟨12, 2, 0, 354987, 26735, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_26735_354987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26735 ⟨354987, by decide⟩ :=
  accepted_of_selected 12 26735 ⟨354987, by decide⟩ ⟨12, 2, 0, 354987, 26735, 3373, 65536⟩
    (by decide) selected_cut_13547

theorem unmarked_context_11_6683_354988 : frontier 10 ⟨354988, by decide⟩
    (prefixCache 11 6683) (prefixPartial 11 6683) = false := by
  decide +kernel

theorem node_context_11_6683_354988 : EJMOriginalGlobalDAGData.nodes 10 ⟨354988, by decide⟩ =
    .split (coordinate 11) (![⟨354835, by decide⟩,⟨354905, by decide⟩,⟨354945, by decide⟩,⟨354987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6683_354988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6683 ⟨354988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6683
    ⟨354988, by decide⟩ (by decide) (![⟨354835, by decide⟩,⟨354905, by decide⟩,⟨354945, by decide⟩,⟨354987, by decide⟩]) unmarked_context_11_6683_354988 node_context_11_6683_354988
  intro a
  fin_cases a
  · exact context_12_26732_354835
  · exact context_12_26733_354905
  · exact context_12_26734_354945
  · exact context_12_26735_354987

theorem unmarked_context_10_1670_354989 : frontier 11 ⟨354989, by decide⟩
    (prefixCache 10 1670) (prefixPartial 10 1670) = false := by
  decide +kernel

theorem node_context_10_1670_354989 : EJMOriginalGlobalDAGData.nodes 11 ⟨354989, by decide⟩ =
    .split (coordinate 10) (![⟨354378, by decide⟩,⟨354509, by decide⟩,⟨354800, by decide⟩,⟨354988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1670_354989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1670 ⟨354989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1670
    ⟨354989, by decide⟩ (by decide) (![⟨354378, by decide⟩,⟨354509, by decide⟩,⟨354800, by decide⟩,⟨354988, by decide⟩]) unmarked_context_10_1670_354989 node_context_10_1670_354989
  intro a
  fin_cases a
  · exact context_11_6680_354378
  · exact context_11_6681_354509
  · exact context_11_6682_354800
  · exact context_11_6683_354988

theorem selected_cut_13548 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106944) = some ⟨13, 1, 0, 3444, 106944, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106944_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106944 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106944 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106944, 1, 16384⟩
    (by decide) selected_cut_13548

theorem selected_cut_13549 : selected 8 ⟨355010, by decide⟩
    (prefixPartial 13 106945) = some ⟨13, 2, 0, 355010, 106945, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_106945_355010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106945 ⟨355010, by decide⟩ :=
  accepted_of_selected 13 106945 ⟨355010, by decide⟩ ⟨13, 2, 0, 355010, 106945, 1185, 16384⟩
    (by decide) selected_cut_13549

theorem selected_cut_13550 : selected 8 ⟨355041, by decide⟩
    (prefixPartial 13 106946) = some ⟨13, 2, 0, 355041, 106946, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_106946_355041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106946 ⟨355041, by decide⟩ :=
  accepted_of_selected 13 106946 ⟨355041, by decide⟩ ⟨13, 2, 0, 355041, 106946, 2521, 16384⟩
    (by decide) selected_cut_13550

theorem selected_cut_13551 : selected 8 ⟨355072, by decide⟩
    (prefixPartial 13 106947) = some ⟨13, 2, 0, 355072, 106947, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_106947_355072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106947 ⟨355072, by decide⟩ :=
  accepted_of_selected 13 106947 ⟨355072, by decide⟩ ⟨13, 2, 0, 355072, 106947, 1349, 16384⟩
    (by decide) selected_cut_13551

theorem unmarked_context_12_26736_355073 : frontier 9 ⟨355073, by decide⟩
    (prefixCache 12 26736) (prefixPartial 12 26736) = false := by
  decide +kernel

theorem node_context_12_26736_355073 : EJMOriginalGlobalDAGData.nodes 9 ⟨355073, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨355010, by decide⟩,⟨355041, by decide⟩,⟨355072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26736_355073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26736 ⟨355073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26736
    ⟨355073, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨355010, by decide⟩,⟨355041, by decide⟩,⟨355072, by decide⟩]) unmarked_context_12_26736_355073 node_context_12_26736_355073
  intro a
  fin_cases a
  · exact context_13_106944_3444
  · exact context_13_106945_355010
  · exact context_13_106946_355041
  · exact context_13_106947_355072

theorem selected_cut_13552 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106948) = some ⟨13, 1, 0, 3444, 106948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106948, 1, 16384⟩
    (by decide) selected_cut_13552

theorem selected_cut_13553 : selected 8 ⟨355081, by decide⟩
    (prefixPartial 13 106949) = some ⟨13, 2, 0, 355081, 106949, 789, 16384⟩ := by
  decide +kernel

theorem context_13_106949_355081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106949 ⟨355081, by decide⟩ :=
  accepted_of_selected 13 106949 ⟨355081, by decide⟩ ⟨13, 2, 0, 355081, 106949, 789, 16384⟩
    (by decide) selected_cut_13553

theorem selected_cut_13554 : selected 8 ⟨355107, by decide⟩
    (prefixPartial 13 106950) = some ⟨13, 2, 0, 355107, 106950, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_106950_355107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106950 ⟨355107, by decide⟩ :=
  accepted_of_selected 13 106950 ⟨355107, by decide⟩ ⟨13, 2, 0, 355107, 106950, 2245, 16384⟩
    (by decide) selected_cut_13554

theorem selected_cut_13555 : selected 8 ⟨355119, by decide⟩
    (prefixPartial 13 106951) = some ⟨13, 2, 0, 355119, 106951, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_106951_355119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106951 ⟨355119, by decide⟩ :=
  accepted_of_selected 13 106951 ⟨355119, by decide⟩ ⟨13, 2, 0, 355119, 106951, 1121, 16384⟩
    (by decide) selected_cut_13555

theorem unmarked_context_12_26737_355120 : frontier 9 ⟨355120, by decide⟩
    (prefixCache 12 26737) (prefixPartial 12 26737) = false := by
  decide +kernel

theorem node_context_12_26737_355120 : EJMOriginalGlobalDAGData.nodes 9 ⟨355120, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨355081, by decide⟩,⟨355107, by decide⟩,⟨355119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26737_355120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26737 ⟨355120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26737
    ⟨355120, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨355081, by decide⟩,⟨355107, by decide⟩,⟨355119, by decide⟩]) unmarked_context_12_26737_355120 node_context_12_26737_355120
  intro a
  fin_cases a
  · exact context_13_106948_3444
  · exact context_13_106949_355081
  · exact context_13_106950_355107
  · exact context_13_106951_355119

theorem selected_cut_13556 : selected 9 ⟨355155, by decide⟩
    (prefixPartial 12 26738) = some ⟨12, 2, 0, 355155, 26738, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_26738_355155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26738 ⟨355155, by decide⟩ :=
  accepted_of_selected 12 26738 ⟨355155, by decide⟩ ⟨12, 2, 0, 355155, 26738, 3249, 65536⟩
    (by decide) selected_cut_13556

theorem selected_cut_13557 : selected 9 ⟨355191, by decide⟩
    (prefixPartial 12 26739) = some ⟨12, 2, 0, 355191, 26739, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_26739_355191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26739 ⟨355191, by decide⟩ :=
  accepted_of_selected 12 26739 ⟨355191, by decide⟩ ⟨12, 2, 0, 355191, 26739, 3365, 65536⟩
    (by decide) selected_cut_13557

theorem unmarked_context_11_6684_355192 : frontier 10 ⟨355192, by decide⟩
    (prefixCache 11 6684) (prefixPartial 11 6684) = false := by
  decide +kernel

theorem node_context_11_6684_355192 : EJMOriginalGlobalDAGData.nodes 10 ⟨355192, by decide⟩ =
    .split (coordinate 11) (![⟨355073, by decide⟩,⟨355120, by decide⟩,⟨355155, by decide⟩,⟨355191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6684_355192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6684 ⟨355192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6684
    ⟨355192, by decide⟩ (by decide) (![⟨355073, by decide⟩,⟨355120, by decide⟩,⟨355155, by decide⟩,⟨355191, by decide⟩]) unmarked_context_11_6684_355192 node_context_11_6684_355192
  intro a
  fin_cases a
  · exact context_12_26736_355073
  · exact context_12_26737_355120
  · exact context_12_26738_355155
  · exact context_12_26739_355191

theorem selected_cut_13558 : selected 9 ⟨355229, by decide⟩
    (prefixPartial 12 26740) = some ⟨12, 2, 0, 355229, 26740, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_26740_355229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26740 ⟨355229, by decide⟩ :=
  accepted_of_selected 12 26740 ⟨355229, by decide⟩ ⟨12, 2, 0, 355229, 26740, 3285, 65536⟩
    (by decide) selected_cut_13558

theorem selected_cut_13559 : selected 9 ⟨355230, by decide⟩
    (prefixPartial 12 26741) = some ⟨12, 1, 0, 355230, 26741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26741_355230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26741 ⟨355230, by decide⟩ :=
  accepted_of_selected 12 26741 ⟨355230, by decide⟩ ⟨12, 1, 0, 355230, 26741, 1, 65536⟩
    (by decide) selected_cut_13559

theorem selected_cut_13560 : selected 9 ⟨355270, by decide⟩
    (prefixPartial 12 26742) = some ⟨12, 2, 0, 355270, 26742, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_26742_355270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26742 ⟨355270, by decide⟩ :=
  accepted_of_selected 12 26742 ⟨355270, by decide⟩ ⟨12, 2, 0, 355270, 26742, 3413, 65536⟩
    (by decide) selected_cut_13560

theorem selected_cut_13561 : selected 9 ⟨355315, by decide⟩
    (prefixPartial 12 26743) = some ⟨12, 2, 0, 355315, 26743, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_26743_355315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26743 ⟨355315, by decide⟩ :=
  accepted_of_selected 12 26743 ⟨355315, by decide⟩ ⟨12, 2, 0, 355315, 26743, 3721, 65536⟩
    (by decide) selected_cut_13561

theorem unmarked_context_11_6685_355316 : frontier 10 ⟨355316, by decide⟩
    (prefixCache 11 6685) (prefixPartial 11 6685) = false := by
  decide +kernel

theorem node_context_11_6685_355316 : EJMOriginalGlobalDAGData.nodes 10 ⟨355316, by decide⟩ =
    .split (coordinate 11) (![⟨355229, by decide⟩,⟨355230, by decide⟩,⟨355270, by decide⟩,⟨355315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6685_355316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6685 ⟨355316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6685
    ⟨355316, by decide⟩ (by decide) (![⟨355229, by decide⟩,⟨355230, by decide⟩,⟨355270, by decide⟩,⟨355315, by decide⟩]) unmarked_context_11_6685_355316 node_context_11_6685_355316
  intro a
  fin_cases a
  · exact context_12_26740_355229
  · exact context_12_26741_355230
  · exact context_12_26742_355270
  · exact context_12_26743_355315

theorem selected_cut_13562 : selected 9 ⟨355354, by decide⟩
    (prefixPartial 12 26744) = some ⟨12, 2, 0, 355354, 26744, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_26744_355354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26744 ⟨355354, by decide⟩ :=
  accepted_of_selected 12 26744 ⟨355354, by decide⟩ ⟨12, 2, 0, 355354, 26744, 3409, 65536⟩
    (by decide) selected_cut_13562

theorem selected_cut_13563 : selected 9 ⟨355397, by decide⟩
    (prefixPartial 12 26745) = some ⟨12, 2, 0, 355397, 26745, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_26745_355397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26745 ⟨355397, by decide⟩ :=
  accepted_of_selected 12 26745 ⟨355397, by decide⟩ ⟨12, 2, 0, 355397, 26745, 3953, 65536⟩
    (by decide) selected_cut_13563

theorem selected_cut_13564 : selected 9 ⟨355434, by decide⟩
    (prefixPartial 12 26746) = some ⟨12, 2, 0, 355434, 26746, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_26746_355434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26746 ⟨355434, by decide⟩ :=
  accepted_of_selected 12 26746 ⟨355434, by decide⟩ ⟨12, 2, 0, 355434, 26746, 3061, 65536⟩
    (by decide) selected_cut_13564

theorem selected_cut_13565 : selected 9 ⟨355463, by decide⟩
    (prefixPartial 12 26747) = some ⟨12, 2, 0, 355463, 26747, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_26747_355463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26747 ⟨355463, by decide⟩ :=
  accepted_of_selected 12 26747 ⟨355463, by decide⟩ ⟨12, 2, 0, 355463, 26747, 3481, 65536⟩
    (by decide) selected_cut_13565

theorem unmarked_context_11_6686_355464 : frontier 10 ⟨355464, by decide⟩
    (prefixCache 11 6686) (prefixPartial 11 6686) = false := by
  decide +kernel

theorem node_context_11_6686_355464 : EJMOriginalGlobalDAGData.nodes 10 ⟨355464, by decide⟩ =
    .split (coordinate 11) (![⟨355354, by decide⟩,⟨355397, by decide⟩,⟨355434, by decide⟩,⟨355463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6686_355464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6686 ⟨355464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6686
    ⟨355464, by decide⟩ (by decide) (![⟨355354, by decide⟩,⟨355397, by decide⟩,⟨355434, by decide⟩,⟨355463, by decide⟩]) unmarked_context_11_6686_355464 node_context_11_6686_355464
  intro a
  fin_cases a
  · exact context_12_26744_355354
  · exact context_12_26745_355397
  · exact context_12_26746_355434
  · exact context_12_26747_355463

theorem selected_cut_13566 : selected 9 ⟨355496, by decide⟩
    (prefixPartial 12 26748) = some ⟨12, 2, 0, 355496, 26748, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_26748_355496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26748 ⟨355496, by decide⟩ :=
  accepted_of_selected 12 26748 ⟨355496, by decide⟩ ⟨12, 2, 0, 355496, 26748, 2725, 65536⟩
    (by decide) selected_cut_13566

theorem selected_cut_13567 : selected 9 ⟨355538, by decide⟩
    (prefixPartial 12 26749) = some ⟨12, 2, 0, 355538, 26749, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_26749_355538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26749 ⟨355538, by decide⟩ :=
  accepted_of_selected 12 26749 ⟨355538, by decide⟩ ⟨12, 2, 0, 355538, 26749, 3481, 65536⟩
    (by decide) selected_cut_13567

theorem selected_cut_13568 : selected 9 ⟨355572, by decide⟩
    (prefixPartial 12 26750) = some ⟨12, 2, 0, 355572, 26750, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_26750_355572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26750 ⟨355572, by decide⟩ :=
  accepted_of_selected 12 26750 ⟨355572, by decide⟩ ⟨12, 2, 0, 355572, 26750, 2713, 65536⟩
    (by decide) selected_cut_13568

theorem selected_cut_13569 : selected 9 ⟨355608, by decide⟩
    (prefixPartial 12 26751) = some ⟨12, 2, 0, 355608, 26751, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_26751_355608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26751 ⟨355608, by decide⟩ :=
  accepted_of_selected 12 26751 ⟨355608, by decide⟩ ⟨12, 2, 0, 355608, 26751, 2937, 65536⟩
    (by decide) selected_cut_13569

theorem unmarked_context_11_6687_355609 : frontier 10 ⟨355609, by decide⟩
    (prefixCache 11 6687) (prefixPartial 11 6687) = false := by
  decide +kernel

theorem node_context_11_6687_355609 : EJMOriginalGlobalDAGData.nodes 10 ⟨355609, by decide⟩ =
    .split (coordinate 11) (![⟨355496, by decide⟩,⟨355538, by decide⟩,⟨355572, by decide⟩,⟨355608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6687_355609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6687 ⟨355609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6687
    ⟨355609, by decide⟩ (by decide) (![⟨355496, by decide⟩,⟨355538, by decide⟩,⟨355572, by decide⟩,⟨355608, by decide⟩]) unmarked_context_11_6687_355609 node_context_11_6687_355609
  intro a
  fin_cases a
  · exact context_12_26748_355496
  · exact context_12_26749_355538
  · exact context_12_26750_355572
  · exact context_12_26751_355608

theorem unmarked_context_10_1671_355610 : frontier 11 ⟨355610, by decide⟩
    (prefixCache 10 1671) (prefixPartial 10 1671) = false := by
  decide +kernel

theorem node_context_10_1671_355610 : EJMOriginalGlobalDAGData.nodes 11 ⟨355610, by decide⟩ =
    .split (coordinate 10) (![⟨355192, by decide⟩,⟨355316, by decide⟩,⟨355464, by decide⟩,⟨355609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1671_355610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1671 ⟨355610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1671
    ⟨355610, by decide⟩ (by decide) (![⟨355192, by decide⟩,⟨355316, by decide⟩,⟨355464, by decide⟩,⟨355609, by decide⟩]) unmarked_context_10_1671_355610 node_context_10_1671_355610
  intro a
  fin_cases a
  · exact context_11_6684_355192
  · exact context_11_6685_355316
  · exact context_11_6686_355464
  · exact context_11_6687_355609

theorem unmarked_context_9_417_355611 : frontier 12 ⟨355611, by decide⟩
    (prefixCache 9 417) (prefixPartial 9 417) = false := by
  decide +kernel

theorem node_context_9_417_355611 : EJMOriginalGlobalDAGData.nodes 12 ⟨355611, by decide⟩ =
    .split (coordinate 9) (![⟨353513, by decide⟩,⟨354171, by decide⟩,⟨354989, by decide⟩,⟨355610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_417_355611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 417 ⟨355611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 417
    ⟨355611, by decide⟩ (by decide) (![⟨353513, by decide⟩,⟨354171, by decide⟩,⟨354989, by decide⟩,⟨355610, by decide⟩]) unmarked_context_9_417_355611 node_context_9_417_355611
  intro a
  fin_cases a
  · exact context_10_1668_353513
  · exact context_10_1669_354171
  · exact context_10_1670_354989
  · exact context_10_1671_355610

theorem selected_cut_13570 : selected 9 ⟨355612, by decide⟩
    (prefixPartial 12 26752) = some ⟨12, 1, 0, 355612, 26752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26752_355612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26752 ⟨355612, by decide⟩ :=
  accepted_of_selected 12 26752 ⟨355612, by decide⟩ ⟨12, 1, 0, 355612, 26752, 1, 65536⟩
    (by decide) selected_cut_13570

theorem selected_cut_13571 : selected 9 ⟨355641, by decide⟩
    (prefixPartial 12 26753) = some ⟨12, 2, 0, 355641, 26753, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_26753_355641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26753 ⟨355641, by decide⟩ :=
  accepted_of_selected 12 26753 ⟨355641, by decide⟩ ⟨12, 2, 0, 355641, 26753, 2113, 65536⟩
    (by decide) selected_cut_13571

theorem selected_cut_13572 : selected 9 ⟨355665, by decide⟩
    (prefixPartial 12 26754) = some ⟨12, 2, 0, 355665, 26754, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_26754_355665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26754 ⟨355665, by decide⟩ :=
  accepted_of_selected 12 26754 ⟨355665, by decide⟩ ⟨12, 2, 0, 355665, 26754, 2069, 65536⟩
    (by decide) selected_cut_13572

theorem selected_cut_13573 : selected 9 ⟨355685, by decide⟩
    (prefixPartial 12 26755) = some ⟨12, 2, 0, 355685, 26755, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_26755_355685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26755 ⟨355685, by decide⟩ :=
  accepted_of_selected 12 26755 ⟨355685, by decide⟩ ⟨12, 2, 0, 355685, 26755, 1913, 65536⟩
    (by decide) selected_cut_13573

theorem unmarked_context_11_6688_355686 : frontier 10 ⟨355686, by decide⟩
    (prefixCache 11 6688) (prefixPartial 11 6688) = false := by
  decide +kernel

theorem node_context_11_6688_355686 : EJMOriginalGlobalDAGData.nodes 10 ⟨355686, by decide⟩ =
    .split (coordinate 11) (![⟨355612, by decide⟩,⟨355641, by decide⟩,⟨355665, by decide⟩,⟨355685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6688_355686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6688 ⟨355686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6688
    ⟨355686, by decide⟩ (by decide) (![⟨355612, by decide⟩,⟨355641, by decide⟩,⟨355665, by decide⟩,⟨355685, by decide⟩]) unmarked_context_11_6688_355686 node_context_11_6688_355686
  intro a
  fin_cases a
  · exact context_12_26752_355612
  · exact context_12_26753_355641
  · exact context_12_26754_355665
  · exact context_12_26755_355685

theorem selected_cut_13574 : selected 9 ⟨355712, by decide⟩
    (prefixPartial 12 26756) = some ⟨12, 2, 0, 355712, 26756, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_26756_355712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26756 ⟨355712, by decide⟩ :=
  accepted_of_selected 12 26756 ⟨355712, by decide⟩ ⟨12, 2, 0, 355712, 26756, 2325, 65536⟩
    (by decide) selected_cut_13574

theorem selected_cut_13575 : selected 9 ⟨355741, by decide⟩
    (prefixPartial 12 26757) = some ⟨12, 2, 0, 355741, 26757, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_26757_355741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26757 ⟨355741, by decide⟩ :=
  accepted_of_selected 12 26757 ⟨355741, by decide⟩ ⟨12, 2, 0, 355741, 26757, 2301, 65536⟩
    (by decide) selected_cut_13575

theorem selected_cut_13576 : selected 9 ⟨355769, by decide⟩
    (prefixPartial 12 26758) = some ⟨12, 2, 0, 355769, 26758, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_26758_355769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26758 ⟨355769, by decide⟩ :=
  accepted_of_selected 12 26758 ⟨355769, by decide⟩ ⟨12, 2, 0, 355769, 26758, 2173, 65536⟩
    (by decide) selected_cut_13576

theorem selected_cut_13577 : selected 9 ⟨355796, by decide⟩
    (prefixPartial 12 26759) = some ⟨12, 2, 0, 355796, 26759, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_26759_355796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26759 ⟨355796, by decide⟩ :=
  accepted_of_selected 12 26759 ⟨355796, by decide⟩ ⟨12, 2, 0, 355796, 26759, 2097, 65536⟩
    (by decide) selected_cut_13577

theorem unmarked_context_11_6689_355797 : frontier 10 ⟨355797, by decide⟩
    (prefixCache 11 6689) (prefixPartial 11 6689) = false := by
  decide +kernel

theorem node_context_11_6689_355797 : EJMOriginalGlobalDAGData.nodes 10 ⟨355797, by decide⟩ =
    .split (coordinate 11) (![⟨355712, by decide⟩,⟨355741, by decide⟩,⟨355769, by decide⟩,⟨355796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6689_355797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6689 ⟨355797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6689
    ⟨355797, by decide⟩ (by decide) (![⟨355712, by decide⟩,⟨355741, by decide⟩,⟨355769, by decide⟩,⟨355796, by decide⟩]) unmarked_context_11_6689_355797 node_context_11_6689_355797
  intro a
  fin_cases a
  · exact context_12_26756_355712
  · exact context_12_26757_355741
  · exact context_12_26758_355769
  · exact context_12_26759_355796

theorem selected_cut_13578 : selected 9 ⟨355825, by decide⟩
    (prefixPartial 12 26760) = some ⟨12, 2, 0, 355825, 26760, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_26760_355825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26760 ⟨355825, by decide⟩ :=
  accepted_of_selected 12 26760 ⟨355825, by decide⟩ ⟨12, 2, 0, 355825, 26760, 2417, 65536⟩
    (by decide) selected_cut_13578

theorem selected_cut_13579 : selected 9 ⟨355855, by decide⟩
    (prefixPartial 12 26761) = some ⟨12, 2, 0, 355855, 26761, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_26761_355855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26761 ⟨355855, by decide⟩ :=
  accepted_of_selected 12 26761 ⟨355855, by decide⟩ ⟨12, 2, 0, 355855, 26761, 2093, 65536⟩
    (by decide) selected_cut_13579

theorem selected_cut_13580 : selected 9 ⟨355879, by decide⟩
    (prefixPartial 12 26762) = some ⟨12, 2, 0, 355879, 26762, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_26762_355879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26762 ⟨355879, by decide⟩ :=
  accepted_of_selected 12 26762 ⟨355879, by decide⟩ ⟨12, 2, 0, 355879, 26762, 2017, 65536⟩
    (by decide) selected_cut_13580

theorem selected_cut_13581 : selected 9 ⟨355903, by decide⟩
    (prefixPartial 12 26763) = some ⟨12, 2, 0, 355903, 26763, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_26763_355903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26763 ⟨355903, by decide⟩ :=
  accepted_of_selected 12 26763 ⟨355903, by decide⟩ ⟨12, 2, 0, 355903, 26763, 2049, 65536⟩
    (by decide) selected_cut_13581

theorem unmarked_context_11_6690_355904 : frontier 10 ⟨355904, by decide⟩
    (prefixCache 11 6690) (prefixPartial 11 6690) = false := by
  decide +kernel

theorem node_context_11_6690_355904 : EJMOriginalGlobalDAGData.nodes 10 ⟨355904, by decide⟩ =
    .split (coordinate 11) (![⟨355825, by decide⟩,⟨355855, by decide⟩,⟨355879, by decide⟩,⟨355903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6690_355904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6690 ⟨355904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6690
    ⟨355904, by decide⟩ (by decide) (![⟨355825, by decide⟩,⟨355855, by decide⟩,⟨355879, by decide⟩,⟨355903, by decide⟩]) unmarked_context_11_6690_355904 node_context_11_6690_355904
  intro a
  fin_cases a
  · exact context_12_26760_355825
  · exact context_12_26761_355855
  · exact context_12_26762_355879
  · exact context_12_26763_355903

theorem selected_cut_13582 : selected 9 ⟨355930, by decide⟩
    (prefixPartial 12 26764) = some ⟨12, 2, 0, 355930, 26764, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_26764_355930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26764 ⟨355930, by decide⟩ :=
  accepted_of_selected 12 26764 ⟨355930, by decide⟩ ⟨12, 2, 0, 355930, 26764, 2077, 65536⟩
    (by decide) selected_cut_13582

theorem selected_cut_13583 : selected 9 ⟨355955, by decide⟩
    (prefixPartial 12 26765) = some ⟨12, 2, 0, 355955, 26765, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_26765_355955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26765 ⟨355955, by decide⟩ :=
  accepted_of_selected 12 26765 ⟨355955, by decide⟩ ⟨12, 2, 0, 355955, 26765, 1917, 65536⟩
    (by decide) selected_cut_13583

theorem selected_cut_13584 : selected 9 ⟨355979, by decide⟩
    (prefixPartial 12 26766) = some ⟨12, 2, 0, 355979, 26766, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_26766_355979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26766 ⟨355979, by decide⟩ :=
  accepted_of_selected 12 26766 ⟨355979, by decide⟩ ⟨12, 2, 0, 355979, 26766, 1961, 65536⟩
    (by decide) selected_cut_13584

theorem selected_cut_13585 : selected 9 ⟨356001, by decide⟩
    (prefixPartial 12 26767) = some ⟨12, 2, 0, 356001, 26767, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_26767_356001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26767 ⟨356001, by decide⟩ :=
  accepted_of_selected 12 26767 ⟨356001, by decide⟩ ⟨12, 2, 0, 356001, 26767, 1881, 65536⟩
    (by decide) selected_cut_13585

theorem unmarked_context_11_6691_356002 : frontier 10 ⟨356002, by decide⟩
    (prefixCache 11 6691) (prefixPartial 11 6691) = false := by
  decide +kernel

theorem node_context_11_6691_356002 : EJMOriginalGlobalDAGData.nodes 10 ⟨356002, by decide⟩ =
    .split (coordinate 11) (![⟨355930, by decide⟩,⟨355955, by decide⟩,⟨355979, by decide⟩,⟨356001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6691_356002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6691 ⟨356002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6691
    ⟨356002, by decide⟩ (by decide) (![⟨355930, by decide⟩,⟨355955, by decide⟩,⟨355979, by decide⟩,⟨356001, by decide⟩]) unmarked_context_11_6691_356002 node_context_11_6691_356002
  intro a
  fin_cases a
  · exact context_12_26764_355930
  · exact context_12_26765_355955
  · exact context_12_26766_355979
  · exact context_12_26767_356001

theorem unmarked_context_10_1672_356003 : frontier 11 ⟨356003, by decide⟩
    (prefixCache 10 1672) (prefixPartial 10 1672) = false := by
  decide +kernel

theorem node_context_10_1672_356003 : EJMOriginalGlobalDAGData.nodes 11 ⟨356003, by decide⟩ =
    .split (coordinate 10) (![⟨355686, by decide⟩,⟨355797, by decide⟩,⟨355904, by decide⟩,⟨356002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1672_356003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1672 ⟨356003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1672
    ⟨356003, by decide⟩ (by decide) (![⟨355686, by decide⟩,⟨355797, by decide⟩,⟨355904, by decide⟩,⟨356002, by decide⟩]) unmarked_context_10_1672_356003 node_context_10_1672_356003
  intro a
  fin_cases a
  · exact context_11_6688_355686
  · exact context_11_6689_355797
  · exact context_11_6690_355904
  · exact context_11_6691_356002

theorem selected_cut_13586 : selected 9 ⟨356053, by decide⟩
    (prefixPartial 12 26768) = some ⟨12, 2, 0, 356053, 26768, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_26768_356053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26768 ⟨356053, by decide⟩ :=
  accepted_of_selected 12 26768 ⟨356053, by decide⟩ ⟨12, 2, 0, 356053, 26768, 3261, 65536⟩
    (by decide) selected_cut_13586

theorem selected_cut_13587 : selected 9 ⟨356080, by decide⟩
    (prefixPartial 12 26769) = some ⟨12, 2, 0, 356080, 26769, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_26769_356080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26769 ⟨356080, by decide⟩ :=
  accepted_of_selected 12 26769 ⟨356080, by decide⟩ ⟨12, 2, 0, 356080, 26769, 2369, 65536⟩
    (by decide) selected_cut_13587

theorem selected_cut_13588 : selected 9 ⟨356102, by decide⟩
    (prefixPartial 12 26770) = some ⟨12, 2, 0, 356102, 26770, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_26770_356102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26770 ⟨356102, by decide⟩ :=
  accepted_of_selected 12 26770 ⟨356102, by decide⟩ ⟨12, 2, 0, 356102, 26770, 2337, 65536⟩
    (by decide) selected_cut_13588

theorem selected_cut_13589 : selected 9 ⟨356122, by decide⟩
    (prefixPartial 12 26771) = some ⟨12, 2, 0, 356122, 26771, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_26771_356122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26771 ⟨356122, by decide⟩ :=
  accepted_of_selected 12 26771 ⟨356122, by decide⟩ ⟨12, 2, 0, 356122, 26771, 2073, 65536⟩
    (by decide) selected_cut_13589

theorem unmarked_context_11_6692_356123 : frontier 10 ⟨356123, by decide⟩
    (prefixCache 11 6692) (prefixPartial 11 6692) = false := by
  decide +kernel

theorem node_context_11_6692_356123 : EJMOriginalGlobalDAGData.nodes 10 ⟨356123, by decide⟩ =
    .split (coordinate 11) (![⟨356053, by decide⟩,⟨356080, by decide⟩,⟨356102, by decide⟩,⟨356122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6692_356123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6692 ⟨356123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6692
    ⟨356123, by decide⟩ (by decide) (![⟨356053, by decide⟩,⟨356080, by decide⟩,⟨356102, by decide⟩,⟨356122, by decide⟩]) unmarked_context_11_6692_356123 node_context_11_6692_356123
  intro a
  fin_cases a
  · exact context_12_26768_356053
  · exact context_12_26769_356080
  · exact context_12_26770_356102
  · exact context_12_26771_356122

theorem selected_cut_13590 : selected 9 ⟨356145, by decide⟩
    (prefixPartial 12 26772) = some ⟨12, 2, 0, 356145, 26772, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_26772_356145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26772 ⟨356145, by decide⟩ :=
  accepted_of_selected 12 26772 ⟨356145, by decide⟩ ⟨12, 2, 0, 356145, 26772, 2153, 65536⟩
    (by decide) selected_cut_13590

theorem selected_cut_13591 : selected 9 ⟨356166, by decide⟩
    (prefixPartial 12 26773) = some ⟨12, 2, 0, 356166, 26773, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_26773_356166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26773 ⟨356166, by decide⟩ :=
  accepted_of_selected 12 26773 ⟨356166, by decide⟩ ⟨12, 2, 0, 356166, 26773, 2317, 65536⟩
    (by decide) selected_cut_13591

theorem selected_cut_13592 : selected 9 ⟨356189, by decide⟩
    (prefixPartial 12 26774) = some ⟨12, 2, 0, 356189, 26774, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_26774_356189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26774 ⟨356189, by decide⟩ :=
  accepted_of_selected 12 26774 ⟨356189, by decide⟩ ⟨12, 2, 0, 356189, 26774, 2305, 65536⟩
    (by decide) selected_cut_13592

theorem selected_cut_13593 : selected 9 ⟨356210, by decide⟩
    (prefixPartial 12 26775) = some ⟨12, 2, 0, 356210, 26775, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_26775_356210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26775 ⟨356210, by decide⟩ :=
  accepted_of_selected 12 26775 ⟨356210, by decide⟩ ⟨12, 2, 0, 356210, 26775, 2117, 65536⟩
    (by decide) selected_cut_13593

theorem unmarked_context_11_6693_356211 : frontier 10 ⟨356211, by decide⟩
    (prefixCache 11 6693) (prefixPartial 11 6693) = false := by
  decide +kernel

theorem node_context_11_6693_356211 : EJMOriginalGlobalDAGData.nodes 10 ⟨356211, by decide⟩ =
    .split (coordinate 11) (![⟨356145, by decide⟩,⟨356166, by decide⟩,⟨356189, by decide⟩,⟨356210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6693_356211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6693 ⟨356211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6693
    ⟨356211, by decide⟩ (by decide) (![⟨356145, by decide⟩,⟨356166, by decide⟩,⟨356189, by decide⟩,⟨356210, by decide⟩]) unmarked_context_11_6693_356211 node_context_11_6693_356211
  intro a
  fin_cases a
  · exact context_12_26772_356145
  · exact context_12_26773_356166
  · exact context_12_26774_356189
  · exact context_12_26775_356210

theorem selected_cut_13594 : selected 9 ⟨356231, by decide⟩
    (prefixPartial 12 26776) = some ⟨12, 2, 0, 356231, 26776, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_26776_356231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26776 ⟨356231, by decide⟩ :=
  accepted_of_selected 12 26776 ⟨356231, by decide⟩ ⟨12, 2, 0, 356231, 26776, 2097, 65536⟩
    (by decide) selected_cut_13594

theorem selected_cut_13595 : selected 9 ⟨356251, by decide⟩
    (prefixPartial 12 26777) = some ⟨12, 2, 0, 356251, 26777, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_26777_356251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26777 ⟨356251, by decide⟩ :=
  accepted_of_selected 12 26777 ⟨356251, by decide⟩ ⟨12, 2, 0, 356251, 26777, 2129, 65536⟩
    (by decide) selected_cut_13595

theorem selected_cut_13596 : selected 9 ⟨356272, by decide⟩
    (prefixPartial 12 26778) = some ⟨12, 2, 0, 356272, 26778, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_26778_356272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26778 ⟨356272, by decide⟩ :=
  accepted_of_selected 12 26778 ⟨356272, by decide⟩ ⟨12, 2, 0, 356272, 26778, 2005, 65536⟩
    (by decide) selected_cut_13596

theorem selected_cut_13597 : selected 9 ⟨356289, by decide⟩
    (prefixPartial 12 26779) = some ⟨12, 2, 0, 356289, 26779, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_26779_356289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26779 ⟨356289, by decide⟩ :=
  accepted_of_selected 12 26779 ⟨356289, by decide⟩ ⟨12, 2, 0, 356289, 26779, 1869, 65536⟩
    (by decide) selected_cut_13597

theorem unmarked_context_11_6694_356290 : frontier 10 ⟨356290, by decide⟩
    (prefixCache 11 6694) (prefixPartial 11 6694) = false := by
  decide +kernel

theorem node_context_11_6694_356290 : EJMOriginalGlobalDAGData.nodes 10 ⟨356290, by decide⟩ =
    .split (coordinate 11) (![⟨356231, by decide⟩,⟨356251, by decide⟩,⟨356272, by decide⟩,⟨356289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6694_356290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6694 ⟨356290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6694
    ⟨356290, by decide⟩ (by decide) (![⟨356231, by decide⟩,⟨356251, by decide⟩,⟨356272, by decide⟩,⟨356289, by decide⟩]) unmarked_context_11_6694_356290 node_context_11_6694_356290
  intro a
  fin_cases a
  · exact context_12_26776_356231
  · exact context_12_26777_356251
  · exact context_12_26778_356272
  · exact context_12_26779_356289

theorem selected_cut_13598 : selected 9 ⟨356310, by decide⟩
    (prefixPartial 12 26780) = some ⟨12, 2, 0, 356310, 26780, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_26780_356310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26780 ⟨356310, by decide⟩ :=
  accepted_of_selected 12 26780 ⟨356310, by decide⟩ ⟨12, 2, 0, 356310, 26780, 1785, 65536⟩
    (by decide) selected_cut_13598

theorem selected_cut_13599 : selected 9 ⟨356328, by decide⟩
    (prefixPartial 12 26781) = some ⟨12, 2, 0, 356328, 26781, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_26781_356328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26781 ⟨356328, by decide⟩ :=
  accepted_of_selected 12 26781 ⟨356328, by decide⟩ ⟨12, 2, 0, 356328, 26781, 1913, 65536⟩
    (by decide) selected_cut_13599

theorem selected_cut_13600 : selected 9 ⟨356348, by decide⟩
    (prefixPartial 12 26782) = some ⟨12, 2, 0, 356348, 26782, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_26782_356348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26782 ⟨356348, by decide⟩ :=
  accepted_of_selected 12 26782 ⟨356348, by decide⟩ ⟨12, 2, 0, 356348, 26782, 1841, 65536⟩
    (by decide) selected_cut_13600

theorem selected_cut_13601 : selected 9 ⟨356369, by decide⟩
    (prefixPartial 12 26783) = some ⟨12, 2, 0, 356369, 26783, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_26783_356369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26783 ⟨356369, by decide⟩ :=
  accepted_of_selected 12 26783 ⟨356369, by decide⟩ ⟨12, 2, 0, 356369, 26783, 1673, 65536⟩
    (by decide) selected_cut_13601

theorem unmarked_context_11_6695_356370 : frontier 10 ⟨356370, by decide⟩
    (prefixCache 11 6695) (prefixPartial 11 6695) = false := by
  decide +kernel

theorem node_context_11_6695_356370 : EJMOriginalGlobalDAGData.nodes 10 ⟨356370, by decide⟩ =
    .split (coordinate 11) (![⟨356310, by decide⟩,⟨356328, by decide⟩,⟨356348, by decide⟩,⟨356369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6695_356370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6695 ⟨356370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6695
    ⟨356370, by decide⟩ (by decide) (![⟨356310, by decide⟩,⟨356328, by decide⟩,⟨356348, by decide⟩,⟨356369, by decide⟩]) unmarked_context_11_6695_356370 node_context_11_6695_356370
  intro a
  fin_cases a
  · exact context_12_26780_356310
  · exact context_12_26781_356328
  · exact context_12_26782_356348
  · exact context_12_26783_356369

theorem unmarked_context_10_1673_356371 : frontier 11 ⟨356371, by decide⟩
    (prefixCache 10 1673) (prefixPartial 10 1673) = false := by
  decide +kernel

theorem node_context_10_1673_356371 : EJMOriginalGlobalDAGData.nodes 11 ⟨356371, by decide⟩ =
    .split (coordinate 10) (![⟨356123, by decide⟩,⟨356211, by decide⟩,⟨356290, by decide⟩,⟨356370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1673_356371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1673 ⟨356371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1673
    ⟨356371, by decide⟩ (by decide) (![⟨356123, by decide⟩,⟨356211, by decide⟩,⟨356290, by decide⟩,⟨356370, by decide⟩]) unmarked_context_10_1673_356371 node_context_10_1673_356371
  intro a
  fin_cases a
  · exact context_11_6692_356123
  · exact context_11_6693_356211
  · exact context_11_6694_356290
  · exact context_11_6695_356370

theorem selected_cut_13602 : selected 9 ⟨356396, by decide⟩
    (prefixPartial 12 26784) = some ⟨12, 2, 0, 356396, 26784, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_26784_356396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26784 ⟨356396, by decide⟩ :=
  accepted_of_selected 12 26784 ⟨356396, by decide⟩ ⟨12, 2, 0, 356396, 26784, 2285, 65536⟩
    (by decide) selected_cut_13602

theorem selected_cut_13603 : selected 9 ⟨356415, by decide⟩
    (prefixPartial 12 26785) = some ⟨12, 2, 0, 356415, 26785, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_26785_356415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26785 ⟨356415, by decide⟩ :=
  accepted_of_selected 12 26785 ⟨356415, by decide⟩ ⟨12, 2, 0, 356415, 26785, 1681, 65536⟩
    (by decide) selected_cut_13603

theorem selected_cut_13604 : selected 9 ⟨356433, by decide⟩
    (prefixPartial 12 26786) = some ⟨12, 2, 0, 356433, 26786, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_26786_356433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26786 ⟨356433, by decide⟩ :=
  accepted_of_selected 12 26786 ⟨356433, by decide⟩ ⟨12, 2, 0, 356433, 26786, 1481, 65536⟩
    (by decide) selected_cut_13604

theorem selected_cut_13605 : selected 9 ⟨356447, by decide⟩
    (prefixPartial 12 26787) = some ⟨12, 2, 0, 356447, 26787, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_26787_356447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26787 ⟨356447, by decide⟩ :=
  accepted_of_selected 12 26787 ⟨356447, by decide⟩ ⟨12, 2, 0, 356447, 26787, 1361, 65536⟩
    (by decide) selected_cut_13605

theorem unmarked_context_11_6696_356448 : frontier 10 ⟨356448, by decide⟩
    (prefixCache 11 6696) (prefixPartial 11 6696) = false := by
  decide +kernel

theorem node_context_11_6696_356448 : EJMOriginalGlobalDAGData.nodes 10 ⟨356448, by decide⟩ =
    .split (coordinate 11) (![⟨356396, by decide⟩,⟨356415, by decide⟩,⟨356433, by decide⟩,⟨356447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6696_356448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6696 ⟨356448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6696
    ⟨356448, by decide⟩ (by decide) (![⟨356396, by decide⟩,⟨356415, by decide⟩,⟨356433, by decide⟩,⟨356447, by decide⟩]) unmarked_context_11_6696_356448 node_context_11_6696_356448
  intro a
  fin_cases a
  · exact context_12_26784_356396
  · exact context_12_26785_356415
  · exact context_12_26786_356433
  · exact context_12_26787_356447

theorem selected_cut_13606 : selected 9 ⟨356465, by decide⟩
    (prefixPartial 12 26788) = some ⟨12, 2, 0, 356465, 26788, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_26788_356465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26788 ⟨356465, by decide⟩ :=
  accepted_of_selected 12 26788 ⟨356465, by decide⟩ ⟨12, 2, 0, 356465, 26788, 1617, 65536⟩
    (by decide) selected_cut_13606

theorem selected_cut_13607 : selected 9 ⟨356481, by decide⟩
    (prefixPartial 12 26789) = some ⟨12, 2, 0, 356481, 26789, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_26789_356481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26789 ⟨356481, by decide⟩ :=
  accepted_of_selected 12 26789 ⟨356481, by decide⟩ ⟨12, 2, 0, 356481, 26789, 1733, 65536⟩
    (by decide) selected_cut_13607

theorem selected_cut_13608 : selected 9 ⟨356498, by decide⟩
    (prefixPartial 12 26790) = some ⟨12, 2, 0, 356498, 26790, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_26790_356498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26790 ⟨356498, by decide⟩ :=
  accepted_of_selected 12 26790 ⟨356498, by decide⟩ ⟨12, 2, 0, 356498, 26790, 1517, 65536⟩
    (by decide) selected_cut_13608

theorem selected_cut_13609 : selected 9 ⟨356513, by decide⟩
    (prefixPartial 12 26791) = some ⟨12, 2, 0, 356513, 26791, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_26791_356513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26791 ⟨356513, by decide⟩ :=
  accepted_of_selected 12 26791 ⟨356513, by decide⟩ ⟨12, 2, 0, 356513, 26791, 1493, 65536⟩
    (by decide) selected_cut_13609

theorem unmarked_context_11_6697_356514 : frontier 10 ⟨356514, by decide⟩
    (prefixCache 11 6697) (prefixPartial 11 6697) = false := by
  decide +kernel

theorem node_context_11_6697_356514 : EJMOriginalGlobalDAGData.nodes 10 ⟨356514, by decide⟩ =
    .split (coordinate 11) (![⟨356465, by decide⟩,⟨356481, by decide⟩,⟨356498, by decide⟩,⟨356513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6697_356514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6697 ⟨356514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6697
    ⟨356514, by decide⟩ (by decide) (![⟨356465, by decide⟩,⟨356481, by decide⟩,⟨356498, by decide⟩,⟨356513, by decide⟩]) unmarked_context_11_6697_356514 node_context_11_6697_356514
  intro a
  fin_cases a
  · exact context_12_26788_356465
  · exact context_12_26789_356481
  · exact context_12_26790_356498
  · exact context_12_26791_356513

theorem selected_cut_13610 : selected 10 ⟨356516, by decide⟩
    (prefixPartial 11 6698) = some ⟨11, 2, 0, 356516, 6698, 5, 262144⟩ := by
  decide +kernel

theorem context_11_6698_356516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6698 ⟨356516, by decide⟩ :=
  accepted_of_selected 11 6698 ⟨356516, by decide⟩ ⟨11, 2, 0, 356516, 6698, 5, 262144⟩
    (by decide) selected_cut_13610

theorem selected_cut_13611 : selected 9 ⟨356530, by decide⟩
    (prefixPartial 12 26796) = some ⟨12, 2, 0, 356530, 26796, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_26796_356530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26796 ⟨356530, by decide⟩ :=
  accepted_of_selected 12 26796 ⟨356530, by decide⟩ ⟨12, 2, 0, 356530, 26796, 1509, 65536⟩
    (by decide) selected_cut_13611

theorem selected_cut_13612 : selected 9 ⟨356544, by decide⟩
    (prefixPartial 12 26797) = some ⟨12, 2, 0, 356544, 26797, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_26797_356544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26797 ⟨356544, by decide⟩ :=
  accepted_of_selected 12 26797 ⟨356544, by decide⟩ ⟨12, 2, 0, 356544, 26797, 1573, 65536⟩
    (by decide) selected_cut_13612

theorem selected_cut_13613 : selected 9 ⟨356558, by decide⟩
    (prefixPartial 12 26798) = some ⟨12, 2, 0, 356558, 26798, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_26798_356558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26798 ⟨356558, by decide⟩ :=
  accepted_of_selected 12 26798 ⟨356558, by decide⟩ ⟨12, 2, 0, 356558, 26798, 1337, 65536⟩
    (by decide) selected_cut_13613

theorem selected_cut_13614 : selected 9 ⟨356572, by decide⟩
    (prefixPartial 12 26799) = some ⟨12, 2, 0, 356572, 26799, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_26799_356572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26799 ⟨356572, by decide⟩ :=
  accepted_of_selected 12 26799 ⟨356572, by decide⟩ ⟨12, 2, 0, 356572, 26799, 1301, 65536⟩
    (by decide) selected_cut_13614

theorem unmarked_context_11_6699_356573 : frontier 10 ⟨356573, by decide⟩
    (prefixCache 11 6699) (prefixPartial 11 6699) = false := by
  decide +kernel

theorem node_context_11_6699_356573 : EJMOriginalGlobalDAGData.nodes 10 ⟨356573, by decide⟩ =
    .split (coordinate 11) (![⟨356530, by decide⟩,⟨356544, by decide⟩,⟨356558, by decide⟩,⟨356572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6699_356573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6699 ⟨356573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6699
    ⟨356573, by decide⟩ (by decide) (![⟨356530, by decide⟩,⟨356544, by decide⟩,⟨356558, by decide⟩,⟨356572, by decide⟩]) unmarked_context_11_6699_356573 node_context_11_6699_356573
  intro a
  fin_cases a
  · exact context_12_26796_356530
  · exact context_12_26797_356544
  · exact context_12_26798_356558
  · exact context_12_26799_356572

theorem unmarked_context_10_1674_356574 : frontier 11 ⟨356574, by decide⟩
    (prefixCache 10 1674) (prefixPartial 10 1674) = false := by
  decide +kernel

theorem node_context_10_1674_356574 : EJMOriginalGlobalDAGData.nodes 11 ⟨356574, by decide⟩ =
    .split (coordinate 10) (![⟨356448, by decide⟩,⟨356514, by decide⟩,⟨356516, by decide⟩,⟨356573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1674_356574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1674 ⟨356574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1674
    ⟨356574, by decide⟩ (by decide) (![⟨356448, by decide⟩,⟨356514, by decide⟩,⟨356516, by decide⟩,⟨356573, by decide⟩]) unmarked_context_10_1674_356574 node_context_10_1674_356574
  intro a
  fin_cases a
  · exact context_11_6696_356448
  · exact context_11_6697_356514
  · exact context_11_6698_356516
  · exact context_11_6699_356573

theorem selected_cut_13615 : selected 9 ⟨356612, by decide⟩
    (prefixPartial 12 26800) = some ⟨12, 2, 0, 356612, 26800, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_26800_356612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26800 ⟨356612, by decide⟩ :=
  accepted_of_selected 12 26800 ⟨356612, by decide⟩ ⟨12, 2, 0, 356612, 26800, 2109, 65536⟩
    (by decide) selected_cut_13615

theorem selected_cut_13616 : selected 9 ⟨356628, by decide⟩
    (prefixPartial 12 26801) = some ⟨12, 2, 0, 356628, 26801, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_26801_356628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26801 ⟨356628, by decide⟩ :=
  accepted_of_selected 12 26801 ⟨356628, by decide⟩ ⟨12, 2, 0, 356628, 26801, 1401, 65536⟩
    (by decide) selected_cut_13616

theorem selected_cut_13617 : selected 9 ⟨356641, by decide⟩
    (prefixPartial 12 26802) = some ⟨12, 2, 0, 356641, 26802, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_26802_356641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26802 ⟨356641, by decide⟩ :=
  accepted_of_selected 12 26802 ⟨356641, by decide⟩ ⟨12, 2, 0, 356641, 26802, 1329, 65536⟩
    (by decide) selected_cut_13617

theorem selected_cut_13618 : selected 9 ⟨356651, by decide⟩
    (prefixPartial 12 26803) = some ⟨12, 2, 0, 356651, 26803, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_26803_356651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26803 ⟨356651, by decide⟩ :=
  accepted_of_selected 12 26803 ⟨356651, by decide⟩ ⟨12, 2, 0, 356651, 26803, 1277, 65536⟩
    (by decide) selected_cut_13618

theorem unmarked_context_11_6700_356652 : frontier 10 ⟨356652, by decide⟩
    (prefixCache 11 6700) (prefixPartial 11 6700) = false := by
  decide +kernel

theorem node_context_11_6700_356652 : EJMOriginalGlobalDAGData.nodes 10 ⟨356652, by decide⟩ =
    .split (coordinate 11) (![⟨356612, by decide⟩,⟨356628, by decide⟩,⟨356641, by decide⟩,⟨356651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6700_356652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6700 ⟨356652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6700
    ⟨356652, by decide⟩ (by decide) (![⟨356612, by decide⟩,⟨356628, by decide⟩,⟨356641, by decide⟩,⟨356651, by decide⟩]) unmarked_context_11_6700_356652 node_context_11_6700_356652
  intro a
  fin_cases a
  · exact context_12_26800_356612
  · exact context_12_26801_356628
  · exact context_12_26802_356641
  · exact context_12_26803_356651

theorem selected_cut_13619 : selected 9 ⟨356667, by decide⟩
    (prefixPartial 12 26804) = some ⟨12, 2, 0, 356667, 26804, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_26804_356667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26804 ⟨356667, by decide⟩ :=
  accepted_of_selected 12 26804 ⟨356667, by decide⟩ ⟨12, 2, 0, 356667, 26804, 1405, 65536⟩
    (by decide) selected_cut_13619

theorem selected_cut_13620 : selected 9 ⟨356685, by decide⟩
    (prefixPartial 12 26805) = some ⟨12, 2, 0, 356685, 26805, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_26805_356685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26805 ⟨356685, by decide⟩ :=
  accepted_of_selected 12 26805 ⟨356685, by decide⟩ ⟨12, 2, 0, 356685, 26805, 1341, 65536⟩
    (by decide) selected_cut_13620

theorem selected_cut_13621 : selected 9 ⟨356697, by decide⟩
    (prefixPartial 12 26806) = some ⟨12, 2, 0, 356697, 26806, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_26806_356697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26806 ⟨356697, by decide⟩ :=
  accepted_of_selected 12 26806 ⟨356697, by decide⟩ ⟨12, 2, 0, 356697, 26806, 1225, 65536⟩
    (by decide) selected_cut_13621

theorem selected_cut_13622 : selected 9 ⟨356707, by decide⟩
    (prefixPartial 12 26807) = some ⟨12, 2, 0, 356707, 26807, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_26807_356707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26807 ⟨356707, by decide⟩ :=
  accepted_of_selected 12 26807 ⟨356707, by decide⟩ ⟨12, 2, 0, 356707, 26807, 1269, 65536⟩
    (by decide) selected_cut_13622

theorem unmarked_context_11_6701_356708 : frontier 10 ⟨356708, by decide⟩
    (prefixCache 11 6701) (prefixPartial 11 6701) = false := by
  decide +kernel

theorem node_context_11_6701_356708 : EJMOriginalGlobalDAGData.nodes 10 ⟨356708, by decide⟩ =
    .split (coordinate 11) (![⟨356667, by decide⟩,⟨356685, by decide⟩,⟨356697, by decide⟩,⟨356707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6701_356708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6701 ⟨356708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6701
    ⟨356708, by decide⟩ (by decide) (![⟨356667, by decide⟩,⟨356685, by decide⟩,⟨356697, by decide⟩,⟨356707, by decide⟩]) unmarked_context_11_6701_356708 node_context_11_6701_356708
  intro a
  fin_cases a
  · exact context_12_26804_356667
  · exact context_12_26805_356685
  · exact context_12_26806_356697
  · exact context_12_26807_356707

theorem selected_cut_13623 : selected 9 ⟨356724, by decide⟩
    (prefixPartial 12 26808) = some ⟨12, 2, 0, 356724, 26808, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_26808_356724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26808 ⟨356724, by decide⟩ :=
  accepted_of_selected 12 26808 ⟨356724, by decide⟩ ⟨12, 2, 0, 356724, 26808, 1389, 65536⟩
    (by decide) selected_cut_13623

theorem selected_cut_13624 : selected 9 ⟨356739, by decide⟩
    (prefixPartial 12 26809) = some ⟨12, 2, 0, 356739, 26809, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_26809_356739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26809 ⟨356739, by decide⟩ :=
  accepted_of_selected 12 26809 ⟨356739, by decide⟩ ⟨12, 2, 0, 356739, 26809, 1313, 65536⟩
    (by decide) selected_cut_13624

theorem selected_cut_13625 : selected 9 ⟨356751, by decide⟩
    (prefixPartial 12 26810) = some ⟨12, 2, 0, 356751, 26810, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_26810_356751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26810 ⟨356751, by decide⟩ :=
  accepted_of_selected 12 26810 ⟨356751, by decide⟩ ⟨12, 2, 0, 356751, 26810, 1193, 65536⟩
    (by decide) selected_cut_13625

theorem selected_cut_13626 : selected 9 ⟨356766, by decide⟩
    (prefixPartial 12 26811) = some ⟨12, 2, 0, 356766, 26811, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_26811_356766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26811 ⟨356766, by decide⟩ :=
  accepted_of_selected 12 26811 ⟨356766, by decide⟩ ⟨12, 2, 0, 356766, 26811, 1257, 65536⟩
    (by decide) selected_cut_13626

theorem unmarked_context_11_6702_356767 : frontier 10 ⟨356767, by decide⟩
    (prefixCache 11 6702) (prefixPartial 11 6702) = false := by
  decide +kernel

theorem node_context_11_6702_356767 : EJMOriginalGlobalDAGData.nodes 10 ⟨356767, by decide⟩ =
    .split (coordinate 11) (![⟨356724, by decide⟩,⟨356739, by decide⟩,⟨356751, by decide⟩,⟨356766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6702_356767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6702 ⟨356767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6702
    ⟨356767, by decide⟩ (by decide) (![⟨356724, by decide⟩,⟨356739, by decide⟩,⟨356751, by decide⟩,⟨356766, by decide⟩]) unmarked_context_11_6702_356767 node_context_11_6702_356767
  intro a
  fin_cases a
  · exact context_12_26808_356724
  · exact context_12_26809_356739
  · exact context_12_26810_356751
  · exact context_12_26811_356766

theorem selected_cut_13627 : selected 9 ⟨356780, by decide⟩
    (prefixPartial 12 26812) = some ⟨12, 2, 0, 356780, 26812, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_26812_356780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26812 ⟨356780, by decide⟩ :=
  accepted_of_selected 12 26812 ⟨356780, by decide⟩ ⟨12, 2, 0, 356780, 26812, 1233, 65536⟩
    (by decide) selected_cut_13627

theorem selected_cut_13628 : selected 9 ⟨356794, by decide⟩
    (prefixPartial 12 26813) = some ⟨12, 2, 0, 356794, 26813, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_26813_356794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26813 ⟨356794, by decide⟩ :=
  accepted_of_selected 12 26813 ⟨356794, by decide⟩ ⟨12, 2, 0, 356794, 26813, 1093, 65536⟩
    (by decide) selected_cut_13628

theorem selected_cut_13629 : selected 9 ⟨356805, by decide⟩
    (prefixPartial 12 26814) = some ⟨12, 2, 0, 356805, 26814, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_26814_356805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26814 ⟨356805, by decide⟩ :=
  accepted_of_selected 12 26814 ⟨356805, by decide⟩ ⟨12, 2, 0, 356805, 26814, 1033, 65536⟩
    (by decide) selected_cut_13629

theorem selected_cut_13630 : selected 9 ⟨356818, by decide⟩
    (prefixPartial 12 26815) = some ⟨12, 2, 0, 356818, 26815, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_26815_356818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26815 ⟨356818, by decide⟩ :=
  accepted_of_selected 12 26815 ⟨356818, by decide⟩ ⟨12, 2, 0, 356818, 26815, 1065, 65536⟩
    (by decide) selected_cut_13630

theorem unmarked_context_11_6703_356819 : frontier 10 ⟨356819, by decide⟩
    (prefixCache 11 6703) (prefixPartial 11 6703) = false := by
  decide +kernel

theorem node_context_11_6703_356819 : EJMOriginalGlobalDAGData.nodes 10 ⟨356819, by decide⟩ =
    .split (coordinate 11) (![⟨356780, by decide⟩,⟨356794, by decide⟩,⟨356805, by decide⟩,⟨356818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6703_356819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6703 ⟨356819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6703
    ⟨356819, by decide⟩ (by decide) (![⟨356780, by decide⟩,⟨356794, by decide⟩,⟨356805, by decide⟩,⟨356818, by decide⟩]) unmarked_context_11_6703_356819 node_context_11_6703_356819
  intro a
  fin_cases a
  · exact context_12_26812_356780
  · exact context_12_26813_356794
  · exact context_12_26814_356805
  · exact context_12_26815_356818

theorem unmarked_context_10_1675_356820 : frontier 11 ⟨356820, by decide⟩
    (prefixCache 10 1675) (prefixPartial 10 1675) = false := by
  decide +kernel

theorem node_context_10_1675_356820 : EJMOriginalGlobalDAGData.nodes 11 ⟨356820, by decide⟩ =
    .split (coordinate 10) (![⟨356652, by decide⟩,⟨356708, by decide⟩,⟨356767, by decide⟩,⟨356819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1675_356820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1675 ⟨356820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1675
    ⟨356820, by decide⟩ (by decide) (![⟨356652, by decide⟩,⟨356708, by decide⟩,⟨356767, by decide⟩,⟨356819, by decide⟩]) unmarked_context_10_1675_356820 node_context_10_1675_356820
  intro a
  fin_cases a
  · exact context_11_6700_356652
  · exact context_11_6701_356708
  · exact context_11_6702_356767
  · exact context_11_6703_356819

theorem unmarked_context_9_418_356821 : frontier 12 ⟨356821, by decide⟩
    (prefixCache 9 418) (prefixPartial 9 418) = false := by
  decide +kernel

theorem node_context_9_418_356821 : EJMOriginalGlobalDAGData.nodes 12 ⟨356821, by decide⟩ =
    .split (coordinate 9) (![⟨356003, by decide⟩,⟨356371, by decide⟩,⟨356574, by decide⟩,⟨356820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_418_356821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 418 ⟨356821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 418
    ⟨356821, by decide⟩ (by decide) (![⟨356003, by decide⟩,⟨356371, by decide⟩,⟨356574, by decide⟩,⟨356820, by decide⟩]) unmarked_context_9_418_356821 node_context_9_418_356821
  intro a
  fin_cases a
  · exact context_10_1672_356003
  · exact context_10_1673_356371
  · exact context_10_1674_356574
  · exact context_10_1675_356820

theorem selected_cut_13631 : selected 10 ⟨356864, by decide⟩
    (prefixPartial 11 6704) = some ⟨11, 2, 0, 356864, 6704, 3981, 262144⟩ := by
  decide +kernel

theorem context_11_6704_356864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6704 ⟨356864, by decide⟩ :=
  accepted_of_selected 11 6704 ⟨356864, by decide⟩ ⟨11, 2, 0, 356864, 6704, 3981, 262144⟩
    (by decide) selected_cut_13631

theorem selected_cut_13632 : selected 10 ⟨356894, by decide⟩
    (prefixPartial 11 6705) = some ⟨11, 2, 0, 356894, 6705, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_6705_356894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6705 ⟨356894, by decide⟩ :=
  accepted_of_selected 11 6705 ⟨356894, by decide⟩ ⟨11, 2, 0, 356894, 6705, 3273, 262144⟩
    (by decide) selected_cut_13632

theorem selected_cut_13633 : selected 10 ⟨356925, by decide⟩
    (prefixPartial 11 6706) = some ⟨11, 2, 0, 356925, 6706, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_6706_356925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6706 ⟨356925, by decide⟩ :=
  accepted_of_selected 11 6706 ⟨356925, by decide⟩ ⟨11, 2, 0, 356925, 6706, 3249, 262144⟩
    (by decide) selected_cut_13633

theorem selected_cut_13634 : selected 10 ⟨356952, by decide⟩
    (prefixPartial 11 6707) = some ⟨11, 2, 0, 356952, 6707, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_6707_356952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6707 ⟨356952, by decide⟩ :=
  accepted_of_selected 11 6707 ⟨356952, by decide⟩ ⟨11, 2, 0, 356952, 6707, 2909, 262144⟩
    (by decide) selected_cut_13634

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
