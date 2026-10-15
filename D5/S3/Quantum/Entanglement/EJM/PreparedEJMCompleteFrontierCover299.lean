/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover298
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28707 : selected 8 ⟨724062, by decide⟩
    (prefixPartial 13 371781) = some ⟨13, 2, 0, 724062, 371781, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_371781_724062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371781 ⟨724062, by decide⟩ :=
  accepted_of_selected 13 371781 ⟨724062, by decide⟩ ⟨13, 2, 0, 724062, 371781, 1605, 16384⟩
    (by decide) selected_cut_28707

theorem selected_cut_28708 : selected 8 ⟨724081, by decide⟩
    (prefixPartial 13 371782) = some ⟨13, 2, 0, 724081, 371782, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_371782_724081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371782 ⟨724081, by decide⟩ :=
  accepted_of_selected 13 371782 ⟨724081, by decide⟩ ⟨13, 2, 0, 724081, 371782, 1633, 16384⟩
    (by decide) selected_cut_28708

theorem selected_cut_28709 : selected 8 ⟨724087, by decide⟩
    (prefixPartial 13 371783) = some ⟨13, 2, 0, 724087, 371783, 601, 16384⟩ := by
  decide +kernel

theorem context_13_371783_724087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371783 ⟨724087, by decide⟩ :=
  accepted_of_selected 13 371783 ⟨724087, by decide⟩ ⟨13, 2, 0, 724087, 371783, 601, 16384⟩
    (by decide) selected_cut_28709

theorem unmarked_context_12_92945_724088 : frontier 9 ⟨724088, by decide⟩
    (prefixCache 12 92945) (prefixPartial 12 92945) = false := by
  decide +kernel

theorem node_context_12_92945_724088 : EJMOriginalGlobalDAGData.nodes 9 ⟨724088, by decide⟩ =
    .split (coordinate 12) (![⟨724035, by decide⟩,⟨724062, by decide⟩,⟨724081, by decide⟩,⟨724087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92945_724088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92945 ⟨724088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92945
    ⟨724088, by decide⟩ (by decide) (![⟨724035, by decide⟩,⟨724062, by decide⟩,⟨724081, by decide⟩,⟨724087, by decide⟩]) unmarked_context_12_92945_724088 node_context_12_92945_724088
  intro a
  fin_cases a
  · exact context_13_371780_724035
  · exact context_13_371781_724062
  · exact context_13_371782_724081
  · exact context_13_371783_724087

theorem selected_cut_28710 : selected 8 ⟨724119, by decide⟩
    (prefixPartial 13 371784) = some ⟨13, 2, 0, 724119, 371784, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_371784_724119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371784 ⟨724119, by decide⟩ :=
  accepted_of_selected 13 371784 ⟨724119, by decide⟩ ⟨13, 2, 0, 724119, 371784, 2261, 16384⟩
    (by decide) selected_cut_28710

theorem selected_cut_28711 : selected 8 ⟨724150, by decide⟩
    (prefixPartial 13 371785) = some ⟨13, 2, 0, 724150, 371785, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_371785_724150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371785 ⟨724150, by decide⟩ :=
  accepted_of_selected 13 371785 ⟨724150, by decide⟩ ⟨13, 2, 0, 724150, 371785, 1897, 16384⟩
    (by decide) selected_cut_28711

theorem selected_cut_28712 : selected 8 ⟨724175, by decide⟩
    (prefixPartial 13 371786) = some ⟨13, 2, 0, 724175, 371786, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_371786_724175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371786 ⟨724175, by decide⟩ :=
  accepted_of_selected 13 371786 ⟨724175, by decide⟩ ⟨13, 2, 0, 724175, 371786, 1569, 16384⟩
    (by decide) selected_cut_28712

theorem selected_cut_28713 : selected 8 ⟨724181, by decide⟩
    (prefixPartial 13 371787) = some ⟨13, 2, 0, 724181, 371787, 645, 16384⟩ := by
  decide +kernel

theorem context_13_371787_724181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371787 ⟨724181, by decide⟩ :=
  accepted_of_selected 13 371787 ⟨724181, by decide⟩ ⟨13, 2, 0, 724181, 371787, 645, 16384⟩
    (by decide) selected_cut_28713

theorem unmarked_context_12_92946_724182 : frontier 9 ⟨724182, by decide⟩
    (prefixCache 12 92946) (prefixPartial 12 92946) = false := by
  decide +kernel

theorem node_context_12_92946_724182 : EJMOriginalGlobalDAGData.nodes 9 ⟨724182, by decide⟩ =
    .split (coordinate 12) (![⟨724119, by decide⟩,⟨724150, by decide⟩,⟨724175, by decide⟩,⟨724181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92946_724182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92946 ⟨724182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92946
    ⟨724182, by decide⟩ (by decide) (![⟨724119, by decide⟩,⟨724150, by decide⟩,⟨724175, by decide⟩,⟨724181, by decide⟩]) unmarked_context_12_92946_724182 node_context_12_92946_724182
  intro a
  fin_cases a
  · exact context_13_371784_724119
  · exact context_13_371785_724150
  · exact context_13_371786_724175
  · exact context_13_371787_724181

theorem selected_cut_28714 : selected 8 ⟨724207, by decide⟩
    (prefixPartial 13 371788) = some ⟨13, 2, 0, 724207, 371788, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_371788_724207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371788 ⟨724207, by decide⟩ :=
  accepted_of_selected 13 371788 ⟨724207, by decide⟩ ⟨13, 2, 0, 724207, 371788, 2045, 16384⟩
    (by decide) selected_cut_28714

theorem selected_cut_28715 : selected 8 ⟨724230, by decide⟩
    (prefixPartial 13 371789) = some ⟨13, 2, 0, 724230, 371789, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_371789_724230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371789 ⟨724230, by decide⟩ :=
  accepted_of_selected 13 371789 ⟨724230, by decide⟩ ⟨13, 2, 0, 724230, 371789, 1925, 16384⟩
    (by decide) selected_cut_28715

theorem selected_cut_28716 : selected 8 ⟨724249, by decide⟩
    (prefixPartial 13 371790) = some ⟨13, 2, 0, 724249, 371790, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_371790_724249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371790 ⟨724249, by decide⟩ :=
  accepted_of_selected 13 371790 ⟨724249, by decide⟩ ⟨13, 2, 0, 724249, 371790, 1473, 16384⟩
    (by decide) selected_cut_28716

theorem selected_cut_28717 : selected 8 ⟨724254, by decide⟩
    (prefixPartial 13 371791) = some ⟨13, 2, 0, 724254, 371791, 589, 16384⟩ := by
  decide +kernel

theorem context_13_371791_724254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371791 ⟨724254, by decide⟩ :=
  accepted_of_selected 13 371791 ⟨724254, by decide⟩ ⟨13, 2, 0, 724254, 371791, 589, 16384⟩
    (by decide) selected_cut_28717

theorem unmarked_context_12_92947_724255 : frontier 9 ⟨724255, by decide⟩
    (prefixCache 12 92947) (prefixPartial 12 92947) = false := by
  decide +kernel

theorem node_context_12_92947_724255 : EJMOriginalGlobalDAGData.nodes 9 ⟨724255, by decide⟩ =
    .split (coordinate 12) (![⟨724207, by decide⟩,⟨724230, by decide⟩,⟨724249, by decide⟩,⟨724254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92947_724255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92947 ⟨724255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92947
    ⟨724255, by decide⟩ (by decide) (![⟨724207, by decide⟩,⟨724230, by decide⟩,⟨724249, by decide⟩,⟨724254, by decide⟩]) unmarked_context_12_92947_724255 node_context_12_92947_724255
  intro a
  fin_cases a
  · exact context_13_371788_724207
  · exact context_13_371789_724230
  · exact context_13_371790_724249
  · exact context_13_371791_724254

theorem unmarked_context_11_23236_724256 : frontier 10 ⟨724256, by decide⟩
    (prefixCache 11 23236) (prefixPartial 11 23236) = false := by
  decide +kernel

theorem node_context_11_23236_724256 : EJMOriginalGlobalDAGData.nodes 10 ⟨724256, by decide⟩ =
    .split (coordinate 11) (![⟨723995, by decide⟩,⟨724088, by decide⟩,⟨724182, by decide⟩,⟨724255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23236_724256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23236 ⟨724256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23236
    ⟨724256, by decide⟩ (by decide) (![⟨723995, by decide⟩,⟨724088, by decide⟩,⟨724182, by decide⟩,⟨724255, by decide⟩]) unmarked_context_11_23236_724256 node_context_11_23236_724256
  intro a
  fin_cases a
  · exact context_12_92944_723995
  · exact context_12_92945_724088
  · exact context_12_92946_724182
  · exact context_12_92947_724255

theorem selected_cut_28718 : selected 8 ⟨724280, by decide⟩
    (prefixPartial 13 371792) = some ⟨13, 2, 0, 724280, 371792, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_371792_724280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371792 ⟨724280, by decide⟩ :=
  accepted_of_selected 13 371792 ⟨724280, by decide⟩ ⟨13, 2, 0, 724280, 371792, 1805, 16384⟩
    (by decide) selected_cut_28718

theorem selected_cut_28719 : selected 8 ⟨724315, by decide⟩
    (prefixPartial 13 371793) = some ⟨13, 2, 0, 724315, 371793, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_371793_724315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371793 ⟨724315, by decide⟩ :=
  accepted_of_selected 13 371793 ⟨724315, by decide⟩ ⟨13, 2, 0, 724315, 371793, 2133, 16384⟩
    (by decide) selected_cut_28719

theorem selected_cut_28720 : selected 8 ⟨724338, by decide⟩
    (prefixPartial 13 371794) = some ⟨13, 2, 0, 724338, 371794, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_371794_724338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371794 ⟨724338, by decide⟩ :=
  accepted_of_selected 13 371794 ⟨724338, by decide⟩ ⟨13, 2, 0, 724338, 371794, 1641, 16384⟩
    (by decide) selected_cut_28720

theorem selected_cut_28721 : selected 8 ⟨724345, by decide⟩
    (prefixPartial 13 371795) = some ⟨13, 2, 0, 724345, 371795, 789, 16384⟩ := by
  decide +kernel

theorem context_13_371795_724345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371795 ⟨724345, by decide⟩ :=
  accepted_of_selected 13 371795 ⟨724345, by decide⟩ ⟨13, 2, 0, 724345, 371795, 789, 16384⟩
    (by decide) selected_cut_28721

theorem unmarked_context_12_92948_724346 : frontier 9 ⟨724346, by decide⟩
    (prefixCache 12 92948) (prefixPartial 12 92948) = false := by
  decide +kernel

theorem node_context_12_92948_724346 : EJMOriginalGlobalDAGData.nodes 9 ⟨724346, by decide⟩ =
    .split (coordinate 12) (![⟨724280, by decide⟩,⟨724315, by decide⟩,⟨724338, by decide⟩,⟨724345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92948_724346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92948 ⟨724346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92948
    ⟨724346, by decide⟩ (by decide) (![⟨724280, by decide⟩,⟨724315, by decide⟩,⟨724338, by decide⟩,⟨724345, by decide⟩]) unmarked_context_12_92948_724346 node_context_12_92948_724346
  intro a
  fin_cases a
  · exact context_13_371792_724280
  · exact context_13_371793_724315
  · exact context_13_371794_724338
  · exact context_13_371795_724345

theorem selected_cut_28722 : selected 8 ⟨724380, by decide⟩
    (prefixPartial 13 371796) = some ⟨13, 2, 0, 724380, 371796, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_371796_724380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371796 ⟨724380, by decide⟩ :=
  accepted_of_selected 13 371796 ⟨724380, by decide⟩ ⟨13, 2, 0, 724380, 371796, 2265, 16384⟩
    (by decide) selected_cut_28722

theorem selected_cut_28723 : selected 8 ⟨724403, by decide⟩
    (prefixPartial 13 371797) = some ⟨13, 2, 0, 724403, 371797, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_371797_724403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371797 ⟨724403, by decide⟩ :=
  accepted_of_selected 13 371797 ⟨724403, by decide⟩ ⟨13, 2, 0, 724403, 371797, 1713, 16384⟩
    (by decide) selected_cut_28723

theorem selected_cut_28724 : selected 8 ⟨724427, by decide⟩
    (prefixPartial 13 371798) = some ⟨13, 2, 0, 724427, 371798, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_371798_724427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371798 ⟨724427, by decide⟩ :=
  accepted_of_selected 13 371798 ⟨724427, by decide⟩ ⟨13, 2, 0, 724427, 371798, 1589, 16384⟩
    (by decide) selected_cut_28724

theorem selected_cut_28725 : selected 8 ⟨724432, by decide⟩
    (prefixPartial 13 371799) = some ⟨13, 2, 0, 724432, 371799, 633, 16384⟩ := by
  decide +kernel

theorem context_13_371799_724432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371799 ⟨724432, by decide⟩ :=
  accepted_of_selected 13 371799 ⟨724432, by decide⟩ ⟨13, 2, 0, 724432, 371799, 633, 16384⟩
    (by decide) selected_cut_28725

theorem unmarked_context_12_92949_724433 : frontier 9 ⟨724433, by decide⟩
    (prefixCache 12 92949) (prefixPartial 12 92949) = false := by
  decide +kernel

theorem node_context_12_92949_724433 : EJMOriginalGlobalDAGData.nodes 9 ⟨724433, by decide⟩ =
    .split (coordinate 12) (![⟨724380, by decide⟩,⟨724403, by decide⟩,⟨724427, by decide⟩,⟨724432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92949_724433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92949 ⟨724433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92949
    ⟨724433, by decide⟩ (by decide) (![⟨724380, by decide⟩,⟨724403, by decide⟩,⟨724427, by decide⟩,⟨724432, by decide⟩]) unmarked_context_12_92949_724433 node_context_12_92949_724433
  intro a
  fin_cases a
  · exact context_13_371796_724380
  · exact context_13_371797_724403
  · exact context_13_371798_724427
  · exact context_13_371799_724432

theorem selected_cut_28726 : selected 8 ⟨724463, by decide⟩
    (prefixPartial 13 371800) = some ⟨13, 2, 0, 724463, 371800, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_371800_724463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371800 ⟨724463, by decide⟩ :=
  accepted_of_selected 13 371800 ⟨724463, by decide⟩ ⟨13, 2, 0, 724463, 371800, 2025, 16384⟩
    (by decide) selected_cut_28726

theorem selected_cut_28727 : selected 8 ⟨724491, by decide⟩
    (prefixPartial 13 371801) = some ⟨13, 2, 0, 724491, 371801, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_371801_724491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371801 ⟨724491, by decide⟩ :=
  accepted_of_selected 13 371801 ⟨724491, by decide⟩ ⟨13, 2, 0, 724491, 371801, 2029, 16384⟩
    (by decide) selected_cut_28727

theorem selected_cut_28728 : selected 8 ⟨724511, by decide⟩
    (prefixPartial 13 371802) = some ⟨13, 2, 0, 724511, 371802, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_371802_724511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371802 ⟨724511, by decide⟩ :=
  accepted_of_selected 13 371802 ⟨724511, by decide⟩ ⟨13, 2, 0, 724511, 371802, 1537, 16384⟩
    (by decide) selected_cut_28728

theorem selected_cut_28729 : selected 8 ⟨724516, by decide⟩
    (prefixPartial 13 371803) = some ⟨13, 2, 0, 724516, 371803, 761, 16384⟩ := by
  decide +kernel

theorem context_13_371803_724516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371803 ⟨724516, by decide⟩ :=
  accepted_of_selected 13 371803 ⟨724516, by decide⟩ ⟨13, 2, 0, 724516, 371803, 761, 16384⟩
    (by decide) selected_cut_28729

theorem unmarked_context_12_92950_724517 : frontier 9 ⟨724517, by decide⟩
    (prefixCache 12 92950) (prefixPartial 12 92950) = false := by
  decide +kernel

theorem node_context_12_92950_724517 : EJMOriginalGlobalDAGData.nodes 9 ⟨724517, by decide⟩ =
    .split (coordinate 12) (![⟨724463, by decide⟩,⟨724491, by decide⟩,⟨724511, by decide⟩,⟨724516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92950_724517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92950 ⟨724517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92950
    ⟨724517, by decide⟩ (by decide) (![⟨724463, by decide⟩,⟨724491, by decide⟩,⟨724511, by decide⟩,⟨724516, by decide⟩]) unmarked_context_12_92950_724517 node_context_12_92950_724517
  intro a
  fin_cases a
  · exact context_13_371800_724463
  · exact context_13_371801_724491
  · exact context_13_371802_724511
  · exact context_13_371803_724516

theorem selected_cut_28730 : selected 8 ⟨724545, by decide⟩
    (prefixPartial 13 371804) = some ⟨13, 2, 0, 724545, 371804, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_371804_724545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371804 ⟨724545, by decide⟩ :=
  accepted_of_selected 13 371804 ⟨724545, by decide⟩ ⟨13, 2, 0, 724545, 371804, 1849, 16384⟩
    (by decide) selected_cut_28730

theorem selected_cut_28731 : selected 8 ⟨724577, by decide⟩
    (prefixPartial 13 371805) = some ⟨13, 2, 0, 724577, 371805, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_371805_724577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371805 ⟨724577, by decide⟩ :=
  accepted_of_selected 13 371805 ⟨724577, by decide⟩ ⟨13, 2, 0, 724577, 371805, 2105, 16384⟩
    (by decide) selected_cut_28731

theorem selected_cut_28732 : selected 8 ⟨724600, by decide⟩
    (prefixPartial 13 371806) = some ⟨13, 2, 0, 724600, 371806, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_371806_724600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371806 ⟨724600, by decide⟩ :=
  accepted_of_selected 13 371806 ⟨724600, by decide⟩ ⟨13, 2, 0, 724600, 371806, 1489, 16384⟩
    (by decide) selected_cut_28732

theorem selected_cut_28733 : selected 8 ⟨724606, by decide⟩
    (prefixPartial 13 371807) = some ⟨13, 2, 0, 724606, 371807, 629, 16384⟩ := by
  decide +kernel

theorem context_13_371807_724606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371807 ⟨724606, by decide⟩ :=
  accepted_of_selected 13 371807 ⟨724606, by decide⟩ ⟨13, 2, 0, 724606, 371807, 629, 16384⟩
    (by decide) selected_cut_28733

theorem unmarked_context_12_92951_724607 : frontier 9 ⟨724607, by decide⟩
    (prefixCache 12 92951) (prefixPartial 12 92951) = false := by
  decide +kernel

theorem node_context_12_92951_724607 : EJMOriginalGlobalDAGData.nodes 9 ⟨724607, by decide⟩ =
    .split (coordinate 12) (![⟨724545, by decide⟩,⟨724577, by decide⟩,⟨724600, by decide⟩,⟨724606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92951_724607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92951 ⟨724607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92951
    ⟨724607, by decide⟩ (by decide) (![⟨724545, by decide⟩,⟨724577, by decide⟩,⟨724600, by decide⟩,⟨724606, by decide⟩]) unmarked_context_12_92951_724607 node_context_12_92951_724607
  intro a
  fin_cases a
  · exact context_13_371804_724545
  · exact context_13_371805_724577
  · exact context_13_371806_724600
  · exact context_13_371807_724606

theorem unmarked_context_11_23237_724608 : frontier 10 ⟨724608, by decide⟩
    (prefixCache 11 23237) (prefixPartial 11 23237) = false := by
  decide +kernel

theorem node_context_11_23237_724608 : EJMOriginalGlobalDAGData.nodes 10 ⟨724608, by decide⟩ =
    .split (coordinate 11) (![⟨724346, by decide⟩,⟨724433, by decide⟩,⟨724517, by decide⟩,⟨724607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23237_724608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23237 ⟨724608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23237
    ⟨724608, by decide⟩ (by decide) (![⟨724346, by decide⟩,⟨724433, by decide⟩,⟨724517, by decide⟩,⟨724607, by decide⟩]) unmarked_context_11_23237_724608 node_context_11_23237_724608
  intro a
  fin_cases a
  · exact context_12_92948_724346
  · exact context_12_92949_724433
  · exact context_12_92950_724517
  · exact context_12_92951_724607

theorem selected_cut_28734 : selected 8 ⟨724631, by decide⟩
    (prefixPartial 13 371808) = some ⟨13, 2, 0, 724631, 371808, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_371808_724631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371808 ⟨724631, by decide⟩ :=
  accepted_of_selected 13 371808 ⟨724631, by decide⟩ ⟨13, 2, 0, 724631, 371808, 1393, 16384⟩
    (by decide) selected_cut_28734

theorem selected_cut_28735 : selected 8 ⟨724655, by decide⟩
    (prefixPartial 13 371809) = some ⟨13, 2, 0, 724655, 371809, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_371809_724655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371809 ⟨724655, by decide⟩ :=
  accepted_of_selected 13 371809 ⟨724655, by decide⟩ ⟨13, 2, 0, 724655, 371809, 1777, 16384⟩
    (by decide) selected_cut_28735

theorem selected_cut_28736 : selected 8 ⟨724672, by decide⟩
    (prefixPartial 13 371810) = some ⟨13, 2, 0, 724672, 371810, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_371810_724672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371810 ⟨724672, by decide⟩ :=
  accepted_of_selected 13 371810 ⟨724672, by decide⟩ ⟨13, 2, 0, 724672, 371810, 1233, 16384⟩
    (by decide) selected_cut_28736

theorem selected_cut_28737 : selected 8 ⟨724679, by decide⟩
    (prefixPartial 13 371811) = some ⟨13, 2, 0, 724679, 371811, 725, 16384⟩ := by
  decide +kernel

theorem context_13_371811_724679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371811 ⟨724679, by decide⟩ :=
  accepted_of_selected 13 371811 ⟨724679, by decide⟩ ⟨13, 2, 0, 724679, 371811, 725, 16384⟩
    (by decide) selected_cut_28737

theorem unmarked_context_12_92952_724680 : frontier 9 ⟨724680, by decide⟩
    (prefixCache 12 92952) (prefixPartial 12 92952) = false := by
  decide +kernel

theorem node_context_12_92952_724680 : EJMOriginalGlobalDAGData.nodes 9 ⟨724680, by decide⟩ =
    .split (coordinate 12) (![⟨724631, by decide⟩,⟨724655, by decide⟩,⟨724672, by decide⟩,⟨724679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92952_724680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92952 ⟨724680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92952
    ⟨724680, by decide⟩ (by decide) (![⟨724631, by decide⟩,⟨724655, by decide⟩,⟨724672, by decide⟩,⟨724679, by decide⟩]) unmarked_context_12_92952_724680 node_context_12_92952_724680
  intro a
  fin_cases a
  · exact context_13_371808_724631
  · exact context_13_371809_724655
  · exact context_13_371810_724672
  · exact context_13_371811_724679

theorem selected_cut_28738 : selected 8 ⟨724706, by decide⟩
    (prefixPartial 13 371812) = some ⟨13, 2, 0, 724706, 371812, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_371812_724706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371812 ⟨724706, by decide⟩ :=
  accepted_of_selected 13 371812 ⟨724706, by decide⟩ ⟨13, 2, 0, 724706, 371812, 1625, 16384⟩
    (by decide) selected_cut_28738

theorem selected_cut_28739 : selected 8 ⟨724730, by decide⟩
    (prefixPartial 13 371813) = some ⟨13, 2, 0, 724730, 371813, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_371813_724730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371813 ⟨724730, by decide⟩ :=
  accepted_of_selected 13 371813 ⟨724730, by decide⟩ ⟨13, 2, 0, 724730, 371813, 1429, 16384⟩
    (by decide) selected_cut_28739

theorem selected_cut_28740 : selected 8 ⟨724749, by decide⟩
    (prefixPartial 13 371814) = some ⟨13, 2, 0, 724749, 371814, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_371814_724749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371814 ⟨724749, by decide⟩ :=
  accepted_of_selected 13 371814 ⟨724749, by decide⟩ ⟨13, 2, 0, 724749, 371814, 1253, 16384⟩
    (by decide) selected_cut_28740

theorem selected_cut_28741 : selected 8 ⟨724755, by decide⟩
    (prefixPartial 13 371815) = some ⟨13, 2, 0, 724755, 371815, 697, 16384⟩ := by
  decide +kernel

theorem context_13_371815_724755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371815 ⟨724755, by decide⟩ :=
  accepted_of_selected 13 371815 ⟨724755, by decide⟩ ⟨13, 2, 0, 724755, 371815, 697, 16384⟩
    (by decide) selected_cut_28741

theorem unmarked_context_12_92953_724756 : frontier 9 ⟨724756, by decide⟩
    (prefixCache 12 92953) (prefixPartial 12 92953) = false := by
  decide +kernel

theorem node_context_12_92953_724756 : EJMOriginalGlobalDAGData.nodes 9 ⟨724756, by decide⟩ =
    .split (coordinate 12) (![⟨724706, by decide⟩,⟨724730, by decide⟩,⟨724749, by decide⟩,⟨724755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92953_724756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92953 ⟨724756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92953
    ⟨724756, by decide⟩ (by decide) (![⟨724706, by decide⟩,⟨724730, by decide⟩,⟨724749, by decide⟩,⟨724755, by decide⟩]) unmarked_context_12_92953_724756 node_context_12_92953_724756
  intro a
  fin_cases a
  · exact context_13_371812_724706
  · exact context_13_371813_724730
  · exact context_13_371814_724749
  · exact context_13_371815_724755

theorem selected_cut_28742 : selected 8 ⟨724776, by decide⟩
    (prefixPartial 13 371816) = some ⟨13, 2, 0, 724776, 371816, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_371816_724776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371816 ⟨724776, by decide⟩ :=
  accepted_of_selected 13 371816 ⟨724776, by decide⟩ ⟨13, 2, 0, 724776, 371816, 1409, 16384⟩
    (by decide) selected_cut_28742

theorem selected_cut_28743 : selected 8 ⟨724800, by decide⟩
    (prefixPartial 13 371817) = some ⟨13, 2, 0, 724800, 371817, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_371817_724800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371817 ⟨724800, by decide⟩ :=
  accepted_of_selected 13 371817 ⟨724800, by decide⟩ ⟨13, 2, 0, 724800, 371817, 1705, 16384⟩
    (by decide) selected_cut_28743

theorem selected_cut_28744 : selected 8 ⟨724817, by decide⟩
    (prefixPartial 13 371818) = some ⟨13, 2, 0, 724817, 371818, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_371818_724817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371818 ⟨724817, by decide⟩ :=
  accepted_of_selected 13 371818 ⟨724817, by decide⟩ ⟨13, 2, 0, 724817, 371818, 1201, 16384⟩
    (by decide) selected_cut_28744

theorem selected_cut_28745 : selected 8 ⟨724824, by decide⟩
    (prefixPartial 13 371819) = some ⟨13, 2, 0, 724824, 371819, 689, 16384⟩ := by
  decide +kernel

theorem context_13_371819_724824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371819 ⟨724824, by decide⟩ :=
  accepted_of_selected 13 371819 ⟨724824, by decide⟩ ⟨13, 2, 0, 724824, 371819, 689, 16384⟩
    (by decide) selected_cut_28745

theorem unmarked_context_12_92954_724825 : frontier 9 ⟨724825, by decide⟩
    (prefixCache 12 92954) (prefixPartial 12 92954) = false := by
  decide +kernel

theorem node_context_12_92954_724825 : EJMOriginalGlobalDAGData.nodes 9 ⟨724825, by decide⟩ =
    .split (coordinate 12) (![⟨724776, by decide⟩,⟨724800, by decide⟩,⟨724817, by decide⟩,⟨724824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92954_724825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92954 ⟨724825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92954
    ⟨724825, by decide⟩ (by decide) (![⟨724776, by decide⟩,⟨724800, by decide⟩,⟨724817, by decide⟩,⟨724824, by decide⟩]) unmarked_context_12_92954_724825 node_context_12_92954_724825
  intro a
  fin_cases a
  · exact context_13_371816_724776
  · exact context_13_371817_724800
  · exact context_13_371818_724817
  · exact context_13_371819_724824

theorem selected_cut_28746 : selected 8 ⟨724846, by decide⟩
    (prefixPartial 13 371820) = some ⟨13, 2, 0, 724846, 371820, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_371820_724846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371820 ⟨724846, by decide⟩ :=
  accepted_of_selected 13 371820 ⟨724846, by decide⟩ ⟨13, 2, 0, 724846, 371820, 1289, 16384⟩
    (by decide) selected_cut_28746

theorem selected_cut_28747 : selected 8 ⟨724877, by decide⟩
    (prefixPartial 13 371821) = some ⟨13, 2, 0, 724877, 371821, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_371821_724877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371821 ⟨724877, by decide⟩ :=
  accepted_of_selected 13 371821 ⟨724877, by decide⟩ ⟨13, 2, 0, 724877, 371821, 1805, 16384⟩
    (by decide) selected_cut_28747

theorem selected_cut_28748 : selected 8 ⟨724897, by decide⟩
    (prefixPartial 13 371822) = some ⟨13, 2, 0, 724897, 371822, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_371822_724897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371822 ⟨724897, by decide⟩ :=
  accepted_of_selected 13 371822 ⟨724897, by decide⟩ ⟨13, 2, 0, 724897, 371822, 1077, 16384⟩
    (by decide) selected_cut_28748

theorem selected_cut_28749 : selected 8 ⟨724902, by decide⟩
    (prefixPartial 13 371823) = some ⟨13, 2, 0, 724902, 371823, 609, 16384⟩ := by
  decide +kernel

theorem context_13_371823_724902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371823 ⟨724902, by decide⟩ :=
  accepted_of_selected 13 371823 ⟨724902, by decide⟩ ⟨13, 2, 0, 724902, 371823, 609, 16384⟩
    (by decide) selected_cut_28749

theorem unmarked_context_12_92955_724903 : frontier 9 ⟨724903, by decide⟩
    (prefixCache 12 92955) (prefixPartial 12 92955) = false := by
  decide +kernel

theorem node_context_12_92955_724903 : EJMOriginalGlobalDAGData.nodes 9 ⟨724903, by decide⟩ =
    .split (coordinate 12) (![⟨724846, by decide⟩,⟨724877, by decide⟩,⟨724897, by decide⟩,⟨724902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92955_724903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92955 ⟨724903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92955
    ⟨724903, by decide⟩ (by decide) (![⟨724846, by decide⟩,⟨724877, by decide⟩,⟨724897, by decide⟩,⟨724902, by decide⟩]) unmarked_context_12_92955_724903 node_context_12_92955_724903
  intro a
  fin_cases a
  · exact context_13_371820_724846
  · exact context_13_371821_724877
  · exact context_13_371822_724897
  · exact context_13_371823_724902

theorem unmarked_context_11_23238_724904 : frontier 10 ⟨724904, by decide⟩
    (prefixCache 11 23238) (prefixPartial 11 23238) = false := by
  decide +kernel

theorem node_context_11_23238_724904 : EJMOriginalGlobalDAGData.nodes 10 ⟨724904, by decide⟩ =
    .split (coordinate 11) (![⟨724680, by decide⟩,⟨724756, by decide⟩,⟨724825, by decide⟩,⟨724903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23238_724904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23238 ⟨724904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23238
    ⟨724904, by decide⟩ (by decide) (![⟨724680, by decide⟩,⟨724756, by decide⟩,⟨724825, by decide⟩,⟨724903, by decide⟩]) unmarked_context_11_23238_724904 node_context_11_23238_724904
  intro a
  fin_cases a
  · exact context_12_92952_724680
  · exact context_12_92953_724756
  · exact context_12_92954_724825
  · exact context_12_92955_724903

theorem selected_cut_28750 : selected 8 ⟨724923, by decide⟩
    (prefixPartial 13 371824) = some ⟨13, 2, 0, 724923, 371824, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_371824_724923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371824 ⟨724923, by decide⟩ :=
  accepted_of_selected 13 371824 ⟨724923, by decide⟩ ⟨13, 2, 0, 724923, 371824, 1361, 16384⟩
    (by decide) selected_cut_28750

theorem selected_cut_28751 : selected 8 ⟨724953, by decide⟩
    (prefixPartial 13 371825) = some ⟨13, 2, 0, 724953, 371825, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_371825_724953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371825 ⟨724953, by decide⟩ :=
  accepted_of_selected 13 371825 ⟨724953, by decide⟩ ⟨13, 2, 0, 724953, 371825, 1713, 16384⟩
    (by decide) selected_cut_28751

theorem selected_cut_28752 : selected 8 ⟨724968, by decide⟩
    (prefixPartial 13 371826) = some ⟨13, 2, 0, 724968, 371826, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_371826_724968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371826 ⟨724968, by decide⟩ :=
  accepted_of_selected 13 371826 ⟨724968, by decide⟩ ⟨13, 2, 0, 724968, 371826, 1253, 16384⟩
    (by decide) selected_cut_28752

theorem selected_cut_28753 : selected 8 ⟨724974, by decide⟩
    (prefixPartial 13 371827) = some ⟨13, 2, 0, 724974, 371827, 677, 16384⟩ := by
  decide +kernel

theorem context_13_371827_724974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371827 ⟨724974, by decide⟩ :=
  accepted_of_selected 13 371827 ⟨724974, by decide⟩ ⟨13, 2, 0, 724974, 371827, 677, 16384⟩
    (by decide) selected_cut_28753

theorem unmarked_context_12_92956_724975 : frontier 9 ⟨724975, by decide⟩
    (prefixCache 12 92956) (prefixPartial 12 92956) = false := by
  decide +kernel

theorem node_context_12_92956_724975 : EJMOriginalGlobalDAGData.nodes 9 ⟨724975, by decide⟩ =
    .split (coordinate 12) (![⟨724923, by decide⟩,⟨724953, by decide⟩,⟨724968, by decide⟩,⟨724974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92956_724975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92956 ⟨724975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92956
    ⟨724975, by decide⟩ (by decide) (![⟨724923, by decide⟩,⟨724953, by decide⟩,⟨724968, by decide⟩,⟨724974, by decide⟩]) unmarked_context_12_92956_724975 node_context_12_92956_724975
  intro a
  fin_cases a
  · exact context_13_371824_724923
  · exact context_13_371825_724953
  · exact context_13_371826_724968
  · exact context_13_371827_724974

theorem selected_cut_28754 : selected 8 ⟨725001, by decide⟩
    (prefixPartial 13 371828) = some ⟨13, 2, 0, 725001, 371828, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_371828_725001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371828 ⟨725001, by decide⟩ :=
  accepted_of_selected 13 371828 ⟨725001, by decide⟩ ⟨13, 2, 0, 725001, 371828, 1557, 16384⟩
    (by decide) selected_cut_28754

theorem selected_cut_28755 : selected 8 ⟨725021, by decide⟩
    (prefixPartial 13 371829) = some ⟨13, 2, 0, 725021, 371829, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_371829_725021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371829 ⟨725021, by decide⟩ :=
  accepted_of_selected 13 371829 ⟨725021, by decide⟩ ⟨13, 2, 0, 725021, 371829, 1453, 16384⟩
    (by decide) selected_cut_28755

theorem selected_cut_28756 : selected 8 ⟨725037, by decide⟩
    (prefixPartial 13 371830) = some ⟨13, 2, 0, 725037, 371830, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_371830_725037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371830 ⟨725037, by decide⟩ :=
  accepted_of_selected 13 371830 ⟨725037, by decide⟩ ⟨13, 2, 0, 725037, 371830, 1353, 16384⟩
    (by decide) selected_cut_28756

theorem selected_cut_28757 : selected 8 ⟨725042, by decide⟩
    (prefixPartial 13 371831) = some ⟨13, 2, 0, 725042, 371831, 653, 16384⟩ := by
  decide +kernel

theorem context_13_371831_725042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371831 ⟨725042, by decide⟩ :=
  accepted_of_selected 13 371831 ⟨725042, by decide⟩ ⟨13, 2, 0, 725042, 371831, 653, 16384⟩
    (by decide) selected_cut_28757

theorem unmarked_context_12_92957_725043 : frontier 9 ⟨725043, by decide⟩
    (prefixCache 12 92957) (prefixPartial 12 92957) = false := by
  decide +kernel

theorem node_context_12_92957_725043 : EJMOriginalGlobalDAGData.nodes 9 ⟨725043, by decide⟩ =
    .split (coordinate 12) (![⟨725001, by decide⟩,⟨725021, by decide⟩,⟨725037, by decide⟩,⟨725042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92957_725043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92957 ⟨725043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92957
    ⟨725043, by decide⟩ (by decide) (![⟨725001, by decide⟩,⟨725021, by decide⟩,⟨725037, by decide⟩,⟨725042, by decide⟩]) unmarked_context_12_92957_725043 node_context_12_92957_725043
  intro a
  fin_cases a
  · exact context_13_371828_725001
  · exact context_13_371829_725021
  · exact context_13_371830_725037
  · exact context_13_371831_725042

theorem selected_cut_28758 : selected 8 ⟨725064, by decide⟩
    (prefixPartial 13 371832) = some ⟨13, 2, 0, 725064, 371832, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_371832_725064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371832 ⟨725064, by decide⟩ :=
  accepted_of_selected 13 371832 ⟨725064, by decide⟩ ⟨13, 2, 0, 725064, 371832, 1381, 16384⟩
    (by decide) selected_cut_28758

theorem selected_cut_28759 : selected 8 ⟨725101, by decide⟩
    (prefixPartial 13 371833) = some ⟨13, 2, 0, 725101, 371833, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_371833_725101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371833 ⟨725101, by decide⟩ :=
  accepted_of_selected 13 371833 ⟨725101, by decide⟩ ⟨13, 2, 0, 725101, 371833, 1801, 16384⟩
    (by decide) selected_cut_28759

theorem selected_cut_28760 : selected 8 ⟨725116, by decide⟩
    (prefixPartial 13 371834) = some ⟨13, 2, 0, 725116, 371834, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_371834_725116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371834 ⟨725116, by decide⟩ :=
  accepted_of_selected 13 371834 ⟨725116, by decide⟩ ⟨13, 2, 0, 725116, 371834, 1225, 16384⟩
    (by decide) selected_cut_28760

theorem selected_cut_28761 : selected 8 ⟨725121, by decide⟩
    (prefixPartial 13 371835) = some ⟨13, 2, 0, 725121, 371835, 681, 16384⟩ := by
  decide +kernel

theorem context_13_371835_725121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371835 ⟨725121, by decide⟩ :=
  accepted_of_selected 13 371835 ⟨725121, by decide⟩ ⟨13, 2, 0, 725121, 371835, 681, 16384⟩
    (by decide) selected_cut_28761

theorem unmarked_context_12_92958_725122 : frontier 9 ⟨725122, by decide⟩
    (prefixCache 12 92958) (prefixPartial 12 92958) = false := by
  decide +kernel

theorem node_context_12_92958_725122 : EJMOriginalGlobalDAGData.nodes 9 ⟨725122, by decide⟩ =
    .split (coordinate 12) (![⟨725064, by decide⟩,⟨725101, by decide⟩,⟨725116, by decide⟩,⟨725121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92958_725122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92958 ⟨725122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92958
    ⟨725122, by decide⟩ (by decide) (![⟨725064, by decide⟩,⟨725101, by decide⟩,⟨725116, by decide⟩,⟨725121, by decide⟩]) unmarked_context_12_92958_725122 node_context_12_92958_725122
  intro a
  fin_cases a
  · exact context_13_371832_725064
  · exact context_13_371833_725101
  · exact context_13_371834_725116
  · exact context_13_371835_725121

theorem selected_cut_28762 : selected 8 ⟨725159, by decide⟩
    (prefixPartial 13 371836) = some ⟨13, 2, 0, 725159, 371836, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_371836_725159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371836 ⟨725159, by decide⟩ :=
  accepted_of_selected 13 371836 ⟨725159, by decide⟩ ⟨13, 2, 0, 725159, 371836, 2213, 16384⟩
    (by decide) selected_cut_28762

theorem selected_cut_28763 : selected 8 ⟨725222, by decide⟩
    (prefixPartial 13 371837) = some ⟨13, 2, 0, 725222, 371837, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_371837_725222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371837 ⟨725222, by decide⟩ :=
  accepted_of_selected 13 371837 ⟨725222, by decide⟩ ⟨13, 2, 0, 725222, 371837, 3041, 16384⟩
    (by decide) selected_cut_28763

theorem selected_cut_28764 : selected 8 ⟨725245, by decide⟩
    (prefixPartial 13 371838) = some ⟨13, 2, 0, 725245, 371838, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_371838_725245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371838 ⟨725245, by decide⟩ :=
  accepted_of_selected 13 371838 ⟨725245, by decide⟩ ⟨13, 2, 0, 725245, 371838, 1645, 16384⟩
    (by decide) selected_cut_28764

theorem selected_cut_28765 : selected 8 ⟨725251, by decide⟩
    (prefixPartial 13 371839) = some ⟨13, 2, 0, 725251, 371839, 921, 16384⟩ := by
  decide +kernel

theorem context_13_371839_725251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371839 ⟨725251, by decide⟩ :=
  accepted_of_selected 13 371839 ⟨725251, by decide⟩ ⟨13, 2, 0, 725251, 371839, 921, 16384⟩
    (by decide) selected_cut_28765

theorem unmarked_context_12_92959_725252 : frontier 9 ⟨725252, by decide⟩
    (prefixCache 12 92959) (prefixPartial 12 92959) = false := by
  decide +kernel

theorem node_context_12_92959_725252 : EJMOriginalGlobalDAGData.nodes 9 ⟨725252, by decide⟩ =
    .split (coordinate 12) (![⟨725159, by decide⟩,⟨725222, by decide⟩,⟨725245, by decide⟩,⟨725251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92959_725252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92959 ⟨725252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92959
    ⟨725252, by decide⟩ (by decide) (![⟨725159, by decide⟩,⟨725222, by decide⟩,⟨725245, by decide⟩,⟨725251, by decide⟩]) unmarked_context_12_92959_725252 node_context_12_92959_725252
  intro a
  fin_cases a
  · exact context_13_371836_725159
  · exact context_13_371837_725222
  · exact context_13_371838_725245
  · exact context_13_371839_725251

theorem unmarked_context_11_23239_725253 : frontier 10 ⟨725253, by decide⟩
    (prefixCache 11 23239) (prefixPartial 11 23239) = false := by
  decide +kernel

theorem node_context_11_23239_725253 : EJMOriginalGlobalDAGData.nodes 10 ⟨725253, by decide⟩ =
    .split (coordinate 11) (![⟨724975, by decide⟩,⟨725043, by decide⟩,⟨725122, by decide⟩,⟨725252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23239_725253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23239 ⟨725253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23239
    ⟨725253, by decide⟩ (by decide) (![⟨724975, by decide⟩,⟨725043, by decide⟩,⟨725122, by decide⟩,⟨725252, by decide⟩]) unmarked_context_11_23239_725253 node_context_11_23239_725253
  intro a
  fin_cases a
  · exact context_12_92956_724975
  · exact context_12_92957_725043
  · exact context_12_92958_725122
  · exact context_12_92959_725252

theorem unmarked_context_10_5809_725254 : frontier 11 ⟨725254, by decide⟩
    (prefixCache 10 5809) (prefixPartial 10 5809) = false := by
  decide +kernel

theorem node_context_10_5809_725254 : EJMOriginalGlobalDAGData.nodes 11 ⟨725254, by decide⟩ =
    .split (coordinate 10) (![⟨724256, by decide⟩,⟨724608, by decide⟩,⟨724904, by decide⟩,⟨725253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5809_725254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5809 ⟨725254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5809
    ⟨725254, by decide⟩ (by decide) (![⟨724256, by decide⟩,⟨724608, by decide⟩,⟨724904, by decide⟩,⟨725253, by decide⟩]) unmarked_context_10_5809_725254 node_context_10_5809_725254
  intro a
  fin_cases a
  · exact context_11_23236_724256
  · exact context_11_23237_724608
  · exact context_11_23238_724904
  · exact context_11_23239_725253

theorem selected_cut_28766 : selected 8 ⟨725283, by decide⟩
    (prefixPartial 13 371840) = some ⟨13, 2, 0, 725283, 371840, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_371840_725283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371840 ⟨725283, by decide⟩ :=
  accepted_of_selected 13 371840 ⟨725283, by decide⟩ ⟨13, 2, 0, 725283, 371840, 1341, 16384⟩
    (by decide) selected_cut_28766

theorem selected_cut_28767 : selected 8 ⟨725327, by decide⟩
    (prefixPartial 13 371841) = some ⟨13, 2, 0, 725327, 371841, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_371841_725327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371841 ⟨725327, by decide⟩ :=
  accepted_of_selected 13 371841 ⟨725327, by decide⟩ ⟨13, 2, 0, 725327, 371841, 1749, 16384⟩
    (by decide) selected_cut_28767

theorem selected_cut_28768 : selected 8 ⟨725338, by decide⟩
    (prefixPartial 13 371842) = some ⟨13, 2, 0, 725338, 371842, 837, 16384⟩ := by
  decide +kernel

theorem context_13_371842_725338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371842 ⟨725338, by decide⟩ :=
  accepted_of_selected 13 371842 ⟨725338, by decide⟩ ⟨13, 2, 0, 725338, 371842, 837, 16384⟩
    (by decide) selected_cut_28768

theorem selected_cut_28769 : selected 8 ⟨725343, by decide⟩
    (prefixPartial 13 371843) = some ⟨13, 2, 0, 725343, 371843, 709, 16384⟩ := by
  decide +kernel

theorem context_13_371843_725343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371843 ⟨725343, by decide⟩ :=
  accepted_of_selected 13 371843 ⟨725343, by decide⟩ ⟨13, 2, 0, 725343, 371843, 709, 16384⟩
    (by decide) selected_cut_28769

theorem unmarked_context_12_92960_725344 : frontier 9 ⟨725344, by decide⟩
    (prefixCache 12 92960) (prefixPartial 12 92960) = false := by
  decide +kernel

theorem node_context_12_92960_725344 : EJMOriginalGlobalDAGData.nodes 9 ⟨725344, by decide⟩ =
    .split (coordinate 12) (![⟨725283, by decide⟩,⟨725327, by decide⟩,⟨725338, by decide⟩,⟨725343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92960_725344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92960 ⟨725344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92960
    ⟨725344, by decide⟩ (by decide) (![⟨725283, by decide⟩,⟨725327, by decide⟩,⟨725338, by decide⟩,⟨725343, by decide⟩]) unmarked_context_12_92960_725344 node_context_12_92960_725344
  intro a
  fin_cases a
  · exact context_13_371840_725283
  · exact context_13_371841_725327
  · exact context_13_371842_725338
  · exact context_13_371843_725343

theorem selected_cut_28770 : selected 8 ⟨725374, by decide⟩
    (prefixPartial 13 371844) = some ⟨13, 2, 0, 725374, 371844, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_371844_725374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371844 ⟨725374, by decide⟩ :=
  accepted_of_selected 13 371844 ⟨725374, by decide⟩ ⟨13, 2, 0, 725374, 371844, 1349, 16384⟩
    (by decide) selected_cut_28770

theorem selected_cut_28771 : selected 8 ⟨725409, by decide⟩
    (prefixPartial 13 371845) = some ⟨13, 2, 0, 725409, 371845, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_371845_725409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371845 ⟨725409, by decide⟩ :=
  accepted_of_selected 13 371845 ⟨725409, by decide⟩ ⟨13, 2, 0, 725409, 371845, 1501, 16384⟩
    (by decide) selected_cut_28771

theorem selected_cut_28772 : selected 8 ⟨725419, by decide⟩
    (prefixPartial 13 371846) = some ⟨13, 2, 0, 725419, 371846, 905, 16384⟩ := by
  decide +kernel

theorem context_13_371846_725419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371846 ⟨725419, by decide⟩ :=
  accepted_of_selected 13 371846 ⟨725419, by decide⟩ ⟨13, 2, 0, 725419, 371846, 905, 16384⟩
    (by decide) selected_cut_28772

theorem selected_cut_28773 : selected 8 ⟨725423, by decide⟩
    (prefixPartial 13 371847) = some ⟨13, 2, 0, 725423, 371847, 585, 16384⟩ := by
  decide +kernel

theorem context_13_371847_725423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371847 ⟨725423, by decide⟩ :=
  accepted_of_selected 13 371847 ⟨725423, by decide⟩ ⟨13, 2, 0, 725423, 371847, 585, 16384⟩
    (by decide) selected_cut_28773

theorem unmarked_context_12_92961_725424 : frontier 9 ⟨725424, by decide⟩
    (prefixCache 12 92961) (prefixPartial 12 92961) = false := by
  decide +kernel

theorem node_context_12_92961_725424 : EJMOriginalGlobalDAGData.nodes 9 ⟨725424, by decide⟩ =
    .split (coordinate 12) (![⟨725374, by decide⟩,⟨725409, by decide⟩,⟨725419, by decide⟩,⟨725423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92961_725424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92961 ⟨725424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92961
    ⟨725424, by decide⟩ (by decide) (![⟨725374, by decide⟩,⟨725409, by decide⟩,⟨725419, by decide⟩,⟨725423, by decide⟩]) unmarked_context_12_92961_725424 node_context_12_92961_725424
  intro a
  fin_cases a
  · exact context_13_371844_725374
  · exact context_13_371845_725409
  · exact context_13_371846_725419
  · exact context_13_371847_725423

theorem selected_cut_28774 : selected 8 ⟨725445, by decide⟩
    (prefixPartial 13 371848) = some ⟨13, 2, 0, 725445, 371848, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_371848_725445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371848 ⟨725445, by decide⟩ :=
  accepted_of_selected 13 371848 ⟨725445, by decide⟩ ⟨13, 2, 0, 725445, 371848, 1129, 16384⟩
    (by decide) selected_cut_28774

theorem selected_cut_28775 : selected 8 ⟨725484, by decide⟩
    (prefixPartial 13 371849) = some ⟨13, 2, 0, 725484, 371849, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_371849_725484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371849 ⟨725484, by decide⟩ :=
  accepted_of_selected 13 371849 ⟨725484, by decide⟩ ⟨13, 2, 0, 725484, 371849, 1705, 16384⟩
    (by decide) selected_cut_28775

theorem selected_cut_28776 : selected 8 ⟨725499, by decide⟩
    (prefixPartial 13 371850) = some ⟨13, 2, 0, 725499, 371850, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_371850_725499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371850 ⟨725499, by decide⟩ :=
  accepted_of_selected 13 371850 ⟨725499, by decide⟩ ⟨13, 2, 0, 725499, 371850, 1037, 16384⟩
    (by decide) selected_cut_28776

theorem selected_cut_28777 : selected 8 ⟨725503, by decide⟩
    (prefixPartial 13 371851) = some ⟨13, 2, 0, 725503, 371851, 613, 16384⟩ := by
  decide +kernel

theorem context_13_371851_725503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371851 ⟨725503, by decide⟩ :=
  accepted_of_selected 13 371851 ⟨725503, by decide⟩ ⟨13, 2, 0, 725503, 371851, 613, 16384⟩
    (by decide) selected_cut_28777

theorem unmarked_context_12_92962_725504 : frontier 9 ⟨725504, by decide⟩
    (prefixCache 12 92962) (prefixPartial 12 92962) = false := by
  decide +kernel

theorem node_context_12_92962_725504 : EJMOriginalGlobalDAGData.nodes 9 ⟨725504, by decide⟩ =
    .split (coordinate 12) (![⟨725445, by decide⟩,⟨725484, by decide⟩,⟨725499, by decide⟩,⟨725503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92962_725504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92962 ⟨725504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92962
    ⟨725504, by decide⟩ (by decide) (![⟨725445, by decide⟩,⟨725484, by decide⟩,⟨725499, by decide⟩,⟨725503, by decide⟩]) unmarked_context_12_92962_725504 node_context_12_92962_725504
  intro a
  fin_cases a
  · exact context_13_371848_725445
  · exact context_13_371849_725484
  · exact context_13_371850_725499
  · exact context_13_371851_725503

theorem selected_cut_28778 : selected 9 ⟨725572, by decide⟩
    (prefixPartial 12 92963) = some ⟨12, 2, 0, 725572, 92963, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_92963_725572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92963 ⟨725572, by decide⟩ :=
  accepted_of_selected 12 92963 ⟨725572, by decide⟩ ⟨12, 2, 0, 725572, 92963, 3977, 65536⟩
    (by decide) selected_cut_28778

theorem unmarked_context_11_23240_725573 : frontier 10 ⟨725573, by decide⟩
    (prefixCache 11 23240) (prefixPartial 11 23240) = false := by
  decide +kernel

theorem node_context_11_23240_725573 : EJMOriginalGlobalDAGData.nodes 10 ⟨725573, by decide⟩ =
    .split (coordinate 11) (![⟨725344, by decide⟩,⟨725424, by decide⟩,⟨725504, by decide⟩,⟨725572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23240_725573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23240 ⟨725573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23240
    ⟨725573, by decide⟩ (by decide) (![⟨725344, by decide⟩,⟨725424, by decide⟩,⟨725504, by decide⟩,⟨725572, by decide⟩]) unmarked_context_11_23240_725573 node_context_11_23240_725573
  intro a
  fin_cases a
  · exact context_12_92960_725344
  · exact context_12_92961_725424
  · exact context_12_92962_725504
  · exact context_12_92963_725572

theorem selected_cut_28779 : selected 8 ⟨725602, by decide⟩
    (prefixPartial 13 371856) = some ⟨13, 2, 0, 725602, 371856, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_371856_725602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371856 ⟨725602, by decide⟩ :=
  accepted_of_selected 13 371856 ⟨725602, by decide⟩ ⟨13, 2, 0, 725602, 371856, 1053, 16384⟩
    (by decide) selected_cut_28779

theorem selected_cut_28780 : selected 8 ⟨725641, by decide⟩
    (prefixPartial 13 371857) = some ⟨13, 2, 0, 725641, 371857, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_371857_725641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371857 ⟨725641, by decide⟩ :=
  accepted_of_selected 13 371857 ⟨725641, by decide⟩ ⟨13, 2, 0, 725641, 371857, 1729, 16384⟩
    (by decide) selected_cut_28780

theorem selected_cut_28781 : selected 8 ⟨725653, by decide⟩
    (prefixPartial 13 371858) = some ⟨13, 2, 0, 725653, 371858, 993, 16384⟩ := by
  decide +kernel

theorem context_13_371858_725653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371858 ⟨725653, by decide⟩ :=
  accepted_of_selected 13 371858 ⟨725653, by decide⟩ ⟨13, 2, 0, 725653, 371858, 993, 16384⟩
    (by decide) selected_cut_28781

theorem selected_cut_28782 : selected 8 ⟨725658, by decide⟩
    (prefixPartial 13 371859) = some ⟨13, 2, 0, 725658, 371859, 841, 16384⟩ := by
  decide +kernel

theorem context_13_371859_725658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371859 ⟨725658, by decide⟩ :=
  accepted_of_selected 13 371859 ⟨725658, by decide⟩ ⟨13, 2, 0, 725658, 371859, 841, 16384⟩
    (by decide) selected_cut_28782

theorem unmarked_context_12_92964_725659 : frontier 9 ⟨725659, by decide⟩
    (prefixCache 12 92964) (prefixPartial 12 92964) = false := by
  decide +kernel

theorem node_context_12_92964_725659 : EJMOriginalGlobalDAGData.nodes 9 ⟨725659, by decide⟩ =
    .split (coordinate 12) (![⟨725602, by decide⟩,⟨725641, by decide⟩,⟨725653, by decide⟩,⟨725658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92964_725659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92964 ⟨725659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92964
    ⟨725659, by decide⟩ (by decide) (![⟨725602, by decide⟩,⟨725641, by decide⟩,⟨725653, by decide⟩,⟨725658, by decide⟩]) unmarked_context_12_92964_725659 node_context_12_92964_725659
  intro a
  fin_cases a
  · exact context_13_371856_725602
  · exact context_13_371857_725641
  · exact context_13_371858_725653
  · exact context_13_371859_725658

theorem selected_cut_28783 : selected 9 ⟨725723, by decide⟩
    (prefixPartial 12 92965) = some ⟨12, 2, 0, 725723, 92965, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_92965_725723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92965 ⟨725723, by decide⟩ :=
  accepted_of_selected 12 92965 ⟨725723, by decide⟩ ⟨12, 2, 0, 725723, 92965, 3913, 65536⟩
    (by decide) selected_cut_28783

theorem selected_cut_28784 : selected 8 ⟨725742, by decide⟩
    (prefixPartial 13 371864) = some ⟨13, 2, 0, 725742, 371864, 973, 16384⟩ := by
  decide +kernel

theorem context_13_371864_725742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371864 ⟨725742, by decide⟩ :=
  accepted_of_selected 13 371864 ⟨725742, by decide⟩ ⟨13, 2, 0, 725742, 371864, 973, 16384⟩
    (by decide) selected_cut_28784

theorem selected_cut_28785 : selected 8 ⟨725774, by decide⟩
    (prefixPartial 13 371865) = some ⟨13, 2, 0, 725774, 371865, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_371865_725774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371865 ⟨725774, by decide⟩ :=
  accepted_of_selected 13 371865 ⟨725774, by decide⟩ ⟨13, 2, 0, 725774, 371865, 1553, 16384⟩
    (by decide) selected_cut_28785

theorem selected_cut_28786 : selected 8 ⟨725786, by decide⟩
    (prefixPartial 13 371866) = some ⟨13, 2, 0, 725786, 371866, 973, 16384⟩ := by
  decide +kernel

theorem context_13_371866_725786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371866 ⟨725786, by decide⟩ :=
  accepted_of_selected 13 371866 ⟨725786, by decide⟩ ⟨13, 2, 0, 725786, 371866, 973, 16384⟩
    (by decide) selected_cut_28786

theorem selected_cut_28787 : selected 8 ⟨725792, by decide⟩
    (prefixPartial 13 371867) = some ⟨13, 2, 0, 725792, 371867, 785, 16384⟩ := by
  decide +kernel

theorem context_13_371867_725792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371867 ⟨725792, by decide⟩ :=
  accepted_of_selected 13 371867 ⟨725792, by decide⟩ ⟨13, 2, 0, 725792, 371867, 785, 16384⟩
    (by decide) selected_cut_28787

theorem unmarked_context_12_92966_725793 : frontier 9 ⟨725793, by decide⟩
    (prefixCache 12 92966) (prefixPartial 12 92966) = false := by
  decide +kernel

theorem node_context_12_92966_725793 : EJMOriginalGlobalDAGData.nodes 9 ⟨725793, by decide⟩ =
    .split (coordinate 12) (![⟨725742, by decide⟩,⟨725774, by decide⟩,⟨725786, by decide⟩,⟨725792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92966_725793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92966 ⟨725793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92966
    ⟨725793, by decide⟩ (by decide) (![⟨725742, by decide⟩,⟨725774, by decide⟩,⟨725786, by decide⟩,⟨725792, by decide⟩]) unmarked_context_12_92966_725793 node_context_12_92966_725793
  intro a
  fin_cases a
  · exact context_13_371864_725742
  · exact context_13_371865_725774
  · exact context_13_371866_725786
  · exact context_13_371867_725792

theorem selected_cut_28788 : selected 9 ⟨725860, by decide⟩
    (prefixPartial 12 92967) = some ⟨12, 2, 0, 725860, 92967, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_92967_725860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92967 ⟨725860, by decide⟩ :=
  accepted_of_selected 12 92967 ⟨725860, by decide⟩ ⟨12, 2, 0, 725860, 92967, 3845, 65536⟩
    (by decide) selected_cut_28788

theorem unmarked_context_11_23241_725861 : frontier 10 ⟨725861, by decide⟩
    (prefixCache 11 23241) (prefixPartial 11 23241) = false := by
  decide +kernel

theorem node_context_11_23241_725861 : EJMOriginalGlobalDAGData.nodes 10 ⟨725861, by decide⟩ =
    .split (coordinate 11) (![⟨725659, by decide⟩,⟨725723, by decide⟩,⟨725793, by decide⟩,⟨725860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23241_725861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23241 ⟨725861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23241
    ⟨725861, by decide⟩ (by decide) (![⟨725659, by decide⟩,⟨725723, by decide⟩,⟨725793, by decide⟩,⟨725860, by decide⟩]) unmarked_context_11_23241_725861 node_context_11_23241_725861
  intro a
  fin_cases a
  · exact context_12_92964_725659
  · exact context_12_92965_725723
  · exact context_12_92966_725793
  · exact context_12_92967_725860

theorem selected_cut_28789 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 92968) = some ⟨12, 1, 0, 224365, 92968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92968_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92968 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 92968 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 92968, 1, 65536⟩
    (by decide) selected_cut_28789

theorem selected_cut_28790 : selected 8 ⟨725885, by decide⟩
    (prefixPartial 13 371876) = some ⟨13, 2, 0, 725885, 371876, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_371876_725885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371876 ⟨725885, by decide⟩ :=
  accepted_of_selected 13 371876 ⟨725885, by decide⟩ ⟨13, 2, 0, 725885, 371876, 1265, 16384⟩
    (by decide) selected_cut_28790

theorem selected_cut_28791 : selected 8 ⟨725923, by decide⟩
    (prefixPartial 13 371877) = some ⟨13, 2, 0, 725923, 371877, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_371877_725923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371877 ⟨725923, by decide⟩ :=
  accepted_of_selected 13 371877 ⟨725923, by decide⟩ ⟨13, 2, 0, 725923, 371877, 1653, 16384⟩
    (by decide) selected_cut_28791

theorem selected_cut_28792 : selected 8 ⟨725936, by decide⟩
    (prefixPartial 13 371878) = some ⟨13, 2, 0, 725936, 371878, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_371878_725936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371878 ⟨725936, by decide⟩ :=
  accepted_of_selected 13 371878 ⟨725936, by decide⟩ ⟨13, 2, 0, 725936, 371878, 1237, 16384⟩
    (by decide) selected_cut_28792

theorem selected_cut_28793 : selected 8 ⟨725944, by decide⟩
    (prefixPartial 13 371879) = some ⟨13, 2, 0, 725944, 371879, 889, 16384⟩ := by
  decide +kernel

theorem context_13_371879_725944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371879 ⟨725944, by decide⟩ :=
  accepted_of_selected 13 371879 ⟨725944, by decide⟩ ⟨13, 2, 0, 725944, 371879, 889, 16384⟩
    (by decide) selected_cut_28793

theorem unmarked_context_12_92969_725945 : frontier 9 ⟨725945, by decide⟩
    (prefixCache 12 92969) (prefixPartial 12 92969) = false := by
  decide +kernel

theorem node_context_12_92969_725945 : EJMOriginalGlobalDAGData.nodes 9 ⟨725945, by decide⟩ =
    .split (coordinate 12) (![⟨725885, by decide⟩,⟨725923, by decide⟩,⟨725936, by decide⟩,⟨725944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92969_725945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92969 ⟨725945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92969
    ⟨725945, by decide⟩ (by decide) (![⟨725885, by decide⟩,⟨725923, by decide⟩,⟨725936, by decide⟩,⟨725944, by decide⟩]) unmarked_context_12_92969_725945 node_context_12_92969_725945
  intro a
  fin_cases a
  · exact context_13_371876_725885
  · exact context_13_371877_725923
  · exact context_13_371878_725936
  · exact context_13_371879_725944

theorem selected_cut_28794 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 92970) = some ⟨12, 1, 0, 224365, 92970, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92970_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92970 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 92970 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 92970, 1, 65536⟩
    (by decide) selected_cut_28794

theorem selected_cut_28795 : selected 9 ⟨726083, by decide⟩
    (prefixPartial 12 92971) = some ⟨12, 2, 0, 726083, 92971, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_92971_726083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92971 ⟨726083, by decide⟩ :=
  accepted_of_selected 12 92971 ⟨726083, by decide⟩ ⟨12, 2, 0, 726083, 92971, 2041, 65536⟩
    (by decide) selected_cut_28795

theorem unmarked_context_11_23242_726084 : frontier 10 ⟨726084, by decide⟩
    (prefixCache 11 23242) (prefixPartial 11 23242) = false := by
  decide +kernel

theorem node_context_11_23242_726084 : EJMOriginalGlobalDAGData.nodes 10 ⟨726084, by decide⟩ =
    .split (coordinate 11) (![⟨224365, by decide⟩,⟨725945, by decide⟩,⟨224365, by decide⟩,⟨726083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23242_726084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23242 ⟨726084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23242
    ⟨726084, by decide⟩ (by decide) (![⟨224365, by decide⟩,⟨725945, by decide⟩,⟨224365, by decide⟩,⟨726083, by decide⟩]) unmarked_context_11_23242_726084 node_context_11_23242_726084
  intro a
  fin_cases a
  · exact context_12_92968_224365
  · exact context_12_92969_725945
  · exact context_12_92970_224365
  · exact context_12_92971_726083

theorem selected_cut_28796 : selected 9 ⟨726140, by decide⟩
    (prefixPartial 12 92972) = some ⟨12, 2, 0, 726140, 92972, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_92972_726140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92972 ⟨726140, by decide⟩ :=
  accepted_of_selected 12 92972 ⟨726140, by decide⟩ ⟨12, 2, 0, 726140, 92972, 3825, 65536⟩
    (by decide) selected_cut_28796

theorem selected_cut_28797 : selected 9 ⟨726198, by decide⟩
    (prefixPartial 12 92973) = some ⟨12, 2, 0, 726198, 92973, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_92973_726198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92973 ⟨726198, by decide⟩ :=
  accepted_of_selected 12 92973 ⟨726198, by decide⟩ ⟨12, 2, 0, 726198, 92973, 3557, 65536⟩
    (by decide) selected_cut_28797

theorem selected_cut_28798 : selected 9 ⟨726250, by decide⟩
    (prefixPartial 12 92974) = some ⟨12, 2, 0, 726250, 92974, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_92974_726250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92974 ⟨726250, by decide⟩ :=
  accepted_of_selected 12 92974 ⟨726250, by decide⟩ ⟨12, 2, 0, 726250, 92974, 3629, 65536⟩
    (by decide) selected_cut_28798

theorem selected_cut_28799 : selected 8 ⟨726268, by decide⟩
    (prefixPartial 13 371900) = some ⟨13, 2, 0, 726268, 371900, 929, 16384⟩ := by
  decide +kernel

theorem context_13_371900_726268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371900 ⟨726268, by decide⟩ :=
  accepted_of_selected 13 371900 ⟨726268, by decide⟩ ⟨13, 2, 0, 726268, 371900, 929, 16384⟩
    (by decide) selected_cut_28799

theorem selected_cut_28800 : selected 8 ⟨726314, by decide⟩
    (prefixPartial 13 371901) = some ⟨13, 2, 0, 726314, 371901, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_371901_726314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371901 ⟨726314, by decide⟩ :=
  accepted_of_selected 13 371901 ⟨726314, by decide⟩ ⟨13, 2, 0, 726314, 371901, 1885, 16384⟩
    (by decide) selected_cut_28800

theorem selected_cut_28801 : selected 8 ⟨726331, by decide⟩
    (prefixPartial 13 371902) = some ⟨13, 2, 0, 726331, 371902, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_371902_726331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371902 ⟨726331, by decide⟩ :=
  accepted_of_selected 13 371902 ⟨726331, by decide⟩ ⟨13, 2, 0, 726331, 371902, 1569, 16384⟩
    (by decide) selected_cut_28801

theorem selected_cut_28802 : selected 8 ⟨726338, by decide⟩
    (prefixPartial 13 371903) = some ⟨13, 2, 0, 726338, 371903, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_371903_726338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371903 ⟨726338, by decide⟩ :=
  accepted_of_selected 13 371903 ⟨726338, by decide⟩ ⟨13, 2, 0, 726338, 371903, 1005, 16384⟩
    (by decide) selected_cut_28802

theorem unmarked_context_12_92975_726339 : frontier 9 ⟨726339, by decide⟩
    (prefixCache 12 92975) (prefixPartial 12 92975) = false := by
  decide +kernel

theorem node_context_12_92975_726339 : EJMOriginalGlobalDAGData.nodes 9 ⟨726339, by decide⟩ =
    .split (coordinate 12) (![⟨726268, by decide⟩,⟨726314, by decide⟩,⟨726331, by decide⟩,⟨726338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92975_726339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92975 ⟨726339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92975
    ⟨726339, by decide⟩ (by decide) (![⟨726268, by decide⟩,⟨726314, by decide⟩,⟨726331, by decide⟩,⟨726338, by decide⟩]) unmarked_context_12_92975_726339 node_context_12_92975_726339
  intro a
  fin_cases a
  · exact context_13_371900_726268
  · exact context_13_371901_726314
  · exact context_13_371902_726331
  · exact context_13_371903_726338

theorem unmarked_context_11_23243_726340 : frontier 10 ⟨726340, by decide⟩
    (prefixCache 11 23243) (prefixPartial 11 23243) = false := by
  decide +kernel

theorem node_context_11_23243_726340 : EJMOriginalGlobalDAGData.nodes 10 ⟨726340, by decide⟩ =
    .split (coordinate 11) (![⟨726140, by decide⟩,⟨726198, by decide⟩,⟨726250, by decide⟩,⟨726339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23243_726340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23243 ⟨726340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23243
    ⟨726340, by decide⟩ (by decide) (![⟨726140, by decide⟩,⟨726198, by decide⟩,⟨726250, by decide⟩,⟨726339, by decide⟩]) unmarked_context_11_23243_726340 node_context_11_23243_726340
  intro a
  fin_cases a
  · exact context_12_92972_726140
  · exact context_12_92973_726198
  · exact context_12_92974_726250
  · exact context_12_92975_726339

theorem unmarked_context_10_5810_726341 : frontier 11 ⟨726341, by decide⟩
    (prefixCache 10 5810) (prefixPartial 10 5810) = false := by
  decide +kernel

theorem node_context_10_5810_726341 : EJMOriginalGlobalDAGData.nodes 11 ⟨726341, by decide⟩ =
    .split (coordinate 10) (![⟨725573, by decide⟩,⟨725861, by decide⟩,⟨726084, by decide⟩,⟨726340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5810_726341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5810 ⟨726341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5810
    ⟨726341, by decide⟩ (by decide) (![⟨725573, by decide⟩,⟨725861, by decide⟩,⟨726084, by decide⟩,⟨726340, by decide⟩]) unmarked_context_10_5810_726341 node_context_10_5810_726341
  intro a
  fin_cases a
  · exact context_11_23240_725573
  · exact context_11_23241_725861
  · exact context_11_23242_726084
  · exact context_11_23243_726340

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
