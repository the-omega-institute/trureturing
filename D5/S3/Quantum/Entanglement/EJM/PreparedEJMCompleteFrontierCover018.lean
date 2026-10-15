/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover017
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_01731 : selected 8 ⟨59287, by decide⟩
    (prefixPartial 13 18810) = some ⟨13, 2, 0, 59287, 18810, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_18810_59287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18810 ⟨59287, by decide⟩ :=
  accepted_of_selected 13 18810 ⟨59287, by decide⟩ ⟨13, 2, 0, 59287, 18810, 2497, 16384⟩
    (by decide) selected_cut_01731

theorem selected_cut_01732 : selected 8 ⟨59311, by decide⟩
    (prefixPartial 13 18811) = some ⟨13, 2, 0, 59311, 18811, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_18811_59311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18811 ⟨59311, by decide⟩ :=
  accepted_of_selected 13 18811 ⟨59311, by decide⟩ ⟨13, 2, 0, 59311, 18811, 1333, 16384⟩
    (by decide) selected_cut_01732

theorem unmarked_context_12_4702_59312 : frontier 9 ⟨59312, by decide⟩
    (prefixCache 12 4702) (prefixPartial 12 4702) = false := by
  decide +kernel

theorem node_context_12_4702_59312 : EJMOriginalGlobalDAGData.nodes 9 ⟨59312, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59248, by decide⟩,⟨59287, by decide⟩,⟨59311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4702_59312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4702 ⟨59312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4702
    ⟨59312, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59248, by decide⟩,⟨59287, by decide⟩,⟨59311, by decide⟩]) unmarked_context_12_4702_59312 node_context_12_4702_59312
  intro a
  fin_cases a
  · exact context_13_18808_3444
  · exact context_13_18809_59248
  · exact context_13_18810_59287
  · exact context_13_18811_59311

theorem selected_cut_01733 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18812) = some ⟨13, 1, 0, 3444, 18812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18812, 1, 16384⟩
    (by decide) selected_cut_01733

theorem selected_cut_01734 : selected 8 ⟨59336, by decide⟩
    (prefixPartial 13 18813) = some ⟨13, 2, 0, 59336, 18813, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_18813_59336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18813 ⟨59336, by decide⟩ :=
  accepted_of_selected 13 18813 ⟨59336, by decide⟩ ⟨13, 2, 0, 59336, 18813, 1661, 16384⟩
    (by decide) selected_cut_01734

theorem selected_cut_01735 : selected 8 ⟨59361, by decide⟩
    (prefixPartial 13 18814) = some ⟨13, 2, 0, 59361, 18814, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_18814_59361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18814 ⟨59361, by decide⟩ :=
  accepted_of_selected 13 18814 ⟨59361, by decide⟩ ⟨13, 2, 0, 59361, 18814, 2481, 16384⟩
    (by decide) selected_cut_01735

theorem selected_cut_01736 : selected 8 ⟨59386, by decide⟩
    (prefixPartial 13 18815) = some ⟨13, 2, 0, 59386, 18815, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_18815_59386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18815 ⟨59386, by decide⟩ :=
  accepted_of_selected 13 18815 ⟨59386, by decide⟩ ⟨13, 2, 0, 59386, 18815, 1373, 16384⟩
    (by decide) selected_cut_01736

theorem unmarked_context_12_4703_59387 : frontier 9 ⟨59387, by decide⟩
    (prefixCache 12 4703) (prefixPartial 12 4703) = false := by
  decide +kernel

theorem node_context_12_4703_59387 : EJMOriginalGlobalDAGData.nodes 9 ⟨59387, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59336, by decide⟩,⟨59361, by decide⟩,⟨59386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4703_59387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4703 ⟨59387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4703
    ⟨59387, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59336, by decide⟩,⟨59361, by decide⟩,⟨59386, by decide⟩]) unmarked_context_12_4703_59387 node_context_12_4703_59387
  intro a
  fin_cases a
  · exact context_13_18812_3444
  · exact context_13_18813_59336
  · exact context_13_18814_59361
  · exact context_13_18815_59386

theorem unmarked_context_11_1175_59388 : frontier 10 ⟨59388, by decide⟩
    (prefixCache 11 1175) (prefixPartial 11 1175) = false := by
  decide +kernel

theorem node_context_11_1175_59388 : EJMOriginalGlobalDAGData.nodes 10 ⟨59388, by decide⟩ =
    .split (coordinate 11) (![⟨59144, by decide⟩,⟨59229, by decide⟩,⟨59312, by decide⟩,⟨59387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1175_59388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1175 ⟨59388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1175
    ⟨59388, by decide⟩ (by decide) (![⟨59144, by decide⟩,⟨59229, by decide⟩,⟨59312, by decide⟩,⟨59387, by decide⟩]) unmarked_context_11_1175_59388 node_context_11_1175_59388
  intro a
  fin_cases a
  · exact context_12_4700_59144
  · exact context_12_4701_59229
  · exact context_12_4702_59312
  · exact context_12_4703_59387

theorem unmarked_context_10_293_59389 : frontier 11 ⟨59389, by decide⟩
    (prefixCache 10 293) (prefixPartial 10 293) = false := by
  decide +kernel

theorem node_context_10_293_59389 : EJMOriginalGlobalDAGData.nodes 11 ⟨59389, by decide⟩ =
    .split (coordinate 10) (![⟨58455, by decide⟩,⟨58721, by decide⟩,⟨59088, by decide⟩,⟨59388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_293_59389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 293 ⟨59389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 293
    ⟨59389, by decide⟩ (by decide) (![⟨58455, by decide⟩,⟨58721, by decide⟩,⟨59088, by decide⟩,⟨59388, by decide⟩]) unmarked_context_10_293_59389 node_context_10_293_59389
  intro a
  fin_cases a
  · exact context_11_1172_58455
  · exact context_11_1173_58721
  · exact context_11_1174_59088
  · exact context_11_1175_59388

theorem selected_cut_01737 : selected 9 ⟨59435, by decide⟩
    (prefixPartial 12 4704) = some ⟨12, 2, 0, 59435, 4704, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_4704_59435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4704 ⟨59435, by decide⟩ :=
  accepted_of_selected 12 4704 ⟨59435, by decide⟩ ⟨12, 2, 0, 59435, 4704, 3601, 65536⟩
    (by decide) selected_cut_01737

theorem selected_cut_01738 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18820) = some ⟨13, 1, 0, 3444, 18820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18820, 1, 16384⟩
    (by decide) selected_cut_01738

theorem selected_cut_01739 : selected 8 ⟨59450, by decide⟩
    (prefixPartial 13 18821) = some ⟨13, 2, 0, 59450, 18821, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_18821_59450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18821 ⟨59450, by decide⟩ :=
  accepted_of_selected 13 18821 ⟨59450, by decide⟩ ⟨13, 2, 0, 59450, 18821, 1609, 16384⟩
    (by decide) selected_cut_01739

theorem selected_cut_01740 : selected 8 ⟨59474, by decide⟩
    (prefixPartial 13 18822) = some ⟨13, 2, 0, 59474, 18822, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_18822_59474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18822 ⟨59474, by decide⟩ :=
  accepted_of_selected 13 18822 ⟨59474, by decide⟩ ⟨13, 2, 0, 59474, 18822, 2053, 16384⟩
    (by decide) selected_cut_01740

theorem selected_cut_01741 : selected 8 ⟨59485, by decide⟩
    (prefixPartial 13 18823) = some ⟨13, 2, 0, 59485, 18823, 989, 16384⟩ := by
  decide +kernel

theorem context_13_18823_59485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18823 ⟨59485, by decide⟩ :=
  accepted_of_selected 13 18823 ⟨59485, by decide⟩ ⟨13, 2, 0, 59485, 18823, 989, 16384⟩
    (by decide) selected_cut_01741

theorem unmarked_context_12_4705_59486 : frontier 9 ⟨59486, by decide⟩
    (prefixCache 12 4705) (prefixPartial 12 4705) = false := by
  decide +kernel

theorem node_context_12_4705_59486 : EJMOriginalGlobalDAGData.nodes 9 ⟨59486, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59450, by decide⟩,⟨59474, by decide⟩,⟨59485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4705_59486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4705 ⟨59486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4705
    ⟨59486, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59450, by decide⟩,⟨59474, by decide⟩,⟨59485, by decide⟩]) unmarked_context_12_4705_59486 node_context_12_4705_59486
  intro a
  fin_cases a
  · exact context_13_18820_3444
  · exact context_13_18821_59450
  · exact context_13_18822_59474
  · exact context_13_18823_59485

theorem selected_cut_01742 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18824) = some ⟨13, 1, 0, 3444, 18824, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18824_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18824 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18824 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18824, 1, 16384⟩
    (by decide) selected_cut_01742

theorem selected_cut_01743 : selected 8 ⟨59509, by decide⟩
    (prefixPartial 13 18825) = some ⟨13, 2, 0, 59509, 18825, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_18825_59509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18825 ⟨59509, by decide⟩ :=
  accepted_of_selected 13 18825 ⟨59509, by decide⟩ ⟨13, 2, 0, 59509, 18825, 1549, 16384⟩
    (by decide) selected_cut_01743

theorem selected_cut_01744 : selected 8 ⟨59536, by decide⟩
    (prefixPartial 13 18826) = some ⟨13, 2, 0, 59536, 18826, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_18826_59536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18826 ⟨59536, by decide⟩ :=
  accepted_of_selected 13 18826 ⟨59536, by decide⟩ ⟨13, 2, 0, 59536, 18826, 2017, 16384⟩
    (by decide) selected_cut_01744

theorem selected_cut_01745 : selected 8 ⟨59551, by decide⟩
    (prefixPartial 13 18827) = some ⟨13, 2, 0, 59551, 18827, 961, 16384⟩ := by
  decide +kernel

theorem context_13_18827_59551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18827 ⟨59551, by decide⟩ :=
  accepted_of_selected 13 18827 ⟨59551, by decide⟩ ⟨13, 2, 0, 59551, 18827, 961, 16384⟩
    (by decide) selected_cut_01745

theorem unmarked_context_12_4706_59552 : frontier 9 ⟨59552, by decide⟩
    (prefixCache 12 4706) (prefixPartial 12 4706) = false := by
  decide +kernel

theorem node_context_12_4706_59552 : EJMOriginalGlobalDAGData.nodes 9 ⟨59552, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59509, by decide⟩,⟨59536, by decide⟩,⟨59551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4706_59552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4706 ⟨59552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4706
    ⟨59552, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59509, by decide⟩,⟨59536, by decide⟩,⟨59551, by decide⟩]) unmarked_context_12_4706_59552 node_context_12_4706_59552
  intro a
  fin_cases a
  · exact context_13_18824_3444
  · exact context_13_18825_59509
  · exact context_13_18826_59536
  · exact context_13_18827_59551

theorem selected_cut_01746 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18828) = some ⟨13, 1, 0, 3444, 18828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18828, 1, 16384⟩
    (by decide) selected_cut_01746

theorem selected_cut_01747 : selected 8 ⟨59576, by decide⟩
    (prefixPartial 13 18829) = some ⟨13, 2, 0, 59576, 18829, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_18829_59576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18829 ⟨59576, by decide⟩ :=
  accepted_of_selected 13 18829 ⟨59576, by decide⟩ ⟨13, 2, 0, 59576, 18829, 1653, 16384⟩
    (by decide) selected_cut_01747

theorem selected_cut_01748 : selected 8 ⟨59601, by decide⟩
    (prefixPartial 13 18830) = some ⟨13, 2, 0, 59601, 18830, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_18830_59601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18830 ⟨59601, by decide⟩ :=
  accepted_of_selected 13 18830 ⟨59601, by decide⟩ ⟨13, 2, 0, 59601, 18830, 2101, 16384⟩
    (by decide) selected_cut_01748

theorem selected_cut_01749 : selected 8 ⟨59615, by decide⟩
    (prefixPartial 13 18831) = some ⟨13, 2, 0, 59615, 18831, 949, 16384⟩ := by
  decide +kernel

theorem context_13_18831_59615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18831 ⟨59615, by decide⟩ :=
  accepted_of_selected 13 18831 ⟨59615, by decide⟩ ⟨13, 2, 0, 59615, 18831, 949, 16384⟩
    (by decide) selected_cut_01749

theorem unmarked_context_12_4707_59616 : frontier 9 ⟨59616, by decide⟩
    (prefixCache 12 4707) (prefixPartial 12 4707) = false := by
  decide +kernel

theorem node_context_12_4707_59616 : EJMOriginalGlobalDAGData.nodes 9 ⟨59616, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59576, by decide⟩,⟨59601, by decide⟩,⟨59615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4707_59616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4707 ⟨59616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4707
    ⟨59616, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59576, by decide⟩,⟨59601, by decide⟩,⟨59615, by decide⟩]) unmarked_context_12_4707_59616 node_context_12_4707_59616
  intro a
  fin_cases a
  · exact context_13_18828_3444
  · exact context_13_18829_59576
  · exact context_13_18830_59601
  · exact context_13_18831_59615

theorem unmarked_context_11_1176_59617 : frontier 10 ⟨59617, by decide⟩
    (prefixCache 11 1176) (prefixPartial 11 1176) = false := by
  decide +kernel

theorem node_context_11_1176_59617 : EJMOriginalGlobalDAGData.nodes 10 ⟨59617, by decide⟩ =
    .split (coordinate 11) (![⟨59435, by decide⟩,⟨59486, by decide⟩,⟨59552, by decide⟩,⟨59616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1176_59617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1176 ⟨59617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1176
    ⟨59617, by decide⟩ (by decide) (![⟨59435, by decide⟩,⟨59486, by decide⟩,⟨59552, by decide⟩,⟨59616, by decide⟩]) unmarked_context_11_1176_59617 node_context_11_1176_59617
  intro a
  fin_cases a
  · exact context_12_4704_59435
  · exact context_12_4705_59486
  · exact context_12_4706_59552
  · exact context_12_4707_59616

theorem selected_cut_01750 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18832) = some ⟨13, 1, 0, 3444, 18832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18832, 1, 16384⟩
    (by decide) selected_cut_01750

theorem selected_cut_01751 : selected 8 ⟨59639, by decide⟩
    (prefixPartial 13 18833) = some ⟨13, 2, 0, 59639, 18833, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_18833_59639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18833 ⟨59639, by decide⟩ :=
  accepted_of_selected 13 18833 ⟨59639, by decide⟩ ⟨13, 2, 0, 59639, 18833, 1521, 16384⟩
    (by decide) selected_cut_01751

theorem selected_cut_01752 : selected 8 ⟨59670, by decide⟩
    (prefixPartial 13 18834) = some ⟨13, 2, 0, 59670, 18834, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_18834_59670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18834 ⟨59670, by decide⟩ :=
  accepted_of_selected 13 18834 ⟨59670, by decide⟩ ⟨13, 2, 0, 59670, 18834, 2089, 16384⟩
    (by decide) selected_cut_01752

theorem selected_cut_01753 : selected 8 ⟨59682, by decide⟩
    (prefixPartial 13 18835) = some ⟨13, 2, 0, 59682, 18835, 897, 16384⟩ := by
  decide +kernel

theorem context_13_18835_59682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18835 ⟨59682, by decide⟩ :=
  accepted_of_selected 13 18835 ⟨59682, by decide⟩ ⟨13, 2, 0, 59682, 18835, 897, 16384⟩
    (by decide) selected_cut_01753

theorem unmarked_context_12_4708_59683 : frontier 9 ⟨59683, by decide⟩
    (prefixCache 12 4708) (prefixPartial 12 4708) = false := by
  decide +kernel

theorem node_context_12_4708_59683 : EJMOriginalGlobalDAGData.nodes 9 ⟨59683, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59639, by decide⟩,⟨59670, by decide⟩,⟨59682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4708_59683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4708 ⟨59683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4708
    ⟨59683, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59639, by decide⟩,⟨59670, by decide⟩,⟨59682, by decide⟩]) unmarked_context_12_4708_59683 node_context_12_4708_59683
  intro a
  fin_cases a
  · exact context_13_18832_3444
  · exact context_13_18833_59639
  · exact context_13_18834_59670
  · exact context_13_18835_59682

theorem selected_cut_01754 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18836) = some ⟨13, 1, 0, 3444, 18836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18836, 1, 16384⟩
    (by decide) selected_cut_01754

theorem selected_cut_01755 : selected 8 ⟨59710, by decide⟩
    (prefixPartial 13 18837) = some ⟨13, 2, 0, 59710, 18837, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_18837_59710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18837 ⟨59710, by decide⟩ :=
  accepted_of_selected 13 18837 ⟨59710, by decide⟩ ⟨13, 2, 0, 59710, 18837, 1665, 16384⟩
    (by decide) selected_cut_01755

theorem selected_cut_01756 : selected 8 ⟨59733, by decide⟩
    (prefixPartial 13 18838) = some ⟨13, 2, 0, 59733, 18838, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_18838_59733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18838 ⟨59733, by decide⟩ :=
  accepted_of_selected 13 18838 ⟨59733, by decide⟩ ⟨13, 2, 0, 59733, 18838, 2493, 16384⟩
    (by decide) selected_cut_01756

theorem selected_cut_01757 : selected 8 ⟨59741, by decide⟩
    (prefixPartial 13 18839) = some ⟨13, 2, 0, 59741, 18839, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_18839_59741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18839 ⟨59741, by decide⟩ :=
  accepted_of_selected 13 18839 ⟨59741, by decide⟩ ⟨13, 2, 0, 59741, 18839, 1157, 16384⟩
    (by decide) selected_cut_01757

theorem unmarked_context_12_4709_59742 : frontier 9 ⟨59742, by decide⟩
    (prefixCache 12 4709) (prefixPartial 12 4709) = false := by
  decide +kernel

theorem node_context_12_4709_59742 : EJMOriginalGlobalDAGData.nodes 9 ⟨59742, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59710, by decide⟩,⟨59733, by decide⟩,⟨59741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4709_59742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4709 ⟨59742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4709
    ⟨59742, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59710, by decide⟩,⟨59733, by decide⟩,⟨59741, by decide⟩]) unmarked_context_12_4709_59742 node_context_12_4709_59742
  intro a
  fin_cases a
  · exact context_13_18836_3444
  · exact context_13_18837_59710
  · exact context_13_18838_59733
  · exact context_13_18839_59741

theorem selected_cut_01758 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18840) = some ⟨13, 1, 0, 3444, 18840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18840, 1, 16384⟩
    (by decide) selected_cut_01758

theorem selected_cut_01759 : selected 8 ⟨59769, by decide⟩
    (prefixPartial 13 18841) = some ⟨13, 2, 0, 59769, 18841, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_18841_59769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18841 ⟨59769, by decide⟩ :=
  accepted_of_selected 13 18841 ⟨59769, by decide⟩ ⟨13, 2, 0, 59769, 18841, 1617, 16384⟩
    (by decide) selected_cut_01759

theorem selected_cut_01760 : selected 8 ⟨59796, by decide⟩
    (prefixPartial 13 18842) = some ⟨13, 2, 0, 59796, 18842, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_18842_59796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18842 ⟨59796, by decide⟩ :=
  accepted_of_selected 13 18842 ⟨59796, by decide⟩ ⟨13, 2, 0, 59796, 18842, 2445, 16384⟩
    (by decide) selected_cut_01760

theorem selected_cut_01761 : selected 8 ⟨59804, by decide⟩
    (prefixPartial 13 18843) = some ⟨13, 2, 0, 59804, 18843, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_18843_59804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18843 ⟨59804, by decide⟩ :=
  accepted_of_selected 13 18843 ⟨59804, by decide⟩ ⟨13, 2, 0, 59804, 18843, 1209, 16384⟩
    (by decide) selected_cut_01761

theorem unmarked_context_12_4710_59805 : frontier 9 ⟨59805, by decide⟩
    (prefixCache 12 4710) (prefixPartial 12 4710) = false := by
  decide +kernel

theorem node_context_12_4710_59805 : EJMOriginalGlobalDAGData.nodes 9 ⟨59805, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59769, by decide⟩,⟨59796, by decide⟩,⟨59804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4710_59805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4710 ⟨59805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4710
    ⟨59805, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59769, by decide⟩,⟨59796, by decide⟩,⟨59804, by decide⟩]) unmarked_context_12_4710_59805 node_context_12_4710_59805
  intro a
  fin_cases a
  · exact context_13_18840_3444
  · exact context_13_18841_59769
  · exact context_13_18842_59796
  · exact context_13_18843_59804

theorem selected_cut_01762 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18844) = some ⟨13, 1, 0, 3444, 18844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18844, 1, 16384⟩
    (by decide) selected_cut_01762

theorem selected_cut_01763 : selected 8 ⟨59837, by decide⟩
    (prefixPartial 13 18845) = some ⟨13, 2, 0, 59837, 18845, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_18845_59837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18845 ⟨59837, by decide⟩ :=
  accepted_of_selected 13 18845 ⟨59837, by decide⟩ ⟨13, 2, 0, 59837, 18845, 1661, 16384⟩
    (by decide) selected_cut_01763

theorem selected_cut_01764 : selected 8 ⟨59864, by decide⟩
    (prefixPartial 13 18846) = some ⟨13, 2, 0, 59864, 18846, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_18846_59864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18846 ⟨59864, by decide⟩ :=
  accepted_of_selected 13 18846 ⟨59864, by decide⟩ ⟨13, 2, 0, 59864, 18846, 2757, 16384⟩
    (by decide) selected_cut_01764

theorem selected_cut_01765 : selected 8 ⟨59876, by decide⟩
    (prefixPartial 13 18847) = some ⟨13, 2, 0, 59876, 18847, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_18847_59876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18847 ⟨59876, by decide⟩ :=
  accepted_of_selected 13 18847 ⟨59876, by decide⟩ ⟨13, 2, 0, 59876, 18847, 1149, 16384⟩
    (by decide) selected_cut_01765

theorem unmarked_context_12_4711_59877 : frontier 9 ⟨59877, by decide⟩
    (prefixCache 12 4711) (prefixPartial 12 4711) = false := by
  decide +kernel

theorem node_context_12_4711_59877 : EJMOriginalGlobalDAGData.nodes 9 ⟨59877, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59837, by decide⟩,⟨59864, by decide⟩,⟨59876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4711_59877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4711 ⟨59877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4711
    ⟨59877, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59837, by decide⟩,⟨59864, by decide⟩,⟨59876, by decide⟩]) unmarked_context_12_4711_59877 node_context_12_4711_59877
  intro a
  fin_cases a
  · exact context_13_18844_3444
  · exact context_13_18845_59837
  · exact context_13_18846_59864
  · exact context_13_18847_59876

theorem unmarked_context_11_1177_59878 : frontier 10 ⟨59878, by decide⟩
    (prefixCache 11 1177) (prefixPartial 11 1177) = false := by
  decide +kernel

theorem node_context_11_1177_59878 : EJMOriginalGlobalDAGData.nodes 10 ⟨59878, by decide⟩ =
    .split (coordinate 11) (![⟨59683, by decide⟩,⟨59742, by decide⟩,⟨59805, by decide⟩,⟨59877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1177_59878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1177 ⟨59878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1177
    ⟨59878, by decide⟩ (by decide) (![⟨59683, by decide⟩,⟨59742, by decide⟩,⟨59805, by decide⟩,⟨59877, by decide⟩]) unmarked_context_11_1177_59878 node_context_11_1177_59878
  intro a
  fin_cases a
  · exact context_12_4708_59683
  · exact context_12_4709_59742
  · exact context_12_4710_59805
  · exact context_12_4711_59877

theorem selected_cut_01766 : selected 9 ⟨59919, by decide⟩
    (prefixPartial 12 4712) = some ⟨12, 2, 0, 59919, 4712, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_4712_59919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4712 ⟨59919, by decide⟩ :=
  accepted_of_selected 12 4712 ⟨59919, by decide⟩ ⟨12, 2, 0, 59919, 4712, 3769, 65536⟩
    (by decide) selected_cut_01766

theorem selected_cut_01767 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18852) = some ⟨13, 1, 0, 3444, 18852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18852, 1, 16384⟩
    (by decide) selected_cut_01767

theorem selected_cut_01768 : selected 8 ⟨59936, by decide⟩
    (prefixPartial 13 18853) = some ⟨13, 2, 0, 59936, 18853, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_18853_59936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18853 ⟨59936, by decide⟩ :=
  accepted_of_selected 13 18853 ⟨59936, by decide⟩ ⟨13, 2, 0, 59936, 18853, 1161, 16384⟩
    (by decide) selected_cut_01768

theorem selected_cut_01769 : selected 8 ⟨59959, by decide⟩
    (prefixPartial 13 18854) = some ⟨13, 2, 0, 59959, 18854, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_18854_59959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18854 ⟨59959, by decide⟩ :=
  accepted_of_selected 13 18854 ⟨59959, by decide⟩ ⟨13, 2, 0, 59959, 18854, 2349, 16384⟩
    (by decide) selected_cut_01769

theorem selected_cut_01770 : selected 8 ⟨59968, by decide⟩
    (prefixPartial 13 18855) = some ⟨13, 2, 0, 59968, 18855, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_18855_59968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18855 ⟨59968, by decide⟩ :=
  accepted_of_selected 13 18855 ⟨59968, by decide⟩ ⟨13, 2, 0, 59968, 18855, 1133, 16384⟩
    (by decide) selected_cut_01770

theorem unmarked_context_12_4713_59969 : frontier 9 ⟨59969, by decide⟩
    (prefixCache 12 4713) (prefixPartial 12 4713) = false := by
  decide +kernel

theorem node_context_12_4713_59969 : EJMOriginalGlobalDAGData.nodes 9 ⟨59969, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59936, by decide⟩,⟨59959, by decide⟩,⟨59968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4713_59969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4713 ⟨59969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4713
    ⟨59969, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59936, by decide⟩,⟨59959, by decide⟩,⟨59968, by decide⟩]) unmarked_context_12_4713_59969 node_context_12_4713_59969
  intro a
  fin_cases a
  · exact context_13_18852_3444
  · exact context_13_18853_59936
  · exact context_13_18854_59959
  · exact context_13_18855_59968

theorem selected_cut_01771 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18856) = some ⟨13, 1, 0, 3444, 18856, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18856_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18856 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18856 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18856, 1, 16384⟩
    (by decide) selected_cut_01771

theorem selected_cut_01772 : selected 8 ⟨60000, by decide⟩
    (prefixPartial 13 18857) = some ⟨13, 2, 0, 60000, 18857, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_18857_60000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18857 ⟨60000, by decide⟩ :=
  accepted_of_selected 13 18857 ⟨60000, by decide⟩ ⟨13, 2, 0, 60000, 18857, 1733, 16384⟩
    (by decide) selected_cut_01772

theorem selected_cut_01773 : selected 8 ⟨60088, by decide⟩
    (prefixPartial 13 18858) = some ⟨13, 2, 0, 60088, 18858, 3805, 16384⟩ := by
  decide +kernel

theorem context_13_18858_60088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18858 ⟨60088, by decide⟩ :=
  accepted_of_selected 13 18858 ⟨60088, by decide⟩ ⟨13, 2, 0, 60088, 18858, 3805, 16384⟩
    (by decide) selected_cut_01773

theorem selected_cut_01774 : selected 8 ⟨60121, by decide⟩
    (prefixPartial 13 18859) = some ⟨13, 2, 0, 60121, 18859, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_18859_60121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18859 ⟨60121, by decide⟩ :=
  accepted_of_selected 13 18859 ⟨60121, by decide⟩ ⟨13, 2, 0, 60121, 18859, 1561, 16384⟩
    (by decide) selected_cut_01774

theorem unmarked_context_12_4714_60122 : frontier 9 ⟨60122, by decide⟩
    (prefixCache 12 4714) (prefixPartial 12 4714) = false := by
  decide +kernel

theorem node_context_12_4714_60122 : EJMOriginalGlobalDAGData.nodes 9 ⟨60122, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60000, by decide⟩,⟨60088, by decide⟩,⟨60121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4714_60122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4714 ⟨60122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4714
    ⟨60122, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60000, by decide⟩,⟨60088, by decide⟩,⟨60121, by decide⟩]) unmarked_context_12_4714_60122 node_context_12_4714_60122
  intro a
  fin_cases a
  · exact context_13_18856_3444
  · exact context_13_18857_60000
  · exact context_13_18858_60088
  · exact context_13_18859_60121

theorem selected_cut_01775 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18860) = some ⟨13, 1, 0, 3444, 18860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18860, 1, 16384⟩
    (by decide) selected_cut_01775

theorem selected_cut_01776 : selected 8 ⟨60136, by decide⟩
    (prefixPartial 13 18861) = some ⟨13, 2, 0, 60136, 18861, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_18861_60136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18861 ⟨60136, by decide⟩ :=
  accepted_of_selected 13 18861 ⟨60136, by decide⟩ ⟨13, 2, 0, 60136, 18861, 1105, 16384⟩
    (by decide) selected_cut_01776

theorem selected_cut_01777 : selected 8 ⟨60157, by decide⟩
    (prefixPartial 13 18862) = some ⟨13, 2, 0, 60157, 18862, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_18862_60157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18862 ⟨60157, by decide⟩ :=
  accepted_of_selected 13 18862 ⟨60157, by decide⟩ ⟨13, 2, 0, 60157, 18862, 2369, 16384⟩
    (by decide) selected_cut_01777

theorem selected_cut_01778 : selected 8 ⟨60164, by decide⟩
    (prefixPartial 13 18863) = some ⟨13, 2, 0, 60164, 18863, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_18863_60164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18863 ⟨60164, by decide⟩ :=
  accepted_of_selected 13 18863 ⟨60164, by decide⟩ ⟨13, 2, 0, 60164, 18863, 1113, 16384⟩
    (by decide) selected_cut_01778

theorem unmarked_context_12_4715_60165 : frontier 9 ⟨60165, by decide⟩
    (prefixCache 12 4715) (prefixPartial 12 4715) = false := by
  decide +kernel

theorem node_context_12_4715_60165 : EJMOriginalGlobalDAGData.nodes 9 ⟨60165, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60136, by decide⟩,⟨60157, by decide⟩,⟨60164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4715_60165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4715 ⟨60165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4715
    ⟨60165, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60136, by decide⟩,⟨60157, by decide⟩,⟨60164, by decide⟩]) unmarked_context_12_4715_60165 node_context_12_4715_60165
  intro a
  fin_cases a
  · exact context_13_18860_3444
  · exact context_13_18861_60136
  · exact context_13_18862_60157
  · exact context_13_18863_60164

theorem unmarked_context_11_1178_60166 : frontier 10 ⟨60166, by decide⟩
    (prefixCache 11 1178) (prefixPartial 11 1178) = false := by
  decide +kernel

theorem node_context_11_1178_60166 : EJMOriginalGlobalDAGData.nodes 10 ⟨60166, by decide⟩ =
    .split (coordinate 11) (![⟨59919, by decide⟩,⟨59969, by decide⟩,⟨60122, by decide⟩,⟨60165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1178_60166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1178 ⟨60166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1178
    ⟨60166, by decide⟩ (by decide) (![⟨59919, by decide⟩,⟨59969, by decide⟩,⟨60122, by decide⟩,⟨60165, by decide⟩]) unmarked_context_11_1178_60166 node_context_11_1178_60166
  intro a
  fin_cases a
  · exact context_12_4712_59919
  · exact context_12_4713_59969
  · exact context_12_4714_60122
  · exact context_12_4715_60165

theorem selected_cut_01779 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18864) = some ⟨13, 1, 0, 3444, 18864, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18864_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18864 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18864 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18864, 1, 16384⟩
    (by decide) selected_cut_01779

theorem selected_cut_01780 : selected 8 ⟨60179, by decide⟩
    (prefixPartial 13 18865) = some ⟨13, 2, 0, 60179, 18865, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_18865_60179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18865 ⟨60179, by decide⟩ :=
  accepted_of_selected 13 18865 ⟨60179, by decide⟩ ⟨13, 2, 0, 60179, 18865, 1029, 16384⟩
    (by decide) selected_cut_01780

theorem selected_cut_01781 : selected 8 ⟨60213, by decide⟩
    (prefixPartial 13 18866) = some ⟨13, 2, 0, 60213, 18866, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_18866_60213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18866 ⟨60213, by decide⟩ :=
  accepted_of_selected 13 18866 ⟨60213, by decide⟩ ⟨13, 2, 0, 60213, 18866, 2285, 16384⟩
    (by decide) selected_cut_01781

theorem selected_cut_01782 : selected 8 ⟨60224, by decide⟩
    (prefixPartial 13 18867) = some ⟨13, 2, 0, 60224, 18867, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_18867_60224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18867 ⟨60224, by decide⟩ :=
  accepted_of_selected 13 18867 ⟨60224, by decide⟩ ⟨13, 2, 0, 60224, 18867, 1049, 16384⟩
    (by decide) selected_cut_01782

theorem unmarked_context_12_4716_60225 : frontier 9 ⟨60225, by decide⟩
    (prefixCache 12 4716) (prefixPartial 12 4716) = false := by
  decide +kernel

theorem node_context_12_4716_60225 : EJMOriginalGlobalDAGData.nodes 9 ⟨60225, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60179, by decide⟩,⟨60213, by decide⟩,⟨60224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4716_60225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4716 ⟨60225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4716
    ⟨60225, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60179, by decide⟩,⟨60213, by decide⟩,⟨60224, by decide⟩]) unmarked_context_12_4716_60225 node_context_12_4716_60225
  intro a
  fin_cases a
  · exact context_13_18864_3444
  · exact context_13_18865_60179
  · exact context_13_18866_60213
  · exact context_13_18867_60224

theorem selected_cut_01783 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18868) = some ⟨13, 1, 0, 3444, 18868, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18868_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18868 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18868 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18868, 1, 16384⟩
    (by decide) selected_cut_01783

theorem selected_cut_01784 : selected 8 ⟨60240, by decide⟩
    (prefixPartial 13 18869) = some ⟨13, 2, 0, 60240, 18869, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_18869_60240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18869 ⟨60240, by decide⟩ :=
  accepted_of_selected 13 18869 ⟨60240, by decide⟩ ⟨13, 2, 0, 60240, 18869, 1121, 16384⟩
    (by decide) selected_cut_01784

theorem selected_cut_01785 : selected 8 ⟨60278, by decide⟩
    (prefixPartial 13 18870) = some ⟨13, 2, 0, 60278, 18870, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_18870_60278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18870 ⟨60278, by decide⟩ :=
  accepted_of_selected 13 18870 ⟨60278, by decide⟩ ⟨13, 2, 0, 60278, 18870, 2661, 16384⟩
    (by decide) selected_cut_01785

theorem selected_cut_01786 : selected 8 ⟨60295, by decide⟩
    (prefixPartial 13 18871) = some ⟨13, 2, 0, 60295, 18871, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_18871_60295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18871 ⟨60295, by decide⟩ :=
  accepted_of_selected 13 18871 ⟨60295, by decide⟩ ⟨13, 2, 0, 60295, 18871, 1225, 16384⟩
    (by decide) selected_cut_01786

theorem unmarked_context_12_4717_60296 : frontier 9 ⟨60296, by decide⟩
    (prefixCache 12 4717) (prefixPartial 12 4717) = false := by
  decide +kernel

theorem node_context_12_4717_60296 : EJMOriginalGlobalDAGData.nodes 9 ⟨60296, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60240, by decide⟩,⟨60278, by decide⟩,⟨60295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4717_60296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4717 ⟨60296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4717
    ⟨60296, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60240, by decide⟩,⟨60278, by decide⟩,⟨60295, by decide⟩]) unmarked_context_12_4717_60296 node_context_12_4717_60296
  intro a
  fin_cases a
  · exact context_13_18868_3444
  · exact context_13_18869_60240
  · exact context_13_18870_60278
  · exact context_13_18871_60295

theorem selected_cut_01787 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18872) = some ⟨13, 1, 0, 3444, 18872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18872, 1, 16384⟩
    (by decide) selected_cut_01787

theorem selected_cut_01788 : selected 8 ⟨60306, by decide⟩
    (prefixPartial 13 18873) = some ⟨13, 2, 0, 60306, 18873, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_18873_60306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18873 ⟨60306, by decide⟩ :=
  accepted_of_selected 13 18873 ⟨60306, by decide⟩ ⟨13, 2, 0, 60306, 18873, 1001, 16384⟩
    (by decide) selected_cut_01788

theorem selected_cut_01789 : selected 8 ⟨60340, by decide⟩
    (prefixPartial 13 18874) = some ⟨13, 2, 0, 60340, 18874, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_18874_60340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18874 ⟨60340, by decide⟩ :=
  accepted_of_selected 13 18874 ⟨60340, by decide⟩ ⟨13, 2, 0, 60340, 18874, 2589, 16384⟩
    (by decide) selected_cut_01789

theorem selected_cut_01790 : selected 8 ⟨60355, by decide⟩
    (prefixPartial 13 18875) = some ⟨13, 2, 0, 60355, 18875, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_18875_60355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18875 ⟨60355, by decide⟩ :=
  accepted_of_selected 13 18875 ⟨60355, by decide⟩ ⟨13, 2, 0, 60355, 18875, 1165, 16384⟩
    (by decide) selected_cut_01790

theorem unmarked_context_12_4718_60356 : frontier 9 ⟨60356, by decide⟩
    (prefixCache 12 4718) (prefixPartial 12 4718) = false := by
  decide +kernel

theorem node_context_12_4718_60356 : EJMOriginalGlobalDAGData.nodes 9 ⟨60356, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60306, by decide⟩,⟨60340, by decide⟩,⟨60355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4718_60356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4718 ⟨60356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4718
    ⟨60356, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60306, by decide⟩,⟨60340, by decide⟩,⟨60355, by decide⟩]) unmarked_context_12_4718_60356 node_context_12_4718_60356
  intro a
  fin_cases a
  · exact context_13_18872_3444
  · exact context_13_18873_60306
  · exact context_13_18874_60340
  · exact context_13_18875_60355

theorem selected_cut_01791 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18876) = some ⟨13, 1, 0, 3444, 18876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18876, 1, 16384⟩
    (by decide) selected_cut_01791

theorem selected_cut_01792 : selected 8 ⟨60368, by decide⟩
    (prefixPartial 13 18877) = some ⟨13, 2, 0, 60368, 18877, 997, 16384⟩ := by
  decide +kernel

theorem context_13_18877_60368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18877 ⟨60368, by decide⟩ :=
  accepted_of_selected 13 18877 ⟨60368, by decide⟩ ⟨13, 2, 0, 60368, 18877, 997, 16384⟩
    (by decide) selected_cut_01792

theorem selected_cut_01793 : selected 8 ⟨60393, by decide⟩
    (prefixPartial 13 18878) = some ⟨13, 2, 0, 60393, 18878, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_18878_60393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18878 ⟨60393, by decide⟩ :=
  accepted_of_selected 13 18878 ⟨60393, by decide⟩ ⟨13, 2, 0, 60393, 18878, 2621, 16384⟩
    (by decide) selected_cut_01793

theorem selected_cut_01794 : selected 8 ⟨60403, by decide⟩
    (prefixPartial 13 18879) = some ⟨13, 2, 0, 60403, 18879, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_18879_60403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18879 ⟨60403, by decide⟩ :=
  accepted_of_selected 13 18879 ⟨60403, by decide⟩ ⟨13, 2, 0, 60403, 18879, 1209, 16384⟩
    (by decide) selected_cut_01794

theorem unmarked_context_12_4719_60404 : frontier 9 ⟨60404, by decide⟩
    (prefixCache 12 4719) (prefixPartial 12 4719) = false := by
  decide +kernel

theorem node_context_12_4719_60404 : EJMOriginalGlobalDAGData.nodes 9 ⟨60404, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60368, by decide⟩,⟨60393, by decide⟩,⟨60403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4719_60404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4719 ⟨60404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4719
    ⟨60404, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60368, by decide⟩,⟨60393, by decide⟩,⟨60403, by decide⟩]) unmarked_context_12_4719_60404 node_context_12_4719_60404
  intro a
  fin_cases a
  · exact context_13_18876_3444
  · exact context_13_18877_60368
  · exact context_13_18878_60393
  · exact context_13_18879_60403

theorem unmarked_context_11_1179_60405 : frontier 10 ⟨60405, by decide⟩
    (prefixCache 11 1179) (prefixPartial 11 1179) = false := by
  decide +kernel

theorem node_context_11_1179_60405 : EJMOriginalGlobalDAGData.nodes 10 ⟨60405, by decide⟩ =
    .split (coordinate 11) (![⟨60225, by decide⟩,⟨60296, by decide⟩,⟨60356, by decide⟩,⟨60404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1179_60405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1179 ⟨60405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1179
    ⟨60405, by decide⟩ (by decide) (![⟨60225, by decide⟩,⟨60296, by decide⟩,⟨60356, by decide⟩,⟨60404, by decide⟩]) unmarked_context_11_1179_60405 node_context_11_1179_60405
  intro a
  fin_cases a
  · exact context_12_4716_60225
  · exact context_12_4717_60296
  · exact context_12_4718_60356
  · exact context_12_4719_60404

theorem unmarked_context_10_294_60406 : frontier 11 ⟨60406, by decide⟩
    (prefixCache 10 294) (prefixPartial 10 294) = false := by
  decide +kernel

theorem node_context_10_294_60406 : EJMOriginalGlobalDAGData.nodes 11 ⟨60406, by decide⟩ =
    .split (coordinate 10) (![⟨59617, by decide⟩,⟨59878, by decide⟩,⟨60166, by decide⟩,⟨60405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_294_60406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 294 ⟨60406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 294
    ⟨60406, by decide⟩ (by decide) (![⟨59617, by decide⟩,⟨59878, by decide⟩,⟨60166, by decide⟩,⟨60405, by decide⟩]) unmarked_context_10_294_60406 node_context_10_294_60406
  intro a
  fin_cases a
  · exact context_11_1176_59617
  · exact context_11_1177_59878
  · exact context_11_1178_60166
  · exact context_11_1179_60405

theorem selected_cut_01795 : selected 9 ⟨60444, by decide⟩
    (prefixPartial 12 4720) = some ⟨12, 2, 0, 60444, 4720, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_4720_60444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4720 ⟨60444, by decide⟩ :=
  accepted_of_selected 12 4720 ⟨60444, by decide⟩ ⟨12, 2, 0, 60444, 4720, 2877, 65536⟩
    (by decide) selected_cut_01795

theorem selected_cut_01796 : selected 9 ⟨60487, by decide⟩
    (prefixPartial 12 4721) = some ⟨12, 2, 0, 60487, 4721, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_4721_60487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4721 ⟨60487, by decide⟩ :=
  accepted_of_selected 12 4721 ⟨60487, by decide⟩ ⟨12, 2, 0, 60487, 4721, 3661, 65536⟩
    (by decide) selected_cut_01796

theorem selected_cut_01797 : selected 9 ⟨60532, by decide⟩
    (prefixPartial 12 4722) = some ⟨12, 2, 0, 60532, 4722, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_4722_60532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4722 ⟨60532, by decide⟩ :=
  accepted_of_selected 12 4722 ⟨60532, by decide⟩ ⟨12, 2, 0, 60532, 4722, 3589, 65536⟩
    (by decide) selected_cut_01797

theorem selected_cut_01798 : selected 9 ⟨60580, by decide⟩
    (prefixPartial 12 4723) = some ⟨12, 2, 0, 60580, 4723, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_4723_60580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4723 ⟨60580, by decide⟩ :=
  accepted_of_selected 12 4723 ⟨60580, by decide⟩ ⟨12, 2, 0, 60580, 4723, 3821, 65536⟩
    (by decide) selected_cut_01798

theorem unmarked_context_11_1180_60581 : frontier 10 ⟨60581, by decide⟩
    (prefixCache 11 1180) (prefixPartial 11 1180) = false := by
  decide +kernel

theorem node_context_11_1180_60581 : EJMOriginalGlobalDAGData.nodes 10 ⟨60581, by decide⟩ =
    .split (coordinate 11) (![⟨60444, by decide⟩,⟨60487, by decide⟩,⟨60532, by decide⟩,⟨60580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1180_60581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1180 ⟨60581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1180
    ⟨60581, by decide⟩ (by decide) (![⟨60444, by decide⟩,⟨60487, by decide⟩,⟨60532, by decide⟩,⟨60580, by decide⟩]) unmarked_context_11_1180_60581 node_context_11_1180_60581
  intro a
  fin_cases a
  · exact context_12_4720_60444
  · exact context_12_4721_60487
  · exact context_12_4722_60532
  · exact context_12_4723_60580

theorem selected_cut_01799 : selected 9 ⟨60632, by decide⟩
    (prefixPartial 12 4724) = some ⟨12, 2, 0, 60632, 4724, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_4724_60632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4724 ⟨60632, by decide⟩ :=
  accepted_of_selected 12 4724 ⟨60632, by decide⟩ ⟨12, 2, 0, 60632, 4724, 3777, 65536⟩
    (by decide) selected_cut_01799

theorem selected_cut_01800 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18900) = some ⟨13, 1, 0, 3444, 18900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18900, 1, 16384⟩
    (by decide) selected_cut_01800

theorem selected_cut_01801 : selected 8 ⟨60643, by decide⟩
    (prefixPartial 13 18901) = some ⟨13, 2, 0, 60643, 18901, 805, 16384⟩ := by
  decide +kernel

theorem context_13_18901_60643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18901 ⟨60643, by decide⟩ :=
  accepted_of_selected 13 18901 ⟨60643, by decide⟩ ⟨13, 2, 0, 60643, 18901, 805, 16384⟩
    (by decide) selected_cut_01801

theorem selected_cut_01802 : selected 8 ⟨60668, by decide⟩
    (prefixPartial 13 18902) = some ⟨13, 2, 0, 60668, 18902, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_18902_60668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18902 ⟨60668, by decide⟩ :=
  accepted_of_selected 13 18902 ⟨60668, by decide⟩ ⟨13, 2, 0, 60668, 18902, 2477, 16384⟩
    (by decide) selected_cut_01802

theorem selected_cut_01803 : selected 8 ⟨60679, by decide⟩
    (prefixPartial 13 18903) = some ⟨13, 2, 0, 60679, 18903, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_18903_60679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18903 ⟨60679, by decide⟩ :=
  accepted_of_selected 13 18903 ⟨60679, by decide⟩ ⟨13, 2, 0, 60679, 18903, 1109, 16384⟩
    (by decide) selected_cut_01803

theorem unmarked_context_12_4725_60680 : frontier 9 ⟨60680, by decide⟩
    (prefixCache 12 4725) (prefixPartial 12 4725) = false := by
  decide +kernel

theorem node_context_12_4725_60680 : EJMOriginalGlobalDAGData.nodes 9 ⟨60680, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60643, by decide⟩,⟨60668, by decide⟩,⟨60679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4725_60680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4725 ⟨60680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4725
    ⟨60680, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60643, by decide⟩,⟨60668, by decide⟩,⟨60679, by decide⟩]) unmarked_context_12_4725_60680 node_context_12_4725_60680
  intro a
  fin_cases a
  · exact context_13_18900_3444
  · exact context_13_18901_60643
  · exact context_13_18902_60668
  · exact context_13_18903_60679

theorem selected_cut_01804 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18904) = some ⟨13, 1, 0, 3444, 18904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18904, 1, 16384⟩
    (by decide) selected_cut_01804

theorem selected_cut_01805 : selected 8 ⟨60690, by decide⟩
    (prefixPartial 13 18905) = some ⟨13, 2, 0, 60690, 18905, 729, 16384⟩ := by
  decide +kernel

theorem context_13_18905_60690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18905 ⟨60690, by decide⟩ :=
  accepted_of_selected 13 18905 ⟨60690, by decide⟩ ⟨13, 2, 0, 60690, 18905, 729, 16384⟩
    (by decide) selected_cut_01805

theorem selected_cut_01806 : selected 8 ⟨60716, by decide⟩
    (prefixPartial 13 18906) = some ⟨13, 2, 0, 60716, 18906, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_18906_60716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18906 ⟨60716, by decide⟩ :=
  accepted_of_selected 13 18906 ⟨60716, by decide⟩ ⟨13, 2, 0, 60716, 18906, 2477, 16384⟩
    (by decide) selected_cut_01806

theorem selected_cut_01807 : selected 8 ⟨60729, by decide⟩
    (prefixPartial 13 18907) = some ⟨13, 2, 0, 60729, 18907, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_18907_60729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18907 ⟨60729, by decide⟩ :=
  accepted_of_selected 13 18907 ⟨60729, by decide⟩ ⟨13, 2, 0, 60729, 18907, 1197, 16384⟩
    (by decide) selected_cut_01807

theorem unmarked_context_12_4726_60730 : frontier 9 ⟨60730, by decide⟩
    (prefixCache 12 4726) (prefixPartial 12 4726) = false := by
  decide +kernel

theorem node_context_12_4726_60730 : EJMOriginalGlobalDAGData.nodes 9 ⟨60730, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60690, by decide⟩,⟨60716, by decide⟩,⟨60729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4726_60730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4726 ⟨60730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4726
    ⟨60730, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60690, by decide⟩,⟨60716, by decide⟩,⟨60729, by decide⟩]) unmarked_context_12_4726_60730 node_context_12_4726_60730
  intro a
  fin_cases a
  · exact context_13_18904_3444
  · exact context_13_18905_60690
  · exact context_13_18906_60716
  · exact context_13_18907_60729

theorem selected_cut_01808 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18908) = some ⟨13, 1, 0, 3444, 18908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18908, 1, 16384⟩
    (by decide) selected_cut_01808

theorem selected_cut_01809 : selected 8 ⟨60742, by decide⟩
    (prefixPartial 13 18909) = some ⟨13, 2, 0, 60742, 18909, 693, 16384⟩ := by
  decide +kernel

theorem context_13_18909_60742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18909 ⟨60742, by decide⟩ :=
  accepted_of_selected 13 18909 ⟨60742, by decide⟩ ⟨13, 2, 0, 60742, 18909, 693, 16384⟩
    (by decide) selected_cut_01809

theorem selected_cut_01810 : selected 8 ⟨60785, by decide⟩
    (prefixPartial 13 18910) = some ⟨13, 2, 0, 60785, 18910, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_18910_60785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18910 ⟨60785, by decide⟩ :=
  accepted_of_selected 13 18910 ⟨60785, by decide⟩ ⟨13, 2, 0, 60785, 18910, 2917, 16384⟩
    (by decide) selected_cut_01810

theorem selected_cut_01811 : selected 8 ⟨60803, by decide⟩
    (prefixPartial 13 18911) = some ⟨13, 2, 0, 60803, 18911, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_18911_60803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18911 ⟨60803, by decide⟩ :=
  accepted_of_selected 13 18911 ⟨60803, by decide⟩ ⟨13, 2, 0, 60803, 18911, 1237, 16384⟩
    (by decide) selected_cut_01811

theorem unmarked_context_12_4727_60804 : frontier 9 ⟨60804, by decide⟩
    (prefixCache 12 4727) (prefixPartial 12 4727) = false := by
  decide +kernel

theorem node_context_12_4727_60804 : EJMOriginalGlobalDAGData.nodes 9 ⟨60804, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60742, by decide⟩,⟨60785, by decide⟩,⟨60803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4727_60804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4727 ⟨60804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4727
    ⟨60804, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60742, by decide⟩,⟨60785, by decide⟩,⟨60803, by decide⟩]) unmarked_context_12_4727_60804 node_context_12_4727_60804
  intro a
  fin_cases a
  · exact context_13_18908_3444
  · exact context_13_18909_60742
  · exact context_13_18910_60785
  · exact context_13_18911_60803

theorem unmarked_context_11_1181_60805 : frontier 10 ⟨60805, by decide⟩
    (prefixCache 11 1181) (prefixPartial 11 1181) = false := by
  decide +kernel

theorem node_context_11_1181_60805 : EJMOriginalGlobalDAGData.nodes 10 ⟨60805, by decide⟩ =
    .split (coordinate 11) (![⟨60632, by decide⟩,⟨60680, by decide⟩,⟨60730, by decide⟩,⟨60804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1181_60805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1181 ⟨60805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1181
    ⟨60805, by decide⟩ (by decide) (![⟨60632, by decide⟩,⟨60680, by decide⟩,⟨60730, by decide⟩,⟨60804, by decide⟩]) unmarked_context_11_1181_60805 node_context_11_1181_60805
  intro a
  fin_cases a
  · exact context_12_4724_60632
  · exact context_12_4725_60680
  · exact context_12_4726_60730
  · exact context_12_4727_60804

theorem selected_cut_01812 : selected 9 ⟨60843, by decide⟩
    (prefixPartial 12 4728) = some ⟨12, 2, 0, 60843, 4728, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_4728_60843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4728 ⟨60843, by decide⟩ :=
  accepted_of_selected 12 4728 ⟨60843, by decide⟩ ⟨12, 2, 0, 60843, 4728, 3245, 65536⟩
    (by decide) selected_cut_01812

theorem selected_cut_01813 : selected 9 ⟨60879, by decide⟩
    (prefixPartial 12 4729) = some ⟨12, 2, 0, 60879, 4729, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_4729_60879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4729 ⟨60879, by decide⟩ :=
  accepted_of_selected 12 4729 ⟨60879, by decide⟩ ⟨12, 2, 0, 60879, 4729, 4041, 65536⟩
    (by decide) selected_cut_01813

theorem selected_cut_01814 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18920) = some ⟨13, 1, 0, 3444, 18920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18920, 1, 16384⟩
    (by decide) selected_cut_01814

theorem selected_cut_01815 : selected 8 ⟨60892, by decide⟩
    (prefixPartial 13 18921) = some ⟨13, 2, 0, 60892, 18921, 593, 16384⟩ := by
  decide +kernel

theorem context_13_18921_60892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18921 ⟨60892, by decide⟩ :=
  accepted_of_selected 13 18921 ⟨60892, by decide⟩ ⟨13, 2, 0, 60892, 18921, 593, 16384⟩
    (by decide) selected_cut_01815

theorem selected_cut_01816 : selected 7 ⟨60918, by decide⟩
    (prefixPartial 14 75688) = some ⟨14, 2, 0, 60918, 75688, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_75688_60918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75688 ⟨60918, by decide⟩ :=
  accepted_of_selected 14 75688 ⟨60918, by decide⟩ ⟨14, 2, 0, 60918, 75688, 1289, 4096⟩
    (by decide) selected_cut_01816

theorem selected_cut_01817 : selected 7 ⟨60954, by decide⟩
    (prefixPartial 14 75689) = some ⟨14, 2, 0, 60954, 75689, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_75689_60954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75689 ⟨60954, by decide⟩ :=
  accepted_of_selected 14 75689 ⟨60954, by decide⟩ ⟨14, 2, 0, 60954, 75689, 1333, 4096⟩
    (by decide) selected_cut_01817

theorem selected_cut_01818 : selected 7 ⟨60971, by decide⟩
    (prefixPartial 14 75690) = some ⟨14, 2, 0, 60971, 75690, 877, 4096⟩ := by
  decide +kernel

theorem context_14_75690_60971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75690 ⟨60971, by decide⟩ :=
  accepted_of_selected 14 75690 ⟨60971, by decide⟩ ⟨14, 2, 0, 60971, 75690, 877, 4096⟩
    (by decide) selected_cut_01818

theorem selected_cut_01819 : selected 7 ⟨60990, by decide⟩
    (prefixPartial 14 75691) = some ⟨14, 2, 0, 60990, 75691, 933, 4096⟩ := by
  decide +kernel

theorem context_14_75691_60990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75691 ⟨60990, by decide⟩ :=
  accepted_of_selected 14 75691 ⟨60990, by decide⟩ ⟨14, 2, 0, 60990, 75691, 933, 4096⟩
    (by decide) selected_cut_01819

theorem unmarked_context_13_18922_60991 : frontier 8 ⟨60991, by decide⟩
    (prefixCache 13 18922) (prefixPartial 13 18922) = false := by
  decide +kernel

theorem node_context_13_18922_60991 : EJMOriginalGlobalDAGData.nodes 8 ⟨60991, by decide⟩ =
    .split (coordinate 13) (![⟨60918, by decide⟩,⟨60954, by decide⟩,⟨60971, by decide⟩,⟨60990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18922_60991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18922 ⟨60991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18922
    ⟨60991, by decide⟩ (by decide) (![⟨60918, by decide⟩,⟨60954, by decide⟩,⟨60971, by decide⟩,⟨60990, by decide⟩]) unmarked_context_13_18922_60991 node_context_13_18922_60991
  intro a
  fin_cases a
  · exact context_14_75688_60918
  · exact context_14_75689_60954
  · exact context_14_75690_60971
  · exact context_14_75691_60990

theorem selected_cut_01820 : selected 8 ⟨61027, by decide⟩
    (prefixPartial 13 18923) = some ⟨13, 2, 0, 61027, 18923, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_18923_61027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18923 ⟨61027, by decide⟩ :=
  accepted_of_selected 13 18923 ⟨61027, by decide⟩ ⟨13, 2, 0, 61027, 18923, 1705, 16384⟩
    (by decide) selected_cut_01820

theorem unmarked_context_12_4730_61028 : frontier 9 ⟨61028, by decide⟩
    (prefixCache 12 4730) (prefixPartial 12 4730) = false := by
  decide +kernel

theorem node_context_12_4730_61028 : EJMOriginalGlobalDAGData.nodes 9 ⟨61028, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨60892, by decide⟩,⟨60991, by decide⟩,⟨61027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4730_61028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4730 ⟨61028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4730
    ⟨61028, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨60892, by decide⟩,⟨60991, by decide⟩,⟨61027, by decide⟩]) unmarked_context_12_4730_61028 node_context_12_4730_61028
  intro a
  fin_cases a
  · exact context_13_18920_3444
  · exact context_13_18921_60892
  · exact context_13_18922_60991
  · exact context_13_18923_61027

theorem selected_cut_01821 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18924) = some ⟨13, 1, 0, 3444, 18924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18924, 1, 16384⟩
    (by decide) selected_cut_01821

theorem selected_cut_01822 : selected 8 ⟨61032, by decide⟩
    (prefixPartial 13 18925) = some ⟨13, 2, 0, 61032, 18925, 297, 16384⟩ := by
  decide +kernel

theorem context_13_18925_61032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18925 ⟨61032, by decide⟩ :=
  accepted_of_selected 13 18925 ⟨61032, by decide⟩ ⟨13, 2, 0, 61032, 18925, 297, 16384⟩
    (by decide) selected_cut_01822

theorem selected_cut_01823 : selected 8 ⟨61062, by decide⟩
    (prefixPartial 13 18926) = some ⟨13, 2, 0, 61062, 18926, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_18926_61062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18926 ⟨61062, by decide⟩ :=
  accepted_of_selected 13 18926 ⟨61062, by decide⟩ ⟨13, 2, 0, 61062, 18926, 2621, 16384⟩
    (by decide) selected_cut_01823

theorem selected_cut_01824 : selected 8 ⟨61073, by decide⟩
    (prefixPartial 13 18927) = some ⟨13, 2, 0, 61073, 18927, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_18927_61073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18927 ⟨61073, by decide⟩ :=
  accepted_of_selected 13 18927 ⟨61073, by decide⟩ ⟨13, 2, 0, 61073, 18927, 1233, 16384⟩
    (by decide) selected_cut_01824

theorem unmarked_context_12_4731_61074 : frontier 9 ⟨61074, by decide⟩
    (prefixCache 12 4731) (prefixPartial 12 4731) = false := by
  decide +kernel

theorem node_context_12_4731_61074 : EJMOriginalGlobalDAGData.nodes 9 ⟨61074, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨61032, by decide⟩,⟨61062, by decide⟩,⟨61073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4731_61074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4731 ⟨61074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4731
    ⟨61074, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨61032, by decide⟩,⟨61062, by decide⟩,⟨61073, by decide⟩]) unmarked_context_12_4731_61074 node_context_12_4731_61074
  intro a
  fin_cases a
  · exact context_13_18924_3444
  · exact context_13_18925_61032
  · exact context_13_18926_61062
  · exact context_13_18927_61073

theorem unmarked_context_11_1182_61075 : frontier 10 ⟨61075, by decide⟩
    (prefixCache 11 1182) (prefixPartial 11 1182) = false := by
  decide +kernel

theorem node_context_11_1182_61075 : EJMOriginalGlobalDAGData.nodes 10 ⟨61075, by decide⟩ =
    .split (coordinate 11) (![⟨60843, by decide⟩,⟨60879, by decide⟩,⟨61028, by decide⟩,⟨61074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1182_61075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1182 ⟨61075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1182
    ⟨61075, by decide⟩ (by decide) (![⟨60843, by decide⟩,⟨60879, by decide⟩,⟨61028, by decide⟩,⟨61074, by decide⟩]) unmarked_context_11_1182_61075 node_context_11_1182_61075
  intro a
  fin_cases a
  · exact context_12_4728_60843
  · exact context_12_4729_60879
  · exact context_12_4730_61028
  · exact context_12_4731_61074

theorem selected_cut_01825 : selected 9 ⟨61107, by decide⟩
    (prefixPartial 12 4732) = some ⟨12, 2, 0, 61107, 4732, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_4732_61107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4732 ⟨61107, by decide⟩ :=
  accepted_of_selected 12 4732 ⟨61107, by decide⟩ ⟨12, 2, 0, 61107, 4732, 3129, 65536⟩
    (by decide) selected_cut_01825

theorem selected_cut_01826 : selected 9 ⟨61154, by decide⟩
    (prefixPartial 12 4733) = some ⟨12, 2, 0, 61154, 4733, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_4733_61154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4733 ⟨61154, by decide⟩ :=
  accepted_of_selected 12 4733 ⟨61154, by decide⟩ ⟨12, 2, 0, 61154, 4733, 3749, 65536⟩
    (by decide) selected_cut_01826

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
