/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover191
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_71699_472200 : frontier 9 ⟨472200, by decide⟩
    (prefixCache 12 71699) (prefixPartial 12 71699) = false := by
  decide +kernel

theorem node_context_12_71699_472200 : EJMOriginalGlobalDAGData.nodes 9 ⟨472200, by decide⟩ =
    .split (coordinate 12) (![⟨472132, by decide⟩,⟨472169, by decide⟩,⟨472193, by decide⟩,⟨472199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71699_472200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71699 ⟨472200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71699
    ⟨472200, by decide⟩ (by decide) (![⟨472132, by decide⟩,⟨472169, by decide⟩,⟨472193, by decide⟩,⟨472199, by decide⟩]) unmarked_context_12_71699_472200 node_context_12_71699_472200
  intro a
  fin_cases a
  · exact context_13_286796_472132
  · exact context_13_286797_472169
  · exact context_13_286798_472193
  · exact context_13_286799_472199

theorem unmarked_context_11_17924_472201 : frontier 10 ⟨472201, by decide⟩
    (prefixCache 11 17924) (prefixPartial 11 17924) = false := by
  decide +kernel

theorem node_context_11_17924_472201 : EJMOriginalGlobalDAGData.nodes 10 ⟨472201, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨471977, by decide⟩,⟨472091, by decide⟩,⟨472200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17924_472201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17924 ⟨472201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17924
    ⟨472201, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨471977, by decide⟩,⟨472091, by decide⟩,⟨472200, by decide⟩]) unmarked_context_11_17924_472201 node_context_11_17924_472201
  intro a
  fin_cases a
  · exact context_12_71696_435160
  · exact context_12_71697_471977
  · exact context_12_71698_472091
  · exact context_12_71699_472200

theorem selected_cut_18435 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 71700) = some ⟨12, 1, 0, 449505, 71700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71700_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71700 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 71700 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 71700, 1, 65536⟩
    (by decide) selected_cut_18435

theorem selected_cut_18436 : selected 8 ⟨472235, by decide⟩
    (prefixPartial 13 286804) = some ⟨13, 2, 0, 472235, 286804, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_286804_472235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286804 ⟨472235, by decide⟩ :=
  accepted_of_selected 13 286804 ⟨472235, by decide⟩ ⟨13, 2, 0, 472235, 286804, 1405, 16384⟩
    (by decide) selected_cut_18436

theorem selected_cut_18437 : selected 8 ⟨472276, by decide⟩
    (prefixPartial 13 286805) = some ⟨13, 2, 0, 472276, 286805, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_286805_472276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286805 ⟨472276, by decide⟩ :=
  accepted_of_selected 13 286805 ⟨472276, by decide⟩ ⟨13, 2, 0, 472276, 286805, 2033, 16384⟩
    (by decide) selected_cut_18437

theorem selected_cut_18438 : selected 8 ⟨472303, by decide⟩
    (prefixPartial 13 286806) = some ⟨13, 2, 0, 472303, 286806, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_286806_472303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286806 ⟨472303, by decide⟩ :=
  accepted_of_selected 13 286806 ⟨472303, by decide⟩ ⟨13, 2, 0, 472303, 286806, 1441, 16384⟩
    (by decide) selected_cut_18438

theorem selected_cut_18439 : selected 8 ⟨472322, by decide⟩
    (prefixPartial 13 286807) = some ⟨13, 2, 0, 472322, 286807, 873, 16384⟩ := by
  decide +kernel

theorem context_13_286807_472322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286807 ⟨472322, by decide⟩ :=
  accepted_of_selected 13 286807 ⟨472322, by decide⟩ ⟨13, 2, 0, 472322, 286807, 873, 16384⟩
    (by decide) selected_cut_18439

theorem unmarked_context_12_71701_472323 : frontier 9 ⟨472323, by decide⟩
    (prefixCache 12 71701) (prefixPartial 12 71701) = false := by
  decide +kernel

theorem node_context_12_71701_472323 : EJMOriginalGlobalDAGData.nodes 9 ⟨472323, by decide⟩ =
    .split (coordinate 12) (![⟨472235, by decide⟩,⟨472276, by decide⟩,⟨472303, by decide⟩,⟨472322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71701_472323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71701 ⟨472323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71701
    ⟨472323, by decide⟩ (by decide) (![⟨472235, by decide⟩,⟨472276, by decide⟩,⟨472303, by decide⟩,⟨472322, by decide⟩]) unmarked_context_12_71701_472323 node_context_12_71701_472323
  intro a
  fin_cases a
  · exact context_13_286804_472235
  · exact context_13_286805_472276
  · exact context_13_286806_472303
  · exact context_13_286807_472322

theorem selected_cut_18440 : selected 8 ⟨472371, by decide⟩
    (prefixPartial 13 286808) = some ⟨13, 2, 0, 472371, 286808, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_286808_472371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286808 ⟨472371, by decide⟩ :=
  accepted_of_selected 13 286808 ⟨472371, by decide⟩ ⟨13, 2, 0, 472371, 286808, 1909, 16384⟩
    (by decide) selected_cut_18440

theorem selected_cut_18441 : selected 8 ⟨472416, by decide⟩
    (prefixPartial 13 286809) = some ⟨13, 2, 0, 472416, 286809, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_286809_472416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286809 ⟨472416, by decide⟩ :=
  accepted_of_selected 13 286809 ⟨472416, by decide⟩ ⟨13, 2, 0, 472416, 286809, 2421, 16384⟩
    (by decide) selected_cut_18441

theorem selected_cut_18442 : selected 8 ⟨472439, by decide⟩
    (prefixPartial 13 286810) = some ⟨13, 2, 0, 472439, 286810, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_286810_472439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286810 ⟨472439, by decide⟩ :=
  accepted_of_selected 13 286810 ⟨472439, by decide⟩ ⟨13, 2, 0, 472439, 286810, 1617, 16384⟩
    (by decide) selected_cut_18442

theorem selected_cut_18443 : selected 8 ⟨472453, by decide⟩
    (prefixPartial 13 286811) = some ⟨13, 2, 0, 472453, 286811, 977, 16384⟩ := by
  decide +kernel

theorem context_13_286811_472453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286811 ⟨472453, by decide⟩ :=
  accepted_of_selected 13 286811 ⟨472453, by decide⟩ ⟨13, 2, 0, 472453, 286811, 977, 16384⟩
    (by decide) selected_cut_18443

theorem unmarked_context_12_71702_472454 : frontier 9 ⟨472454, by decide⟩
    (prefixCache 12 71702) (prefixPartial 12 71702) = false := by
  decide +kernel

theorem node_context_12_71702_472454 : EJMOriginalGlobalDAGData.nodes 9 ⟨472454, by decide⟩ =
    .split (coordinate 12) (![⟨472371, by decide⟩,⟨472416, by decide⟩,⟨472439, by decide⟩,⟨472453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71702_472454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71702 ⟨472454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71702
    ⟨472454, by decide⟩ (by decide) (![⟨472371, by decide⟩,⟨472416, by decide⟩,⟨472439, by decide⟩,⟨472453, by decide⟩]) unmarked_context_12_71702_472454 node_context_12_71702_472454
  intro a
  fin_cases a
  · exact context_13_286808_472371
  · exact context_13_286809_472416
  · exact context_13_286810_472439
  · exact context_13_286811_472453

theorem selected_cut_18444 : selected 8 ⟨472495, by decide⟩
    (prefixPartial 13 286812) = some ⟨13, 2, 0, 472495, 286812, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_286812_472495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286812 ⟨472495, by decide⟩ :=
  accepted_of_selected 13 286812 ⟨472495, by decide⟩ ⟨13, 2, 0, 472495, 286812, 1845, 16384⟩
    (by decide) selected_cut_18444

theorem selected_cut_18445 : selected 8 ⟨472567, by decide⟩
    (prefixPartial 13 286813) = some ⟨13, 2, 0, 472567, 286813, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_286813_472567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286813 ⟨472567, by decide⟩ :=
  accepted_of_selected 13 286813 ⟨472567, by decide⟩ ⟨13, 2, 0, 472567, 286813, 2545, 16384⟩
    (by decide) selected_cut_18445

theorem selected_cut_18446 : selected 8 ⟨472596, by decide⟩
    (prefixPartial 13 286814) = some ⟨13, 2, 0, 472596, 286814, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_286814_472596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286814 ⟨472596, by decide⟩ :=
  accepted_of_selected 13 286814 ⟨472596, by decide⟩ ⟨13, 2, 0, 472596, 286814, 1669, 16384⟩
    (by decide) selected_cut_18446

theorem selected_cut_18447 : selected 8 ⟨472602, by decide⟩
    (prefixPartial 13 286815) = some ⟨13, 2, 0, 472602, 286815, 733, 16384⟩ := by
  decide +kernel

theorem context_13_286815_472602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286815 ⟨472602, by decide⟩ :=
  accepted_of_selected 13 286815 ⟨472602, by decide⟩ ⟨13, 2, 0, 472602, 286815, 733, 16384⟩
    (by decide) selected_cut_18447

theorem unmarked_context_12_71703_472603 : frontier 9 ⟨472603, by decide⟩
    (prefixCache 12 71703) (prefixPartial 12 71703) = false := by
  decide +kernel

theorem node_context_12_71703_472603 : EJMOriginalGlobalDAGData.nodes 9 ⟨472603, by decide⟩ =
    .split (coordinate 12) (![⟨472495, by decide⟩,⟨472567, by decide⟩,⟨472596, by decide⟩,⟨472602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71703_472603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71703 ⟨472603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71703
    ⟨472603, by decide⟩ (by decide) (![⟨472495, by decide⟩,⟨472567, by decide⟩,⟨472596, by decide⟩,⟨472602, by decide⟩]) unmarked_context_12_71703_472603 node_context_12_71703_472603
  intro a
  fin_cases a
  · exact context_13_286812_472495
  · exact context_13_286813_472567
  · exact context_13_286814_472596
  · exact context_13_286815_472602

theorem unmarked_context_11_17925_472604 : frontier 10 ⟨472604, by decide⟩
    (prefixCache 11 17925) (prefixPartial 11 17925) = false := by
  decide +kernel

theorem node_context_11_17925_472604 : EJMOriginalGlobalDAGData.nodes 10 ⟨472604, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨472323, by decide⟩,⟨472454, by decide⟩,⟨472603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17925_472604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17925 ⟨472604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17925
    ⟨472604, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨472323, by decide⟩,⟨472454, by decide⟩,⟨472603, by decide⟩]) unmarked_context_11_17925_472604 node_context_11_17925_472604
  intro a
  fin_cases a
  · exact context_12_71700_449505
  · exact context_12_71701_472323
  · exact context_12_71702_472454
  · exact context_12_71703_472603

theorem selected_cut_18448 : selected 8 ⟨472635, by decide⟩
    (prefixPartial 13 286816) = some ⟨13, 2, 0, 472635, 286816, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_286816_472635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286816 ⟨472635, by decide⟩ :=
  accepted_of_selected 13 286816 ⟨472635, by decide⟩ ⟨13, 2, 0, 472635, 286816, 1721, 16384⟩
    (by decide) selected_cut_18448

theorem selected_cut_18449 : selected 8 ⟨472702, by decide⟩
    (prefixPartial 13 286817) = some ⟨13, 2, 0, 472702, 286817, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_286817_472702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286817 ⟨472702, by decide⟩ :=
  accepted_of_selected 13 286817 ⟨472702, by decide⟩ ⟨13, 2, 0, 472702, 286817, 2865, 16384⟩
    (by decide) selected_cut_18449

theorem selected_cut_18450 : selected 8 ⟨472749, by decide⟩
    (prefixPartial 13 286818) = some ⟨13, 2, 0, 472749, 286818, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_286818_472749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286818 ⟨472749, by decide⟩ :=
  accepted_of_selected 13 286818 ⟨472749, by decide⟩ ⟨13, 2, 0, 472749, 286818, 1993, 16384⟩
    (by decide) selected_cut_18450

theorem selected_cut_18451 : selected 8 ⟨472762, by decide⟩
    (prefixPartial 13 286819) = some ⟨13, 2, 0, 472762, 286819, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_286819_472762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286819 ⟨472762, by decide⟩ :=
  accepted_of_selected 13 286819 ⟨472762, by decide⟩ ⟨13, 2, 0, 472762, 286819, 1061, 16384⟩
    (by decide) selected_cut_18451

theorem unmarked_context_12_71704_472763 : frontier 9 ⟨472763, by decide⟩
    (prefixCache 12 71704) (prefixPartial 12 71704) = false := by
  decide +kernel

theorem node_context_12_71704_472763 : EJMOriginalGlobalDAGData.nodes 9 ⟨472763, by decide⟩ =
    .split (coordinate 12) (![⟨472635, by decide⟩,⟨472702, by decide⟩,⟨472749, by decide⟩,⟨472762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71704_472763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71704 ⟨472763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71704
    ⟨472763, by decide⟩ (by decide) (![⟨472635, by decide⟩,⟨472702, by decide⟩,⟨472749, by decide⟩,⟨472762, by decide⟩]) unmarked_context_12_71704_472763 node_context_12_71704_472763
  intro a
  fin_cases a
  · exact context_13_286816_472635
  · exact context_13_286817_472702
  · exact context_13_286818_472749
  · exact context_13_286819_472762

theorem selected_cut_18452 : selected 8 ⟨472797, by decide⟩
    (prefixPartial 13 286820) = some ⟨13, 2, 0, 472797, 286820, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_286820_472797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286820 ⟨472797, by decide⟩ :=
  accepted_of_selected 13 286820 ⟨472797, by decide⟩ ⟨13, 2, 0, 472797, 286820, 1461, 16384⟩
    (by decide) selected_cut_18452

theorem selected_cut_18453 : selected 8 ⟨472828, by decide⟩
    (prefixPartial 13 286821) = some ⟨13, 2, 0, 472828, 286821, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_286821_472828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286821 ⟨472828, by decide⟩ :=
  accepted_of_selected 13 286821 ⟨472828, by decide⟩ ⟨13, 2, 0, 472828, 286821, 2041, 16384⟩
    (by decide) selected_cut_18453

theorem selected_cut_18454 : selected 8 ⟨472850, by decide⟩
    (prefixPartial 13 286822) = some ⟨13, 2, 0, 472850, 286822, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_286822_472850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286822 ⟨472850, by decide⟩ :=
  accepted_of_selected 13 286822 ⟨472850, by decide⟩ ⟨13, 2, 0, 472850, 286822, 1649, 16384⟩
    (by decide) selected_cut_18454

theorem selected_cut_18455 : selected 8 ⟨472860, by decide⟩
    (prefixPartial 13 286823) = some ⟨13, 2, 0, 472860, 286823, 949, 16384⟩ := by
  decide +kernel

theorem context_13_286823_472860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286823 ⟨472860, by decide⟩ :=
  accepted_of_selected 13 286823 ⟨472860, by decide⟩ ⟨13, 2, 0, 472860, 286823, 949, 16384⟩
    (by decide) selected_cut_18455

theorem unmarked_context_12_71705_472861 : frontier 9 ⟨472861, by decide⟩
    (prefixCache 12 71705) (prefixPartial 12 71705) = false := by
  decide +kernel

theorem node_context_12_71705_472861 : EJMOriginalGlobalDAGData.nodes 9 ⟨472861, by decide⟩ =
    .split (coordinate 12) (![⟨472797, by decide⟩,⟨472828, by decide⟩,⟨472850, by decide⟩,⟨472860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71705_472861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71705 ⟨472861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71705
    ⟨472861, by decide⟩ (by decide) (![⟨472797, by decide⟩,⟨472828, by decide⟩,⟨472850, by decide⟩,⟨472860, by decide⟩]) unmarked_context_12_71705_472861 node_context_12_71705_472861
  intro a
  fin_cases a
  · exact context_13_286820_472797
  · exact context_13_286821_472828
  · exact context_13_286822_472850
  · exact context_13_286823_472860

theorem selected_cut_18456 : selected 8 ⟨472895, by decide⟩
    (prefixPartial 13 286824) = some ⟨13, 2, 0, 472895, 286824, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_286824_472895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286824 ⟨472895, by decide⟩ :=
  accepted_of_selected 13 286824 ⟨472895, by decide⟩ ⟨13, 2, 0, 472895, 286824, 1341, 16384⟩
    (by decide) selected_cut_18456

theorem selected_cut_18457 : selected 8 ⟨472928, by decide⟩
    (prefixPartial 13 286825) = some ⟨13, 2, 0, 472928, 286825, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_286825_472928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286825 ⟨472928, by decide⟩ :=
  accepted_of_selected 13 286825 ⟨472928, by decide⟩ ⟨13, 2, 0, 472928, 286825, 2073, 16384⟩
    (by decide) selected_cut_18457

theorem selected_cut_18458 : selected 8 ⟨472952, by decide⟩
    (prefixPartial 13 286826) = some ⟨13, 2, 0, 472952, 286826, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_286826_472952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286826 ⟨472952, by decide⟩ :=
  accepted_of_selected 13 286826 ⟨472952, by decide⟩ ⟨13, 2, 0, 472952, 286826, 1501, 16384⟩
    (by decide) selected_cut_18458

theorem selected_cut_18459 : selected 8 ⟨472959, by decide⟩
    (prefixPartial 13 286827) = some ⟨13, 2, 0, 472959, 286827, 917, 16384⟩ := by
  decide +kernel

theorem context_13_286827_472959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286827 ⟨472959, by decide⟩ :=
  accepted_of_selected 13 286827 ⟨472959, by decide⟩ ⟨13, 2, 0, 472959, 286827, 917, 16384⟩
    (by decide) selected_cut_18459

theorem unmarked_context_12_71706_472960 : frontier 9 ⟨472960, by decide⟩
    (prefixCache 12 71706) (prefixPartial 12 71706) = false := by
  decide +kernel

theorem node_context_12_71706_472960 : EJMOriginalGlobalDAGData.nodes 9 ⟨472960, by decide⟩ =
    .split (coordinate 12) (![⟨472895, by decide⟩,⟨472928, by decide⟩,⟨472952, by decide⟩,⟨472959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71706_472960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71706 ⟨472960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71706
    ⟨472960, by decide⟩ (by decide) (![⟨472895, by decide⟩,⟨472928, by decide⟩,⟨472952, by decide⟩,⟨472959, by decide⟩]) unmarked_context_12_71706_472960 node_context_12_71706_472960
  intro a
  fin_cases a
  · exact context_13_286824_472895
  · exact context_13_286825_472928
  · exact context_13_286826_472952
  · exact context_13_286827_472959

theorem selected_cut_18460 : selected 8 ⟨472990, by decide⟩
    (prefixPartial 13 286828) = some ⟨13, 2, 0, 472990, 286828, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_286828_472990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286828 ⟨472990, by decide⟩ :=
  accepted_of_selected 13 286828 ⟨472990, by decide⟩ ⟨13, 2, 0, 472990, 286828, 1417, 16384⟩
    (by decide) selected_cut_18460

theorem selected_cut_18461 : selected 8 ⟨473031, by decide⟩
    (prefixPartial 13 286829) = some ⟨13, 2, 0, 473031, 286829, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_286829_473031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286829 ⟨473031, by decide⟩ :=
  accepted_of_selected 13 286829 ⟨473031, by decide⟩ ⟨13, 2, 0, 473031, 286829, 2325, 16384⟩
    (by decide) selected_cut_18461

theorem selected_cut_18462 : selected 8 ⟨473055, by decide⟩
    (prefixPartial 13 286830) = some ⟨13, 2, 0, 473055, 286830, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_286830_473055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286830 ⟨473055, by decide⟩ :=
  accepted_of_selected 13 286830 ⟨473055, by decide⟩ ⟨13, 2, 0, 473055, 286830, 1613, 16384⟩
    (by decide) selected_cut_18462

theorem selected_cut_18463 : selected 8 ⟨473061, by decide⟩
    (prefixPartial 13 286831) = some ⟨13, 2, 0, 473061, 286831, 781, 16384⟩ := by
  decide +kernel

theorem context_13_286831_473061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286831 ⟨473061, by decide⟩ :=
  accepted_of_selected 13 286831 ⟨473061, by decide⟩ ⟨13, 2, 0, 473061, 286831, 781, 16384⟩
    (by decide) selected_cut_18463

theorem unmarked_context_12_71707_473062 : frontier 9 ⟨473062, by decide⟩
    (prefixCache 12 71707) (prefixPartial 12 71707) = false := by
  decide +kernel

theorem node_context_12_71707_473062 : EJMOriginalGlobalDAGData.nodes 9 ⟨473062, by decide⟩ =
    .split (coordinate 12) (![⟨472990, by decide⟩,⟨473031, by decide⟩,⟨473055, by decide⟩,⟨473061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71707_473062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71707 ⟨473062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71707
    ⟨473062, by decide⟩ (by decide) (![⟨472990, by decide⟩,⟨473031, by decide⟩,⟨473055, by decide⟩,⟨473061, by decide⟩]) unmarked_context_12_71707_473062 node_context_12_71707_473062
  intro a
  fin_cases a
  · exact context_13_286828_472990
  · exact context_13_286829_473031
  · exact context_13_286830_473055
  · exact context_13_286831_473061

theorem unmarked_context_11_17926_473063 : frontier 10 ⟨473063, by decide⟩
    (prefixCache 11 17926) (prefixPartial 11 17926) = false := by
  decide +kernel

theorem node_context_11_17926_473063 : EJMOriginalGlobalDAGData.nodes 10 ⟨473063, by decide⟩ =
    .split (coordinate 11) (![⟨472763, by decide⟩,⟨472861, by decide⟩,⟨472960, by decide⟩,⟨473062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17926_473063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17926 ⟨473063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17926
    ⟨473063, by decide⟩ (by decide) (![⟨472763, by decide⟩,⟨472861, by decide⟩,⟨472960, by decide⟩,⟨473062, by decide⟩]) unmarked_context_11_17926_473063 node_context_11_17926_473063
  intro a
  fin_cases a
  · exact context_12_71704_472763
  · exact context_12_71705_472861
  · exact context_12_71706_472960
  · exact context_12_71707_473062

theorem selected_cut_18464 : selected 8 ⟨473091, by decide⟩
    (prefixPartial 13 286832) = some ⟨13, 2, 0, 473091, 286832, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_286832_473091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286832 ⟨473091, by decide⟩ :=
  accepted_of_selected 13 286832 ⟨473091, by decide⟩ ⟨13, 2, 0, 473091, 286832, 1449, 16384⟩
    (by decide) selected_cut_18464

theorem selected_cut_18465 : selected 8 ⟨473143, by decide⟩
    (prefixPartial 13 286833) = some ⟨13, 2, 0, 473143, 286833, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_286833_473143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286833 ⟨473143, by decide⟩ :=
  accepted_of_selected 13 286833 ⟨473143, by decide⟩ ⟨13, 2, 0, 473143, 286833, 2865, 16384⟩
    (by decide) selected_cut_18465

theorem selected_cut_18466 : selected 8 ⟨473190, by decide⟩
    (prefixPartial 13 286834) = some ⟨13, 2, 0, 473190, 286834, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_286834_473190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286834 ⟨473190, by decide⟩ :=
  accepted_of_selected 13 286834 ⟨473190, by decide⟩ ⟨13, 2, 0, 473190, 286834, 2245, 16384⟩
    (by decide) selected_cut_18466

theorem selected_cut_18467 : selected 8 ⟨473210, by decide⟩
    (prefixPartial 13 286835) = some ⟨13, 2, 0, 473210, 286835, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_286835_473210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286835 ⟨473210, by decide⟩ :=
  accepted_of_selected 13 286835 ⟨473210, by decide⟩ ⟨13, 2, 0, 473210, 286835, 1121, 16384⟩
    (by decide) selected_cut_18467

theorem unmarked_context_12_71708_473211 : frontier 9 ⟨473211, by decide⟩
    (prefixCache 12 71708) (prefixPartial 12 71708) = false := by
  decide +kernel

theorem node_context_12_71708_473211 : EJMOriginalGlobalDAGData.nodes 9 ⟨473211, by decide⟩ =
    .split (coordinate 12) (![⟨473091, by decide⟩,⟨473143, by decide⟩,⟨473190, by decide⟩,⟨473210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71708_473211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71708 ⟨473211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71708
    ⟨473211, by decide⟩ (by decide) (![⟨473091, by decide⟩,⟨473143, by decide⟩,⟨473190, by decide⟩,⟨473210, by decide⟩]) unmarked_context_12_71708_473211 node_context_12_71708_473211
  intro a
  fin_cases a
  · exact context_13_286832_473091
  · exact context_13_286833_473143
  · exact context_13_286834_473190
  · exact context_13_286835_473210

theorem selected_cut_18468 : selected 8 ⟨473235, by decide⟩
    (prefixPartial 13 286836) = some ⟨13, 2, 0, 473235, 286836, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_286836_473235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286836 ⟨473235, by decide⟩ :=
  accepted_of_selected 13 286836 ⟨473235, by decide⟩ ⟨13, 2, 0, 473235, 286836, 1217, 16384⟩
    (by decide) selected_cut_18468

theorem selected_cut_18469 : selected 8 ⟨473272, by decide⟩
    (prefixPartial 13 286837) = some ⟨13, 2, 0, 473272, 286837, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_286837_473272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286837 ⟨473272, by decide⟩ :=
  accepted_of_selected 13 286837 ⟨473272, by decide⟩ ⟨13, 2, 0, 473272, 286837, 2105, 16384⟩
    (by decide) selected_cut_18469

theorem selected_cut_18470 : selected 8 ⟨473301, by decide⟩
    (prefixPartial 13 286838) = some ⟨13, 2, 0, 473301, 286838, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_286838_473301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286838 ⟨473301, by decide⟩ :=
  accepted_of_selected 13 286838 ⟨473301, by decide⟩ ⟨13, 2, 0, 473301, 286838, 1929, 16384⟩
    (by decide) selected_cut_18470

theorem selected_cut_18471 : selected 8 ⟨473315, by decide⟩
    (prefixPartial 13 286839) = some ⟨13, 2, 0, 473315, 286839, 961, 16384⟩ := by
  decide +kernel

theorem context_13_286839_473315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286839 ⟨473315, by decide⟩ :=
  accepted_of_selected 13 286839 ⟨473315, by decide⟩ ⟨13, 2, 0, 473315, 286839, 961, 16384⟩
    (by decide) selected_cut_18471

theorem unmarked_context_12_71709_473316 : frontier 9 ⟨473316, by decide⟩
    (prefixCache 12 71709) (prefixPartial 12 71709) = false := by
  decide +kernel

theorem node_context_12_71709_473316 : EJMOriginalGlobalDAGData.nodes 9 ⟨473316, by decide⟩ =
    .split (coordinate 12) (![⟨473235, by decide⟩,⟨473272, by decide⟩,⟨473301, by decide⟩,⟨473315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71709_473316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71709 ⟨473316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71709
    ⟨473316, by decide⟩ (by decide) (![⟨473235, by decide⟩,⟨473272, by decide⟩,⟨473301, by decide⟩,⟨473315, by decide⟩]) unmarked_context_12_71709_473316 node_context_12_71709_473316
  intro a
  fin_cases a
  · exact context_13_286836_473235
  · exact context_13_286837_473272
  · exact context_13_286838_473301
  · exact context_13_286839_473315

theorem selected_cut_18472 : selected 8 ⟨473347, by decide⟩
    (prefixPartial 13 286840) = some ⟨13, 2, 0, 473347, 286840, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_286840_473347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286840 ⟨473347, by decide⟩ :=
  accepted_of_selected 13 286840 ⟨473347, by decide⟩ ⟨13, 2, 0, 473347, 286840, 1357, 16384⟩
    (by decide) selected_cut_18472

theorem selected_cut_18473 : selected 8 ⟨473378, by decide⟩
    (prefixPartial 13 286841) = some ⟨13, 2, 0, 473378, 286841, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_286841_473378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286841 ⟨473378, by decide⟩ :=
  accepted_of_selected 13 286841 ⟨473378, by decide⟩ ⟨13, 2, 0, 473378, 286841, 2357, 16384⟩
    (by decide) selected_cut_18473

theorem selected_cut_18474 : selected 8 ⟨473402, by decide⟩
    (prefixPartial 13 286842) = some ⟨13, 2, 0, 473402, 286842, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_286842_473402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286842 ⟨473402, by decide⟩ :=
  accepted_of_selected 13 286842 ⟨473402, by decide⟩ ⟨13, 2, 0, 473402, 286842, 1989, 16384⟩
    (by decide) selected_cut_18474

theorem selected_cut_18475 : selected 8 ⟨473409, by decide⟩
    (prefixPartial 13 286843) = some ⟨13, 2, 0, 473409, 286843, 965, 16384⟩ := by
  decide +kernel

theorem context_13_286843_473409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286843 ⟨473409, by decide⟩ :=
  accepted_of_selected 13 286843 ⟨473409, by decide⟩ ⟨13, 2, 0, 473409, 286843, 965, 16384⟩
    (by decide) selected_cut_18475

theorem unmarked_context_12_71710_473410 : frontier 9 ⟨473410, by decide⟩
    (prefixCache 12 71710) (prefixPartial 12 71710) = false := by
  decide +kernel

theorem node_context_12_71710_473410 : EJMOriginalGlobalDAGData.nodes 9 ⟨473410, by decide⟩ =
    .split (coordinate 12) (![⟨473347, by decide⟩,⟨473378, by decide⟩,⟨473402, by decide⟩,⟨473409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71710_473410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71710 ⟨473410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71710
    ⟨473410, by decide⟩ (by decide) (![⟨473347, by decide⟩,⟨473378, by decide⟩,⟨473402, by decide⟩,⟨473409, by decide⟩]) unmarked_context_12_71710_473410 node_context_12_71710_473410
  intro a
  fin_cases a
  · exact context_13_286840_473347
  · exact context_13_286841_473378
  · exact context_13_286842_473402
  · exact context_13_286843_473409

theorem selected_cut_18476 : selected 8 ⟨473439, by decide⟩
    (prefixPartial 13 286844) = some ⟨13, 2, 0, 473439, 286844, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_286844_473439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286844 ⟨473439, by decide⟩ :=
  accepted_of_selected 13 286844 ⟨473439, by decide⟩ ⟨13, 2, 0, 473439, 286844, 1029, 16384⟩
    (by decide) selected_cut_18476

theorem selected_cut_18477 : selected 8 ⟨473479, by decide⟩
    (prefixPartial 13 286845) = some ⟨13, 2, 0, 473479, 286845, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_286845_473479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286845 ⟨473479, by decide⟩ :=
  accepted_of_selected 13 286845 ⟨473479, by decide⟩ ⟨13, 2, 0, 473479, 286845, 2249, 16384⟩
    (by decide) selected_cut_18477

theorem selected_cut_18478 : selected 8 ⟨473498, by decide⟩
    (prefixPartial 13 286846) = some ⟨13, 2, 0, 473498, 286846, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_286846_473498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286846 ⟨473498, by decide⟩ :=
  accepted_of_selected 13 286846 ⟨473498, by decide⟩ ⟨13, 2, 0, 473498, 286846, 1793, 16384⟩
    (by decide) selected_cut_18478

theorem selected_cut_18479 : selected 8 ⟨473503, by decide⟩
    (prefixPartial 13 286847) = some ⟨13, 2, 0, 473503, 286847, 753, 16384⟩ := by
  decide +kernel

theorem context_13_286847_473503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286847 ⟨473503, by decide⟩ :=
  accepted_of_selected 13 286847 ⟨473503, by decide⟩ ⟨13, 2, 0, 473503, 286847, 753, 16384⟩
    (by decide) selected_cut_18479

theorem unmarked_context_12_71711_473504 : frontier 9 ⟨473504, by decide⟩
    (prefixCache 12 71711) (prefixPartial 12 71711) = false := by
  decide +kernel

theorem node_context_12_71711_473504 : EJMOriginalGlobalDAGData.nodes 9 ⟨473504, by decide⟩ =
    .split (coordinate 12) (![⟨473439, by decide⟩,⟨473479, by decide⟩,⟨473498, by decide⟩,⟨473503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71711_473504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71711 ⟨473504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71711
    ⟨473504, by decide⟩ (by decide) (![⟨473439, by decide⟩,⟨473479, by decide⟩,⟨473498, by decide⟩,⟨473503, by decide⟩]) unmarked_context_12_71711_473504 node_context_12_71711_473504
  intro a
  fin_cases a
  · exact context_13_286844_473439
  · exact context_13_286845_473479
  · exact context_13_286846_473498
  · exact context_13_286847_473503

theorem unmarked_context_11_17927_473505 : frontier 10 ⟨473505, by decide⟩
    (prefixCache 11 17927) (prefixPartial 11 17927) = false := by
  decide +kernel

theorem node_context_11_17927_473505 : EJMOriginalGlobalDAGData.nodes 10 ⟨473505, by decide⟩ =
    .split (coordinate 11) (![⟨473211, by decide⟩,⟨473316, by decide⟩,⟨473410, by decide⟩,⟨473504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17927_473505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17927 ⟨473505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17927
    ⟨473505, by decide⟩ (by decide) (![⟨473211, by decide⟩,⟨473316, by decide⟩,⟨473410, by decide⟩,⟨473504, by decide⟩]) unmarked_context_11_17927_473505 node_context_11_17927_473505
  intro a
  fin_cases a
  · exact context_12_71708_473211
  · exact context_12_71709_473316
  · exact context_12_71710_473410
  · exact context_12_71711_473504

theorem unmarked_context_10_4481_473506 : frontier 11 ⟨473506, by decide⟩
    (prefixCache 10 4481) (prefixPartial 10 4481) = false := by
  decide +kernel

theorem node_context_10_4481_473506 : EJMOriginalGlobalDAGData.nodes 11 ⟨473506, by decide⟩ =
    .split (coordinate 10) (![⟨472201, by decide⟩,⟨472604, by decide⟩,⟨473063, by decide⟩,⟨473505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4481_473506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4481 ⟨473506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4481
    ⟨473506, by decide⟩ (by decide) (![⟨472201, by decide⟩,⟨472604, by decide⟩,⟨473063, by decide⟩,⟨473505, by decide⟩]) unmarked_context_10_4481_473506 node_context_10_4481_473506
  intro a
  fin_cases a
  · exact context_11_17924_472201
  · exact context_11_17925_472604
  · exact context_11_17926_473063
  · exact context_11_17927_473505

theorem selected_cut_18480 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 71712) = some ⟨12, 1, 0, 435790, 71712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71712_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71712 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 71712 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 71712, 1, 65536⟩
    (by decide) selected_cut_18480

theorem selected_cut_18481 : selected 8 ⟨473526, by decide⟩
    (prefixPartial 13 286852) = some ⟨13, 2, 0, 473526, 286852, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_286852_473526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286852 ⟨473526, by decide⟩ :=
  accepted_of_selected 13 286852 ⟨473526, by decide⟩ ⟨13, 2, 0, 473526, 286852, 1049, 16384⟩
    (by decide) selected_cut_18481

theorem selected_cut_18482 : selected 8 ⟨473552, by decide⟩
    (prefixPartial 13 286853) = some ⟨13, 2, 0, 473552, 286853, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_286853_473552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286853 ⟨473552, by decide⟩ :=
  accepted_of_selected 13 286853 ⟨473552, by decide⟩ ⟨13, 2, 0, 473552, 286853, 1825, 16384⟩
    (by decide) selected_cut_18482

theorem selected_cut_18483 : selected 8 ⟨473572, by decide⟩
    (prefixPartial 13 286854) = some ⟨13, 2, 0, 473572, 286854, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_286854_473572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286854 ⟨473572, by decide⟩ :=
  accepted_of_selected 13 286854 ⟨473572, by decide⟩ ⟨13, 2, 0, 473572, 286854, 1141, 16384⟩
    (by decide) selected_cut_18483

theorem selected_cut_18484 : selected 8 ⟨473578, by decide⟩
    (prefixPartial 13 286855) = some ⟨13, 2, 0, 473578, 286855, 737, 16384⟩ := by
  decide +kernel

theorem context_13_286855_473578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286855 ⟨473578, by decide⟩ :=
  accepted_of_selected 13 286855 ⟨473578, by decide⟩ ⟨13, 2, 0, 473578, 286855, 737, 16384⟩
    (by decide) selected_cut_18484

theorem unmarked_context_12_71713_473579 : frontier 9 ⟨473579, by decide⟩
    (prefixCache 12 71713) (prefixPartial 12 71713) = false := by
  decide +kernel

theorem node_context_12_71713_473579 : EJMOriginalGlobalDAGData.nodes 9 ⟨473579, by decide⟩ =
    .split (coordinate 12) (![⟨473526, by decide⟩,⟨473552, by decide⟩,⟨473572, by decide⟩,⟨473578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71713_473579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71713 ⟨473579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71713
    ⟨473579, by decide⟩ (by decide) (![⟨473526, by decide⟩,⟨473552, by decide⟩,⟨473572, by decide⟩,⟨473578, by decide⟩]) unmarked_context_12_71713_473579 node_context_12_71713_473579
  intro a
  fin_cases a
  · exact context_13_286852_473526
  · exact context_13_286853_473552
  · exact context_13_286854_473572
  · exact context_13_286855_473578

theorem selected_cut_18485 : selected 8 ⟨473597, by decide⟩
    (prefixPartial 13 286856) = some ⟨13, 2, 0, 473597, 286856, 965, 16384⟩ := by
  decide +kernel

theorem context_13_286856_473597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286856 ⟨473597, by decide⟩ :=
  accepted_of_selected 13 286856 ⟨473597, by decide⟩ ⟨13, 2, 0, 473597, 286856, 965, 16384⟩
    (by decide) selected_cut_18485

theorem selected_cut_18486 : selected 8 ⟨473634, by decide⟩
    (prefixPartial 13 286857) = some ⟨13, 2, 0, 473634, 286857, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_286857_473634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286857 ⟨473634, by decide⟩ :=
  accepted_of_selected 13 286857 ⟨473634, by decide⟩ ⟨13, 2, 0, 473634, 286857, 2109, 16384⟩
    (by decide) selected_cut_18486

theorem selected_cut_18487 : selected 8 ⟨473652, by decide⟩
    (prefixPartial 13 286858) = some ⟨13, 2, 0, 473652, 286858, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_286858_473652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286858 ⟨473652, by decide⟩ :=
  accepted_of_selected 13 286858 ⟨473652, by decide⟩ ⟨13, 2, 0, 473652, 286858, 1305, 16384⟩
    (by decide) selected_cut_18487

theorem selected_cut_18488 : selected 8 ⟨473658, by decide⟩
    (prefixPartial 13 286859) = some ⟨13, 2, 0, 473658, 286859, 753, 16384⟩ := by
  decide +kernel

theorem context_13_286859_473658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286859 ⟨473658, by decide⟩ :=
  accepted_of_selected 13 286859 ⟨473658, by decide⟩ ⟨13, 2, 0, 473658, 286859, 753, 16384⟩
    (by decide) selected_cut_18488

theorem unmarked_context_12_71714_473659 : frontier 9 ⟨473659, by decide⟩
    (prefixCache 12 71714) (prefixPartial 12 71714) = false := by
  decide +kernel

theorem node_context_12_71714_473659 : EJMOriginalGlobalDAGData.nodes 9 ⟨473659, by decide⟩ =
    .split (coordinate 12) (![⟨473597, by decide⟩,⟨473634, by decide⟩,⟨473652, by decide⟩,⟨473658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71714_473659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71714 ⟨473659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71714
    ⟨473659, by decide⟩ (by decide) (![⟨473597, by decide⟩,⟨473634, by decide⟩,⟨473652, by decide⟩,⟨473658, by decide⟩]) unmarked_context_12_71714_473659 node_context_12_71714_473659
  intro a
  fin_cases a
  · exact context_13_286856_473597
  · exact context_13_286857_473634
  · exact context_13_286858_473652
  · exact context_13_286859_473658

theorem selected_cut_18489 : selected 8 ⟨473676, by decide⟩
    (prefixPartial 13 286860) = some ⟨13, 2, 0, 473676, 286860, 877, 16384⟩ := by
  decide +kernel

theorem context_13_286860_473676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286860 ⟨473676, by decide⟩ :=
  accepted_of_selected 13 286860 ⟨473676, by decide⟩ ⟨13, 2, 0, 473676, 286860, 877, 16384⟩
    (by decide) selected_cut_18489

theorem selected_cut_18490 : selected 8 ⟨473706, by decide⟩
    (prefixPartial 13 286861) = some ⟨13, 2, 0, 473706, 286861, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_286861_473706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286861 ⟨473706, by decide⟩ :=
  accepted_of_selected 13 286861 ⟨473706, by decide⟩ ⟨13, 2, 0, 473706, 286861, 2233, 16384⟩
    (by decide) selected_cut_18490

theorem selected_cut_18491 : selected 8 ⟨473725, by decide⟩
    (prefixPartial 13 286862) = some ⟨13, 2, 0, 473725, 286862, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_286862_473725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286862 ⟨473725, by decide⟩ :=
  accepted_of_selected 13 286862 ⟨473725, by decide⟩ ⟨13, 2, 0, 473725, 286862, 1249, 16384⟩
    (by decide) selected_cut_18491

theorem selected_cut_18492 : selected 8 ⟨473729, by decide⟩
    (prefixPartial 13 286863) = some ⟨13, 2, 0, 473729, 286863, 633, 16384⟩ := by
  decide +kernel

theorem context_13_286863_473729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286863 ⟨473729, by decide⟩ :=
  accepted_of_selected 13 286863 ⟨473729, by decide⟩ ⟨13, 2, 0, 473729, 286863, 633, 16384⟩
    (by decide) selected_cut_18492

theorem unmarked_context_12_71715_473730 : frontier 9 ⟨473730, by decide⟩
    (prefixCache 12 71715) (prefixPartial 12 71715) = false := by
  decide +kernel

theorem node_context_12_71715_473730 : EJMOriginalGlobalDAGData.nodes 9 ⟨473730, by decide⟩ =
    .split (coordinate 12) (![⟨473676, by decide⟩,⟨473706, by decide⟩,⟨473725, by decide⟩,⟨473729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71715_473730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71715 ⟨473730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71715
    ⟨473730, by decide⟩ (by decide) (![⟨473676, by decide⟩,⟨473706, by decide⟩,⟨473725, by decide⟩,⟨473729, by decide⟩]) unmarked_context_12_71715_473730 node_context_12_71715_473730
  intro a
  fin_cases a
  · exact context_13_286860_473676
  · exact context_13_286861_473706
  · exact context_13_286862_473725
  · exact context_13_286863_473729

theorem unmarked_context_11_17928_473731 : frontier 10 ⟨473731, by decide⟩
    (prefixCache 11 17928) (prefixPartial 11 17928) = false := by
  decide +kernel

theorem node_context_11_17928_473731 : EJMOriginalGlobalDAGData.nodes 10 ⟨473731, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨473579, by decide⟩,⟨473659, by decide⟩,⟨473730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17928_473731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17928 ⟨473731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17928
    ⟨473731, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨473579, by decide⟩,⟨473659, by decide⟩,⟨473730, by decide⟩]) unmarked_context_11_17928_473731 node_context_11_17928_473731
  intro a
  fin_cases a
  · exact context_12_71712_435790
  · exact context_12_71713_473579
  · exact context_12_71714_473659
  · exact context_12_71715_473730

theorem selected_cut_18493 : selected 8 ⟨473762, by decide⟩
    (prefixPartial 13 286864) = some ⟨13, 2, 0, 473762, 286864, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_286864_473762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286864 ⟨473762, by decide⟩ :=
  accepted_of_selected 13 286864 ⟨473762, by decide⟩ ⟨13, 2, 0, 473762, 286864, 1301, 16384⟩
    (by decide) selected_cut_18493

theorem selected_cut_18494 : selected 8 ⟨473812, by decide⟩
    (prefixPartial 13 286865) = some ⟨13, 2, 0, 473812, 286865, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_286865_473812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286865 ⟨473812, by decide⟩ :=
  accepted_of_selected 13 286865 ⟨473812, by decide⟩ ⟨13, 2, 0, 473812, 286865, 2861, 16384⟩
    (by decide) selected_cut_18494

theorem selected_cut_18495 : selected 8 ⟨473838, by decide⟩
    (prefixPartial 13 286866) = some ⟨13, 2, 0, 473838, 286866, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_286866_473838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286866 ⟨473838, by decide⟩ :=
  accepted_of_selected 13 286866 ⟨473838, by decide⟩ ⟨13, 2, 0, 473838, 286866, 1785, 16384⟩
    (by decide) selected_cut_18495

theorem selected_cut_18496 : selected 8 ⟨473849, by decide⟩
    (prefixPartial 13 286867) = some ⟨13, 2, 0, 473849, 286867, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_286867_473849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286867 ⟨473849, by decide⟩ :=
  accepted_of_selected 13 286867 ⟨473849, by decide⟩ ⟨13, 2, 0, 473849, 286867, 1041, 16384⟩
    (by decide) selected_cut_18496

theorem unmarked_context_12_71716_473850 : frontier 9 ⟨473850, by decide⟩
    (prefixCache 12 71716) (prefixPartial 12 71716) = false := by
  decide +kernel

theorem node_context_12_71716_473850 : EJMOriginalGlobalDAGData.nodes 9 ⟨473850, by decide⟩ =
    .split (coordinate 12) (![⟨473762, by decide⟩,⟨473812, by decide⟩,⟨473838, by decide⟩,⟨473849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71716_473850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71716 ⟨473850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71716
    ⟨473850, by decide⟩ (by decide) (![⟨473762, by decide⟩,⟨473812, by decide⟩,⟨473838, by decide⟩,⟨473849, by decide⟩]) unmarked_context_12_71716_473850 node_context_12_71716_473850
  intro a
  fin_cases a
  · exact context_13_286864_473762
  · exact context_13_286865_473812
  · exact context_13_286866_473838
  · exact context_13_286867_473849

theorem selected_cut_18497 : selected 8 ⟨473867, by decide⟩
    (prefixPartial 13 286868) = some ⟨13, 2, 0, 473867, 286868, 969, 16384⟩ := by
  decide +kernel

theorem context_13_286868_473867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286868 ⟨473867, by decide⟩ :=
  accepted_of_selected 13 286868 ⟨473867, by decide⟩ ⟨13, 2, 0, 473867, 286868, 969, 16384⟩
    (by decide) selected_cut_18497

theorem selected_cut_18498 : selected 8 ⟨473896, by decide⟩
    (prefixPartial 13 286869) = some ⟨13, 2, 0, 473896, 286869, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_286869_473896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286869 ⟨473896, by decide⟩ :=
  accepted_of_selected 13 286869 ⟨473896, by decide⟩ ⟨13, 2, 0, 473896, 286869, 1869, 16384⟩
    (by decide) selected_cut_18498

theorem selected_cut_18499 : selected 8 ⟨473913, by decide⟩
    (prefixPartial 13 286870) = some ⟨13, 2, 0, 473913, 286870, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_286870_473913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286870 ⟨473913, by decide⟩ :=
  accepted_of_selected 13 286870 ⟨473913, by decide⟩ ⟨13, 2, 0, 473913, 286870, 1121, 16384⟩
    (by decide) selected_cut_18499

theorem selected_cut_18500 : selected 8 ⟨473921, by decide⟩
    (prefixPartial 13 286871) = some ⟨13, 2, 0, 473921, 286871, 797, 16384⟩ := by
  decide +kernel

theorem context_13_286871_473921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286871 ⟨473921, by decide⟩ :=
  accepted_of_selected 13 286871 ⟨473921, by decide⟩ ⟨13, 2, 0, 473921, 286871, 797, 16384⟩
    (by decide) selected_cut_18500

theorem unmarked_context_12_71717_473922 : frontier 9 ⟨473922, by decide⟩
    (prefixCache 12 71717) (prefixPartial 12 71717) = false := by
  decide +kernel

theorem node_context_12_71717_473922 : EJMOriginalGlobalDAGData.nodes 9 ⟨473922, by decide⟩ =
    .split (coordinate 12) (![⟨473867, by decide⟩,⟨473896, by decide⟩,⟨473913, by decide⟩,⟨473921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71717_473922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71717 ⟨473922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71717
    ⟨473922, by decide⟩ (by decide) (![⟨473867, by decide⟩,⟨473896, by decide⟩,⟨473913, by decide⟩,⟨473921, by decide⟩]) unmarked_context_12_71717_473922 node_context_12_71717_473922
  intro a
  fin_cases a
  · exact context_13_286868_473867
  · exact context_13_286869_473896
  · exact context_13_286870_473913
  · exact context_13_286871_473921

theorem selected_cut_18501 : selected 8 ⟨473944, by decide⟩
    (prefixPartial 13 286872) = some ⟨13, 2, 0, 473944, 286872, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_286872_473944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286872 ⟨473944, by decide⟩ :=
  accepted_of_selected 13 286872 ⟨473944, by decide⟩ ⟨13, 2, 0, 473944, 286872, 1133, 16384⟩
    (by decide) selected_cut_18501

theorem selected_cut_18502 : selected 8 ⟨473988, by decide⟩
    (prefixPartial 13 286873) = some ⟨13, 2, 0, 473988, 286873, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_286873_473988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286873 ⟨473988, by decide⟩ :=
  accepted_of_selected 13 286873 ⟨473988, by decide⟩ ⟨13, 2, 0, 473988, 286873, 2453, 16384⟩
    (by decide) selected_cut_18502

theorem selected_cut_18503 : selected 8 ⟨474008, by decide⟩
    (prefixPartial 13 286874) = some ⟨13, 2, 0, 474008, 286874, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_286874_474008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286874 ⟨474008, by decide⟩ :=
  accepted_of_selected 13 286874 ⟨474008, by decide⟩ ⟨13, 2, 0, 474008, 286874, 1289, 16384⟩
    (by decide) selected_cut_18503

theorem selected_cut_18504 : selected 8 ⟨474014, by decide⟩
    (prefixPartial 13 286875) = some ⟨13, 2, 0, 474014, 286875, 857, 16384⟩ := by
  decide +kernel

theorem context_13_286875_474014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286875 ⟨474014, by decide⟩ :=
  accepted_of_selected 13 286875 ⟨474014, by decide⟩ ⟨13, 2, 0, 474014, 286875, 857, 16384⟩
    (by decide) selected_cut_18504

theorem unmarked_context_12_71718_474015 : frontier 9 ⟨474015, by decide⟩
    (prefixCache 12 71718) (prefixPartial 12 71718) = false := by
  decide +kernel

theorem node_context_12_71718_474015 : EJMOriginalGlobalDAGData.nodes 9 ⟨474015, by decide⟩ =
    .split (coordinate 12) (![⟨473944, by decide⟩,⟨473988, by decide⟩,⟨474008, by decide⟩,⟨474014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71718_474015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71718 ⟨474015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71718
    ⟨474015, by decide⟩ (by decide) (![⟨473944, by decide⟩,⟨473988, by decide⟩,⟨474008, by decide⟩,⟨474014, by decide⟩]) unmarked_context_12_71718_474015 node_context_12_71718_474015
  intro a
  fin_cases a
  · exact context_13_286872_473944
  · exact context_13_286873_473988
  · exact context_13_286874_474008
  · exact context_13_286875_474014

theorem selected_cut_18505 : selected 8 ⟨474036, by decide⟩
    (prefixPartial 13 286876) = some ⟨13, 2, 0, 474036, 286876, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_286876_474036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286876 ⟨474036, by decide⟩ :=
  accepted_of_selected 13 286876 ⟨474036, by decide⟩ ⟨13, 2, 0, 474036, 286876, 1109, 16384⟩
    (by decide) selected_cut_18505

theorem selected_cut_18506 : selected 8 ⟨474082, by decide⟩
    (prefixPartial 13 286877) = some ⟨13, 2, 0, 474082, 286877, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_286877_474082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286877 ⟨474082, by decide⟩ :=
  accepted_of_selected 13 286877 ⟨474082, by decide⟩ ⟨13, 2, 0, 474082, 286877, 2693, 16384⟩
    (by decide) selected_cut_18506

theorem selected_cut_18507 : selected 8 ⟨474101, by decide⟩
    (prefixPartial 13 286878) = some ⟨13, 2, 0, 474101, 286878, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_286878_474101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286878 ⟨474101, by decide⟩ :=
  accepted_of_selected 13 286878 ⟨474101, by decide⟩ ⟨13, 2, 0, 474101, 286878, 1257, 16384⟩
    (by decide) selected_cut_18507

theorem selected_cut_18508 : selected 8 ⟨474108, by decide⟩
    (prefixPartial 13 286879) = some ⟨13, 2, 0, 474108, 286879, 793, 16384⟩ := by
  decide +kernel

theorem context_13_286879_474108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286879 ⟨474108, by decide⟩ :=
  accepted_of_selected 13 286879 ⟨474108, by decide⟩ ⟨13, 2, 0, 474108, 286879, 793, 16384⟩
    (by decide) selected_cut_18508

theorem unmarked_context_12_71719_474109 : frontier 9 ⟨474109, by decide⟩
    (prefixCache 12 71719) (prefixPartial 12 71719) = false := by
  decide +kernel

theorem node_context_12_71719_474109 : EJMOriginalGlobalDAGData.nodes 9 ⟨474109, by decide⟩ =
    .split (coordinate 12) (![⟨474036, by decide⟩,⟨474082, by decide⟩,⟨474101, by decide⟩,⟨474108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71719_474109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71719 ⟨474109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71719
    ⟨474109, by decide⟩ (by decide) (![⟨474036, by decide⟩,⟨474082, by decide⟩,⟨474101, by decide⟩,⟨474108, by decide⟩]) unmarked_context_12_71719_474109 node_context_12_71719_474109
  intro a
  fin_cases a
  · exact context_13_286876_474036
  · exact context_13_286877_474082
  · exact context_13_286878_474101
  · exact context_13_286879_474108

theorem unmarked_context_11_17929_474110 : frontier 10 ⟨474110, by decide⟩
    (prefixCache 11 17929) (prefixPartial 11 17929) = false := by
  decide +kernel

theorem node_context_11_17929_474110 : EJMOriginalGlobalDAGData.nodes 10 ⟨474110, by decide⟩ =
    .split (coordinate 11) (![⟨473850, by decide⟩,⟨473922, by decide⟩,⟨474015, by decide⟩,⟨474109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17929_474110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17929 ⟨474110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17929
    ⟨474110, by decide⟩ (by decide) (![⟨473850, by decide⟩,⟨473922, by decide⟩,⟨474015, by decide⟩,⟨474109, by decide⟩]) unmarked_context_11_17929_474110 node_context_11_17929_474110
  intro a
  fin_cases a
  · exact context_12_71716_473850
  · exact context_12_71717_473922
  · exact context_12_71718_474015
  · exact context_12_71719_474109

theorem selected_cut_18509 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 71720) = some ⟨12, 1, 0, 450498, 71720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71720_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71720 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 71720 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 71720, 1, 65536⟩
    (by decide) selected_cut_18509

theorem selected_cut_18510 : selected 8 ⟨474138, by decide⟩
    (prefixPartial 13 286884) = some ⟨13, 2, 0, 474138, 286884, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_286884_474138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286884 ⟨474138, by decide⟩ :=
  accepted_of_selected 13 286884 ⟨474138, by decide⟩ ⟨13, 2, 0, 474138, 286884, 1149, 16384⟩
    (by decide) selected_cut_18510

theorem selected_cut_18511 : selected 8 ⟨474172, by decide⟩
    (prefixPartial 13 286885) = some ⟨13, 2, 0, 474172, 286885, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_286885_474172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286885 ⟨474172, by decide⟩ :=
  accepted_of_selected 13 286885 ⟨474172, by decide⟩ ⟨13, 2, 0, 474172, 286885, 2669, 16384⟩
    (by decide) selected_cut_18511

theorem selected_cut_18512 : selected 8 ⟨474195, by decide⟩
    (prefixPartial 13 286886) = some ⟨13, 2, 0, 474195, 286886, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_286886_474195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286886 ⟨474195, by decide⟩ :=
  accepted_of_selected 13 286886 ⟨474195, by decide⟩ ⟨13, 2, 0, 474195, 286886, 1833, 16384⟩
    (by decide) selected_cut_18512

theorem selected_cut_18513 : selected 8 ⟨474206, by decide⟩
    (prefixPartial 13 286887) = some ⟨13, 2, 0, 474206, 286887, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_286887_474206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286887 ⟨474206, by decide⟩ :=
  accepted_of_selected 13 286887 ⟨474206, by decide⟩ ⟨13, 2, 0, 474206, 286887, 1089, 16384⟩
    (by decide) selected_cut_18513

theorem unmarked_context_12_71721_474207 : frontier 9 ⟨474207, by decide⟩
    (prefixCache 12 71721) (prefixPartial 12 71721) = false := by
  decide +kernel

theorem node_context_12_71721_474207 : EJMOriginalGlobalDAGData.nodes 9 ⟨474207, by decide⟩ =
    .split (coordinate 12) (![⟨474138, by decide⟩,⟨474172, by decide⟩,⟨474195, by decide⟩,⟨474206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71721_474207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71721 ⟨474207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71721
    ⟨474207, by decide⟩ (by decide) (![⟨474138, by decide⟩,⟨474172, by decide⟩,⟨474195, by decide⟩,⟨474206, by decide⟩]) unmarked_context_12_71721_474207 node_context_12_71721_474207
  intro a
  fin_cases a
  · exact context_13_286884_474138
  · exact context_13_286885_474172
  · exact context_13_286886_474195
  · exact context_13_286887_474206

theorem selected_cut_18514 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 71722) = some ⟨12, 1, 0, 474208, 71722, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71722_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71722 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 71722 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 71722, 1, 65536⟩
    (by decide) selected_cut_18514

theorem selected_cut_18515 : selected 8 ⟨474230, by decide⟩
    (prefixPartial 13 286892) = some ⟨13, 2, 0, 474230, 286892, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_286892_474230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286892 ⟨474230, by decide⟩ :=
  accepted_of_selected 13 286892 ⟨474230, by decide⟩ ⟨13, 2, 0, 474230, 286892, 1177, 16384⟩
    (by decide) selected_cut_18515

theorem selected_cut_18516 : selected 8 ⟨474283, by decide⟩
    (prefixPartial 13 286893) = some ⟨13, 2, 0, 474283, 286893, 3465, 16384⟩ := by
  decide +kernel

theorem context_13_286893_474283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286893 ⟨474283, by decide⟩ :=
  accepted_of_selected 13 286893 ⟨474283, by decide⟩ ⟨13, 2, 0, 474283, 286893, 3465, 16384⟩
    (by decide) selected_cut_18516

theorem selected_cut_18517 : selected 8 ⟨474308, by decide⟩
    (prefixPartial 13 286894) = some ⟨13, 2, 0, 474308, 286894, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_286894_474308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286894 ⟨474308, by decide⟩ :=
  accepted_of_selected 13 286894 ⟨474308, by decide⟩ ⟨13, 2, 0, 474308, 286894, 1877, 16384⟩
    (by decide) selected_cut_18517

theorem selected_cut_18518 : selected 8 ⟨474318, by decide⟩
    (prefixPartial 13 286895) = some ⟨13, 2, 0, 474318, 286895, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_286895_474318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286895 ⟨474318, by decide⟩ :=
  accepted_of_selected 13 286895 ⟨474318, by decide⟩ ⟨13, 2, 0, 474318, 286895, 1057, 16384⟩
    (by decide) selected_cut_18518

theorem unmarked_context_12_71723_474319 : frontier 9 ⟨474319, by decide⟩
    (prefixCache 12 71723) (prefixPartial 12 71723) = false := by
  decide +kernel

theorem node_context_12_71723_474319 : EJMOriginalGlobalDAGData.nodes 9 ⟨474319, by decide⟩ =
    .split (coordinate 12) (![⟨474230, by decide⟩,⟨474283, by decide⟩,⟨474308, by decide⟩,⟨474318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71723_474319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71723 ⟨474319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71723
    ⟨474319, by decide⟩ (by decide) (![⟨474230, by decide⟩,⟨474283, by decide⟩,⟨474308, by decide⟩,⟨474318, by decide⟩]) unmarked_context_12_71723_474319 node_context_12_71723_474319
  intro a
  fin_cases a
  · exact context_13_286892_474230
  · exact context_13_286893_474283
  · exact context_13_286894_474308
  · exact context_13_286895_474318

theorem unmarked_context_11_17930_474320 : frontier 10 ⟨474320, by decide⟩
    (prefixCache 11 17930) (prefixPartial 11 17930) = false := by
  decide +kernel

theorem node_context_11_17930_474320 : EJMOriginalGlobalDAGData.nodes 10 ⟨474320, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨474207, by decide⟩,⟨474208, by decide⟩,⟨474319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17930_474320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17930 ⟨474320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17930
    ⟨474320, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨474207, by decide⟩,⟨474208, by decide⟩,⟨474319, by decide⟩]) unmarked_context_11_17930_474320 node_context_11_17930_474320
  intro a
  fin_cases a
  · exact context_12_71720_450498
  · exact context_12_71721_474207
  · exact context_12_71722_474208
  · exact context_12_71723_474319

theorem selected_cut_18519 : selected 8 ⟨474343, by decide⟩
    (prefixPartial 13 286896) = some ⟨13, 2, 0, 474343, 286896, 909, 16384⟩ := by
  decide +kernel

theorem context_13_286896_474343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286896 ⟨474343, by decide⟩ :=
  accepted_of_selected 13 286896 ⟨474343, by decide⟩ ⟨13, 2, 0, 474343, 286896, 909, 16384⟩
    (by decide) selected_cut_18519

theorem selected_cut_18520 : selected 8 ⟨474399, by decide⟩
    (prefixPartial 13 286897) = some ⟨13, 2, 0, 474399, 286897, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_286897_474399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286897 ⟨474399, by decide⟩ :=
  accepted_of_selected 13 286897 ⟨474399, by decide⟩ ⟨13, 2, 0, 474399, 286897, 3173, 16384⟩
    (by decide) selected_cut_18520

theorem selected_cut_18521 : selected 8 ⟨474427, by decide⟩
    (prefixPartial 13 286898) = some ⟨13, 2, 0, 474427, 286898, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_286898_474427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286898 ⟨474427, by decide⟩ :=
  accepted_of_selected 13 286898 ⟨474427, by decide⟩ ⟨13, 2, 0, 474427, 286898, 2129, 16384⟩
    (by decide) selected_cut_18521

theorem selected_cut_18522 : selected 8 ⟨474438, by decide⟩
    (prefixPartial 13 286899) = some ⟨13, 2, 0, 474438, 286899, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_286899_474438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286899 ⟨474438, by decide⟩ :=
  accepted_of_selected 13 286899 ⟨474438, by decide⟩ ⟨13, 2, 0, 474438, 286899, 1001, 16384⟩
    (by decide) selected_cut_18522

theorem unmarked_context_12_71724_474439 : frontier 9 ⟨474439, by decide⟩
    (prefixCache 12 71724) (prefixPartial 12 71724) = false := by
  decide +kernel

theorem node_context_12_71724_474439 : EJMOriginalGlobalDAGData.nodes 9 ⟨474439, by decide⟩ =
    .split (coordinate 12) (![⟨474343, by decide⟩,⟨474399, by decide⟩,⟨474427, by decide⟩,⟨474438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71724_474439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71724 ⟨474439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71724
    ⟨474439, by decide⟩ (by decide) (![⟨474343, by decide⟩,⟨474399, by decide⟩,⟨474427, by decide⟩,⟨474438, by decide⟩]) unmarked_context_12_71724_474439 node_context_12_71724_474439
  intro a
  fin_cases a
  · exact context_13_286896_474343
  · exact context_13_286897_474399
  · exact context_13_286898_474427
  · exact context_13_286899_474438

theorem selected_cut_18523 : selected 8 ⟨474457, by decide⟩
    (prefixPartial 13 286900) = some ⟨13, 2, 0, 474457, 286900, 737, 16384⟩ := by
  decide +kernel

theorem context_13_286900_474457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286900 ⟨474457, by decide⟩ :=
  accepted_of_selected 13 286900 ⟨474457, by decide⟩ ⟨13, 2, 0, 474457, 286900, 737, 16384⟩
    (by decide) selected_cut_18523

theorem selected_cut_18524 : selected 8 ⟨474484, by decide⟩
    (prefixPartial 13 286901) = some ⟨13, 2, 0, 474484, 286901, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_286901_474484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286901 ⟨474484, by decide⟩ :=
  accepted_of_selected 13 286901 ⟨474484, by decide⟩ ⟨13, 2, 0, 474484, 286901, 2285, 16384⟩
    (by decide) selected_cut_18524

theorem selected_cut_18525 : selected 8 ⟨474505, by decide⟩
    (prefixPartial 13 286902) = some ⟨13, 2, 0, 474505, 286902, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_286902_474505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286902 ⟨474505, by decide⟩ :=
  accepted_of_selected 13 286902 ⟨474505, by decide⟩ ⟨13, 2, 0, 474505, 286902, 1685, 16384⟩
    (by decide) selected_cut_18525

theorem selected_cut_18526 : selected 8 ⟨474510, by decide⟩
    (prefixPartial 13 286903) = some ⟨13, 2, 0, 474510, 286903, 873, 16384⟩ := by
  decide +kernel

theorem context_13_286903_474510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286903 ⟨474510, by decide⟩ :=
  accepted_of_selected 13 286903 ⟨474510, by decide⟩ ⟨13, 2, 0, 474510, 286903, 873, 16384⟩
    (by decide) selected_cut_18526

theorem unmarked_context_12_71725_474511 : frontier 9 ⟨474511, by decide⟩
    (prefixCache 12 71725) (prefixPartial 12 71725) = false := by
  decide +kernel

theorem node_context_12_71725_474511 : EJMOriginalGlobalDAGData.nodes 9 ⟨474511, by decide⟩ =
    .split (coordinate 12) (![⟨474457, by decide⟩,⟨474484, by decide⟩,⟨474505, by decide⟩,⟨474510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71725_474511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71725 ⟨474511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71725
    ⟨474511, by decide⟩ (by decide) (![⟨474457, by decide⟩,⟨474484, by decide⟩,⟨474505, by decide⟩,⟨474510, by decide⟩]) unmarked_context_12_71725_474511 node_context_12_71725_474511
  intro a
  fin_cases a
  · exact context_13_286900_474457
  · exact context_13_286901_474484
  · exact context_13_286902_474505
  · exact context_13_286903_474510

theorem selected_cut_18527 : selected 8 ⟨474527, by decide⟩
    (prefixPartial 13 286904) = some ⟨13, 2, 0, 474527, 286904, 705, 16384⟩ := by
  decide +kernel

theorem context_13_286904_474527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286904 ⟨474527, by decide⟩ :=
  accepted_of_selected 13 286904 ⟨474527, by decide⟩ ⟨13, 2, 0, 474527, 286904, 705, 16384⟩
    (by decide) selected_cut_18527

theorem selected_cut_18528 : selected 8 ⟨474565, by decide⟩
    (prefixPartial 13 286905) = some ⟨13, 2, 0, 474565, 286905, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_286905_474565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286905 ⟨474565, by decide⟩ :=
  accepted_of_selected 13 286905 ⟨474565, by decide⟩ ⟨13, 2, 0, 474565, 286905, 2749, 16384⟩
    (by decide) selected_cut_18528

theorem selected_cut_18529 : selected 8 ⟨474587, by decide⟩
    (prefixPartial 13 286906) = some ⟨13, 2, 0, 474587, 286906, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_286906_474587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286906 ⟨474587, by decide⟩ :=
  accepted_of_selected 13 286906 ⟨474587, by decide⟩ ⟨13, 2, 0, 474587, 286906, 1801, 16384⟩
    (by decide) selected_cut_18529

theorem selected_cut_18530 : selected 8 ⟨474592, by decide⟩
    (prefixPartial 13 286907) = some ⟨13, 2, 0, 474592, 286907, 829, 16384⟩ := by
  decide +kernel

theorem context_13_286907_474592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286907 ⟨474592, by decide⟩ :=
  accepted_of_selected 13 286907 ⟨474592, by decide⟩ ⟨13, 2, 0, 474592, 286907, 829, 16384⟩
    (by decide) selected_cut_18530

theorem unmarked_context_12_71726_474593 : frontier 9 ⟨474593, by decide⟩
    (prefixCache 12 71726) (prefixPartial 12 71726) = false := by
  decide +kernel

theorem node_context_12_71726_474593 : EJMOriginalGlobalDAGData.nodes 9 ⟨474593, by decide⟩ =
    .split (coordinate 12) (![⟨474527, by decide⟩,⟨474565, by decide⟩,⟨474587, by decide⟩,⟨474592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71726_474593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71726 ⟨474593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71726
    ⟨474593, by decide⟩ (by decide) (![⟨474527, by decide⟩,⟨474565, by decide⟩,⟨474587, by decide⟩,⟨474592, by decide⟩]) unmarked_context_12_71726_474593 node_context_12_71726_474593
  intro a
  fin_cases a
  · exact context_13_286904_474527
  · exact context_13_286905_474565
  · exact context_13_286906_474587
  · exact context_13_286907_474592

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
