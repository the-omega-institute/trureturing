/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover153
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14788 : selected 8 ⟨381086, by decide⟩
    (prefixPartial 13 109723) = some ⟨13, 2, 0, 381086, 109723, 845, 16384⟩ := by
  decide +kernel

theorem context_13_109723_381086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109723 ⟨381086, by decide⟩ :=
  accepted_of_selected 13 109723 ⟨381086, by decide⟩ ⟨13, 2, 0, 381086, 109723, 845, 16384⟩
    (by decide) selected_cut_14788

theorem unmarked_context_12_27430_381087 : frontier 9 ⟨381087, by decide⟩
    (prefixCache 12 27430) (prefixPartial 12 27430) = false := by
  decide +kernel

theorem node_context_12_27430_381087 : EJMOriginalGlobalDAGData.nodes 9 ⟨381087, by decide⟩ =
    .split (coordinate 12) (![⟨381041, by decide⟩,⟨381066, by decide⟩,⟨381082, by decide⟩,⟨381086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27430_381087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27430 ⟨381087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27430
    ⟨381087, by decide⟩ (by decide) (![⟨381041, by decide⟩,⟨381066, by decide⟩,⟨381082, by decide⟩,⟨381086, by decide⟩]) unmarked_context_12_27430_381087 node_context_12_27430_381087
  intro a
  fin_cases a
  · exact context_13_109720_381041
  · exact context_13_109721_381066
  · exact context_13_109722_381082
  · exact context_13_109723_381086

theorem selected_cut_14789 : selected 8 ⟨381098, by decide⟩
    (prefixPartial 13 109724) = some ⟨13, 2, 0, 381098, 109724, 801, 16384⟩ := by
  decide +kernel

theorem context_13_109724_381098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109724 ⟨381098, by decide⟩ :=
  accepted_of_selected 13 109724 ⟨381098, by decide⟩ ⟨13, 2, 0, 381098, 109724, 801, 16384⟩
    (by decide) selected_cut_14789

theorem selected_cut_14790 : selected 8 ⟨381122, by decide⟩
    (prefixPartial 13 109725) = some ⟨13, 2, 0, 381122, 109725, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_109725_381122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109725 ⟨381122, by decide⟩ :=
  accepted_of_selected 13 109725 ⟨381122, by decide⟩ ⟨13, 2, 0, 381122, 109725, 2017, 16384⟩
    (by decide) selected_cut_14790

theorem selected_cut_14791 : selected 8 ⟨381138, by decide⟩
    (prefixPartial 13 109726) = some ⟨13, 2, 0, 381138, 109726, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_109726_381138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109726 ⟨381138, by decide⟩ :=
  accepted_of_selected 13 109726 ⟨381138, by decide⟩ ⟨13, 2, 0, 381138, 109726, 1349, 16384⟩
    (by decide) selected_cut_14791

theorem selected_cut_14792 : selected 8 ⟨381145, by decide⟩
    (prefixPartial 13 109727) = some ⟨13, 2, 0, 381145, 109727, 801, 16384⟩ := by
  decide +kernel

theorem context_13_109727_381145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109727 ⟨381145, by decide⟩ :=
  accepted_of_selected 13 109727 ⟨381145, by decide⟩ ⟨13, 2, 0, 381145, 109727, 801, 16384⟩
    (by decide) selected_cut_14792

theorem unmarked_context_12_27431_381146 : frontier 9 ⟨381146, by decide⟩
    (prefixCache 12 27431) (prefixPartial 12 27431) = false := by
  decide +kernel

theorem node_context_12_27431_381146 : EJMOriginalGlobalDAGData.nodes 9 ⟨381146, by decide⟩ =
    .split (coordinate 12) (![⟨381098, by decide⟩,⟨381122, by decide⟩,⟨381138, by decide⟩,⟨381145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27431_381146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27431 ⟨381146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27431
    ⟨381146, by decide⟩ (by decide) (![⟨381098, by decide⟩,⟨381122, by decide⟩,⟨381138, by decide⟩,⟨381145, by decide⟩]) unmarked_context_12_27431_381146 node_context_12_27431_381146
  intro a
  fin_cases a
  · exact context_13_109724_381098
  · exact context_13_109725_381122
  · exact context_13_109726_381138
  · exact context_13_109727_381145

theorem unmarked_context_11_6857_381147 : frontier 10 ⟨381147, by decide⟩
    (prefixCache 11 6857) (prefixPartial 11 6857) = false := by
  decide +kernel

theorem node_context_11_6857_381147 : EJMOriginalGlobalDAGData.nodes 10 ⟨381147, by decide⟩ =
    .split (coordinate 11) (![⟨380972, by decide⟩,⟨381031, by decide⟩,⟨381087, by decide⟩,⟨381146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6857_381147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6857 ⟨381147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6857
    ⟨381147, by decide⟩ (by decide) (![⟨380972, by decide⟩,⟨381031, by decide⟩,⟨381087, by decide⟩,⟨381146, by decide⟩]) unmarked_context_11_6857_381147 node_context_11_6857_381147
  intro a
  fin_cases a
  · exact context_12_27428_380972
  · exact context_12_27429_381031
  · exact context_12_27430_381087
  · exact context_12_27431_381146

theorem selected_cut_14793 : selected 8 ⟨381158, by decide⟩
    (prefixPartial 13 109728) = some ⟨13, 2, 0, 381158, 109728, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_109728_381158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109728 ⟨381158, by decide⟩ :=
  accepted_of_selected 13 109728 ⟨381158, by decide⟩ ⟨13, 2, 0, 381158, 109728, 1049, 16384⟩
    (by decide) selected_cut_14793

theorem selected_cut_14794 : selected 8 ⟨381216, by decide⟩
    (prefixPartial 13 109729) = some ⟨13, 2, 0, 381216, 109729, 3485, 16384⟩ := by
  decide +kernel

theorem context_13_109729_381216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109729 ⟨381216, by decide⟩ :=
  accepted_of_selected 13 109729 ⟨381216, by decide⟩ ⟨13, 2, 0, 381216, 109729, 3485, 16384⟩
    (by decide) selected_cut_14794

theorem selected_cut_14795 : selected 8 ⟨381234, by decide⟩
    (prefixPartial 13 109730) = some ⟨13, 2, 0, 381234, 109730, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_109730_381234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109730 ⟨381234, by decide⟩ :=
  accepted_of_selected 13 109730 ⟨381234, by decide⟩ ⟨13, 2, 0, 381234, 109730, 1757, 16384⟩
    (by decide) selected_cut_14795

theorem selected_cut_14796 : selected 8 ⟨381249, by decide⟩
    (prefixPartial 13 109731) = some ⟨13, 2, 0, 381249, 109731, 989, 16384⟩ := by
  decide +kernel

theorem context_13_109731_381249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109731 ⟨381249, by decide⟩ :=
  accepted_of_selected 13 109731 ⟨381249, by decide⟩ ⟨13, 2, 0, 381249, 109731, 989, 16384⟩
    (by decide) selected_cut_14796

theorem unmarked_context_12_27432_381250 : frontier 9 ⟨381250, by decide⟩
    (prefixCache 12 27432) (prefixPartial 12 27432) = false := by
  decide +kernel

theorem node_context_12_27432_381250 : EJMOriginalGlobalDAGData.nodes 9 ⟨381250, by decide⟩ =
    .split (coordinate 12) (![⟨381158, by decide⟩,⟨381216, by decide⟩,⟨381234, by decide⟩,⟨381249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27432_381250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27432 ⟨381250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27432
    ⟨381250, by decide⟩ (by decide) (![⟨381158, by decide⟩,⟨381216, by decide⟩,⟨381234, by decide⟩,⟨381249, by decide⟩]) unmarked_context_12_27432_381250 node_context_12_27432_381250
  intro a
  fin_cases a
  · exact context_13_109728_381158
  · exact context_13_109729_381216
  · exact context_13_109730_381234
  · exact context_13_109731_381249

theorem selected_cut_14797 : selected 8 ⟨381270, by decide⟩
    (prefixPartial 13 109732) = some ⟨13, 2, 0, 381270, 109732, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_109732_381270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109732 ⟨381270, by decide⟩ :=
  accepted_of_selected 13 109732 ⟨381270, by decide⟩ ⟨13, 2, 0, 381270, 109732, 1157, 16384⟩
    (by decide) selected_cut_14797

theorem selected_cut_14798 : selected 8 ⟨381336, by decide⟩
    (prefixPartial 13 109733) = some ⟨13, 2, 0, 381336, 109733, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_109733_381336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109733 ⟨381336, by decide⟩ :=
  accepted_of_selected 13 109733 ⟨381336, by decide⟩ ⟨13, 2, 0, 381336, 109733, 3477, 16384⟩
    (by decide) selected_cut_14798

theorem selected_cut_14799 : selected 8 ⟨381357, by decide⟩
    (prefixPartial 13 109734) = some ⟨13, 2, 0, 381357, 109734, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_109734_381357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109734 ⟨381357, by decide⟩ :=
  accepted_of_selected 13 109734 ⟨381357, by decide⟩ ⟨13, 2, 0, 381357, 109734, 1769, 16384⟩
    (by decide) selected_cut_14799

theorem selected_cut_14800 : selected 8 ⟨381372, by decide⟩
    (prefixPartial 13 109735) = some ⟨13, 2, 0, 381372, 109735, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_109735_381372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109735 ⟨381372, by decide⟩ :=
  accepted_of_selected 13 109735 ⟨381372, by decide⟩ ⟨13, 2, 0, 381372, 109735, 1025, 16384⟩
    (by decide) selected_cut_14800

theorem unmarked_context_12_27433_381373 : frontier 9 ⟨381373, by decide⟩
    (prefixCache 12 27433) (prefixPartial 12 27433) = false := by
  decide +kernel

theorem node_context_12_27433_381373 : EJMOriginalGlobalDAGData.nodes 9 ⟨381373, by decide⟩ =
    .split (coordinate 12) (![⟨381270, by decide⟩,⟨381336, by decide⟩,⟨381357, by decide⟩,⟨381372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27433_381373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27433 ⟨381373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27433
    ⟨381373, by decide⟩ (by decide) (![⟨381270, by decide⟩,⟨381336, by decide⟩,⟨381357, by decide⟩,⟨381372, by decide⟩]) unmarked_context_12_27433_381373 node_context_12_27433_381373
  intro a
  fin_cases a
  · exact context_13_109732_381270
  · exact context_13_109733_381336
  · exact context_13_109734_381357
  · exact context_13_109735_381372

theorem selected_cut_14801 : selected 9 ⟨381598, by decide⟩
    (prefixPartial 12 27434) = some ⟨12, 2, 0, 381598, 27434, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_27434_381598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27434 ⟨381598, by decide⟩ :=
  accepted_of_selected 12 27434 ⟨381598, by decide⟩ ⟨12, 2, 0, 381598, 27434, 3729, 65536⟩
    (by decide) selected_cut_14801

theorem selected_cut_14802 : selected 8 ⟨381608, by decide⟩
    (prefixPartial 13 109740) = some ⟨13, 2, 0, 381608, 109740, 985, 16384⟩ := by
  decide +kernel

theorem context_13_109740_381608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109740 ⟨381608, by decide⟩ :=
  accepted_of_selected 13 109740 ⟨381608, by decide⟩ ⟨13, 2, 0, 381608, 109740, 985, 16384⟩
    (by decide) selected_cut_14802

theorem selected_cut_14803 : selected 8 ⟨381675, by decide⟩
    (prefixPartial 13 109741) = some ⟨13, 2, 0, 381675, 109741, 3557, 16384⟩ := by
  decide +kernel

theorem context_13_109741_381675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109741 ⟨381675, by decide⟩ :=
  accepted_of_selected 13 109741 ⟨381675, by decide⟩ ⟨13, 2, 0, 381675, 109741, 3557, 16384⟩
    (by decide) selected_cut_14803

theorem selected_cut_14804 : selected 8 ⟨381693, by decide⟩
    (prefixPartial 13 109742) = some ⟨13, 2, 0, 381693, 109742, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_109742_381693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109742 ⟨381693, by decide⟩ :=
  accepted_of_selected 13 109742 ⟨381693, by decide⟩ ⟨13, 2, 0, 381693, 109742, 1573, 16384⟩
    (by decide) selected_cut_14804

theorem selected_cut_14805 : selected 8 ⟨381701, by decide⟩
    (prefixPartial 13 109743) = some ⟨13, 2, 0, 381701, 109743, 829, 16384⟩ := by
  decide +kernel

theorem context_13_109743_381701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109743 ⟨381701, by decide⟩ :=
  accepted_of_selected 13 109743 ⟨381701, by decide⟩ ⟨13, 2, 0, 381701, 109743, 829, 16384⟩
    (by decide) selected_cut_14805

theorem unmarked_context_12_27435_381702 : frontier 9 ⟨381702, by decide⟩
    (prefixCache 12 27435) (prefixPartial 12 27435) = false := by
  decide +kernel

theorem node_context_12_27435_381702 : EJMOriginalGlobalDAGData.nodes 9 ⟨381702, by decide⟩ =
    .split (coordinate 12) (![⟨381608, by decide⟩,⟨381675, by decide⟩,⟨381693, by decide⟩,⟨381701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27435_381702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27435 ⟨381702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27435
    ⟨381702, by decide⟩ (by decide) (![⟨381608, by decide⟩,⟨381675, by decide⟩,⟨381693, by decide⟩,⟨381701, by decide⟩]) unmarked_context_12_27435_381702 node_context_12_27435_381702
  intro a
  fin_cases a
  · exact context_13_109740_381608
  · exact context_13_109741_381675
  · exact context_13_109742_381693
  · exact context_13_109743_381701

theorem unmarked_context_11_6858_381703 : frontier 10 ⟨381703, by decide⟩
    (prefixCache 11 6858) (prefixPartial 11 6858) = false := by
  decide +kernel

theorem node_context_11_6858_381703 : EJMOriginalGlobalDAGData.nodes 10 ⟨381703, by decide⟩ =
    .split (coordinate 11) (![⟨381250, by decide⟩,⟨381373, by decide⟩,⟨381598, by decide⟩,⟨381702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6858_381703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6858 ⟨381703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6858
    ⟨381703, by decide⟩ (by decide) (![⟨381250, by decide⟩,⟨381373, by decide⟩,⟨381598, by decide⟩,⟨381702, by decide⟩]) unmarked_context_11_6858_381703 node_context_11_6858_381703
  intro a
  fin_cases a
  · exact context_12_27432_381250
  · exact context_12_27433_381373
  · exact context_12_27434_381598
  · exact context_12_27435_381702

theorem selected_cut_14806 : selected 8 ⟨381710, by decide⟩
    (prefixPartial 13 109744) = some ⟨13, 2, 0, 381710, 109744, 617, 16384⟩ := by
  decide +kernel

theorem context_13_109744_381710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109744 ⟨381710, by decide⟩ :=
  accepted_of_selected 13 109744 ⟨381710, by decide⟩ ⟨13, 2, 0, 381710, 109744, 617, 16384⟩
    (by decide) selected_cut_14806

theorem selected_cut_14807 : selected 8 ⟨381743, by decide⟩
    (prefixPartial 13 109745) = some ⟨13, 2, 0, 381743, 109745, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_109745_381743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109745 ⟨381743, by decide⟩ :=
  accepted_of_selected 13 109745 ⟨381743, by decide⟩ ⟨13, 2, 0, 381743, 109745, 2213, 16384⟩
    (by decide) selected_cut_14807

theorem selected_cut_14808 : selected 8 ⟨381759, by decide⟩
    (prefixPartial 13 109746) = some ⟨13, 2, 0, 381759, 109746, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_109746_381759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109746 ⟨381759, by decide⟩ :=
  accepted_of_selected 13 109746 ⟨381759, by decide⟩ ⟨13, 2, 0, 381759, 109746, 1117, 16384⟩
    (by decide) selected_cut_14808

theorem selected_cut_14809 : selected 8 ⟨381763, by decide⟩
    (prefixPartial 13 109747) = some ⟨13, 2, 0, 381763, 109747, 745, 16384⟩ := by
  decide +kernel

theorem context_13_109747_381763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109747 ⟨381763, by decide⟩ :=
  accepted_of_selected 13 109747 ⟨381763, by decide⟩ ⟨13, 2, 0, 381763, 109747, 745, 16384⟩
    (by decide) selected_cut_14809

theorem unmarked_context_12_27436_381764 : frontier 9 ⟨381764, by decide⟩
    (prefixCache 12 27436) (prefixPartial 12 27436) = false := by
  decide +kernel

theorem node_context_12_27436_381764 : EJMOriginalGlobalDAGData.nodes 9 ⟨381764, by decide⟩ =
    .split (coordinate 12) (![⟨381710, by decide⟩,⟨381743, by decide⟩,⟨381759, by decide⟩,⟨381763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27436_381764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27436 ⟨381764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27436
    ⟨381764, by decide⟩ (by decide) (![⟨381710, by decide⟩,⟨381743, by decide⟩,⟨381759, by decide⟩,⟨381763, by decide⟩]) unmarked_context_12_27436_381764 node_context_12_27436_381764
  intro a
  fin_cases a
  · exact context_13_109744_381710
  · exact context_13_109745_381743
  · exact context_13_109746_381759
  · exact context_13_109747_381763

theorem selected_cut_14810 : selected 8 ⟨381777, by decide⟩
    (prefixPartial 13 109748) = some ⟨13, 2, 0, 381777, 109748, 733, 16384⟩ := by
  decide +kernel

theorem context_13_109748_381777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109748 ⟨381777, by decide⟩ :=
  accepted_of_selected 13 109748 ⟨381777, by decide⟩ ⟨13, 2, 0, 381777, 109748, 733, 16384⟩
    (by decide) selected_cut_14810

theorem selected_cut_14811 : selected 8 ⟨381809, by decide⟩
    (prefixPartial 13 109749) = some ⟨13, 2, 0, 381809, 109749, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_109749_381809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109749 ⟨381809, by decide⟩ :=
  accepted_of_selected 13 109749 ⟨381809, by decide⟩ ⟨13, 2, 0, 381809, 109749, 2097, 16384⟩
    (by decide) selected_cut_14811

theorem selected_cut_14812 : selected 8 ⟨381825, by decide⟩
    (prefixPartial 13 109750) = some ⟨13, 2, 0, 381825, 109750, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_109750_381825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109750 ⟨381825, by decide⟩ :=
  accepted_of_selected 13 109750 ⟨381825, by decide⟩ ⟨13, 2, 0, 381825, 109750, 1285, 16384⟩
    (by decide) selected_cut_14812

theorem selected_cut_14813 : selected 8 ⟨381829, by decide⟩
    (prefixPartial 13 109751) = some ⟨13, 2, 0, 381829, 109751, 677, 16384⟩ := by
  decide +kernel

theorem context_13_109751_381829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109751 ⟨381829, by decide⟩ :=
  accepted_of_selected 13 109751 ⟨381829, by decide⟩ ⟨13, 2, 0, 381829, 109751, 677, 16384⟩
    (by decide) selected_cut_14813

theorem unmarked_context_12_27437_381830 : frontier 9 ⟨381830, by decide⟩
    (prefixCache 12 27437) (prefixPartial 12 27437) = false := by
  decide +kernel

theorem node_context_12_27437_381830 : EJMOriginalGlobalDAGData.nodes 9 ⟨381830, by decide⟩ =
    .split (coordinate 12) (![⟨381777, by decide⟩,⟨381809, by decide⟩,⟨381825, by decide⟩,⟨381829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27437_381830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27437 ⟨381830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27437
    ⟨381830, by decide⟩ (by decide) (![⟨381777, by decide⟩,⟨381809, by decide⟩,⟨381825, by decide⟩,⟨381829, by decide⟩]) unmarked_context_12_27437_381830 node_context_12_27437_381830
  intro a
  fin_cases a
  · exact context_13_109748_381777
  · exact context_13_109749_381809
  · exact context_13_109750_381825
  · exact context_13_109751_381829

theorem selected_cut_14814 : selected 8 ⟨381844, by decide⟩
    (prefixPartial 13 109752) = some ⟨13, 2, 0, 381844, 109752, 701, 16384⟩ := by
  decide +kernel

theorem context_13_109752_381844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109752 ⟨381844, by decide⟩ :=
  accepted_of_selected 13 109752 ⟨381844, by decide⟩ ⟨13, 2, 0, 381844, 109752, 701, 16384⟩
    (by decide) selected_cut_14814

theorem selected_cut_14815 : selected 8 ⟨381878, by decide⟩
    (prefixPartial 13 109753) = some ⟨13, 2, 0, 381878, 109753, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_109753_381878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109753 ⟨381878, by decide⟩ :=
  accepted_of_selected 13 109753 ⟨381878, by decide⟩ ⟨13, 2, 0, 381878, 109753, 2253, 16384⟩
    (by decide) selected_cut_14815

theorem selected_cut_14816 : selected 8 ⟨381892, by decide⟩
    (prefixPartial 13 109754) = some ⟨13, 2, 0, 381892, 109754, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_109754_381892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109754 ⟨381892, by decide⟩ :=
  accepted_of_selected 13 109754 ⟨381892, by decide⟩ ⟨13, 2, 0, 381892, 109754, 1141, 16384⟩
    (by decide) selected_cut_14816

theorem selected_cut_14817 : selected 8 ⟨381897, by decide⟩
    (prefixPartial 13 109755) = some ⟨13, 2, 0, 381897, 109755, 657, 16384⟩ := by
  decide +kernel

theorem context_13_109755_381897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109755 ⟨381897, by decide⟩ :=
  accepted_of_selected 13 109755 ⟨381897, by decide⟩ ⟨13, 2, 0, 381897, 109755, 657, 16384⟩
    (by decide) selected_cut_14817

theorem unmarked_context_12_27438_381898 : frontier 9 ⟨381898, by decide⟩
    (prefixCache 12 27438) (prefixPartial 12 27438) = false := by
  decide +kernel

theorem node_context_12_27438_381898 : EJMOriginalGlobalDAGData.nodes 9 ⟨381898, by decide⟩ =
    .split (coordinate 12) (![⟨381844, by decide⟩,⟨381878, by decide⟩,⟨381892, by decide⟩,⟨381897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27438_381898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27438 ⟨381898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27438
    ⟨381898, by decide⟩ (by decide) (![⟨381844, by decide⟩,⟨381878, by decide⟩,⟨381892, by decide⟩,⟨381897, by decide⟩]) unmarked_context_12_27438_381898 node_context_12_27438_381898
  intro a
  fin_cases a
  · exact context_13_109752_381844
  · exact context_13_109753_381878
  · exact context_13_109754_381892
  · exact context_13_109755_381897

theorem selected_cut_14818 : selected 8 ⟨381914, by decide⟩
    (prefixPartial 13 109756) = some ⟨13, 2, 0, 381914, 109756, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_109756_381914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109756 ⟨381914, by decide⟩ :=
  accepted_of_selected 13 109756 ⟨381914, by decide⟩ ⟨13, 2, 0, 381914, 109756, 1045, 16384⟩
    (by decide) selected_cut_14818

theorem selected_cut_14819 : selected 8 ⟨382008, by decide⟩
    (prefixPartial 13 109757) = some ⟨13, 2, 0, 382008, 109757, 3793, 16384⟩ := by
  decide +kernel

theorem context_13_109757_382008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109757 ⟨382008, by decide⟩ :=
  accepted_of_selected 13 109757 ⟨382008, by decide⟩ ⟨13, 2, 0, 382008, 109757, 3793, 16384⟩
    (by decide) selected_cut_14819

theorem selected_cut_14820 : selected 8 ⟨382029, by decide⟩
    (prefixPartial 13 109758) = some ⟨13, 2, 0, 382029, 109758, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_109758_382029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109758 ⟨382029, by decide⟩ :=
  accepted_of_selected 13 109758 ⟨382029, by decide⟩ ⟨13, 2, 0, 382029, 109758, 2001, 16384⟩
    (by decide) selected_cut_14820

theorem selected_cut_14821 : selected 8 ⟨382040, by decide⟩
    (prefixPartial 13 109759) = some ⟨13, 2, 0, 382040, 109759, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_109759_382040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109759 ⟨382040, by decide⟩ :=
  accepted_of_selected 13 109759 ⟨382040, by decide⟩ ⟨13, 2, 0, 382040, 109759, 1013, 16384⟩
    (by decide) selected_cut_14821

theorem unmarked_context_12_27439_382041 : frontier 9 ⟨382041, by decide⟩
    (prefixCache 12 27439) (prefixPartial 12 27439) = false := by
  decide +kernel

theorem node_context_12_27439_382041 : EJMOriginalGlobalDAGData.nodes 9 ⟨382041, by decide⟩ =
    .split (coordinate 12) (![⟨381914, by decide⟩,⟨382008, by decide⟩,⟨382029, by decide⟩,⟨382040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27439_382041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27439 ⟨382041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27439
    ⟨382041, by decide⟩ (by decide) (![⟨381914, by decide⟩,⟨382008, by decide⟩,⟨382029, by decide⟩,⟨382040, by decide⟩]) unmarked_context_12_27439_382041 node_context_12_27439_382041
  intro a
  fin_cases a
  · exact context_13_109756_381914
  · exact context_13_109757_382008
  · exact context_13_109758_382029
  · exact context_13_109759_382040

theorem unmarked_context_11_6859_382042 : frontier 10 ⟨382042, by decide⟩
    (prefixCache 11 6859) (prefixPartial 11 6859) = false := by
  decide +kernel

theorem node_context_11_6859_382042 : EJMOriginalGlobalDAGData.nodes 10 ⟨382042, by decide⟩ =
    .split (coordinate 11) (![⟨381764, by decide⟩,⟨381830, by decide⟩,⟨381898, by decide⟩,⟨382041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6859_382042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6859 ⟨382042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6859
    ⟨382042, by decide⟩ (by decide) (![⟨381764, by decide⟩,⟨381830, by decide⟩,⟨381898, by decide⟩,⟨382041, by decide⟩]) unmarked_context_11_6859_382042 node_context_11_6859_382042
  intro a
  fin_cases a
  · exact context_12_27436_381764
  · exact context_12_27437_381830
  · exact context_12_27438_381898
  · exact context_12_27439_382041

theorem unmarked_context_10_1714_382043 : frontier 11 ⟨382043, by decide⟩
    (prefixCache 10 1714) (prefixPartial 10 1714) = false := by
  decide +kernel

theorem node_context_10_1714_382043 : EJMOriginalGlobalDAGData.nodes 11 ⟨382043, by decide⟩ =
    .split (coordinate 10) (![⟨380909, by decide⟩,⟨381147, by decide⟩,⟨381703, by decide⟩,⟨382042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1714_382043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1714 ⟨382043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1714
    ⟨382043, by decide⟩ (by decide) (![⟨380909, by decide⟩,⟨381147, by decide⟩,⟨381703, by decide⟩,⟨382042, by decide⟩]) unmarked_context_10_1714_382043 node_context_10_1714_382043
  intro a
  fin_cases a
  · exact context_11_6856_380909
  · exact context_11_6857_381147
  · exact context_11_6858_381703
  · exact context_11_6859_382042

theorem selected_cut_14822 : selected 8 ⟨382049, by decide⟩
    (prefixPartial 13 109760) = some ⟨13, 2, 0, 382049, 109760, 573, 16384⟩ := by
  decide +kernel

theorem context_13_109760_382049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109760 ⟨382049, by decide⟩ :=
  accepted_of_selected 13 109760 ⟨382049, by decide⟩ ⟨13, 2, 0, 382049, 109760, 573, 16384⟩
    (by decide) selected_cut_14822

theorem selected_cut_14823 : selected 8 ⟨382071, by decide⟩
    (prefixPartial 13 109761) = some ⟨13, 2, 0, 382071, 109761, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_109761_382071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109761 ⟨382071, by decide⟩ :=
  accepted_of_selected 13 109761 ⟨382071, by decide⟩ ⟨13, 2, 0, 382071, 109761, 2281, 16384⟩
    (by decide) selected_cut_14823

theorem selected_cut_14824 : selected 8 ⟨382087, by decide⟩
    (prefixPartial 13 109762) = some ⟨13, 2, 0, 382087, 109762, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_109762_382087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109762 ⟨382087, by decide⟩ :=
  accepted_of_selected 13 109762 ⟨382087, by decide⟩ ⟨13, 2, 0, 382087, 109762, 1289, 16384⟩
    (by decide) selected_cut_14824

theorem selected_cut_14825 : selected 8 ⟨382092, by decide⟩
    (prefixPartial 13 109763) = some ⟨13, 2, 0, 382092, 109763, 813, 16384⟩ := by
  decide +kernel

theorem context_13_109763_382092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109763 ⟨382092, by decide⟩ :=
  accepted_of_selected 13 109763 ⟨382092, by decide⟩ ⟨13, 2, 0, 382092, 109763, 813, 16384⟩
    (by decide) selected_cut_14825

theorem unmarked_context_12_27440_382093 : frontier 9 ⟨382093, by decide⟩
    (prefixCache 12 27440) (prefixPartial 12 27440) = false := by
  decide +kernel

theorem node_context_12_27440_382093 : EJMOriginalGlobalDAGData.nodes 9 ⟨382093, by decide⟩ =
    .split (coordinate 12) (![⟨382049, by decide⟩,⟨382071, by decide⟩,⟨382087, by decide⟩,⟨382092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27440_382093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27440 ⟨382093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27440
    ⟨382093, by decide⟩ (by decide) (![⟨382049, by decide⟩,⟨382071, by decide⟩,⟨382087, by decide⟩,⟨382092, by decide⟩]) unmarked_context_12_27440_382093 node_context_12_27440_382093
  intro a
  fin_cases a
  · exact context_13_109760_382049
  · exact context_13_109761_382071
  · exact context_13_109762_382087
  · exact context_13_109763_382092

theorem selected_cut_14826 : selected 8 ⟨382099, by decide⟩
    (prefixPartial 13 109764) = some ⟨13, 2, 0, 382099, 109764, 625, 16384⟩ := by
  decide +kernel

theorem context_13_109764_382099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109764 ⟨382099, by decide⟩ :=
  accepted_of_selected 13 109764 ⟨382099, by decide⟩ ⟨13, 2, 0, 382099, 109764, 625, 16384⟩
    (by decide) selected_cut_14826

theorem selected_cut_14827 : selected 8 ⟨382132, by decide⟩
    (prefixPartial 13 109765) = some ⟨13, 2, 0, 382132, 109765, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_109765_382132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109765 ⟨382132, by decide⟩ :=
  accepted_of_selected 13 109765 ⟨382132, by decide⟩ ⟨13, 2, 0, 382132, 109765, 2401, 16384⟩
    (by decide) selected_cut_14827

theorem selected_cut_14828 : selected 8 ⟨382150, by decide⟩
    (prefixPartial 13 109766) = some ⟨13, 2, 0, 382150, 109766, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_109766_382150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109766 ⟨382150, by decide⟩ :=
  accepted_of_selected 13 109766 ⟨382150, by decide⟩ ⟨13, 2, 0, 382150, 109766, 1589, 16384⟩
    (by decide) selected_cut_14828

theorem selected_cut_14829 : selected 8 ⟨382154, by decide⟩
    (prefixPartial 13 109767) = some ⟨13, 2, 0, 382154, 109767, 733, 16384⟩ := by
  decide +kernel

theorem context_13_109767_382154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109767 ⟨382154, by decide⟩ :=
  accepted_of_selected 13 109767 ⟨382154, by decide⟩ ⟨13, 2, 0, 382154, 109767, 733, 16384⟩
    (by decide) selected_cut_14829

theorem unmarked_context_12_27441_382155 : frontier 9 ⟨382155, by decide⟩
    (prefixCache 12 27441) (prefixPartial 12 27441) = false := by
  decide +kernel

theorem node_context_12_27441_382155 : EJMOriginalGlobalDAGData.nodes 9 ⟨382155, by decide⟩ =
    .split (coordinate 12) (![⟨382099, by decide⟩,⟨382132, by decide⟩,⟨382150, by decide⟩,⟨382154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27441_382155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27441 ⟨382155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27441
    ⟨382155, by decide⟩ (by decide) (![⟨382099, by decide⟩,⟨382132, by decide⟩,⟨382150, by decide⟩,⟨382154, by decide⟩]) unmarked_context_12_27441_382155 node_context_12_27441_382155
  intro a
  fin_cases a
  · exact context_13_109764_382099
  · exact context_13_109765_382132
  · exact context_13_109766_382150
  · exact context_13_109767_382154

theorem selected_cut_14830 : selected 8 ⟨382160, by decide⟩
    (prefixPartial 13 109768) = some ⟨13, 2, 0, 382160, 109768, 569, 16384⟩ := by
  decide +kernel

theorem context_13_109768_382160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109768 ⟨382160, by decide⟩ :=
  accepted_of_selected 13 109768 ⟨382160, by decide⟩ ⟨13, 2, 0, 382160, 109768, 569, 16384⟩
    (by decide) selected_cut_14830

theorem selected_cut_14831 : selected 8 ⟨382186, by decide⟩
    (prefixPartial 13 109769) = some ⟨13, 2, 0, 382186, 109769, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_109769_382186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109769 ⟨382186, by decide⟩ :=
  accepted_of_selected 13 109769 ⟨382186, by decide⟩ ⟨13, 2, 0, 382186, 109769, 2501, 16384⟩
    (by decide) selected_cut_14831

theorem selected_cut_14832 : selected 8 ⟨382209, by decide⟩
    (prefixPartial 13 109770) = some ⟨13, 2, 0, 382209, 109770, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_109770_382209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109770 ⟨382209, by decide⟩ :=
  accepted_of_selected 13 109770 ⟨382209, by decide⟩ ⟨13, 2, 0, 382209, 109770, 1617, 16384⟩
    (by decide) selected_cut_14832

theorem selected_cut_14833 : selected 8 ⟨382213, by decide⟩
    (prefixPartial 13 109771) = some ⟨13, 2, 0, 382213, 109771, 733, 16384⟩ := by
  decide +kernel

theorem context_13_109771_382213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109771 ⟨382213, by decide⟩ :=
  accepted_of_selected 13 109771 ⟨382213, by decide⟩ ⟨13, 2, 0, 382213, 109771, 733, 16384⟩
    (by decide) selected_cut_14833

theorem unmarked_context_12_27442_382214 : frontier 9 ⟨382214, by decide⟩
    (prefixCache 12 27442) (prefixPartial 12 27442) = false := by
  decide +kernel

theorem node_context_12_27442_382214 : EJMOriginalGlobalDAGData.nodes 9 ⟨382214, by decide⟩ =
    .split (coordinate 12) (![⟨382160, by decide⟩,⟨382186, by decide⟩,⟨382209, by decide⟩,⟨382213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27442_382214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27442 ⟨382214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27442
    ⟨382214, by decide⟩ (by decide) (![⟨382160, by decide⟩,⟨382186, by decide⟩,⟨382209, by decide⟩,⟨382213, by decide⟩]) unmarked_context_12_27442_382214 node_context_12_27442_382214
  intro a
  fin_cases a
  · exact context_13_109768_382160
  · exact context_13_109769_382186
  · exact context_13_109770_382209
  · exact context_13_109771_382213

theorem selected_cut_14834 : selected 8 ⟨382220, by decide⟩
    (prefixPartial 13 109772) = some ⟨13, 2, 0, 382220, 109772, 573, 16384⟩ := by
  decide +kernel

theorem context_13_109772_382220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109772 ⟨382220, by decide⟩ :=
  accepted_of_selected 13 109772 ⟨382220, by decide⟩ ⟨13, 2, 0, 382220, 109772, 573, 16384⟩
    (by decide) selected_cut_14834

theorem selected_cut_14835 : selected 8 ⟨382246, by decide⟩
    (prefixPartial 13 109773) = some ⟨13, 2, 0, 382246, 109773, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_109773_382246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109773 ⟨382246, by decide⟩ :=
  accepted_of_selected 13 109773 ⟨382246, by decide⟩ ⟨13, 2, 0, 382246, 109773, 2549, 16384⟩
    (by decide) selected_cut_14835

theorem selected_cut_14836 : selected 8 ⟨382265, by decide⟩
    (prefixPartial 13 109774) = some ⟨13, 2, 0, 382265, 109774, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_109774_382265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109774 ⟨382265, by decide⟩ :=
  accepted_of_selected 13 109774 ⟨382265, by decide⟩ ⟨13, 2, 0, 382265, 109774, 1513, 16384⟩
    (by decide) selected_cut_14836

theorem selected_cut_14837 : selected 8 ⟨382271, by decide⟩
    (prefixPartial 13 109775) = some ⟨13, 2, 0, 382271, 109775, 701, 16384⟩ := by
  decide +kernel

theorem context_13_109775_382271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109775 ⟨382271, by decide⟩ :=
  accepted_of_selected 13 109775 ⟨382271, by decide⟩ ⟨13, 2, 0, 382271, 109775, 701, 16384⟩
    (by decide) selected_cut_14837

theorem unmarked_context_12_27443_382272 : frontier 9 ⟨382272, by decide⟩
    (prefixCache 12 27443) (prefixPartial 12 27443) = false := by
  decide +kernel

theorem node_context_12_27443_382272 : EJMOriginalGlobalDAGData.nodes 9 ⟨382272, by decide⟩ =
    .split (coordinate 12) (![⟨382220, by decide⟩,⟨382246, by decide⟩,⟨382265, by decide⟩,⟨382271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27443_382272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27443 ⟨382272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27443
    ⟨382272, by decide⟩ (by decide) (![⟨382220, by decide⟩,⟨382246, by decide⟩,⟨382265, by decide⟩,⟨382271, by decide⟩]) unmarked_context_12_27443_382272 node_context_12_27443_382272
  intro a
  fin_cases a
  · exact context_13_109772_382220
  · exact context_13_109773_382246
  · exact context_13_109774_382265
  · exact context_13_109775_382271

theorem unmarked_context_11_6860_382273 : frontier 10 ⟨382273, by decide⟩
    (prefixCache 11 6860) (prefixPartial 11 6860) = false := by
  decide +kernel

theorem node_context_11_6860_382273 : EJMOriginalGlobalDAGData.nodes 10 ⟨382273, by decide⟩ =
    .split (coordinate 11) (![⟨382093, by decide⟩,⟨382155, by decide⟩,⟨382214, by decide⟩,⟨382272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6860_382273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6860 ⟨382273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6860
    ⟨382273, by decide⟩ (by decide) (![⟨382093, by decide⟩,⟨382155, by decide⟩,⟨382214, by decide⟩,⟨382272, by decide⟩]) unmarked_context_11_6860_382273 node_context_11_6860_382273
  intro a
  fin_cases a
  · exact context_12_27440_382093
  · exact context_12_27441_382155
  · exact context_12_27442_382214
  · exact context_12_27443_382272

theorem selected_cut_14838 : selected 8 ⟨382278, by decide⟩
    (prefixPartial 13 109776) = some ⟨13, 2, 0, 382278, 109776, 421, 16384⟩ := by
  decide +kernel

theorem context_13_109776_382278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109776 ⟨382278, by decide⟩ :=
  accepted_of_selected 13 109776 ⟨382278, by decide⟩ ⟨13, 2, 0, 382278, 109776, 421, 16384⟩
    (by decide) selected_cut_14838

theorem selected_cut_14839 : selected 8 ⟨382309, by decide⟩
    (prefixPartial 13 109777) = some ⟨13, 2, 0, 382309, 109777, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_109777_382309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109777 ⟨382309, by decide⟩ :=
  accepted_of_selected 13 109777 ⟨382309, by decide⟩ ⟨13, 2, 0, 382309, 109777, 2661, 16384⟩
    (by decide) selected_cut_14839

theorem selected_cut_14840 : selected 8 ⟨382329, by decide⟩
    (prefixPartial 13 109778) = some ⟨13, 2, 0, 382329, 109778, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_109778_382329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109778 ⟨382329, by decide⟩ :=
  accepted_of_selected 13 109778 ⟨382329, by decide⟩ ⟨13, 2, 0, 382329, 109778, 1553, 16384⟩
    (by decide) selected_cut_14840

theorem selected_cut_14841 : selected 8 ⟨382337, by decide⟩
    (prefixPartial 13 109779) = some ⟨13, 2, 0, 382337, 109779, 841, 16384⟩ := by
  decide +kernel

theorem context_13_109779_382337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109779 ⟨382337, by decide⟩ :=
  accepted_of_selected 13 109779 ⟨382337, by decide⟩ ⟨13, 2, 0, 382337, 109779, 841, 16384⟩
    (by decide) selected_cut_14841

theorem unmarked_context_12_27444_382338 : frontier 9 ⟨382338, by decide⟩
    (prefixCache 12 27444) (prefixPartial 12 27444) = false := by
  decide +kernel

theorem node_context_12_27444_382338 : EJMOriginalGlobalDAGData.nodes 9 ⟨382338, by decide⟩ =
    .split (coordinate 12) (![⟨382278, by decide⟩,⟨382309, by decide⟩,⟨382329, by decide⟩,⟨382337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27444_382338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27444 ⟨382338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27444
    ⟨382338, by decide⟩ (by decide) (![⟨382278, by decide⟩,⟨382309, by decide⟩,⟨382329, by decide⟩,⟨382337, by decide⟩]) unmarked_context_12_27444_382338 node_context_12_27444_382338
  intro a
  fin_cases a
  · exact context_13_109776_382278
  · exact context_13_109777_382309
  · exact context_13_109778_382329
  · exact context_13_109779_382337

theorem selected_cut_14842 : selected 8 ⟨382343, by decide⟩
    (prefixPartial 13 109780) = some ⟨13, 2, 0, 382343, 109780, 425, 16384⟩ := by
  decide +kernel

theorem context_13_109780_382343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109780 ⟨382343, by decide⟩ :=
  accepted_of_selected 13 109780 ⟨382343, by decide⟩ ⟨13, 2, 0, 382343, 109780, 425, 16384⟩
    (by decide) selected_cut_14842

theorem selected_cut_14843 : selected 8 ⟨382367, by decide⟩
    (prefixPartial 13 109781) = some ⟨13, 2, 0, 382367, 109781, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_109781_382367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109781 ⟨382367, by decide⟩ :=
  accepted_of_selected 13 109781 ⟨382367, by decide⟩ ⟨13, 2, 0, 382367, 109781, 2293, 16384⟩
    (by decide) selected_cut_14843

theorem selected_cut_14844 : selected 8 ⟨382386, by decide⟩
    (prefixPartial 13 109782) = some ⟨13, 2, 0, 382386, 109782, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_109782_382386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109782 ⟨382386, by decide⟩ :=
  accepted_of_selected 13 109782 ⟨382386, by decide⟩ ⟨13, 2, 0, 382386, 109782, 1553, 16384⟩
    (by decide) selected_cut_14844

theorem selected_cut_14845 : selected 8 ⟨382390, by decide⟩
    (prefixPartial 13 109783) = some ⟨13, 2, 0, 382390, 109783, 801, 16384⟩ := by
  decide +kernel

theorem context_13_109783_382390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109783 ⟨382390, by decide⟩ :=
  accepted_of_selected 13 109783 ⟨382390, by decide⟩ ⟨13, 2, 0, 382390, 109783, 801, 16384⟩
    (by decide) selected_cut_14845

theorem unmarked_context_12_27445_382391 : frontier 9 ⟨382391, by decide⟩
    (prefixCache 12 27445) (prefixPartial 12 27445) = false := by
  decide +kernel

theorem node_context_12_27445_382391 : EJMOriginalGlobalDAGData.nodes 9 ⟨382391, by decide⟩ =
    .split (coordinate 12) (![⟨382343, by decide⟩,⟨382367, by decide⟩,⟨382386, by decide⟩,⟨382390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27445_382391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27445 ⟨382391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27445
    ⟨382391, by decide⟩ (by decide) (![⟨382343, by decide⟩,⟨382367, by decide⟩,⟨382386, by decide⟩,⟨382390, by decide⟩]) unmarked_context_12_27445_382391 node_context_12_27445_382391
  intro a
  fin_cases a
  · exact context_13_109780_382343
  · exact context_13_109781_382367
  · exact context_13_109782_382386
  · exact context_13_109783_382390

theorem selected_cut_14846 : selected 8 ⟨382396, by decide⟩
    (prefixPartial 13 109784) = some ⟨13, 2, 0, 382396, 109784, 409, 16384⟩ := by
  decide +kernel

theorem context_13_109784_382396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109784 ⟨382396, by decide⟩ :=
  accepted_of_selected 13 109784 ⟨382396, by decide⟩ ⟨13, 2, 0, 382396, 109784, 409, 16384⟩
    (by decide) selected_cut_14846

theorem selected_cut_14847 : selected 8 ⟨382422, by decide⟩
    (prefixPartial 13 109785) = some ⟨13, 2, 0, 382422, 109785, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_109785_382422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109785 ⟨382422, by decide⟩ :=
  accepted_of_selected 13 109785 ⟨382422, by decide⟩ ⟨13, 2, 0, 382422, 109785, 2577, 16384⟩
    (by decide) selected_cut_14847

theorem selected_cut_14848 : selected 8 ⟨382439, by decide⟩
    (prefixPartial 13 109786) = some ⟨13, 2, 0, 382439, 109786, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_109786_382439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109786 ⟨382439, by decide⟩ :=
  accepted_of_selected 13 109786 ⟨382439, by decide⟩ ⟨13, 2, 0, 382439, 109786, 1733, 16384⟩
    (by decide) selected_cut_14848

theorem selected_cut_14849 : selected 8 ⟨382444, by decide⟩
    (prefixPartial 13 109787) = some ⟨13, 2, 0, 382444, 109787, 857, 16384⟩ := by
  decide +kernel

theorem context_13_109787_382444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109787 ⟨382444, by decide⟩ :=
  accepted_of_selected 13 109787 ⟨382444, by decide⟩ ⟨13, 2, 0, 382444, 109787, 857, 16384⟩
    (by decide) selected_cut_14849

theorem unmarked_context_12_27446_382445 : frontier 9 ⟨382445, by decide⟩
    (prefixCache 12 27446) (prefixPartial 12 27446) = false := by
  decide +kernel

theorem node_context_12_27446_382445 : EJMOriginalGlobalDAGData.nodes 9 ⟨382445, by decide⟩ =
    .split (coordinate 12) (![⟨382396, by decide⟩,⟨382422, by decide⟩,⟨382439, by decide⟩,⟨382444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27446_382445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27446 ⟨382445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27446
    ⟨382445, by decide⟩ (by decide) (![⟨382396, by decide⟩,⟨382422, by decide⟩,⟨382439, by decide⟩,⟨382444, by decide⟩]) unmarked_context_12_27446_382445 node_context_12_27446_382445
  intro a
  fin_cases a
  · exact context_13_109784_382396
  · exact context_13_109785_382422
  · exact context_13_109786_382439
  · exact context_13_109787_382444

theorem selected_cut_14850 : selected 8 ⟨382450, by decide⟩
    (prefixPartial 13 109788) = some ⟨13, 2, 0, 382450, 109788, 341, 16384⟩ := by
  decide +kernel

theorem context_13_109788_382450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109788 ⟨382450, by decide⟩ :=
  accepted_of_selected 13 109788 ⟨382450, by decide⟩ ⟨13, 2, 0, 382450, 109788, 341, 16384⟩
    (by decide) selected_cut_14850

theorem selected_cut_14851 : selected 8 ⟨382473, by decide⟩
    (prefixPartial 13 109789) = some ⟨13, 2, 0, 382473, 109789, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_109789_382473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109789 ⟨382473, by decide⟩ :=
  accepted_of_selected 13 109789 ⟨382473, by decide⟩ ⟨13, 2, 0, 382473, 109789, 2417, 16384⟩
    (by decide) selected_cut_14851

theorem selected_cut_14852 : selected 8 ⟨382492, by decide⟩
    (prefixPartial 13 109790) = some ⟨13, 2, 0, 382492, 109790, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_109790_382492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109790 ⟨382492, by decide⟩ :=
  accepted_of_selected 13 109790 ⟨382492, by decide⟩ ⟨13, 2, 0, 382492, 109790, 1597, 16384⟩
    (by decide) selected_cut_14852

theorem selected_cut_14853 : selected 8 ⟨382497, by decide⟩
    (prefixPartial 13 109791) = some ⟨13, 2, 0, 382497, 109791, 785, 16384⟩ := by
  decide +kernel

theorem context_13_109791_382497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109791 ⟨382497, by decide⟩ :=
  accepted_of_selected 13 109791 ⟨382497, by decide⟩ ⟨13, 2, 0, 382497, 109791, 785, 16384⟩
    (by decide) selected_cut_14853

theorem unmarked_context_12_27447_382498 : frontier 9 ⟨382498, by decide⟩
    (prefixCache 12 27447) (prefixPartial 12 27447) = false := by
  decide +kernel

theorem node_context_12_27447_382498 : EJMOriginalGlobalDAGData.nodes 9 ⟨382498, by decide⟩ =
    .split (coordinate 12) (![⟨382450, by decide⟩,⟨382473, by decide⟩,⟨382492, by decide⟩,⟨382497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27447_382498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27447 ⟨382498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27447
    ⟨382498, by decide⟩ (by decide) (![⟨382450, by decide⟩,⟨382473, by decide⟩,⟨382492, by decide⟩,⟨382497, by decide⟩]) unmarked_context_12_27447_382498 node_context_12_27447_382498
  intro a
  fin_cases a
  · exact context_13_109788_382450
  · exact context_13_109789_382473
  · exact context_13_109790_382492
  · exact context_13_109791_382497

theorem unmarked_context_11_6861_382499 : frontier 10 ⟨382499, by decide⟩
    (prefixCache 11 6861) (prefixPartial 11 6861) = false := by
  decide +kernel

theorem node_context_11_6861_382499 : EJMOriginalGlobalDAGData.nodes 10 ⟨382499, by decide⟩ =
    .split (coordinate 11) (![⟨382338, by decide⟩,⟨382391, by decide⟩,⟨382445, by decide⟩,⟨382498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6861_382499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6861 ⟨382499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6861
    ⟨382499, by decide⟩ (by decide) (![⟨382338, by decide⟩,⟨382391, by decide⟩,⟨382445, by decide⟩,⟨382498, by decide⟩]) unmarked_context_11_6861_382499 node_context_11_6861_382499
  intro a
  fin_cases a
  · exact context_12_27444_382338
  · exact context_12_27445_382391
  · exact context_12_27446_382445
  · exact context_12_27447_382498

theorem selected_cut_14854 : selected 8 ⟨382502, by decide⟩
    (prefixPartial 13 109792) = some ⟨13, 2, 0, 382502, 109792, 301, 16384⟩ := by
  decide +kernel

theorem context_13_109792_382502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109792 ⟨382502, by decide⟩ :=
  accepted_of_selected 13 109792 ⟨382502, by decide⟩ ⟨13, 2, 0, 382502, 109792, 301, 16384⟩
    (by decide) selected_cut_14854

theorem selected_cut_14855 : selected 8 ⟨382539, by decide⟩
    (prefixPartial 13 109793) = some ⟨13, 2, 0, 382539, 109793, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_109793_382539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109793 ⟨382539, by decide⟩ :=
  accepted_of_selected 13 109793 ⟨382539, by decide⟩ ⟨13, 2, 0, 382539, 109793, 2765, 16384⟩
    (by decide) selected_cut_14855

theorem selected_cut_14856 : selected 8 ⟨382556, by decide⟩
    (prefixPartial 13 109794) = some ⟨13, 2, 0, 382556, 109794, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_109794_382556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109794 ⟨382556, by decide⟩ :=
  accepted_of_selected 13 109794 ⟨382556, by decide⟩ ⟨13, 2, 0, 382556, 109794, 1641, 16384⟩
    (by decide) selected_cut_14856

theorem selected_cut_14857 : selected 8 ⟨382565, by decide⟩
    (prefixPartial 13 109795) = some ⟨13, 2, 0, 382565, 109795, 905, 16384⟩ := by
  decide +kernel

theorem context_13_109795_382565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109795 ⟨382565, by decide⟩ :=
  accepted_of_selected 13 109795 ⟨382565, by decide⟩ ⟨13, 2, 0, 382565, 109795, 905, 16384⟩
    (by decide) selected_cut_14857

theorem unmarked_context_12_27448_382566 : frontier 9 ⟨382566, by decide⟩
    (prefixCache 12 27448) (prefixPartial 12 27448) = false := by
  decide +kernel

theorem node_context_12_27448_382566 : EJMOriginalGlobalDAGData.nodes 9 ⟨382566, by decide⟩ =
    .split (coordinate 12) (![⟨382502, by decide⟩,⟨382539, by decide⟩,⟨382556, by decide⟩,⟨382565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27448_382566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27448 ⟨382566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27448
    ⟨382566, by decide⟩ (by decide) (![⟨382502, by decide⟩,⟨382539, by decide⟩,⟨382556, by decide⟩,⟨382565, by decide⟩]) unmarked_context_12_27448_382566 node_context_12_27448_382566
  intro a
  fin_cases a
  · exact context_13_109792_382502
  · exact context_13_109793_382539
  · exact context_13_109794_382556
  · exact context_13_109795_382565

theorem selected_cut_14858 : selected 8 ⟨382571, by decide⟩
    (prefixPartial 13 109796) = some ⟨13, 2, 0, 382571, 109796, 277, 16384⟩ := by
  decide +kernel

theorem context_13_109796_382571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109796 ⟨382571, by decide⟩ :=
  accepted_of_selected 13 109796 ⟨382571, by decide⟩ ⟨13, 2, 0, 382571, 109796, 277, 16384⟩
    (by decide) selected_cut_14858

theorem selected_cut_14859 : selected 8 ⟨382600, by decide⟩
    (prefixPartial 13 109797) = some ⟨13, 2, 0, 382600, 109797, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_109797_382600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109797 ⟨382600, by decide⟩ :=
  accepted_of_selected 13 109797 ⟨382600, by decide⟩ ⟨13, 2, 0, 382600, 109797, 2533, 16384⟩
    (by decide) selected_cut_14859

theorem selected_cut_14860 : selected 8 ⟨382618, by decide⟩
    (prefixPartial 13 109798) = some ⟨13, 2, 0, 382618, 109798, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_109798_382618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109798 ⟨382618, by decide⟩ :=
  accepted_of_selected 13 109798 ⟨382618, by decide⟩ ⟨13, 2, 0, 382618, 109798, 1573, 16384⟩
    (by decide) selected_cut_14860

theorem selected_cut_14861 : selected 8 ⟨382625, by decide⟩
    (prefixPartial 13 109799) = some ⟨13, 2, 0, 382625, 109799, 877, 16384⟩ := by
  decide +kernel

theorem context_13_109799_382625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109799 ⟨382625, by decide⟩ :=
  accepted_of_selected 13 109799 ⟨382625, by decide⟩ ⟨13, 2, 0, 382625, 109799, 877, 16384⟩
    (by decide) selected_cut_14861

theorem unmarked_context_12_27449_382626 : frontier 9 ⟨382626, by decide⟩
    (prefixCache 12 27449) (prefixPartial 12 27449) = false := by
  decide +kernel

theorem node_context_12_27449_382626 : EJMOriginalGlobalDAGData.nodes 9 ⟨382626, by decide⟩ =
    .split (coordinate 12) (![⟨382571, by decide⟩,⟨382600, by decide⟩,⟨382618, by decide⟩,⟨382625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27449_382626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27449 ⟨382626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27449
    ⟨382626, by decide⟩ (by decide) (![⟨382571, by decide⟩,⟨382600, by decide⟩,⟨382618, by decide⟩,⟨382625, by decide⟩]) unmarked_context_12_27449_382626 node_context_12_27449_382626
  intro a
  fin_cases a
  · exact context_13_109796_382571
  · exact context_13_109797_382600
  · exact context_13_109798_382618
  · exact context_13_109799_382625

theorem selected_cut_14862 : selected 8 ⟨382630, by decide⟩
    (prefixPartial 13 109800) = some ⟨13, 2, 0, 382630, 109800, 205, 16384⟩ := by
  decide +kernel

theorem context_13_109800_382630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109800 ⟨382630, by decide⟩ :=
  accepted_of_selected 13 109800 ⟨382630, by decide⟩ ⟨13, 2, 0, 382630, 109800, 205, 16384⟩
    (by decide) selected_cut_14862

theorem selected_cut_14863 : selected 8 ⟨382655, by decide⟩
    (prefixPartial 13 109801) = some ⟨13, 2, 0, 382655, 109801, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_109801_382655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109801 ⟨382655, by decide⟩ :=
  accepted_of_selected 13 109801 ⟨382655, by decide⟩ ⟨13, 2, 0, 382655, 109801, 2657, 16384⟩
    (by decide) selected_cut_14863

theorem selected_cut_14864 : selected 8 ⟨382677, by decide⟩
    (prefixPartial 13 109802) = some ⟨13, 2, 0, 382677, 109802, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_109802_382677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109802 ⟨382677, by decide⟩ :=
  accepted_of_selected 13 109802 ⟨382677, by decide⟩ ⟨13, 2, 0, 382677, 109802, 1669, 16384⟩
    (by decide) selected_cut_14864

theorem selected_cut_14865 : selected 8 ⟨382683, by decide⟩
    (prefixPartial 13 109803) = some ⟨13, 2, 0, 382683, 109803, 801, 16384⟩ := by
  decide +kernel

theorem context_13_109803_382683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109803 ⟨382683, by decide⟩ :=
  accepted_of_selected 13 109803 ⟨382683, by decide⟩ ⟨13, 2, 0, 382683, 109803, 801, 16384⟩
    (by decide) selected_cut_14865

theorem unmarked_context_12_27450_382684 : frontier 9 ⟨382684, by decide⟩
    (prefixCache 12 27450) (prefixPartial 12 27450) = false := by
  decide +kernel

theorem node_context_12_27450_382684 : EJMOriginalGlobalDAGData.nodes 9 ⟨382684, by decide⟩ =
    .split (coordinate 12) (![⟨382630, by decide⟩,⟨382655, by decide⟩,⟨382677, by decide⟩,⟨382683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27450_382684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27450 ⟨382684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27450
    ⟨382684, by decide⟩ (by decide) (![⟨382630, by decide⟩,⟨382655, by decide⟩,⟨382677, by decide⟩,⟨382683, by decide⟩]) unmarked_context_12_27450_382684 node_context_12_27450_382684
  intro a
  fin_cases a
  · exact context_13_109800_382630
  · exact context_13_109801_382655
  · exact context_13_109802_382677
  · exact context_13_109803_382683

theorem selected_cut_14866 : selected 8 ⟨382688, by decide⟩
    (prefixPartial 13 109804) = some ⟨13, 2, 0, 382688, 109804, 185, 16384⟩ := by
  decide +kernel

theorem context_13_109804_382688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109804 ⟨382688, by decide⟩ :=
  accepted_of_selected 13 109804 ⟨382688, by decide⟩ ⟨13, 2, 0, 382688, 109804, 185, 16384⟩
    (by decide) selected_cut_14866

theorem selected_cut_14867 : selected 8 ⟨382718, by decide⟩
    (prefixPartial 13 109805) = some ⟨13, 2, 0, 382718, 109805, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_109805_382718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109805 ⟨382718, by decide⟩ :=
  accepted_of_selected 13 109805 ⟨382718, by decide⟩ ⟨13, 2, 0, 382718, 109805, 2765, 16384⟩
    (by decide) selected_cut_14867

theorem selected_cut_14868 : selected 8 ⟨382736, by decide⟩
    (prefixPartial 13 109806) = some ⟨13, 2, 0, 382736, 109806, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_109806_382736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109806 ⟨382736, by decide⟩ :=
  accepted_of_selected 13 109806 ⟨382736, by decide⟩ ⟨13, 2, 0, 382736, 109806, 1429, 16384⟩
    (by decide) selected_cut_14868

theorem selected_cut_14869 : selected 8 ⟨382741, by decide⟩
    (prefixPartial 13 109807) = some ⟨13, 2, 0, 382741, 109807, 713, 16384⟩ := by
  decide +kernel

theorem context_13_109807_382741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109807 ⟨382741, by decide⟩ :=
  accepted_of_selected 13 109807 ⟨382741, by decide⟩ ⟨13, 2, 0, 382741, 109807, 713, 16384⟩
    (by decide) selected_cut_14869

theorem unmarked_context_12_27451_382742 : frontier 9 ⟨382742, by decide⟩
    (prefixCache 12 27451) (prefixPartial 12 27451) = false := by
  decide +kernel

theorem node_context_12_27451_382742 : EJMOriginalGlobalDAGData.nodes 9 ⟨382742, by decide⟩ =
    .split (coordinate 12) (![⟨382688, by decide⟩,⟨382718, by decide⟩,⟨382736, by decide⟩,⟨382741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27451_382742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27451 ⟨382742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27451
    ⟨382742, by decide⟩ (by decide) (![⟨382688, by decide⟩,⟨382718, by decide⟩,⟨382736, by decide⟩,⟨382741, by decide⟩]) unmarked_context_12_27451_382742 node_context_12_27451_382742
  intro a
  fin_cases a
  · exact context_13_109804_382688
  · exact context_13_109805_382718
  · exact context_13_109806_382736
  · exact context_13_109807_382741

theorem unmarked_context_11_6862_382743 : frontier 10 ⟨382743, by decide⟩
    (prefixCache 11 6862) (prefixPartial 11 6862) = false := by
  decide +kernel

theorem node_context_11_6862_382743 : EJMOriginalGlobalDAGData.nodes 10 ⟨382743, by decide⟩ =
    .split (coordinate 11) (![⟨382566, by decide⟩,⟨382626, by decide⟩,⟨382684, by decide⟩,⟨382742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6862_382743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6862 ⟨382743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6862
    ⟨382743, by decide⟩ (by decide) (![⟨382566, by decide⟩,⟨382626, by decide⟩,⟨382684, by decide⟩,⟨382742, by decide⟩]) unmarked_context_11_6862_382743 node_context_11_6862_382743
  intro a
  fin_cases a
  · exact context_12_27448_382566
  · exact context_12_27449_382626
  · exact context_12_27450_382684
  · exact context_12_27451_382742

theorem selected_cut_14870 : selected 8 ⟨382746, by decide⟩
    (prefixPartial 13 109808) = some ⟨13, 2, 0, 382746, 109808, 137, 16384⟩ := by
  decide +kernel

theorem context_13_109808_382746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109808 ⟨382746, by decide⟩ :=
  accepted_of_selected 13 109808 ⟨382746, by decide⟩ ⟨13, 2, 0, 382746, 109808, 137, 16384⟩
    (by decide) selected_cut_14870

theorem selected_cut_14871 : selected 8 ⟨382776, by decide⟩
    (prefixPartial 13 109809) = some ⟨13, 2, 0, 382776, 109809, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_109809_382776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109809 ⟨382776, by decide⟩ :=
  accepted_of_selected 13 109809 ⟨382776, by decide⟩ ⟨13, 2, 0, 382776, 109809, 2157, 16384⟩
    (by decide) selected_cut_14871

theorem selected_cut_14872 : selected 8 ⟨382792, by decide⟩
    (prefixPartial 13 109810) = some ⟨13, 2, 0, 382792, 109810, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_109810_382792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109810 ⟨382792, by decide⟩ :=
  accepted_of_selected 13 109810 ⟨382792, by decide⟩ ⟨13, 2, 0, 382792, 109810, 1233, 16384⟩
    (by decide) selected_cut_14872

theorem selected_cut_14873 : selected 8 ⟨382796, by decide⟩
    (prefixPartial 13 109811) = some ⟨13, 2, 0, 382796, 109811, 777, 16384⟩ := by
  decide +kernel

theorem context_13_109811_382796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109811 ⟨382796, by decide⟩ :=
  accepted_of_selected 13 109811 ⟨382796, by decide⟩ ⟨13, 2, 0, 382796, 109811, 777, 16384⟩
    (by decide) selected_cut_14873

theorem unmarked_context_12_27452_382797 : frontier 9 ⟨382797, by decide⟩
    (prefixCache 12 27452) (prefixPartial 12 27452) = false := by
  decide +kernel

theorem node_context_12_27452_382797 : EJMOriginalGlobalDAGData.nodes 9 ⟨382797, by decide⟩ =
    .split (coordinate 12) (![⟨382746, by decide⟩,⟨382776, by decide⟩,⟨382792, by decide⟩,⟨382796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27452_382797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27452 ⟨382797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27452
    ⟨382797, by decide⟩ (by decide) (![⟨382746, by decide⟩,⟨382776, by decide⟩,⟨382792, by decide⟩,⟨382796, by decide⟩]) unmarked_context_12_27452_382797 node_context_12_27452_382797
  intro a
  fin_cases a
  · exact context_13_109808_382746
  · exact context_13_109809_382776
  · exact context_13_109810_382792
  · exact context_13_109811_382796

theorem selected_cut_14874 : selected 8 ⟨382800, by decide⟩
    (prefixPartial 13 109812) = some ⟨13, 2, 0, 382800, 109812, 141, 16384⟩ := by
  decide +kernel

theorem context_13_109812_382800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109812 ⟨382800, by decide⟩ :=
  accepted_of_selected 13 109812 ⟨382800, by decide⟩ ⟨13, 2, 0, 382800, 109812, 141, 16384⟩
    (by decide) selected_cut_14874

theorem selected_cut_14875 : selected 8 ⟨382825, by decide⟩
    (prefixPartial 13 109813) = some ⟨13, 2, 0, 382825, 109813, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_109813_382825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109813 ⟨382825, by decide⟩ :=
  accepted_of_selected 13 109813 ⟨382825, by decide⟩ ⟨13, 2, 0, 382825, 109813, 1985, 16384⟩
    (by decide) selected_cut_14875

theorem selected_cut_14876 : selected 8 ⟨382841, by decide⟩
    (prefixPartial 13 109814) = some ⟨13, 2, 0, 382841, 109814, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_109814_382841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109814 ⟨382841, by decide⟩ :=
  accepted_of_selected 13 109814 ⟨382841, by decide⟩ ⟨13, 2, 0, 382841, 109814, 1397, 16384⟩
    (by decide) selected_cut_14876

theorem selected_cut_14877 : selected 8 ⟨382845, by decide⟩
    (prefixPartial 13 109815) = some ⟨13, 2, 0, 382845, 109815, 745, 16384⟩ := by
  decide +kernel

theorem context_13_109815_382845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109815 ⟨382845, by decide⟩ :=
  accepted_of_selected 13 109815 ⟨382845, by decide⟩ ⟨13, 2, 0, 382845, 109815, 745, 16384⟩
    (by decide) selected_cut_14877

theorem unmarked_context_12_27453_382846 : frontier 9 ⟨382846, by decide⟩
    (prefixCache 12 27453) (prefixPartial 12 27453) = false := by
  decide +kernel

theorem node_context_12_27453_382846 : EJMOriginalGlobalDAGData.nodes 9 ⟨382846, by decide⟩ =
    .split (coordinate 12) (![⟨382800, by decide⟩,⟨382825, by decide⟩,⟨382841, by decide⟩,⟨382845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27453_382846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27453 ⟨382846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27453
    ⟨382846, by decide⟩ (by decide) (![⟨382800, by decide⟩,⟨382825, by decide⟩,⟨382841, by decide⟩,⟨382845, by decide⟩]) unmarked_context_12_27453_382846 node_context_12_27453_382846
  intro a
  fin_cases a
  · exact context_13_109812_382800
  · exact context_13_109813_382825
  · exact context_13_109814_382841
  · exact context_13_109815_382845

theorem selected_cut_14878 : selected 8 ⟨382849, by decide⟩
    (prefixPartial 13 109816) = some ⟨13, 2, 0, 382849, 109816, 89, 16384⟩ := by
  decide +kernel

theorem context_13_109816_382849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109816 ⟨382849, by decide⟩ :=
  accepted_of_selected 13 109816 ⟨382849, by decide⟩ ⟨13, 2, 0, 382849, 109816, 89, 16384⟩
    (by decide) selected_cut_14878

theorem selected_cut_14879 : selected 8 ⟨382874, by decide⟩
    (prefixPartial 13 109817) = some ⟨13, 2, 0, 382874, 109817, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_109817_382874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109817 ⟨382874, by decide⟩ :=
  accepted_of_selected 13 109817 ⟨382874, by decide⟩ ⟨13, 2, 0, 382874, 109817, 2249, 16384⟩
    (by decide) selected_cut_14879

theorem selected_cut_14880 : selected 8 ⟨382891, by decide⟩
    (prefixPartial 13 109818) = some ⟨13, 2, 0, 382891, 109818, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_109818_382891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109818 ⟨382891, by decide⟩ :=
  accepted_of_selected 13 109818 ⟨382891, by decide⟩ ⟨13, 2, 0, 382891, 109818, 1377, 16384⟩
    (by decide) selected_cut_14880

theorem selected_cut_14881 : selected 8 ⟨382895, by decide⟩
    (prefixPartial 13 109819) = some ⟨13, 2, 0, 382895, 109819, 745, 16384⟩ := by
  decide +kernel

theorem context_13_109819_382895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109819 ⟨382895, by decide⟩ :=
  accepted_of_selected 13 109819 ⟨382895, by decide⟩ ⟨13, 2, 0, 382895, 109819, 745, 16384⟩
    (by decide) selected_cut_14881

theorem unmarked_context_12_27454_382896 : frontier 9 ⟨382896, by decide⟩
    (prefixCache 12 27454) (prefixPartial 12 27454) = false := by
  decide +kernel

theorem node_context_12_27454_382896 : EJMOriginalGlobalDAGData.nodes 9 ⟨382896, by decide⟩ =
    .split (coordinate 12) (![⟨382849, by decide⟩,⟨382874, by decide⟩,⟨382891, by decide⟩,⟨382895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27454_382896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27454 ⟨382896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27454
    ⟨382896, by decide⟩ (by decide) (![⟨382849, by decide⟩,⟨382874, by decide⟩,⟨382891, by decide⟩,⟨382895, by decide⟩]) unmarked_context_12_27454_382896 node_context_12_27454_382896
  intro a
  fin_cases a
  · exact context_13_109816_382849
  · exact context_13_109817_382874
  · exact context_13_109818_382891
  · exact context_13_109819_382895

theorem selected_cut_14882 : selected 8 ⟨382901, by decide⟩
    (prefixPartial 13 109820) = some ⟨13, 2, 0, 382901, 109820, 113, 16384⟩ := by
  decide +kernel

theorem context_13_109820_382901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109820 ⟨382901, by decide⟩ :=
  accepted_of_selected 13 109820 ⟨382901, by decide⟩ ⟨13, 2, 0, 382901, 109820, 113, 16384⟩
    (by decide) selected_cut_14882

theorem selected_cut_14883 : selected 8 ⟨382971, by decide⟩
    (prefixPartial 13 109821) = some ⟨13, 2, 0, 382971, 109821, 3717, 16384⟩ := by
  decide +kernel

theorem context_13_109821_382971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109821 ⟨382971, by decide⟩ :=
  accepted_of_selected 13 109821 ⟨382971, by decide⟩ ⟨13, 2, 0, 382971, 109821, 3717, 16384⟩
    (by decide) selected_cut_14883

theorem selected_cut_14884 : selected 8 ⟨382997, by decide⟩
    (prefixPartial 13 109822) = some ⟨13, 2, 0, 382997, 109822, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_109822_382997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109822 ⟨382997, by decide⟩ :=
  accepted_of_selected 13 109822 ⟨382997, by decide⟩ ⟨13, 2, 0, 382997, 109822, 2085, 16384⟩
    (by decide) selected_cut_14884

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
