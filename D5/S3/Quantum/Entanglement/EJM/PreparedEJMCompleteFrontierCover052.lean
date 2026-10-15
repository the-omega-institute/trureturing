/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover051
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_4700_156207 : frontier 10 ⟨156207, by decide⟩
    (prefixCache 11 4700) (prefixPartial 11 4700) = false := by
  decide +kernel

theorem node_context_11_4700_156207 : EJMOriginalGlobalDAGData.nodes 10 ⟨156207, by decide⟩ =
    .split (coordinate 11) (![⟨156061, by decide⟩,⟨156112, by decide⟩,⟨156155, by decide⟩,⟨156206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4700_156207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4700 ⟨156207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4700
    ⟨156207, by decide⟩ (by decide) (![⟨156061, by decide⟩,⟨156112, by decide⟩,⟨156155, by decide⟩,⟨156206, by decide⟩]) unmarked_context_11_4700_156207 node_context_11_4700_156207
  intro a
  fin_cases a
  · exact context_12_18800_156061
  · exact context_12_18801_156112
  · exact context_12_18802_156155
  · exact context_12_18803_156206

theorem selected_cut_04995 : selected 9 ⟨156245, by decide⟩
    (prefixPartial 12 18804) = some ⟨12, 2, 0, 156245, 18804, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_18804_156245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18804 ⟨156245, by decide⟩ :=
  accepted_of_selected 12 18804 ⟨156245, by decide⟩ ⟨12, 2, 0, 156245, 18804, 3273, 65536⟩
    (by decide) selected_cut_04995

theorem selected_cut_04996 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 18805) = some ⟨12, 1, 0, 126884, 18805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18805_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18805 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 18805 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 18805, 1, 65536⟩
    (by decide) selected_cut_04996

theorem selected_cut_04997 : selected 9 ⟨156281, by decide⟩
    (prefixPartial 12 18806) = some ⟨12, 2, 0, 156281, 18806, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_18806_156281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18806 ⟨156281, by decide⟩ :=
  accepted_of_selected 12 18806 ⟨156281, by decide⟩ ⟨12, 2, 0, 156281, 18806, 3441, 65536⟩
    (by decide) selected_cut_04997

theorem selected_cut_04998 : selected 9 ⟨156319, by decide⟩
    (prefixPartial 12 18807) = some ⟨12, 2, 0, 156319, 18807, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_18807_156319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18807 ⟨156319, by decide⟩ :=
  accepted_of_selected 12 18807 ⟨156319, by decide⟩ ⟨12, 2, 0, 156319, 18807, 3445, 65536⟩
    (by decide) selected_cut_04998

theorem unmarked_context_11_4701_156320 : frontier 10 ⟨156320, by decide⟩
    (prefixCache 11 4701) (prefixPartial 11 4701) = false := by
  decide +kernel

theorem node_context_11_4701_156320 : EJMOriginalGlobalDAGData.nodes 10 ⟨156320, by decide⟩ =
    .split (coordinate 11) (![⟨156245, by decide⟩,⟨126884, by decide⟩,⟨156281, by decide⟩,⟨156319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4701_156320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4701 ⟨156320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4701
    ⟨156320, by decide⟩ (by decide) (![⟨156245, by decide⟩,⟨126884, by decide⟩,⟨156281, by decide⟩,⟨156319, by decide⟩]) unmarked_context_11_4701_156320 node_context_11_4701_156320
  intro a
  fin_cases a
  · exact context_12_18804_156245
  · exact context_12_18805_126884
  · exact context_12_18806_156281
  · exact context_12_18807_156319

theorem selected_cut_04999 : selected 9 ⟨156360, by decide⟩
    (prefixPartial 12 18808) = some ⟨12, 2, 0, 156360, 18808, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_18808_156360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18808 ⟨156360, by decide⟩ :=
  accepted_of_selected 12 18808 ⟨156360, by decide⟩ ⟨12, 2, 0, 156360, 18808, 3653, 65536⟩
    (by decide) selected_cut_04999

theorem selected_cut_05000 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75236) = some ⟨13, 1, 0, 3444, 75236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75236, 1, 16384⟩
    (by decide) selected_cut_05000

theorem selected_cut_05001 : selected 8 ⟨156364, by decide⟩
    (prefixPartial 13 75237) = some ⟨13, 2, 0, 156364, 75237, 381, 16384⟩ := by
  decide +kernel

theorem context_13_75237_156364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75237 ⟨156364, by decide⟩ :=
  accepted_of_selected 13 75237 ⟨156364, by decide⟩ ⟨13, 2, 0, 156364, 75237, 381, 16384⟩
    (by decide) selected_cut_05001

theorem selected_cut_05002 : selected 8 ⟨156392, by decide⟩
    (prefixPartial 13 75238) = some ⟨13, 2, 0, 156392, 75238, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_75238_156392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75238 ⟨156392, by decide⟩ :=
  accepted_of_selected 13 75238 ⟨156392, by decide⟩ ⟨13, 2, 0, 156392, 75238, 2653, 16384⟩
    (by decide) selected_cut_05002

theorem selected_cut_05003 : selected 8 ⟨156411, by decide⟩
    (prefixPartial 13 75239) = some ⟨13, 2, 0, 156411, 75239, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_75239_156411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75239 ⟨156411, by decide⟩ :=
  accepted_of_selected 13 75239 ⟨156411, by decide⟩ ⟨13, 2, 0, 156411, 75239, 1397, 16384⟩
    (by decide) selected_cut_05003

theorem unmarked_context_12_18809_156412 : frontier 9 ⟨156412, by decide⟩
    (prefixCache 12 18809) (prefixPartial 12 18809) = false := by
  decide +kernel

theorem node_context_12_18809_156412 : EJMOriginalGlobalDAGData.nodes 9 ⟨156412, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨156364, by decide⟩,⟨156392, by decide⟩,⟨156411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18809_156412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18809 ⟨156412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18809
    ⟨156412, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨156364, by decide⟩,⟨156392, by decide⟩,⟨156411, by decide⟩]) unmarked_context_12_18809_156412 node_context_12_18809_156412
  intro a
  fin_cases a
  · exact context_13_75236_3444
  · exact context_13_75237_156364
  · exact context_13_75238_156392
  · exact context_13_75239_156411

theorem selected_cut_05004 : selected 9 ⟨156446, by decide⟩
    (prefixPartial 12 18810) = some ⟨12, 2, 0, 156446, 18810, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_18810_156446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18810 ⟨156446, by decide⟩ :=
  accepted_of_selected 12 18810 ⟨156446, by decide⟩ ⟨12, 2, 0, 156446, 18810, 3665, 65536⟩
    (by decide) selected_cut_05004

theorem selected_cut_05005 : selected 9 ⟨156494, by decide⟩
    (prefixPartial 12 18811) = some ⟨12, 2, 0, 156494, 18811, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_18811_156494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18811 ⟨156494, by decide⟩ :=
  accepted_of_selected 12 18811 ⟨156494, by decide⟩ ⟨12, 2, 0, 156494, 18811, 4069, 65536⟩
    (by decide) selected_cut_05005

theorem unmarked_context_11_4702_156495 : frontier 10 ⟨156495, by decide⟩
    (prefixCache 11 4702) (prefixPartial 11 4702) = false := by
  decide +kernel

theorem node_context_11_4702_156495 : EJMOriginalGlobalDAGData.nodes 10 ⟨156495, by decide⟩ =
    .split (coordinate 11) (![⟨156360, by decide⟩,⟨156412, by decide⟩,⟨156446, by decide⟩,⟨156494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4702_156495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4702 ⟨156495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4702
    ⟨156495, by decide⟩ (by decide) (![⟨156360, by decide⟩,⟨156412, by decide⟩,⟨156446, by decide⟩,⟨156494, by decide⟩]) unmarked_context_11_4702_156495 node_context_11_4702_156495
  intro a
  fin_cases a
  · exact context_12_18808_156360
  · exact context_12_18809_156412
  · exact context_12_18810_156446
  · exact context_12_18811_156494

theorem selected_cut_05006 : selected 9 ⟨156530, by decide⟩
    (prefixPartial 12 18812) = some ⟨12, 2, 0, 156530, 18812, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_18812_156530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18812 ⟨156530, by decide⟩ :=
  accepted_of_selected 12 18812 ⟨156530, by decide⟩ ⟨12, 2, 0, 156530, 18812, 3281, 65536⟩
    (by decide) selected_cut_05006

theorem selected_cut_05007 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75252) = some ⟨13, 1, 0, 3444, 75252, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75252_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75252 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75252 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75252, 1, 16384⟩
    (by decide) selected_cut_05007

theorem selected_cut_05008 : selected 8 ⟨156533, by decide⟩
    (prefixPartial 13 75253) = some ⟨13, 2, 0, 156533, 75253, 153, 16384⟩ := by
  decide +kernel

theorem context_13_75253_156533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75253 ⟨156533, by decide⟩ :=
  accepted_of_selected 13 75253 ⟨156533, by decide⟩ ⟨13, 2, 0, 156533, 75253, 153, 16384⟩
    (by decide) selected_cut_05008

theorem selected_cut_05009 : selected 8 ⟨156563, by decide⟩
    (prefixPartial 13 75254) = some ⟨13, 2, 0, 156563, 75254, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_75254_156563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75254 ⟨156563, by decide⟩ :=
  accepted_of_selected 13 75254 ⟨156563, by decide⟩ ⟨13, 2, 0, 156563, 75254, 2637, 16384⟩
    (by decide) selected_cut_05009

theorem selected_cut_05010 : selected 8 ⟨156577, by decide⟩
    (prefixPartial 13 75255) = some ⟨13, 2, 0, 156577, 75255, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_75255_156577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75255 ⟨156577, by decide⟩ :=
  accepted_of_selected 13 75255 ⟨156577, by decide⟩ ⟨13, 2, 0, 156577, 75255, 1345, 16384⟩
    (by decide) selected_cut_05010

theorem unmarked_context_12_18813_156578 : frontier 9 ⟨156578, by decide⟩
    (prefixCache 12 18813) (prefixPartial 12 18813) = false := by
  decide +kernel

theorem node_context_12_18813_156578 : EJMOriginalGlobalDAGData.nodes 9 ⟨156578, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨156533, by decide⟩,⟨156563, by decide⟩,⟨156577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18813_156578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18813 ⟨156578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18813
    ⟨156578, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨156533, by decide⟩,⟨156563, by decide⟩,⟨156577, by decide⟩]) unmarked_context_12_18813_156578 node_context_12_18813_156578
  intro a
  fin_cases a
  · exact context_13_75252_3444
  · exact context_13_75253_156533
  · exact context_13_75254_156563
  · exact context_13_75255_156577

theorem selected_cut_05011 : selected 9 ⟨156616, by decide⟩
    (prefixPartial 12 18814) = some ⟨12, 2, 0, 156616, 18814, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_18814_156616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18814 ⟨156616, by decide⟩ :=
  accepted_of_selected 12 18814 ⟨156616, by decide⟩ ⟨12, 2, 0, 156616, 18814, 3669, 65536⟩
    (by decide) selected_cut_05011

theorem selected_cut_05012 : selected 9 ⟨156652, by decide⟩
    (prefixPartial 12 18815) = some ⟨12, 2, 0, 156652, 18815, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_18815_156652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18815 ⟨156652, by decide⟩ :=
  accepted_of_selected 12 18815 ⟨156652, by decide⟩ ⟨12, 2, 0, 156652, 18815, 3341, 65536⟩
    (by decide) selected_cut_05012

theorem unmarked_context_11_4703_156653 : frontier 10 ⟨156653, by decide⟩
    (prefixCache 11 4703) (prefixPartial 11 4703) = false := by
  decide +kernel

theorem node_context_11_4703_156653 : EJMOriginalGlobalDAGData.nodes 10 ⟨156653, by decide⟩ =
    .split (coordinate 11) (![⟨156530, by decide⟩,⟨156578, by decide⟩,⟨156616, by decide⟩,⟨156652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4703_156653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4703 ⟨156653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4703
    ⟨156653, by decide⟩ (by decide) (![⟨156530, by decide⟩,⟨156578, by decide⟩,⟨156616, by decide⟩,⟨156652, by decide⟩]) unmarked_context_11_4703_156653 node_context_11_4703_156653
  intro a
  fin_cases a
  · exact context_12_18812_156530
  · exact context_12_18813_156578
  · exact context_12_18814_156616
  · exact context_12_18815_156652

theorem unmarked_context_10_1175_156654 : frontier 11 ⟨156654, by decide⟩
    (prefixCache 10 1175) (prefixPartial 10 1175) = false := by
  decide +kernel

theorem node_context_10_1175_156654 : EJMOriginalGlobalDAGData.nodes 11 ⟨156654, by decide⟩ =
    .split (coordinate 10) (![⟨156207, by decide⟩,⟨156320, by decide⟩,⟨156495, by decide⟩,⟨156653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1175_156654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1175 ⟨156654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1175
    ⟨156654, by decide⟩ (by decide) (![⟨156207, by decide⟩,⟨156320, by decide⟩,⟨156495, by decide⟩,⟨156653, by decide⟩]) unmarked_context_10_1175_156654 node_context_10_1175_156654
  intro a
  fin_cases a
  · exact context_11_4700_156207
  · exact context_11_4701_156320
  · exact context_11_4702_156495
  · exact context_11_4703_156653

theorem unmarked_context_9_293_156655 : frontier 12 ⟨156655, by decide⟩
    (prefixCache 9 293) (prefixPartial 9 293) = false := by
  decide +kernel

theorem node_context_9_293_156655 : EJMOriginalGlobalDAGData.nodes 12 ⟨156655, by decide⟩ =
    .split (coordinate 9) (![⟨154286, by decide⟩,⟨155161, by decide⟩,⟨156020, by decide⟩,⟨156654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_293_156655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 293 ⟨156655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 293
    ⟨156655, by decide⟩ (by decide) (![⟨154286, by decide⟩,⟨155161, by decide⟩,⟨156020, by decide⟩,⟨156654, by decide⟩]) unmarked_context_9_293_156655 node_context_9_293_156655
  intro a
  fin_cases a
  · exact context_10_1172_154286
  · exact context_10_1173_155161
  · exact context_10_1174_156020
  · exact context_10_1175_156654

theorem selected_cut_05013 : selected 9 ⟨156685, by decide⟩
    (prefixPartial 12 18816) = some ⟨12, 2, 0, 156685, 18816, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_18816_156685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18816 ⟨156685, by decide⟩ :=
  accepted_of_selected 12 18816 ⟨156685, by decide⟩ ⟨12, 2, 0, 156685, 18816, 2957, 65536⟩
    (by decide) selected_cut_05013

theorem selected_cut_05014 : selected 9 ⟨156718, by decide⟩
    (prefixPartial 12 18817) = some ⟨12, 2, 0, 156718, 18817, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_18817_156718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18817 ⟨156718, by decide⟩ :=
  accepted_of_selected 12 18817 ⟨156718, by decide⟩ ⟨12, 2, 0, 156718, 18817, 2601, 65536⟩
    (by decide) selected_cut_05014

theorem selected_cut_05015 : selected 9 ⟨156742, by decide⟩
    (prefixPartial 12 18818) = some ⟨12, 2, 0, 156742, 18818, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_18818_156742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18818 ⟨156742, by decide⟩ :=
  accepted_of_selected 12 18818 ⟨156742, by decide⟩ ⟨12, 2, 0, 156742, 18818, 2773, 65536⟩
    (by decide) selected_cut_05015

theorem selected_cut_05016 : selected 9 ⟨156775, by decide⟩
    (prefixPartial 12 18819) = some ⟨12, 2, 0, 156775, 18819, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_18819_156775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18819 ⟨156775, by decide⟩ :=
  accepted_of_selected 12 18819 ⟨156775, by decide⟩ ⟨12, 2, 0, 156775, 18819, 2573, 65536⟩
    (by decide) selected_cut_05016

theorem unmarked_context_11_4704_156776 : frontier 10 ⟨156776, by decide⟩
    (prefixCache 11 4704) (prefixPartial 11 4704) = false := by
  decide +kernel

theorem node_context_11_4704_156776 : EJMOriginalGlobalDAGData.nodes 10 ⟨156776, by decide⟩ =
    .split (coordinate 11) (![⟨156685, by decide⟩,⟨156718, by decide⟩,⟨156742, by decide⟩,⟨156775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4704_156776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4704 ⟨156776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4704
    ⟨156776, by decide⟩ (by decide) (![⟨156685, by decide⟩,⟨156718, by decide⟩,⟨156742, by decide⟩,⟨156775, by decide⟩]) unmarked_context_11_4704_156776 node_context_11_4704_156776
  intro a
  fin_cases a
  · exact context_12_18816_156685
  · exact context_12_18817_156718
  · exact context_12_18818_156742
  · exact context_12_18819_156775

theorem selected_cut_05017 : selected 9 ⟨156796, by decide⟩
    (prefixPartial 12 18820) = some ⟨12, 2, 0, 156796, 18820, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_18820_156796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18820 ⟨156796, by decide⟩ :=
  accepted_of_selected 12 18820 ⟨156796, by decide⟩ ⟨12, 2, 0, 156796, 18820, 2773, 65536⟩
    (by decide) selected_cut_05017

theorem selected_cut_05018 : selected 9 ⟨156823, by decide⟩
    (prefixPartial 12 18821) = some ⟨12, 2, 0, 156823, 18821, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_18821_156823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18821 ⟨156823, by decide⟩ :=
  accepted_of_selected 12 18821 ⟨156823, by decide⟩ ⟨12, 2, 0, 156823, 18821, 3281, 65536⟩
    (by decide) selected_cut_05018

theorem selected_cut_05019 : selected 9 ⟨156849, by decide⟩
    (prefixPartial 12 18822) = some ⟨12, 2, 0, 156849, 18822, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_18822_156849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18822 ⟨156849, by decide⟩ :=
  accepted_of_selected 12 18822 ⟨156849, by decide⟩ ⟨12, 2, 0, 156849, 18822, 2621, 65536⟩
    (by decide) selected_cut_05019

theorem selected_cut_05020 : selected 9 ⟨156874, by decide⟩
    (prefixPartial 12 18823) = some ⟨12, 2, 0, 156874, 18823, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_18823_156874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18823 ⟨156874, by decide⟩ :=
  accepted_of_selected 12 18823 ⟨156874, by decide⟩ ⟨12, 2, 0, 156874, 18823, 2501, 65536⟩
    (by decide) selected_cut_05020

theorem unmarked_context_11_4705_156875 : frontier 10 ⟨156875, by decide⟩
    (prefixCache 11 4705) (prefixPartial 11 4705) = false := by
  decide +kernel

theorem node_context_11_4705_156875 : EJMOriginalGlobalDAGData.nodes 10 ⟨156875, by decide⟩ =
    .split (coordinate 11) (![⟨156796, by decide⟩,⟨156823, by decide⟩,⟨156849, by decide⟩,⟨156874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4705_156875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4705 ⟨156875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4705
    ⟨156875, by decide⟩ (by decide) (![⟨156796, by decide⟩,⟨156823, by decide⟩,⟨156849, by decide⟩,⟨156874, by decide⟩]) unmarked_context_11_4705_156875 node_context_11_4705_156875
  intro a
  fin_cases a
  · exact context_12_18820_156796
  · exact context_12_18821_156823
  · exact context_12_18822_156849
  · exact context_12_18823_156874

theorem selected_cut_05021 : selected 9 ⟨156902, by decide⟩
    (prefixPartial 12 18824) = some ⟨12, 2, 0, 156902, 18824, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_18824_156902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18824 ⟨156902, by decide⟩ :=
  accepted_of_selected 12 18824 ⟨156902, by decide⟩ ⟨12, 2, 0, 156902, 18824, 2637, 65536⟩
    (by decide) selected_cut_05021

theorem selected_cut_05022 : selected 9 ⟨156930, by decide⟩
    (prefixPartial 12 18825) = some ⟨12, 2, 0, 156930, 18825, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_18825_156930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18825 ⟨156930, by decide⟩ :=
  accepted_of_selected 12 18825 ⟨156930, by decide⟩ ⟨12, 2, 0, 156930, 18825, 2561, 65536⟩
    (by decide) selected_cut_05022

theorem selected_cut_05023 : selected 9 ⟨156959, by decide⟩
    (prefixPartial 12 18826) = some ⟨12, 2, 0, 156959, 18826, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_18826_156959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18826 ⟨156959, by decide⟩ :=
  accepted_of_selected 12 18826 ⟨156959, by decide⟩ ⟨12, 2, 0, 156959, 18826, 2341, 65536⟩
    (by decide) selected_cut_05023

theorem selected_cut_05024 : selected 9 ⟨156987, by decide⟩
    (prefixPartial 12 18827) = some ⟨12, 2, 0, 156987, 18827, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_18827_156987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18827 ⟨156987, by decide⟩ :=
  accepted_of_selected 12 18827 ⟨156987, by decide⟩ ⟨12, 2, 0, 156987, 18827, 2373, 65536⟩
    (by decide) selected_cut_05024

theorem unmarked_context_11_4706_156988 : frontier 10 ⟨156988, by decide⟩
    (prefixCache 11 4706) (prefixPartial 11 4706) = false := by
  decide +kernel

theorem node_context_11_4706_156988 : EJMOriginalGlobalDAGData.nodes 10 ⟨156988, by decide⟩ =
    .split (coordinate 11) (![⟨156902, by decide⟩,⟨156930, by decide⟩,⟨156959, by decide⟩,⟨156987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4706_156988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4706 ⟨156988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4706
    ⟨156988, by decide⟩ (by decide) (![⟨156902, by decide⟩,⟨156930, by decide⟩,⟨156959, by decide⟩,⟨156987, by decide⟩]) unmarked_context_11_4706_156988 node_context_11_4706_156988
  intro a
  fin_cases a
  · exact context_12_18824_156902
  · exact context_12_18825_156930
  · exact context_12_18826_156959
  · exact context_12_18827_156987

theorem selected_cut_05025 : selected 9 ⟨157015, by decide⟩
    (prefixPartial 12 18828) = some ⟨12, 2, 0, 157015, 18828, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_18828_157015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18828 ⟨157015, by decide⟩ :=
  accepted_of_selected 12 18828 ⟨157015, by decide⟩ ⟨12, 2, 0, 157015, 18828, 2661, 65536⟩
    (by decide) selected_cut_05025

theorem selected_cut_05026 : selected 9 ⟨157041, by decide⟩
    (prefixPartial 12 18829) = some ⟨12, 2, 0, 157041, 18829, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_18829_157041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18829 ⟨157041, by decide⟩ :=
  accepted_of_selected 12 18829 ⟨157041, by decide⟩ ⟨12, 2, 0, 157041, 18829, 2593, 65536⟩
    (by decide) selected_cut_05026

theorem selected_cut_05027 : selected 9 ⟨157066, by decide⟩
    (prefixPartial 12 18830) = some ⟨12, 2, 0, 157066, 18830, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_18830_157066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18830 ⟨157066, by decide⟩ :=
  accepted_of_selected 12 18830 ⟨157066, by decide⟩ ⟨12, 2, 0, 157066, 18830, 2637, 65536⟩
    (by decide) selected_cut_05027

theorem selected_cut_05028 : selected 9 ⟨157091, by decide⟩
    (prefixPartial 12 18831) = some ⟨12, 2, 0, 157091, 18831, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_18831_157091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18831 ⟨157091, by decide⟩ :=
  accepted_of_selected 12 18831 ⟨157091, by decide⟩ ⟨12, 2, 0, 157091, 18831, 2257, 65536⟩
    (by decide) selected_cut_05028

theorem unmarked_context_11_4707_157092 : frontier 10 ⟨157092, by decide⟩
    (prefixCache 11 4707) (prefixPartial 11 4707) = false := by
  decide +kernel

theorem node_context_11_4707_157092 : EJMOriginalGlobalDAGData.nodes 10 ⟨157092, by decide⟩ =
    .split (coordinate 11) (![⟨157015, by decide⟩,⟨157041, by decide⟩,⟨157066, by decide⟩,⟨157091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4707_157092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4707 ⟨157092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4707
    ⟨157092, by decide⟩ (by decide) (![⟨157015, by decide⟩,⟨157041, by decide⟩,⟨157066, by decide⟩,⟨157091, by decide⟩]) unmarked_context_11_4707_157092 node_context_11_4707_157092
  intro a
  fin_cases a
  · exact context_12_18828_157015
  · exact context_12_18829_157041
  · exact context_12_18830_157066
  · exact context_12_18831_157091

theorem unmarked_context_10_1176_157093 : frontier 11 ⟨157093, by decide⟩
    (prefixCache 10 1176) (prefixPartial 10 1176) = false := by
  decide +kernel

theorem node_context_10_1176_157093 : EJMOriginalGlobalDAGData.nodes 11 ⟨157093, by decide⟩ =
    .split (coordinate 10) (![⟨156776, by decide⟩,⟨156875, by decide⟩,⟨156988, by decide⟩,⟨157092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1176_157093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1176 ⟨157093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1176
    ⟨157093, by decide⟩ (by decide) (![⟨156776, by decide⟩,⟨156875, by decide⟩,⟨156988, by decide⟩,⟨157092, by decide⟩]) unmarked_context_10_1176_157093 node_context_10_1176_157093
  intro a
  fin_cases a
  · exact context_11_4704_156776
  · exact context_11_4705_156875
  · exact context_11_4706_156988
  · exact context_11_4707_157092

theorem selected_cut_05029 : selected 9 ⟨157124, by decide⟩
    (prefixPartial 12 18832) = some ⟨12, 2, 0, 157124, 18832, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_18832_157124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18832 ⟨157124, by decide⟩ :=
  accepted_of_selected 12 18832 ⟨157124, by decide⟩ ⟨12, 2, 0, 157124, 18832, 2469, 65536⟩
    (by decide) selected_cut_05029

theorem selected_cut_05030 : selected 9 ⟨157150, by decide⟩
    (prefixPartial 12 18833) = some ⟨12, 2, 0, 157150, 18833, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_18833_157150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18833 ⟨157150, by decide⟩ :=
  accepted_of_selected 12 18833 ⟨157150, by decide⟩ ⟨12, 2, 0, 157150, 18833, 2185, 65536⟩
    (by decide) selected_cut_05030

theorem selected_cut_05031 : selected 9 ⟨157179, by decide⟩
    (prefixPartial 12 18834) = some ⟨12, 2, 0, 157179, 18834, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_18834_157179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18834 ⟨157179, by decide⟩ :=
  accepted_of_selected 12 18834 ⟨157179, by decide⟩ ⟨12, 2, 0, 157179, 18834, 2509, 65536⟩
    (by decide) selected_cut_05031

theorem selected_cut_05032 : selected 9 ⟨157205, by decide⟩
    (prefixPartial 12 18835) = some ⟨12, 2, 0, 157205, 18835, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_18835_157205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18835 ⟨157205, by decide⟩ :=
  accepted_of_selected 12 18835 ⟨157205, by decide⟩ ⟨12, 2, 0, 157205, 18835, 2305, 65536⟩
    (by decide) selected_cut_05032

theorem unmarked_context_11_4708_157206 : frontier 10 ⟨157206, by decide⟩
    (prefixCache 11 4708) (prefixPartial 11 4708) = false := by
  decide +kernel

theorem node_context_11_4708_157206 : EJMOriginalGlobalDAGData.nodes 10 ⟨157206, by decide⟩ =
    .split (coordinate 11) (![⟨157124, by decide⟩,⟨157150, by decide⟩,⟨157179, by decide⟩,⟨157205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4708_157206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4708 ⟨157206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4708
    ⟨157206, by decide⟩ (by decide) (![⟨157124, by decide⟩,⟨157150, by decide⟩,⟨157179, by decide⟩,⟨157205, by decide⟩]) unmarked_context_11_4708_157206 node_context_11_4708_157206
  intro a
  fin_cases a
  · exact context_12_18832_157124
  · exact context_12_18833_157150
  · exact context_12_18834_157179
  · exact context_12_18835_157205

theorem selected_cut_05033 : selected 9 ⟨157229, by decide⟩
    (prefixPartial 12 18836) = some ⟨12, 2, 0, 157229, 18836, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_18836_157229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18836 ⟨157229, by decide⟩ :=
  accepted_of_selected 12 18836 ⟨157229, by decide⟩ ⟨12, 2, 0, 157229, 18836, 1985, 65536⟩
    (by decide) selected_cut_05033

theorem selected_cut_05034 : selected 9 ⟨157250, by decide⟩
    (prefixPartial 12 18837) = some ⟨12, 2, 0, 157250, 18837, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_18837_157250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18837 ⟨157250, by decide⟩ :=
  accepted_of_selected 12 18837 ⟨157250, by decide⟩ ⟨12, 2, 0, 157250, 18837, 2409, 65536⟩
    (by decide) selected_cut_05034

theorem selected_cut_05035 : selected 9 ⟨157270, by decide⟩
    (prefixPartial 12 18838) = some ⟨12, 2, 0, 157270, 18838, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_18838_157270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18838 ⟨157270, by decide⟩ :=
  accepted_of_selected 12 18838 ⟨157270, by decide⟩ ⟨12, 2, 0, 157270, 18838, 2069, 65536⟩
    (by decide) selected_cut_05035

theorem selected_cut_05036 : selected 9 ⟨157289, by decide⟩
    (prefixPartial 12 18839) = some ⟨12, 2, 0, 157289, 18839, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_18839_157289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18839 ⟨157289, by decide⟩ :=
  accepted_of_selected 12 18839 ⟨157289, by decide⟩ ⟨12, 2, 0, 157289, 18839, 1873, 65536⟩
    (by decide) selected_cut_05036

theorem unmarked_context_11_4709_157290 : frontier 10 ⟨157290, by decide⟩
    (prefixCache 11 4709) (prefixPartial 11 4709) = false := by
  decide +kernel

theorem node_context_11_4709_157290 : EJMOriginalGlobalDAGData.nodes 10 ⟨157290, by decide⟩ =
    .split (coordinate 11) (![⟨157229, by decide⟩,⟨157250, by decide⟩,⟨157270, by decide⟩,⟨157289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4709_157290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4709 ⟨157290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4709
    ⟨157290, by decide⟩ (by decide) (![⟨157229, by decide⟩,⟨157250, by decide⟩,⟨157270, by decide⟩,⟨157289, by decide⟩]) unmarked_context_11_4709_157290 node_context_11_4709_157290
  intro a
  fin_cases a
  · exact context_12_18836_157229
  · exact context_12_18837_157250
  · exact context_12_18838_157270
  · exact context_12_18839_157289

theorem selected_cut_05037 : selected 9 ⟨157309, by decide⟩
    (prefixPartial 12 18840) = some ⟨12, 2, 0, 157309, 18840, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_18840_157309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18840 ⟨157309, by decide⟩ :=
  accepted_of_selected 12 18840 ⟨157309, by decide⟩ ⟨12, 2, 0, 157309, 18840, 2025, 65536⟩
    (by decide) selected_cut_05037

theorem selected_cut_05038 : selected 9 ⟨157331, by decide⟩
    (prefixPartial 12 18841) = some ⟨12, 2, 0, 157331, 18841, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_18841_157331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18841 ⟨157331, by decide⟩ :=
  accepted_of_selected 12 18841 ⟨157331, by decide⟩ ⟨12, 2, 0, 157331, 18841, 1897, 65536⟩
    (by decide) selected_cut_05038

theorem selected_cut_05039 : selected 9 ⟨157353, by decide⟩
    (prefixPartial 12 18842) = some ⟨12, 2, 0, 157353, 18842, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_18842_157353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18842 ⟨157353, by decide⟩ :=
  accepted_of_selected 12 18842 ⟨157353, by decide⟩ ⟨12, 2, 0, 157353, 18842, 1989, 65536⟩
    (by decide) selected_cut_05039

theorem selected_cut_05040 : selected 9 ⟨157379, by decide⟩
    (prefixPartial 12 18843) = some ⟨12, 2, 0, 157379, 18843, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_18843_157379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18843 ⟨157379, by decide⟩ :=
  accepted_of_selected 12 18843 ⟨157379, by decide⟩ ⟨12, 2, 0, 157379, 18843, 1981, 65536⟩
    (by decide) selected_cut_05040

theorem unmarked_context_11_4710_157380 : frontier 10 ⟨157380, by decide⟩
    (prefixCache 11 4710) (prefixPartial 11 4710) = false := by
  decide +kernel

theorem node_context_11_4710_157380 : EJMOriginalGlobalDAGData.nodes 10 ⟨157380, by decide⟩ =
    .split (coordinate 11) (![⟨157309, by decide⟩,⟨157331, by decide⟩,⟨157353, by decide⟩,⟨157379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4710_157380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4710 ⟨157380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4710
    ⟨157380, by decide⟩ (by decide) (![⟨157309, by decide⟩,⟨157331, by decide⟩,⟨157353, by decide⟩,⟨157379, by decide⟩]) unmarked_context_11_4710_157380 node_context_11_4710_157380
  intro a
  fin_cases a
  · exact context_12_18840_157309
  · exact context_12_18841_157331
  · exact context_12_18842_157353
  · exact context_12_18843_157379

theorem selected_cut_05041 : selected 9 ⟨157404, by decide⟩
    (prefixPartial 12 18844) = some ⟨12, 2, 0, 157404, 18844, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_18844_157404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18844 ⟨157404, by decide⟩ :=
  accepted_of_selected 12 18844 ⟨157404, by decide⟩ ⟨12, 2, 0, 157404, 18844, 2033, 65536⟩
    (by decide) selected_cut_05041

theorem selected_cut_05042 : selected 9 ⟨157426, by decide⟩
    (prefixPartial 12 18845) = some ⟨12, 2, 0, 157426, 18845, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_18845_157426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18845 ⟨157426, by decide⟩ :=
  accepted_of_selected 12 18845 ⟨157426, by decide⟩ ⟨12, 2, 0, 157426, 18845, 1873, 65536⟩
    (by decide) selected_cut_05042

theorem selected_cut_05043 : selected 9 ⟨157455, by decide⟩
    (prefixPartial 12 18846) = some ⟨12, 2, 0, 157455, 18846, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_18846_157455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18846 ⟨157455, by decide⟩ :=
  accepted_of_selected 12 18846 ⟨157455, by decide⟩ ⟨12, 2, 0, 157455, 18846, 2101, 65536⟩
    (by decide) selected_cut_05043

theorem selected_cut_05044 : selected 9 ⟨157476, by decide⟩
    (prefixPartial 12 18847) = some ⟨12, 2, 0, 157476, 18847, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_18847_157476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18847 ⟨157476, by decide⟩ :=
  accepted_of_selected 12 18847 ⟨157476, by decide⟩ ⟨12, 2, 0, 157476, 18847, 1733, 65536⟩
    (by decide) selected_cut_05044

theorem unmarked_context_11_4711_157477 : frontier 10 ⟨157477, by decide⟩
    (prefixCache 11 4711) (prefixPartial 11 4711) = false := by
  decide +kernel

theorem node_context_11_4711_157477 : EJMOriginalGlobalDAGData.nodes 10 ⟨157477, by decide⟩ =
    .split (coordinate 11) (![⟨157404, by decide⟩,⟨157426, by decide⟩,⟨157455, by decide⟩,⟨157476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4711_157477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4711 ⟨157477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4711
    ⟨157477, by decide⟩ (by decide) (![⟨157404, by decide⟩,⟨157426, by decide⟩,⟨157455, by decide⟩,⟨157476, by decide⟩]) unmarked_context_11_4711_157477 node_context_11_4711_157477
  intro a
  fin_cases a
  · exact context_12_18844_157404
  · exact context_12_18845_157426
  · exact context_12_18846_157455
  · exact context_12_18847_157476

theorem unmarked_context_10_1177_157478 : frontier 11 ⟨157478, by decide⟩
    (prefixCache 10 1177) (prefixPartial 10 1177) = false := by
  decide +kernel

theorem node_context_10_1177_157478 : EJMOriginalGlobalDAGData.nodes 11 ⟨157478, by decide⟩ =
    .split (coordinate 10) (![⟨157206, by decide⟩,⟨157290, by decide⟩,⟨157380, by decide⟩,⟨157477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1177_157478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1177 ⟨157478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1177
    ⟨157478, by decide⟩ (by decide) (![⟨157206, by decide⟩,⟨157290, by decide⟩,⟨157380, by decide⟩,⟨157477, by decide⟩]) unmarked_context_10_1177_157478 node_context_10_1177_157478
  intro a
  fin_cases a
  · exact context_11_4708_157206
  · exact context_11_4709_157290
  · exact context_11_4710_157380
  · exact context_11_4711_157477

theorem selected_cut_05045 : selected 9 ⟨157494, by decide⟩
    (prefixPartial 12 18848) = some ⟨12, 2, 0, 157494, 18848, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_18848_157494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18848 ⟨157494, by decide⟩ :=
  accepted_of_selected 12 18848 ⟨157494, by decide⟩ ⟨12, 2, 0, 157494, 18848, 1885, 65536⟩
    (by decide) selected_cut_05045

theorem selected_cut_05046 : selected 9 ⟨157514, by decide⟩
    (prefixPartial 12 18849) = some ⟨12, 2, 0, 157514, 18849, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_18849_157514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18849 ⟨157514, by decide⟩ :=
  accepted_of_selected 12 18849 ⟨157514, by decide⟩ ⟨12, 2, 0, 157514, 18849, 1705, 65536⟩
    (by decide) selected_cut_05046

theorem selected_cut_05047 : selected 9 ⟨157531, by decide⟩
    (prefixPartial 12 18850) = some ⟨12, 2, 0, 157531, 18850, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_18850_157531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18850 ⟨157531, by decide⟩ :=
  accepted_of_selected 12 18850 ⟨157531, by decide⟩ ⟨12, 2, 0, 157531, 18850, 1765, 65536⟩
    (by decide) selected_cut_05047

theorem selected_cut_05048 : selected 9 ⟨157548, by decide⟩
    (prefixPartial 12 18851) = some ⟨12, 2, 0, 157548, 18851, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_18851_157548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18851 ⟨157548, by decide⟩ :=
  accepted_of_selected 12 18851 ⟨157548, by decide⟩ ⟨12, 2, 0, 157548, 18851, 1645, 65536⟩
    (by decide) selected_cut_05048

theorem unmarked_context_11_4712_157549 : frontier 10 ⟨157549, by decide⟩
    (prefixCache 11 4712) (prefixPartial 11 4712) = false := by
  decide +kernel

theorem node_context_11_4712_157549 : EJMOriginalGlobalDAGData.nodes 10 ⟨157549, by decide⟩ =
    .split (coordinate 11) (![⟨157494, by decide⟩,⟨157514, by decide⟩,⟨157531, by decide⟩,⟨157548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4712_157549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4712 ⟨157549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4712
    ⟨157549, by decide⟩ (by decide) (![⟨157494, by decide⟩,⟨157514, by decide⟩,⟨157531, by decide⟩,⟨157548, by decide⟩]) unmarked_context_11_4712_157549 node_context_11_4712_157549
  intro a
  fin_cases a
  · exact context_12_18848_157494
  · exact context_12_18849_157514
  · exact context_12_18850_157531
  · exact context_12_18851_157548

theorem selected_cut_05049 : selected 9 ⟨157569, by decide⟩
    (prefixPartial 12 18852) = some ⟨12, 2, 0, 157569, 18852, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_18852_157569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18852 ⟨157569, by decide⟩ :=
  accepted_of_selected 12 18852 ⟨157569, by decide⟩ ⟨12, 2, 0, 157569, 18852, 1761, 65536⟩
    (by decide) selected_cut_05049

theorem selected_cut_05050 : selected 9 ⟨157591, by decide⟩
    (prefixPartial 12 18853) = some ⟨12, 2, 0, 157591, 18853, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_18853_157591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18853 ⟨157591, by decide⟩ :=
  accepted_of_selected 12 18853 ⟨157591, by decide⟩ ⟨12, 2, 0, 157591, 18853, 2129, 65536⟩
    (by decide) selected_cut_05050

theorem selected_cut_05051 : selected 9 ⟨157604, by decide⟩
    (prefixPartial 12 18854) = some ⟨12, 2, 0, 157604, 18854, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_18854_157604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18854 ⟨157604, by decide⟩ :=
  accepted_of_selected 12 18854 ⟨157604, by decide⟩ ⟨12, 2, 0, 157604, 18854, 1685, 65536⟩
    (by decide) selected_cut_05051

theorem selected_cut_05052 : selected 9 ⟨157619, by decide⟩
    (prefixPartial 12 18855) = some ⟨12, 2, 0, 157619, 18855, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_18855_157619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18855 ⟨157619, by decide⟩ :=
  accepted_of_selected 12 18855 ⟨157619, by decide⟩ ⟨12, 2, 0, 157619, 18855, 1661, 65536⟩
    (by decide) selected_cut_05052

theorem unmarked_context_11_4713_157620 : frontier 10 ⟨157620, by decide⟩
    (prefixCache 11 4713) (prefixPartial 11 4713) = false := by
  decide +kernel

theorem node_context_11_4713_157620 : EJMOriginalGlobalDAGData.nodes 10 ⟨157620, by decide⟩ =
    .split (coordinate 11) (![⟨157569, by decide⟩,⟨157591, by decide⟩,⟨157604, by decide⟩,⟨157619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4713_157620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4713 ⟨157620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4713
    ⟨157620, by decide⟩ (by decide) (![⟨157569, by decide⟩,⟨157591, by decide⟩,⟨157604, by decide⟩,⟨157619, by decide⟩]) unmarked_context_11_4713_157620 node_context_11_4713_157620
  intro a
  fin_cases a
  · exact context_12_18852_157569
  · exact context_12_18853_157591
  · exact context_12_18854_157604
  · exact context_12_18855_157619

theorem selected_cut_05053 : selected 9 ⟨157649, by decide⟩
    (prefixPartial 12 18856) = some ⟨12, 2, 0, 157649, 18856, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_18856_157649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18856 ⟨157649, by decide⟩ :=
  accepted_of_selected 12 18856 ⟨157649, by decide⟩ ⟨12, 2, 0, 157649, 18856, 2053, 65536⟩
    (by decide) selected_cut_05053

theorem selected_cut_05054 : selected 9 ⟨157666, by decide⟩
    (prefixPartial 12 18857) = some ⟨12, 2, 0, 157666, 18857, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_18857_157666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18857 ⟨157666, by decide⟩ :=
  accepted_of_selected 12 18857 ⟨157666, by decide⟩ ⟨12, 2, 0, 157666, 18857, 1905, 65536⟩
    (by decide) selected_cut_05054

theorem selected_cut_05055 : selected 9 ⟨157705, by decide⟩
    (prefixPartial 12 18858) = some ⟨12, 2, 0, 157705, 18858, 537, 65536⟩ := by
  decide +kernel

theorem context_12_18858_157705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18858 ⟨157705, by decide⟩ :=
  accepted_of_selected 12 18858 ⟨157705, by decide⟩ ⟨12, 2, 0, 157705, 18858, 537, 65536⟩
    (by decide) selected_cut_05055

theorem selected_cut_05056 : selected 9 ⟨157721, by decide⟩
    (prefixPartial 12 18859) = some ⟨12, 2, 0, 157721, 18859, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_18859_157721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18859 ⟨157721, by decide⟩ :=
  accepted_of_selected 12 18859 ⟨157721, by decide⟩ ⟨12, 2, 0, 157721, 18859, 1821, 65536⟩
    (by decide) selected_cut_05056

theorem unmarked_context_11_4714_157722 : frontier 10 ⟨157722, by decide⟩
    (prefixCache 11 4714) (prefixPartial 11 4714) = false := by
  decide +kernel

theorem node_context_11_4714_157722 : EJMOriginalGlobalDAGData.nodes 10 ⟨157722, by decide⟩ =
    .split (coordinate 11) (![⟨157649, by decide⟩,⟨157666, by decide⟩,⟨157705, by decide⟩,⟨157721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4714_157722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4714 ⟨157722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4714
    ⟨157722, by decide⟩ (by decide) (![⟨157649, by decide⟩,⟨157666, by decide⟩,⟨157705, by decide⟩,⟨157721, by decide⟩]) unmarked_context_11_4714_157722 node_context_11_4714_157722
  intro a
  fin_cases a
  · exact context_12_18856_157649
  · exact context_12_18857_157666
  · exact context_12_18858_157705
  · exact context_12_18859_157721

theorem selected_cut_05057 : selected 9 ⟨157739, by decide⟩
    (prefixPartial 12 18860) = some ⟨12, 2, 0, 157739, 18860, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_18860_157739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18860 ⟨157739, by decide⟩ :=
  accepted_of_selected 12 18860 ⟨157739, by decide⟩ ⟨12, 2, 0, 157739, 18860, 1693, 65536⟩
    (by decide) selected_cut_05057

theorem selected_cut_05058 : selected 9 ⟨157754, by decide⟩
    (prefixPartial 12 18861) = some ⟨12, 2, 0, 157754, 18861, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_18861_157754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18861 ⟨157754, by decide⟩ :=
  accepted_of_selected 12 18861 ⟨157754, by decide⟩ ⟨12, 2, 0, 157754, 18861, 1577, 65536⟩
    (by decide) selected_cut_05058

theorem selected_cut_05059 : selected 9 ⟨157771, by decide⟩
    (prefixPartial 12 18862) = some ⟨12, 2, 0, 157771, 18862, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_18862_157771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18862 ⟨157771, by decide⟩ :=
  accepted_of_selected 12 18862 ⟨157771, by decide⟩ ⟨12, 2, 0, 157771, 18862, 1569, 65536⟩
    (by decide) selected_cut_05059

theorem selected_cut_05060 : selected 9 ⟨157786, by decide⟩
    (prefixPartial 12 18863) = some ⟨12, 2, 0, 157786, 18863, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_18863_157786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18863 ⟨157786, by decide⟩ :=
  accepted_of_selected 12 18863 ⟨157786, by decide⟩ ⟨12, 2, 0, 157786, 18863, 1373, 65536⟩
    (by decide) selected_cut_05060

theorem unmarked_context_11_4715_157787 : frontier 10 ⟨157787, by decide⟩
    (prefixCache 11 4715) (prefixPartial 11 4715) = false := by
  decide +kernel

theorem node_context_11_4715_157787 : EJMOriginalGlobalDAGData.nodes 10 ⟨157787, by decide⟩ =
    .split (coordinate 11) (![⟨157739, by decide⟩,⟨157754, by decide⟩,⟨157771, by decide⟩,⟨157786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4715_157787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4715 ⟨157787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4715
    ⟨157787, by decide⟩ (by decide) (![⟨157739, by decide⟩,⟨157754, by decide⟩,⟨157771, by decide⟩,⟨157786, by decide⟩]) unmarked_context_11_4715_157787 node_context_11_4715_157787
  intro a
  fin_cases a
  · exact context_12_18860_157739
  · exact context_12_18861_157754
  · exact context_12_18862_157771
  · exact context_12_18863_157786

theorem unmarked_context_10_1178_157788 : frontier 11 ⟨157788, by decide⟩
    (prefixCache 10 1178) (prefixPartial 10 1178) = false := by
  decide +kernel

theorem node_context_10_1178_157788 : EJMOriginalGlobalDAGData.nodes 11 ⟨157788, by decide⟩ =
    .split (coordinate 10) (![⟨157549, by decide⟩,⟨157620, by decide⟩,⟨157722, by decide⟩,⟨157787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1178_157788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1178 ⟨157788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1178
    ⟨157788, by decide⟩ (by decide) (![⟨157549, by decide⟩,⟨157620, by decide⟩,⟨157722, by decide⟩,⟨157787, by decide⟩]) unmarked_context_10_1178_157788 node_context_10_1178_157788
  intro a
  fin_cases a
  · exact context_11_4712_157549
  · exact context_11_4713_157620
  · exact context_11_4714_157722
  · exact context_11_4715_157787

theorem selected_cut_05061 : selected 9 ⟨157805, by decide⟩
    (prefixPartial 12 18864) = some ⟨12, 2, 0, 157805, 18864, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_18864_157805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18864 ⟨157805, by decide⟩ :=
  accepted_of_selected 12 18864 ⟨157805, by decide⟩ ⟨12, 2, 0, 157805, 18864, 1597, 65536⟩
    (by decide) selected_cut_05061

theorem selected_cut_05062 : selected 9 ⟨157821, by decide⟩
    (prefixPartial 12 18865) = some ⟨12, 2, 0, 157821, 18865, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_18865_157821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18865 ⟨157821, by decide⟩ :=
  accepted_of_selected 12 18865 ⟨157821, by decide⟩ ⟨12, 2, 0, 157821, 18865, 1441, 65536⟩
    (by decide) selected_cut_05062

theorem selected_cut_05063 : selected 9 ⟨157838, by decide⟩
    (prefixPartial 12 18866) = some ⟨12, 2, 0, 157838, 18866, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_18866_157838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18866 ⟨157838, by decide⟩ :=
  accepted_of_selected 12 18866 ⟨157838, by decide⟩ ⟨12, 2, 0, 157838, 18866, 1505, 65536⟩
    (by decide) selected_cut_05063

theorem selected_cut_05064 : selected 9 ⟨157855, by decide⟩
    (prefixPartial 12 18867) = some ⟨12, 2, 0, 157855, 18867, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_18867_157855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18867 ⟨157855, by decide⟩ :=
  accepted_of_selected 12 18867 ⟨157855, by decide⟩ ⟨12, 2, 0, 157855, 18867, 1333, 65536⟩
    (by decide) selected_cut_05064

theorem unmarked_context_11_4716_157856 : frontier 10 ⟨157856, by decide⟩
    (prefixCache 11 4716) (prefixPartial 11 4716) = false := by
  decide +kernel

theorem node_context_11_4716_157856 : EJMOriginalGlobalDAGData.nodes 10 ⟨157856, by decide⟩ =
    .split (coordinate 11) (![⟨157805, by decide⟩,⟨157821, by decide⟩,⟨157838, by decide⟩,⟨157855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4716_157856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4716 ⟨157856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4716
    ⟨157856, by decide⟩ (by decide) (![⟨157805, by decide⟩,⟨157821, by decide⟩,⟨157838, by decide⟩,⟨157855, by decide⟩]) unmarked_context_11_4716_157856 node_context_11_4716_157856
  intro a
  fin_cases a
  · exact context_12_18864_157805
  · exact context_12_18865_157821
  · exact context_12_18866_157838
  · exact context_12_18867_157855

theorem selected_cut_05065 : selected 9 ⟨157870, by decide⟩
    (prefixPartial 12 18868) = some ⟨12, 2, 0, 157870, 18868, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_18868_157870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18868 ⟨157870, by decide⟩ :=
  accepted_of_selected 12 18868 ⟨157870, by decide⟩ ⟨12, 2, 0, 157870, 18868, 1413, 65536⟩
    (by decide) selected_cut_05065

theorem selected_cut_05066 : selected 9 ⟨157894, by decide⟩
    (prefixPartial 12 18869) = some ⟨12, 2, 0, 157894, 18869, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_18869_157894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18869 ⟨157894, by decide⟩ :=
  accepted_of_selected 12 18869 ⟨157894, by decide⟩ ⟨12, 2, 0, 157894, 18869, 1721, 65536⟩
    (by decide) selected_cut_05066

theorem selected_cut_05067 : selected 9 ⟨157906, by decide⟩
    (prefixPartial 12 18870) = some ⟨12, 2, 0, 157906, 18870, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_18870_157906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18870 ⟨157906, by decide⟩ :=
  accepted_of_selected 12 18870 ⟨157906, by decide⟩ ⟨12, 2, 0, 157906, 18870, 1321, 65536⟩
    (by decide) selected_cut_05067

theorem selected_cut_05068 : selected 9 ⟨157919, by decide⟩
    (prefixPartial 12 18871) = some ⟨12, 2, 0, 157919, 18871, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_18871_157919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18871 ⟨157919, by decide⟩ :=
  accepted_of_selected 12 18871 ⟨157919, by decide⟩ ⟨12, 2, 0, 157919, 18871, 1209, 65536⟩
    (by decide) selected_cut_05068

theorem unmarked_context_11_4717_157920 : frontier 10 ⟨157920, by decide⟩
    (prefixCache 11 4717) (prefixPartial 11 4717) = false := by
  decide +kernel

theorem node_context_11_4717_157920 : EJMOriginalGlobalDAGData.nodes 10 ⟨157920, by decide⟩ =
    .split (coordinate 11) (![⟨157870, by decide⟩,⟨157894, by decide⟩,⟨157906, by decide⟩,⟨157919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4717_157920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4717 ⟨157920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4717
    ⟨157920, by decide⟩ (by decide) (![⟨157870, by decide⟩,⟨157894, by decide⟩,⟨157906, by decide⟩,⟨157919, by decide⟩]) unmarked_context_11_4717_157920 node_context_11_4717_157920
  intro a
  fin_cases a
  · exact context_12_18868_157870
  · exact context_12_18869_157894
  · exact context_12_18870_157906
  · exact context_12_18871_157919

theorem selected_cut_05069 : selected 9 ⟨157931, by decide⟩
    (prefixPartial 12 18872) = some ⟨12, 2, 0, 157931, 18872, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_18872_157931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18872 ⟨157931, by decide⟩ :=
  accepted_of_selected 12 18872 ⟨157931, by decide⟩ ⟨12, 2, 0, 157931, 18872, 1393, 65536⟩
    (by decide) selected_cut_05069

theorem selected_cut_05070 : selected 9 ⟨157940, by decide⟩
    (prefixPartial 12 18873) = some ⟨12, 2, 0, 157940, 18873, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_18873_157940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18873 ⟨157940, by decide⟩ :=
  accepted_of_selected 12 18873 ⟨157940, by decide⟩ ⟨12, 2, 0, 157940, 18873, 1377, 65536⟩
    (by decide) selected_cut_05070

theorem selected_cut_05071 : selected 9 ⟨157952, by decide⟩
    (prefixPartial 12 18874) = some ⟨12, 2, 0, 157952, 18874, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_18874_157952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18874 ⟨157952, by decide⟩ :=
  accepted_of_selected 12 18874 ⟨157952, by decide⟩ ⟨12, 2, 0, 157952, 18874, 1265, 65536⟩
    (by decide) selected_cut_05071

theorem selected_cut_05072 : selected 9 ⟨157961, by decide⟩
    (prefixPartial 12 18875) = some ⟨12, 2, 0, 157961, 18875, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_18875_157961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18875 ⟨157961, by decide⟩ :=
  accepted_of_selected 12 18875 ⟨157961, by decide⟩ ⟨12, 2, 0, 157961, 18875, 1217, 65536⟩
    (by decide) selected_cut_05072

theorem unmarked_context_11_4718_157962 : frontier 10 ⟨157962, by decide⟩
    (prefixCache 11 4718) (prefixPartial 11 4718) = false := by
  decide +kernel

theorem node_context_11_4718_157962 : EJMOriginalGlobalDAGData.nodes 10 ⟨157962, by decide⟩ =
    .split (coordinate 11) (![⟨157931, by decide⟩,⟨157940, by decide⟩,⟨157952, by decide⟩,⟨157961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4718_157962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4718 ⟨157962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4718
    ⟨157962, by decide⟩ (by decide) (![⟨157931, by decide⟩,⟨157940, by decide⟩,⟨157952, by decide⟩,⟨157961, by decide⟩]) unmarked_context_11_4718_157962 node_context_11_4718_157962
  intro a
  fin_cases a
  · exact context_12_18872_157931
  · exact context_12_18873_157940
  · exact context_12_18874_157952
  · exact context_12_18875_157961

theorem selected_cut_05073 : selected 9 ⟨157973, by decide⟩
    (prefixPartial 12 18876) = some ⟨12, 2, 0, 157973, 18876, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_18876_157973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18876 ⟨157973, by decide⟩ :=
  accepted_of_selected 12 18876 ⟨157973, by decide⟩ ⟨12, 2, 0, 157973, 18876, 1285, 65536⟩
    (by decide) selected_cut_05073

theorem selected_cut_05074 : selected 9 ⟨157984, by decide⟩
    (prefixPartial 12 18877) = some ⟨12, 2, 0, 157984, 18877, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_18877_157984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18877 ⟨157984, by decide⟩ :=
  accepted_of_selected 12 18877 ⟨157984, by decide⟩ ⟨12, 2, 0, 157984, 18877, 1205, 65536⟩
    (by decide) selected_cut_05074

theorem selected_cut_05075 : selected 9 ⟨157998, by decide⟩
    (prefixPartial 12 18878) = some ⟨12, 2, 0, 157998, 18878, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_18878_157998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18878 ⟨157998, by decide⟩ :=
  accepted_of_selected 12 18878 ⟨157998, by decide⟩ ⟨12, 2, 0, 157998, 18878, 1169, 65536⟩
    (by decide) selected_cut_05075

theorem selected_cut_05076 : selected 9 ⟨158011, by decide⟩
    (prefixPartial 12 18879) = some ⟨12, 2, 0, 158011, 18879, 993, 65536⟩ := by
  decide +kernel

theorem context_12_18879_158011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18879 ⟨158011, by decide⟩ :=
  accepted_of_selected 12 18879 ⟨158011, by decide⟩ ⟨12, 2, 0, 158011, 18879, 993, 65536⟩
    (by decide) selected_cut_05076

theorem unmarked_context_11_4719_158012 : frontier 10 ⟨158012, by decide⟩
    (prefixCache 11 4719) (prefixPartial 11 4719) = false := by
  decide +kernel

theorem node_context_11_4719_158012 : EJMOriginalGlobalDAGData.nodes 10 ⟨158012, by decide⟩ =
    .split (coordinate 11) (![⟨157973, by decide⟩,⟨157984, by decide⟩,⟨157998, by decide⟩,⟨158011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4719_158012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4719 ⟨158012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4719
    ⟨158012, by decide⟩ (by decide) (![⟨157973, by decide⟩,⟨157984, by decide⟩,⟨157998, by decide⟩,⟨158011, by decide⟩]) unmarked_context_11_4719_158012 node_context_11_4719_158012
  intro a
  fin_cases a
  · exact context_12_18876_157973
  · exact context_12_18877_157984
  · exact context_12_18878_157998
  · exact context_12_18879_158011

theorem unmarked_context_10_1179_158013 : frontier 11 ⟨158013, by decide⟩
    (prefixCache 10 1179) (prefixPartial 10 1179) = false := by
  decide +kernel

theorem node_context_10_1179_158013 : EJMOriginalGlobalDAGData.nodes 11 ⟨158013, by decide⟩ =
    .split (coordinate 10) (![⟨157856, by decide⟩,⟨157920, by decide⟩,⟨157962, by decide⟩,⟨158012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1179_158013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1179 ⟨158013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1179
    ⟨158013, by decide⟩ (by decide) (![⟨157856, by decide⟩,⟨157920, by decide⟩,⟨157962, by decide⟩,⟨158012, by decide⟩]) unmarked_context_10_1179_158013 node_context_10_1179_158013
  intro a
  fin_cases a
  · exact context_11_4716_157856
  · exact context_11_4717_157920
  · exact context_11_4718_157962
  · exact context_11_4719_158012

theorem unmarked_context_9_294_158014 : frontier 12 ⟨158014, by decide⟩
    (prefixCache 9 294) (prefixPartial 9 294) = false := by
  decide +kernel

theorem node_context_9_294_158014 : EJMOriginalGlobalDAGData.nodes 12 ⟨158014, by decide⟩ =
    .split (coordinate 9) (![⟨157093, by decide⟩,⟨157478, by decide⟩,⟨157788, by decide⟩,⟨158013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_294_158014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 294 ⟨158014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 294
    ⟨158014, by decide⟩ (by decide) (![⟨157093, by decide⟩,⟨157478, by decide⟩,⟨157788, by decide⟩,⟨158013, by decide⟩]) unmarked_context_9_294_158014 node_context_9_294_158014
  intro a
  fin_cases a
  · exact context_10_1176_157093
  · exact context_10_1177_157478
  · exact context_10_1178_157788
  · exact context_10_1179_158013

theorem selected_cut_05077 : selected 9 ⟨158022, by decide⟩
    (prefixPartial 12 18880) = some ⟨12, 2, 0, 158022, 18880, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_18880_158022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18880 ⟨158022, by decide⟩ :=
  accepted_of_selected 12 18880 ⟨158022, by decide⟩ ⟨12, 2, 0, 158022, 18880, 1113, 65536⟩
    (by decide) selected_cut_05077

theorem selected_cut_05078 : selected 9 ⟨158033, by decide⟩
    (prefixPartial 12 18881) = some ⟨12, 2, 0, 158033, 18881, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_18881_158033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18881 ⟨158033, by decide⟩ :=
  accepted_of_selected 12 18881 ⟨158033, by decide⟩ ⟨12, 2, 0, 158033, 18881, 1065, 65536⟩
    (by decide) selected_cut_05078

theorem selected_cut_05079 : selected 9 ⟨158042, by decide⟩
    (prefixPartial 12 18882) = some ⟨12, 2, 0, 158042, 18882, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_18882_158042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18882 ⟨158042, by decide⟩ :=
  accepted_of_selected 12 18882 ⟨158042, by decide⟩ ⟨12, 2, 0, 158042, 18882, 1065, 65536⟩
    (by decide) selected_cut_05079

theorem selected_cut_05080 : selected 9 ⟨158048, by decide⟩
    (prefixPartial 12 18883) = some ⟨12, 2, 0, 158048, 18883, 921, 65536⟩ := by
  decide +kernel

theorem context_12_18883_158048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18883 ⟨158048, by decide⟩ :=
  accepted_of_selected 12 18883 ⟨158048, by decide⟩ ⟨12, 2, 0, 158048, 18883, 921, 65536⟩
    (by decide) selected_cut_05080

theorem unmarked_context_11_4720_158049 : frontier 10 ⟨158049, by decide⟩
    (prefixCache 11 4720) (prefixPartial 11 4720) = false := by
  decide +kernel

theorem node_context_11_4720_158049 : EJMOriginalGlobalDAGData.nodes 10 ⟨158049, by decide⟩ =
    .split (coordinate 11) (![⟨158022, by decide⟩,⟨158033, by decide⟩,⟨158042, by decide⟩,⟨158048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4720_158049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4720 ⟨158049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4720
    ⟨158049, by decide⟩ (by decide) (![⟨158022, by decide⟩,⟨158033, by decide⟩,⟨158042, by decide⟩,⟨158048, by decide⟩]) unmarked_context_11_4720_158049 node_context_11_4720_158049
  intro a
  fin_cases a
  · exact context_12_18880_158022
  · exact context_12_18881_158033
  · exact context_12_18882_158042
  · exact context_12_18883_158048

theorem selected_cut_05081 : selected 10 ⟨158091, by decide⟩
    (prefixPartial 11 4721) = some ⟨11, 2, 0, 158091, 4721, 3829, 262144⟩ := by
  decide +kernel

theorem context_11_4721_158091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4721 ⟨158091, by decide⟩ :=
  accepted_of_selected 11 4721 ⟨158091, by decide⟩ ⟨11, 2, 0, 158091, 4721, 3829, 262144⟩
    (by decide) selected_cut_05081

theorem selected_cut_05082 : selected 10 ⟨158122, by decide⟩
    (prefixPartial 11 4722) = some ⟨11, 2, 0, 158122, 4722, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_4722_158122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4722 ⟨158122, by decide⟩ :=
  accepted_of_selected 11 4722 ⟨158122, by decide⟩ ⟨11, 2, 0, 158122, 4722, 3341, 262144⟩
    (by decide) selected_cut_05082

theorem selected_cut_05083 : selected 10 ⟨158155, by decide⟩
    (prefixPartial 11 4723) = some ⟨11, 2, 0, 158155, 4723, 3393, 262144⟩ := by
  decide +kernel

theorem context_11_4723_158155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4723 ⟨158155, by decide⟩ :=
  accepted_of_selected 11 4723 ⟨158155, by decide⟩ ⟨11, 2, 0, 158155, 4723, 3393, 262144⟩
    (by decide) selected_cut_05083

theorem unmarked_context_10_1180_158156 : frontier 11 ⟨158156, by decide⟩
    (prefixCache 10 1180) (prefixPartial 10 1180) = false := by
  decide +kernel

theorem node_context_10_1180_158156 : EJMOriginalGlobalDAGData.nodes 11 ⟨158156, by decide⟩ =
    .split (coordinate 10) (![⟨158049, by decide⟩,⟨158091, by decide⟩,⟨158122, by decide⟩,⟨158155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1180_158156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1180 ⟨158156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1180
    ⟨158156, by decide⟩ (by decide) (![⟨158049, by decide⟩,⟨158091, by decide⟩,⟨158122, by decide⟩,⟨158155, by decide⟩]) unmarked_context_10_1180_158156 node_context_10_1180_158156
  intro a
  fin_cases a
  · exact context_11_4720_158049
  · exact context_11_4721_158091
  · exact context_11_4722_158122
  · exact context_11_4723_158155

theorem selected_cut_05084 : selected 10 ⟨158182, by decide⟩
    (prefixPartial 11 4724) = some ⟨11, 2, 0, 158182, 4724, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_4724_158182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4724 ⟨158182, by decide⟩ :=
  accepted_of_selected 11 4724 ⟨158182, by decide⟩ ⟨11, 2, 0, 158182, 4724, 3137, 262144⟩
    (by decide) selected_cut_05084

theorem selected_cut_05085 : selected 10 ⟨158203, by decide⟩
    (prefixPartial 11 4725) = some ⟨11, 2, 0, 158203, 4725, 2581, 262144⟩ := by
  decide +kernel

theorem context_11_4725_158203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4725 ⟨158203, by decide⟩ :=
  accepted_of_selected 11 4725 ⟨158203, by decide⟩ ⟨11, 2, 0, 158203, 4725, 2581, 262144⟩
    (by decide) selected_cut_05085

theorem selected_cut_05086 : selected 10 ⟨158225, by decide⟩
    (prefixPartial 11 4726) = some ⟨11, 2, 0, 158225, 4726, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_4726_158225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4726 ⟨158225, by decide⟩ :=
  accepted_of_selected 11 4726 ⟨158225, by decide⟩ ⟨11, 2, 0, 158225, 4726, 2313, 262144⟩
    (by decide) selected_cut_05086

theorem selected_cut_05087 : selected 10 ⟨158248, by decide⟩
    (prefixPartial 11 4727) = some ⟨11, 2, 0, 158248, 4727, 2077, 262144⟩ := by
  decide +kernel

theorem context_11_4727_158248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4727 ⟨158248, by decide⟩ :=
  accepted_of_selected 11 4727 ⟨158248, by decide⟩ ⟨11, 2, 0, 158248, 4727, 2077, 262144⟩
    (by decide) selected_cut_05087

theorem unmarked_context_10_1181_158249 : frontier 11 ⟨158249, by decide⟩
    (prefixCache 10 1181) (prefixPartial 10 1181) = false := by
  decide +kernel

theorem node_context_10_1181_158249 : EJMOriginalGlobalDAGData.nodes 11 ⟨158249, by decide⟩ =
    .split (coordinate 10) (![⟨158182, by decide⟩,⟨158203, by decide⟩,⟨158225, by decide⟩,⟨158248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1181_158249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1181 ⟨158249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1181
    ⟨158249, by decide⟩ (by decide) (![⟨158182, by decide⟩,⟨158203, by decide⟩,⟨158225, by decide⟩,⟨158248, by decide⟩]) unmarked_context_10_1181_158249 node_context_10_1181_158249
  intro a
  fin_cases a
  · exact context_11_4724_158182
  · exact context_11_4725_158203
  · exact context_11_4726_158225
  · exact context_11_4727_158248

theorem selected_cut_05088 : selected 10 ⟨158267, by decide⟩
    (prefixPartial 11 4728) = some ⟨11, 2, 0, 158267, 4728, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_4728_158267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4728 ⟨158267, by decide⟩ :=
  accepted_of_selected 11 4728 ⟨158267, by decide⟩ ⟨11, 2, 0, 158267, 4728, 1745, 262144⟩
    (by decide) selected_cut_05088

theorem selected_cut_05089 : selected 10 ⟨158287, by decide⟩
    (prefixPartial 11 4729) = some ⟨11, 2, 0, 158287, 4729, 1501, 262144⟩ := by
  decide +kernel

theorem context_11_4729_158287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4729 ⟨158287, by decide⟩ :=
  accepted_of_selected 11 4729 ⟨158287, by decide⟩ ⟨11, 2, 0, 158287, 4729, 1501, 262144⟩
    (by decide) selected_cut_05089

theorem selected_cut_05090 : selected 10 ⟨158307, by decide⟩
    (prefixPartial 11 4730) = some ⟨11, 2, 0, 158307, 4730, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_4730_158307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4730 ⟨158307, by decide⟩ :=
  accepted_of_selected 11 4730 ⟨158307, by decide⟩ ⟨11, 2, 0, 158307, 4730, 1401, 262144⟩
    (by decide) selected_cut_05090

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
