/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover059
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05762 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5207) = some ⟨11, 1, 0, 1736, 5207, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5207_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5207 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5207 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5207, 1, 262144⟩
    (by decide) selected_cut_05762

theorem unmarked_context_10_1301_176438 : frontier 11 ⟨176438, by decide⟩
    (prefixCache 10 1301) (prefixPartial 10 1301) = false := by
  decide +kernel

theorem node_context_10_1301_176438 : EJMOriginalGlobalDAGData.nodes 11 ⟨176438, by decide⟩ =
    .split (coordinate 10) (![⟨176160, by decide⟩,⟨176226, by decide⟩,⟨176437, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1301_176438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1301 ⟨176438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1301
    ⟨176438, by decide⟩ (by decide) (![⟨176160, by decide⟩,⟨176226, by decide⟩,⟨176437, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1301_176438 node_context_10_1301_176438
  intro a
  fin_cases a
  · exact context_11_5204_176160
  · exact context_11_5205_176226
  · exact context_11_5206_176437
  · exact context_11_5207_1736

theorem selected_cut_05763 : selected 9 ⟨176474, by decide⟩
    (prefixPartial 12 20832) = some ⟨12, 2, 0, 176474, 20832, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_20832_176474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20832 ⟨176474, by decide⟩ :=
  accepted_of_selected 12 20832 ⟨176474, by decide⟩ ⟨12, 2, 0, 176474, 20832, 2653, 65536⟩
    (by decide) selected_cut_05763

theorem selected_cut_05764 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83332) = some ⟨13, 1, 0, 3444, 83332, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83332_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83332 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83332 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83332, 1, 16384⟩
    (by decide) selected_cut_05764

theorem selected_cut_05765 : selected 8 ⟨176485, by decide⟩
    (prefixPartial 13 83333) = some ⟨13, 2, 0, 176485, 83333, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_83333_176485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83333 ⟨176485, by decide⟩ :=
  accepted_of_selected 13 83333 ⟨176485, by decide⟩ ⟨13, 2, 0, 176485, 83333, 1329, 16384⟩
    (by decide) selected_cut_05765

theorem selected_cut_05766 : selected 8 ⟨176508, by decide⟩
    (prefixPartial 13 83334) = some ⟨13, 2, 0, 176508, 83334, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_83334_176508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83334 ⟨176508, by decide⟩ :=
  accepted_of_selected 13 83334 ⟨176508, by decide⟩ ⟨13, 2, 0, 176508, 83334, 1949, 16384⟩
    (by decide) selected_cut_05766

theorem selected_cut_05767 : selected 8 ⟨176513, by decide⟩
    (prefixPartial 13 83335) = some ⟨13, 2, 0, 176513, 83335, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_83335_176513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83335 ⟨176513, by decide⟩ :=
  accepted_of_selected 13 83335 ⟨176513, by decide⟩ ⟨13, 2, 0, 176513, 83335, 1157, 16384⟩
    (by decide) selected_cut_05767

theorem unmarked_context_12_20833_176514 : frontier 9 ⟨176514, by decide⟩
    (prefixCache 12 20833) (prefixPartial 12 20833) = false := by
  decide +kernel

theorem node_context_12_20833_176514 : EJMOriginalGlobalDAGData.nodes 9 ⟨176514, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨176485, by decide⟩,⟨176508, by decide⟩,⟨176513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20833_176514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20833 ⟨176514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20833
    ⟨176514, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨176485, by decide⟩,⟨176508, by decide⟩,⟨176513, by decide⟩]) unmarked_context_12_20833_176514 node_context_12_20833_176514
  intro a
  fin_cases a
  · exact context_13_83332_3444
  · exact context_13_83333_176485
  · exact context_13_83334_176508
  · exact context_13_83335_176513

theorem selected_cut_05768 : selected 9 ⟨176559, by decide⟩
    (prefixPartial 12 20834) = some ⟨12, 2, 0, 176559, 20834, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_20834_176559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20834 ⟨176559, by decide⟩ :=
  accepted_of_selected 12 20834 ⟨176559, by decide⟩ ⟨12, 2, 0, 176559, 20834, 3945, 65536⟩
    (by decide) selected_cut_05768

theorem selected_cut_05769 : selected 9 ⟨176603, by decide⟩
    (prefixPartial 12 20835) = some ⟨12, 2, 0, 176603, 20835, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_20835_176603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20835 ⟨176603, by decide⟩ :=
  accepted_of_selected 12 20835 ⟨176603, by decide⟩ ⟨12, 2, 0, 176603, 20835, 3765, 65536⟩
    (by decide) selected_cut_05769

theorem unmarked_context_11_5208_176604 : frontier 10 ⟨176604, by decide⟩
    (prefixCache 11 5208) (prefixPartial 11 5208) = false := by
  decide +kernel

theorem node_context_11_5208_176604 : EJMOriginalGlobalDAGData.nodes 10 ⟨176604, by decide⟩ =
    .split (coordinate 11) (![⟨176474, by decide⟩,⟨176514, by decide⟩,⟨176559, by decide⟩,⟨176603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5208_176604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5208 ⟨176604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5208
    ⟨176604, by decide⟩ (by decide) (![⟨176474, by decide⟩,⟨176514, by decide⟩,⟨176559, by decide⟩,⟨176603, by decide⟩]) unmarked_context_11_5208_176604 node_context_11_5208_176604
  intro a
  fin_cases a
  · exact context_12_20832_176474
  · exact context_12_20833_176514
  · exact context_12_20834_176559
  · exact context_12_20835_176603

theorem selected_cut_05770 : selected 9 ⟨176636, by decide⟩
    (prefixPartial 12 20836) = some ⟨12, 2, 0, 176636, 20836, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_20836_176636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20836 ⟨176636, by decide⟩ :=
  accepted_of_selected 12 20836 ⟨176636, by decide⟩ ⟨12, 2, 0, 176636, 20836, 2157, 65536⟩
    (by decide) selected_cut_05770

theorem selected_cut_05771 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 20837) = some ⟨12, 1, 0, 126884, 20837, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20837_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20837 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 20837 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 20837, 1, 65536⟩
    (by decide) selected_cut_05771

theorem selected_cut_05772 : selected 9 ⟨176682, by decide⟩
    (prefixPartial 12 20838) = some ⟨12, 2, 0, 176682, 20838, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_20838_176682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20838 ⟨176682, by decide⟩ :=
  accepted_of_selected 12 20838 ⟨176682, by decide⟩ ⟨12, 2, 0, 176682, 20838, 3065, 65536⟩
    (by decide) selected_cut_05772

theorem selected_cut_05773 : selected 9 ⟨176732, by decide⟩
    (prefixPartial 12 20839) = some ⟨12, 2, 0, 176732, 20839, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_20839_176732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20839 ⟨176732, by decide⟩ :=
  accepted_of_selected 12 20839 ⟨176732, by decide⟩ ⟨12, 2, 0, 176732, 20839, 2757, 65536⟩
    (by decide) selected_cut_05773

theorem unmarked_context_11_5209_176733 : frontier 10 ⟨176733, by decide⟩
    (prefixCache 11 5209) (prefixPartial 11 5209) = false := by
  decide +kernel

theorem node_context_11_5209_176733 : EJMOriginalGlobalDAGData.nodes 10 ⟨176733, by decide⟩ =
    .split (coordinate 11) (![⟨176636, by decide⟩,⟨126884, by decide⟩,⟨176682, by decide⟩,⟨176732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5209_176733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5209 ⟨176733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5209
    ⟨176733, by decide⟩ (by decide) (![⟨176636, by decide⟩,⟨126884, by decide⟩,⟨176682, by decide⟩,⟨176732, by decide⟩]) unmarked_context_11_5209_176733 node_context_11_5209_176733
  intro a
  fin_cases a
  · exact context_12_20836_176636
  · exact context_12_20837_126884
  · exact context_12_20838_176682
  · exact context_12_20839_176732

theorem selected_cut_05774 : selected 9 ⟨176770, by decide⟩
    (prefixPartial 12 20840) = some ⟨12, 2, 0, 176770, 20840, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_20840_176770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20840 ⟨176770, by decide⟩ :=
  accepted_of_selected 12 20840 ⟨176770, by decide⟩ ⟨12, 2, 0, 176770, 20840, 2761, 65536⟩
    (by decide) selected_cut_05774

theorem selected_cut_05775 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83364) = some ⟨13, 1, 0, 3444, 83364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83364, 1, 16384⟩
    (by decide) selected_cut_05775

theorem selected_cut_05776 : selected 8 ⟨176780, by decide⟩
    (prefixPartial 13 83365) = some ⟨13, 2, 0, 176780, 83365, 721, 16384⟩ := by
  decide +kernel

theorem context_13_83365_176780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83365 ⟨176780, by decide⟩ :=
  accepted_of_selected 13 83365 ⟨176780, by decide⟩ ⟨13, 2, 0, 176780, 83365, 721, 16384⟩
    (by decide) selected_cut_05776

theorem selected_cut_05777 : selected 8 ⟨176803, by decide⟩
    (prefixPartial 13 83366) = some ⟨13, 2, 0, 176803, 83366, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_83366_176803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83366 ⟨176803, by decide⟩ :=
  accepted_of_selected 13 83366 ⟨176803, by decide⟩ ⟨13, 2, 0, 176803, 83366, 2313, 16384⟩
    (by decide) selected_cut_05777

theorem selected_cut_05778 : selected 8 ⟨176815, by decide⟩
    (prefixPartial 13 83367) = some ⟨13, 2, 0, 176815, 83367, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_83367_176815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83367 ⟨176815, by decide⟩ :=
  accepted_of_selected 13 83367 ⟨176815, by decide⟩ ⟨13, 2, 0, 176815, 83367, 1213, 16384⟩
    (by decide) selected_cut_05778

theorem unmarked_context_12_20841_176816 : frontier 9 ⟨176816, by decide⟩
    (prefixCache 12 20841) (prefixPartial 12 20841) = false := by
  decide +kernel

theorem node_context_12_20841_176816 : EJMOriginalGlobalDAGData.nodes 9 ⟨176816, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨176780, by decide⟩,⟨176803, by decide⟩,⟨176815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20841_176816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20841 ⟨176816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20841
    ⟨176816, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨176780, by decide⟩,⟨176803, by decide⟩,⟨176815, by decide⟩]) unmarked_context_12_20841_176816 node_context_12_20841_176816
  intro a
  fin_cases a
  · exact context_13_83364_3444
  · exact context_13_83365_176780
  · exact context_13_83366_176803
  · exact context_13_83367_176815

theorem selected_cut_05779 : selected 9 ⟨176854, by decide⟩
    (prefixPartial 12 20842) = some ⟨12, 2, 0, 176854, 20842, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_20842_176854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20842 ⟨176854, by decide⟩ :=
  accepted_of_selected 12 20842 ⟨176854, by decide⟩ ⟨12, 2, 0, 176854, 20842, 3577, 65536⟩
    (by decide) selected_cut_05779

theorem selected_cut_05780 : selected 9 ⟨176895, by decide⟩
    (prefixPartial 12 20843) = some ⟨12, 2, 0, 176895, 20843, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_20843_176895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20843 ⟨176895, by decide⟩ :=
  accepted_of_selected 12 20843 ⟨176895, by decide⟩ ⟨12, 2, 0, 176895, 20843, 3489, 65536⟩
    (by decide) selected_cut_05780

theorem unmarked_context_11_5210_176896 : frontier 10 ⟨176896, by decide⟩
    (prefixCache 11 5210) (prefixPartial 11 5210) = false := by
  decide +kernel

theorem node_context_11_5210_176896 : EJMOriginalGlobalDAGData.nodes 10 ⟨176896, by decide⟩ =
    .split (coordinate 11) (![⟨176770, by decide⟩,⟨176816, by decide⟩,⟨176854, by decide⟩,⟨176895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5210_176896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5210 ⟨176896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5210
    ⟨176896, by decide⟩ (by decide) (![⟨176770, by decide⟩,⟨176816, by decide⟩,⟨176854, by decide⟩,⟨176895, by decide⟩]) unmarked_context_11_5210_176896 node_context_11_5210_176896
  intro a
  fin_cases a
  · exact context_12_20840_176770
  · exact context_12_20841_176816
  · exact context_12_20842_176854
  · exact context_12_20843_176895

theorem selected_cut_05781 : selected 9 ⟨176936, by decide⟩
    (prefixPartial 12 20844) = some ⟨12, 2, 0, 176936, 20844, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_20844_176936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20844 ⟨176936, by decide⟩ :=
  accepted_of_selected 12 20844 ⟨176936, by decide⟩ ⟨12, 2, 0, 176936, 20844, 2677, 65536⟩
    (by decide) selected_cut_05781

theorem selected_cut_05782 : selected 9 ⟨176979, by decide⟩
    (prefixPartial 12 20845) = some ⟨12, 2, 0, 176979, 20845, 3969, 65536⟩ := by
  decide +kernel

theorem context_12_20845_176979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20845 ⟨176979, by decide⟩ :=
  accepted_of_selected 12 20845 ⟨176979, by decide⟩ ⟨12, 2, 0, 176979, 20845, 3969, 65536⟩
    (by decide) selected_cut_05782

theorem selected_cut_05783 : selected 9 ⟨177010, by decide⟩
    (prefixPartial 12 20846) = some ⟨12, 2, 0, 177010, 20846, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_20846_177010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20846 ⟨177010, by decide⟩ :=
  accepted_of_selected 12 20846 ⟨177010, by decide⟩ ⟨12, 2, 0, 177010, 20846, 3421, 65536⟩
    (by decide) selected_cut_05783

theorem selected_cut_05784 : selected 9 ⟨177047, by decide⟩
    (prefixPartial 12 20847) = some ⟨12, 2, 0, 177047, 20847, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_20847_177047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20847 ⟨177047, by decide⟩ :=
  accepted_of_selected 12 20847 ⟨177047, by decide⟩ ⟨12, 2, 0, 177047, 20847, 3125, 65536⟩
    (by decide) selected_cut_05784

theorem unmarked_context_11_5211_177048 : frontier 10 ⟨177048, by decide⟩
    (prefixCache 11 5211) (prefixPartial 11 5211) = false := by
  decide +kernel

theorem node_context_11_5211_177048 : EJMOriginalGlobalDAGData.nodes 10 ⟨177048, by decide⟩ =
    .split (coordinate 11) (![⟨176936, by decide⟩,⟨176979, by decide⟩,⟨177010, by decide⟩,⟨177047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5211_177048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5211 ⟨177048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5211
    ⟨177048, by decide⟩ (by decide) (![⟨176936, by decide⟩,⟨176979, by decide⟩,⟨177010, by decide⟩,⟨177047, by decide⟩]) unmarked_context_11_5211_177048 node_context_11_5211_177048
  intro a
  fin_cases a
  · exact context_12_20844_176936
  · exact context_12_20845_176979
  · exact context_12_20846_177010
  · exact context_12_20847_177047

theorem unmarked_context_10_1302_177049 : frontier 11 ⟨177049, by decide⟩
    (prefixCache 10 1302) (prefixPartial 10 1302) = false := by
  decide +kernel

theorem node_context_10_1302_177049 : EJMOriginalGlobalDAGData.nodes 11 ⟨177049, by decide⟩ =
    .split (coordinate 10) (![⟨176604, by decide⟩,⟨176733, by decide⟩,⟨176896, by decide⟩,⟨177048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1302_177049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1302 ⟨177049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1302
    ⟨177049, by decide⟩ (by decide) (![⟨176604, by decide⟩,⟨176733, by decide⟩,⟨176896, by decide⟩,⟨177048, by decide⟩]) unmarked_context_10_1302_177049 node_context_10_1302_177049
  intro a
  fin_cases a
  · exact context_11_5208_176604
  · exact context_11_5209_176733
  · exact context_11_5210_176896
  · exact context_11_5211_177048

theorem selected_cut_05785 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1303) = some ⟨10, 1, 0, 3440, 1303, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1303_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1303 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1303 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1303, 1, 1048576⟩
    (by decide) selected_cut_05785

theorem unmarked_context_9_325_177050 : frontier 12 ⟨177050, by decide⟩
    (prefixCache 9 325) (prefixPartial 9 325) = false := by
  decide +kernel

theorem node_context_9_325_177050 : EJMOriginalGlobalDAGData.nodes 12 ⟨177050, by decide⟩ =
    .split (coordinate 9) (![⟨176032, by decide⟩,⟨176438, by decide⟩,⟨177049, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_325_177050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 325 ⟨177050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 325
    ⟨177050, by decide⟩ (by decide) (![⟨176032, by decide⟩,⟨176438, by decide⟩,⟨177049, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_325_177050 node_context_9_325_177050
  intro a
  fin_cases a
  · exact context_10_1300_176032
  · exact context_10_1301_176438
  · exact context_10_1302_177049
  · exact context_10_1303_3440

theorem selected_cut_05786 : selected 9 ⟨177081, by decide⟩
    (prefixPartial 12 20864) = some ⟨12, 2, 0, 177081, 20864, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_20864_177081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20864 ⟨177081, by decide⟩ :=
  accepted_of_selected 12 20864 ⟨177081, by decide⟩ ⟨12, 2, 0, 177081, 20864, 2829, 65536⟩
    (by decide) selected_cut_05786

theorem selected_cut_05787 : selected 9 ⟨177116, by decide⟩
    (prefixPartial 12 20865) = some ⟨12, 2, 0, 177116, 20865, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_20865_177116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20865 ⟨177116, by decide⟩ :=
  accepted_of_selected 12 20865 ⟨177116, by decide⟩ ⟨12, 2, 0, 177116, 20865, 3305, 65536⟩
    (by decide) selected_cut_05787

theorem selected_cut_05788 : selected 9 ⟨177158, by decide⟩
    (prefixPartial 12 20866) = some ⟨12, 2, 0, 177158, 20866, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_20866_177158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20866 ⟨177158, by decide⟩ :=
  accepted_of_selected 12 20866 ⟨177158, by decide⟩ ⟨12, 2, 0, 177158, 20866, 3345, 65536⟩
    (by decide) selected_cut_05788

theorem selected_cut_05789 : selected 9 ⟨177204, by decide⟩
    (prefixPartial 12 20867) = some ⟨12, 2, 0, 177204, 20867, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_20867_177204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20867 ⟨177204, by decide⟩ :=
  accepted_of_selected 12 20867 ⟨177204, by decide⟩ ⟨12, 2, 0, 177204, 20867, 3641, 65536⟩
    (by decide) selected_cut_05789

theorem unmarked_context_11_5216_177205 : frontier 10 ⟨177205, by decide⟩
    (prefixCache 11 5216) (prefixPartial 11 5216) = false := by
  decide +kernel

theorem node_context_11_5216_177205 : EJMOriginalGlobalDAGData.nodes 10 ⟨177205, by decide⟩ =
    .split (coordinate 11) (![⟨177081, by decide⟩,⟨177116, by decide⟩,⟨177158, by decide⟩,⟨177204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5216_177205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5216 ⟨177205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5216
    ⟨177205, by decide⟩ (by decide) (![⟨177081, by decide⟩,⟨177116, by decide⟩,⟨177158, by decide⟩,⟨177204, by decide⟩]) unmarked_context_11_5216_177205 node_context_11_5216_177205
  intro a
  fin_cases a
  · exact context_12_20864_177081
  · exact context_12_20865_177116
  · exact context_12_20866_177158
  · exact context_12_20867_177204

theorem selected_cut_05790 : selected 9 ⟨177229, by decide⟩
    (prefixPartial 12 20868) = some ⟨12, 2, 0, 177229, 20868, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_20868_177229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20868 ⟨177229, by decide⟩ :=
  accepted_of_selected 12 20868 ⟨177229, by decide⟩ ⟨12, 2, 0, 177229, 20868, 1601, 65536⟩
    (by decide) selected_cut_05790

theorem selected_cut_05791 : selected 9 ⟨177260, by decide⟩
    (prefixPartial 12 20869) = some ⟨12, 2, 0, 177260, 20869, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_20869_177260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20869 ⟨177260, by decide⟩ :=
  accepted_of_selected 12 20869 ⟨177260, by decide⟩ ⟨12, 2, 0, 177260, 20869, 2889, 65536⟩
    (by decide) selected_cut_05791

theorem selected_cut_05792 : selected 9 ⟨177287, by decide⟩
    (prefixPartial 12 20870) = some ⟨12, 2, 0, 177287, 20870, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_20870_177287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20870 ⟨177287, by decide⟩ :=
  accepted_of_selected 12 20870 ⟨177287, by decide⟩ ⟨12, 2, 0, 177287, 20870, 1821, 65536⟩
    (by decide) selected_cut_05792

theorem selected_cut_05793 : selected 9 ⟨177318, by decide⟩
    (prefixPartial 12 20871) = some ⟨12, 2, 0, 177318, 20871, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_20871_177318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20871 ⟨177318, by decide⟩ :=
  accepted_of_selected 12 20871 ⟨177318, by decide⟩ ⟨12, 2, 0, 177318, 20871, 1905, 65536⟩
    (by decide) selected_cut_05793

theorem unmarked_context_11_5217_177319 : frontier 10 ⟨177319, by decide⟩
    (prefixCache 11 5217) (prefixPartial 11 5217) = false := by
  decide +kernel

theorem node_context_11_5217_177319 : EJMOriginalGlobalDAGData.nodes 10 ⟨177319, by decide⟩ =
    .split (coordinate 11) (![⟨177229, by decide⟩,⟨177260, by decide⟩,⟨177287, by decide⟩,⟨177318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5217_177319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5217 ⟨177319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5217
    ⟨177319, by decide⟩ (by decide) (![⟨177229, by decide⟩,⟨177260, by decide⟩,⟨177287, by decide⟩,⟨177318, by decide⟩]) unmarked_context_11_5217_177319 node_context_11_5217_177319
  intro a
  fin_cases a
  · exact context_12_20868_177229
  · exact context_12_20869_177260
  · exact context_12_20870_177287
  · exact context_12_20871_177318

theorem selected_cut_05794 : selected 9 ⟨177354, by decide⟩
    (prefixPartial 12 20872) = some ⟨12, 2, 0, 177354, 20872, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_20872_177354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20872 ⟨177354, by decide⟩ :=
  accepted_of_selected 12 20872 ⟨177354, by decide⟩ ⟨12, 2, 0, 177354, 20872, 1965, 65536⟩
    (by decide) selected_cut_05794

theorem selected_cut_05795 : selected 9 ⟨177389, by decide⟩
    (prefixPartial 12 20873) = some ⟨12, 2, 0, 177389, 20873, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_20873_177389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20873 ⟨177389, by decide⟩ :=
  accepted_of_selected 12 20873 ⟨177389, by decide⟩ ⟨12, 2, 0, 177389, 20873, 2273, 65536⟩
    (by decide) selected_cut_05795

theorem selected_cut_05796 : selected 9 ⟨177422, by decide⟩
    (prefixPartial 12 20874) = some ⟨12, 2, 0, 177422, 20874, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_20874_177422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20874 ⟨177422, by decide⟩ :=
  accepted_of_selected 12 20874 ⟨177422, by decide⟩ ⟨12, 2, 0, 177422, 20874, 2081, 65536⟩
    (by decide) selected_cut_05796

theorem selected_cut_05797 : selected 9 ⟨177450, by decide⟩
    (prefixPartial 12 20875) = some ⟨12, 2, 0, 177450, 20875, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_20875_177450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20875 ⟨177450, by decide⟩ :=
  accepted_of_selected 12 20875 ⟨177450, by decide⟩ ⟨12, 2, 0, 177450, 20875, 2341, 65536⟩
    (by decide) selected_cut_05797

theorem unmarked_context_11_5218_177451 : frontier 10 ⟨177451, by decide⟩
    (prefixCache 11 5218) (prefixPartial 11 5218) = false := by
  decide +kernel

theorem node_context_11_5218_177451 : EJMOriginalGlobalDAGData.nodes 10 ⟨177451, by decide⟩ =
    .split (coordinate 11) (![⟨177354, by decide⟩,⟨177389, by decide⟩,⟨177422, by decide⟩,⟨177450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5218_177451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5218 ⟨177451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5218
    ⟨177451, by decide⟩ (by decide) (![⟨177354, by decide⟩,⟨177389, by decide⟩,⟨177422, by decide⟩,⟨177450, by decide⟩]) unmarked_context_11_5218_177451 node_context_11_5218_177451
  intro a
  fin_cases a
  · exact context_12_20872_177354
  · exact context_12_20873_177389
  · exact context_12_20874_177422
  · exact context_12_20875_177450

theorem selected_cut_05798 : selected 9 ⟨177485, by decide⟩
    (prefixPartial 12 20876) = some ⟨12, 2, 0, 177485, 20876, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_20876_177485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20876 ⟨177485, by decide⟩ :=
  accepted_of_selected 12 20876 ⟨177485, by decide⟩ ⟨12, 2, 0, 177485, 20876, 1709, 65536⟩
    (by decide) selected_cut_05798

theorem selected_cut_05799 : selected 9 ⟨177522, by decide⟩
    (prefixPartial 12 20877) = some ⟨12, 2, 0, 177522, 20877, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_20877_177522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20877 ⟨177522, by decide⟩ :=
  accepted_of_selected 12 20877 ⟨177522, by decide⟩ ⟨12, 2, 0, 177522, 20877, 1969, 65536⟩
    (by decide) selected_cut_05799

theorem selected_cut_05800 : selected 9 ⟨177556, by decide⟩
    (prefixPartial 12 20878) = some ⟨12, 2, 0, 177556, 20878, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_20878_177556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20878 ⟨177556, by decide⟩ :=
  accepted_of_selected 12 20878 ⟨177556, by decide⟩ ⟨12, 2, 0, 177556, 20878, 1873, 65536⟩
    (by decide) selected_cut_05800

theorem selected_cut_05801 : selected 9 ⟨177581, by decide⟩
    (prefixPartial 12 20879) = some ⟨12, 2, 0, 177581, 20879, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_20879_177581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20879 ⟨177581, by decide⟩ :=
  accepted_of_selected 12 20879 ⟨177581, by decide⟩ ⟨12, 2, 0, 177581, 20879, 1997, 65536⟩
    (by decide) selected_cut_05801

theorem unmarked_context_11_5219_177582 : frontier 10 ⟨177582, by decide⟩
    (prefixCache 11 5219) (prefixPartial 11 5219) = false := by
  decide +kernel

theorem node_context_11_5219_177582 : EJMOriginalGlobalDAGData.nodes 10 ⟨177582, by decide⟩ =
    .split (coordinate 11) (![⟨177485, by decide⟩,⟨177522, by decide⟩,⟨177556, by decide⟩,⟨177581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5219_177582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5219 ⟨177582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5219
    ⟨177582, by decide⟩ (by decide) (![⟨177485, by decide⟩,⟨177522, by decide⟩,⟨177556, by decide⟩,⟨177581, by decide⟩]) unmarked_context_11_5219_177582 node_context_11_5219_177582
  intro a
  fin_cases a
  · exact context_12_20876_177485
  · exact context_12_20877_177522
  · exact context_12_20878_177556
  · exact context_12_20879_177581

theorem unmarked_context_10_1304_177583 : frontier 11 ⟨177583, by decide⟩
    (prefixCache 10 1304) (prefixPartial 10 1304) = false := by
  decide +kernel

theorem node_context_10_1304_177583 : EJMOriginalGlobalDAGData.nodes 11 ⟨177583, by decide⟩ =
    .split (coordinate 10) (![⟨177205, by decide⟩,⟨177319, by decide⟩,⟨177451, by decide⟩,⟨177582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1304_177583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1304 ⟨177583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1304
    ⟨177583, by decide⟩ (by decide) (![⟨177205, by decide⟩,⟨177319, by decide⟩,⟨177451, by decide⟩,⟨177582, by decide⟩]) unmarked_context_10_1304_177583 node_context_10_1304_177583
  intro a
  fin_cases a
  · exact context_11_5216_177205
  · exact context_11_5217_177319
  · exact context_11_5218_177451
  · exact context_11_5219_177582

theorem selected_cut_05802 : selected 9 ⟨177601, by decide⟩
    (prefixPartial 12 20880) = some ⟨12, 2, 0, 177601, 20880, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_20880_177601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20880 ⟨177601, by decide⟩ :=
  accepted_of_selected 12 20880 ⟨177601, by decide⟩ ⟨12, 2, 0, 177601, 20880, 1313, 65536⟩
    (by decide) selected_cut_05802

theorem selected_cut_05803 : selected 9 ⟨177624, by decide⟩
    (prefixPartial 12 20881) = some ⟨12, 2, 0, 177624, 20881, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_20881_177624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20881 ⟨177624, by decide⟩ :=
  accepted_of_selected 12 20881 ⟨177624, by decide⟩ ⟨12, 2, 0, 177624, 20881, 1385, 65536⟩
    (by decide) selected_cut_05803

theorem selected_cut_05804 : selected 9 ⟨177649, by decide⟩
    (prefixPartial 12 20882) = some ⟨12, 2, 0, 177649, 20882, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_20882_177649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20882 ⟨177649, by decide⟩ :=
  accepted_of_selected 12 20882 ⟨177649, by decide⟩ ⟨12, 2, 0, 177649, 20882, 1537, 65536⟩
    (by decide) selected_cut_05804

theorem selected_cut_05805 : selected 9 ⟨177674, by decide⟩
    (prefixPartial 12 20883) = some ⟨12, 2, 0, 177674, 20883, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_20883_177674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20883 ⟨177674, by decide⟩ :=
  accepted_of_selected 12 20883 ⟨177674, by decide⟩ ⟨12, 2, 0, 177674, 20883, 1761, 65536⟩
    (by decide) selected_cut_05805

theorem unmarked_context_11_5220_177675 : frontier 10 ⟨177675, by decide⟩
    (prefixCache 11 5220) (prefixPartial 11 5220) = false := by
  decide +kernel

theorem node_context_11_5220_177675 : EJMOriginalGlobalDAGData.nodes 10 ⟨177675, by decide⟩ =
    .split (coordinate 11) (![⟨177601, by decide⟩,⟨177624, by decide⟩,⟨177649, by decide⟩,⟨177674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5220_177675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5220 ⟨177675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5220
    ⟨177675, by decide⟩ (by decide) (![⟨177601, by decide⟩,⟨177624, by decide⟩,⟨177649, by decide⟩,⟨177674, by decide⟩]) unmarked_context_11_5220_177675 node_context_11_5220_177675
  intro a
  fin_cases a
  · exact context_12_20880_177601
  · exact context_12_20881_177624
  · exact context_12_20882_177649
  · exact context_12_20883_177674

theorem selected_cut_05806 : selected 9 ⟨177691, by decide⟩
    (prefixPartial 12 20884) = some ⟨12, 2, 0, 177691, 20884, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_20884_177691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20884 ⟨177691, by decide⟩ :=
  accepted_of_selected 12 20884 ⟨177691, by decide⟩ ⟨12, 2, 0, 177691, 20884, 1065, 65536⟩
    (by decide) selected_cut_05806

theorem selected_cut_05807 : selected 9 ⟨177716, by decide⟩
    (prefixPartial 12 20885) = some ⟨12, 2, 0, 177716, 20885, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_20885_177716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20885 ⟨177716, by decide⟩ :=
  accepted_of_selected 12 20885 ⟨177716, by decide⟩ ⟨12, 2, 0, 177716, 20885, 1705, 65536⟩
    (by decide) selected_cut_05807

theorem selected_cut_05808 : selected 9 ⟨177735, by decide⟩
    (prefixPartial 12 20886) = some ⟨12, 2, 0, 177735, 20886, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_20886_177735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20886 ⟨177735, by decide⟩ :=
  accepted_of_selected 12 20886 ⟨177735, by decide⟩ ⟨12, 2, 0, 177735, 20886, 1085, 65536⟩
    (by decide) selected_cut_05808

theorem selected_cut_05809 : selected 9 ⟨177754, by decide⟩
    (prefixPartial 12 20887) = some ⟨12, 2, 0, 177754, 20887, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_20887_177754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20887 ⟨177754, by decide⟩ :=
  accepted_of_selected 12 20887 ⟨177754, by decide⟩ ⟨12, 2, 0, 177754, 20887, 1177, 65536⟩
    (by decide) selected_cut_05809

theorem unmarked_context_11_5221_177755 : frontier 10 ⟨177755, by decide⟩
    (prefixCache 11 5221) (prefixPartial 11 5221) = false := by
  decide +kernel

theorem node_context_11_5221_177755 : EJMOriginalGlobalDAGData.nodes 10 ⟨177755, by decide⟩ =
    .split (coordinate 11) (![⟨177691, by decide⟩,⟨177716, by decide⟩,⟨177735, by decide⟩,⟨177754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5221_177755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5221 ⟨177755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5221
    ⟨177755, by decide⟩ (by decide) (![⟨177691, by decide⟩,⟨177716, by decide⟩,⟨177735, by decide⟩,⟨177754, by decide⟩]) unmarked_context_11_5221_177755 node_context_11_5221_177755
  intro a
  fin_cases a
  · exact context_12_20884_177691
  · exact context_12_20885_177716
  · exact context_12_20886_177735
  · exact context_12_20887_177754

theorem selected_cut_05810 : selected 9 ⟨177772, by decide⟩
    (prefixPartial 12 20888) = some ⟨12, 2, 0, 177772, 20888, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_20888_177772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20888 ⟨177772, by decide⟩ :=
  accepted_of_selected 12 20888 ⟨177772, by decide⟩ ⟨12, 2, 0, 177772, 20888, 1153, 65536⟩
    (by decide) selected_cut_05810

theorem selected_cut_05811 : selected 9 ⟨177790, by decide⟩
    (prefixPartial 12 20889) = some ⟨12, 2, 0, 177790, 20889, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_20889_177790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20889 ⟨177790, by decide⟩ :=
  accepted_of_selected 12 20889 ⟨177790, by decide⟩ ⟨12, 2, 0, 177790, 20889, 1189, 65536⟩
    (by decide) selected_cut_05811

theorem selected_cut_05812 : selected 9 ⟨177807, by decide⟩
    (prefixPartial 12 20890) = some ⟨12, 2, 0, 177807, 20890, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_20890_177807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20890 ⟨177807, by decide⟩ :=
  accepted_of_selected 12 20890 ⟨177807, by decide⟩ ⟨12, 2, 0, 177807, 20890, 1109, 65536⟩
    (by decide) selected_cut_05812

theorem selected_cut_05813 : selected 9 ⟨177828, by decide⟩
    (prefixPartial 12 20891) = some ⟨12, 2, 0, 177828, 20891, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_20891_177828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20891 ⟨177828, by decide⟩ :=
  accepted_of_selected 12 20891 ⟨177828, by decide⟩ ⟨12, 2, 0, 177828, 20891, 1313, 65536⟩
    (by decide) selected_cut_05813

theorem unmarked_context_11_5222_177829 : frontier 10 ⟨177829, by decide⟩
    (prefixCache 11 5222) (prefixPartial 11 5222) = false := by
  decide +kernel

theorem node_context_11_5222_177829 : EJMOriginalGlobalDAGData.nodes 10 ⟨177829, by decide⟩ =
    .split (coordinate 11) (![⟨177772, by decide⟩,⟨177790, by decide⟩,⟨177807, by decide⟩,⟨177828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5222_177829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5222 ⟨177829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5222
    ⟨177829, by decide⟩ (by decide) (![⟨177772, by decide⟩,⟨177790, by decide⟩,⟨177807, by decide⟩,⟨177828, by decide⟩]) unmarked_context_11_5222_177829 node_context_11_5222_177829
  intro a
  fin_cases a
  · exact context_12_20888_177772
  · exact context_12_20889_177790
  · exact context_12_20890_177807
  · exact context_12_20891_177828

theorem selected_cut_05814 : selected 9 ⟨177844, by decide⟩
    (prefixPartial 12 20892) = some ⟨12, 2, 0, 177844, 20892, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_20892_177844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20892 ⟨177844, by decide⟩ :=
  accepted_of_selected 12 20892 ⟨177844, by decide⟩ ⟨12, 2, 0, 177844, 20892, 1017, 65536⟩
    (by decide) selected_cut_05814

theorem selected_cut_05815 : selected 9 ⟨177863, by decide⟩
    (prefixPartial 12 20893) = some ⟨12, 2, 0, 177863, 20893, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_20893_177863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20893 ⟨177863, by decide⟩ :=
  accepted_of_selected 12 20893 ⟨177863, by decide⟩ ⟨12, 2, 0, 177863, 20893, 1069, 65536⟩
    (by decide) selected_cut_05815

theorem selected_cut_05816 : selected 9 ⟨177884, by decide⟩
    (prefixPartial 12 20894) = some ⟨12, 2, 0, 177884, 20894, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_20894_177884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20894 ⟨177884, by decide⟩ :=
  accepted_of_selected 12 20894 ⟨177884, by decide⟩ ⟨12, 2, 0, 177884, 20894, 1033, 65536⟩
    (by decide) selected_cut_05816

theorem selected_cut_05817 : selected 9 ⟨177902, by decide⟩
    (prefixPartial 12 20895) = some ⟨12, 2, 0, 177902, 20895, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_20895_177902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20895 ⟨177902, by decide⟩ :=
  accepted_of_selected 12 20895 ⟨177902, by decide⟩ ⟨12, 2, 0, 177902, 20895, 1093, 65536⟩
    (by decide) selected_cut_05817

theorem unmarked_context_11_5223_177903 : frontier 10 ⟨177903, by decide⟩
    (prefixCache 11 5223) (prefixPartial 11 5223) = false := by
  decide +kernel

theorem node_context_11_5223_177903 : EJMOriginalGlobalDAGData.nodes 10 ⟨177903, by decide⟩ =
    .split (coordinate 11) (![⟨177844, by decide⟩,⟨177863, by decide⟩,⟨177884, by decide⟩,⟨177902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5223_177903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5223 ⟨177903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5223
    ⟨177903, by decide⟩ (by decide) (![⟨177844, by decide⟩,⟨177863, by decide⟩,⟨177884, by decide⟩,⟨177902, by decide⟩]) unmarked_context_11_5223_177903 node_context_11_5223_177903
  intro a
  fin_cases a
  · exact context_12_20892_177844
  · exact context_12_20893_177863
  · exact context_12_20894_177884
  · exact context_12_20895_177902

theorem unmarked_context_10_1305_177904 : frontier 11 ⟨177904, by decide⟩
    (prefixCache 10 1305) (prefixPartial 10 1305) = false := by
  decide +kernel

theorem node_context_10_1305_177904 : EJMOriginalGlobalDAGData.nodes 11 ⟨177904, by decide⟩ =
    .split (coordinate 10) (![⟨177675, by decide⟩,⟨177755, by decide⟩,⟨177829, by decide⟩,⟨177903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1305_177904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1305 ⟨177904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1305
    ⟨177904, by decide⟩ (by decide) (![⟨177675, by decide⟩,⟨177755, by decide⟩,⟨177829, by decide⟩,⟨177903, by decide⟩]) unmarked_context_10_1305_177904 node_context_10_1305_177904
  intro a
  fin_cases a
  · exact context_11_5220_177675
  · exact context_11_5221_177755
  · exact context_11_5222_177829
  · exact context_11_5223_177903

theorem selected_cut_05818 : selected 10 ⟨177961, by decide⟩
    (prefixPartial 11 5224) = some ⟨11, 2, 0, 177961, 5224, 3849, 262144⟩ := by
  decide +kernel

theorem context_11_5224_177961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5224 ⟨177961, by decide⟩ :=
  accepted_of_selected 11 5224 ⟨177961, by decide⟩ ⟨11, 2, 0, 177961, 5224, 3849, 262144⟩
    (by decide) selected_cut_05818

theorem selected_cut_05819 : selected 10 ⟨178011, by decide⟩
    (prefixPartial 11 5225) = some ⟨11, 2, 0, 178011, 5225, 2981, 262144⟩ := by
  decide +kernel

theorem context_11_5225_178011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5225 ⟨178011, by decide⟩ :=
  accepted_of_selected 11 5225 ⟨178011, by decide⟩ ⟨11, 2, 0, 178011, 5225, 2981, 262144⟩
    (by decide) selected_cut_05819

theorem selected_cut_05820 : selected 10 ⟨178065, by decide⟩
    (prefixPartial 11 5226) = some ⟨11, 2, 0, 178065, 5226, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_5226_178065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5226 ⟨178065, by decide⟩ :=
  accepted_of_selected 11 5226 ⟨178065, by decide⟩ ⟨11, 2, 0, 178065, 5226, 2845, 262144⟩
    (by decide) selected_cut_05820

theorem selected_cut_05821 : selected 10 ⟨178119, by decide⟩
    (prefixPartial 11 5227) = some ⟨11, 2, 0, 178119, 5227, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_5227_178119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5227 ⟨178119, by decide⟩ :=
  accepted_of_selected 11 5227 ⟨178119, by decide⟩ ⟨11, 2, 0, 178119, 5227, 2489, 262144⟩
    (by decide) selected_cut_05821

theorem unmarked_context_10_1306_178120 : frontier 11 ⟨178120, by decide⟩
    (prefixCache 10 1306) (prefixPartial 10 1306) = false := by
  decide +kernel

theorem node_context_10_1306_178120 : EJMOriginalGlobalDAGData.nodes 11 ⟨178120, by decide⟩ =
    .split (coordinate 10) (![⟨177961, by decide⟩,⟨178011, by decide⟩,⟨178065, by decide⟩,⟨178119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1306_178120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1306 ⟨178120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1306
    ⟨178120, by decide⟩ (by decide) (![⟨177961, by decide⟩,⟨178011, by decide⟩,⟨178065, by decide⟩,⟨178119, by decide⟩]) unmarked_context_10_1306_178120 node_context_10_1306_178120
  intro a
  fin_cases a
  · exact context_11_5224_177961
  · exact context_11_5225_178011
  · exact context_11_5226_178065
  · exact context_11_5227_178119

theorem selected_cut_05822 : selected 10 ⟨178146, by decide⟩
    (prefixPartial 11 5228) = some ⟨11, 2, 0, 178146, 5228, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_5228_178146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5228 ⟨178146, by decide⟩ :=
  accepted_of_selected 11 5228 ⟨178146, by decide⟩ ⟨11, 2, 0, 178146, 5228, 1821, 262144⟩
    (by decide) selected_cut_05822

theorem selected_cut_05823 : selected 10 ⟨178170, by decide⟩
    (prefixPartial 11 5229) = some ⟨11, 2, 0, 178170, 5229, 1225, 262144⟩ := by
  decide +kernel

theorem context_11_5229_178170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5229 ⟨178170, by decide⟩ :=
  accepted_of_selected 11 5229 ⟨178170, by decide⟩ ⟨11, 2, 0, 178170, 5229, 1225, 262144⟩
    (by decide) selected_cut_05823

theorem selected_cut_05824 : selected 10 ⟨178194, by decide⟩
    (prefixPartial 11 5230) = some ⟨11, 2, 0, 178194, 5230, 873, 262144⟩ := by
  decide +kernel

theorem context_11_5230_178194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5230 ⟨178194, by decide⟩ :=
  accepted_of_selected 11 5230 ⟨178194, by decide⟩ ⟨11, 2, 0, 178194, 5230, 873, 262144⟩
    (by decide) selected_cut_05824

theorem selected_cut_05825 : selected 10 ⟨178210, by decide⟩
    (prefixPartial 11 5231) = some ⟨11, 2, 0, 178210, 5231, 345, 262144⟩ := by
  decide +kernel

theorem context_11_5231_178210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5231 ⟨178210, by decide⟩ :=
  accepted_of_selected 11 5231 ⟨178210, by decide⟩ ⟨11, 2, 0, 178210, 5231, 345, 262144⟩
    (by decide) selected_cut_05825

theorem unmarked_context_10_1307_178211 : frontier 11 ⟨178211, by decide⟩
    (prefixCache 10 1307) (prefixPartial 10 1307) = false := by
  decide +kernel

theorem node_context_10_1307_178211 : EJMOriginalGlobalDAGData.nodes 11 ⟨178211, by decide⟩ =
    .split (coordinate 10) (![⟨178146, by decide⟩,⟨178170, by decide⟩,⟨178194, by decide⟩,⟨178210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1307_178211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1307 ⟨178211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1307
    ⟨178211, by decide⟩ (by decide) (![⟨178146, by decide⟩,⟨178170, by decide⟩,⟨178194, by decide⟩,⟨178210, by decide⟩]) unmarked_context_10_1307_178211 node_context_10_1307_178211
  intro a
  fin_cases a
  · exact context_11_5228_178146
  · exact context_11_5229_178170
  · exact context_11_5230_178194
  · exact context_11_5231_178210

theorem unmarked_context_9_326_178212 : frontier 12 ⟨178212, by decide⟩
    (prefixCache 9 326) (prefixPartial 9 326) = false := by
  decide +kernel

theorem node_context_9_326_178212 : EJMOriginalGlobalDAGData.nodes 12 ⟨178212, by decide⟩ =
    .split (coordinate 9) (![⟨177583, by decide⟩,⟨177904, by decide⟩,⟨178120, by decide⟩,⟨178211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_326_178212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 326 ⟨178212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 326
    ⟨178212, by decide⟩ (by decide) (![⟨177583, by decide⟩,⟨177904, by decide⟩,⟨178120, by decide⟩,⟨178211, by decide⟩]) unmarked_context_9_326_178212 node_context_9_326_178212
  intro a
  fin_cases a
  · exact context_10_1304_177583
  · exact context_10_1305_177904
  · exact context_10_1306_178120
  · exact context_10_1307_178211

theorem selected_cut_05826 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 327) = some ⟨9, 1, 0, 4601, 327, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_327_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 327 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 327 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 327, 1, 4194304⟩
    (by decide) selected_cut_05826

theorem unmarked_context_8_81_178213 : frontier 13 ⟨178213, by decide⟩
    (prefixCache 8 81) (prefixPartial 8 81) = false := by
  decide +kernel

theorem node_context_8_81_178213 : EJMOriginalGlobalDAGData.nodes 13 ⟨178213, by decide⟩ =
    .split (coordinate 8) (![⟨175519, by decide⟩,⟨177050, by decide⟩,⟨178212, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_81_178213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 81 ⟨178213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 81
    ⟨178213, by decide⟩ (by decide) (![⟨175519, by decide⟩,⟨177050, by decide⟩,⟨178212, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_81_178213 node_context_8_81_178213
  intro a
  fin_cases a
  · exact context_9_324_175519
  · exact context_9_325_177050
  · exact context_9_326_178212
  · exact context_9_327_4601

theorem selected_cut_05827 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 5248) = some ⟨11, 1, 0, 167448, 5248, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5248_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5248 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 5248 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 5248, 1, 262144⟩
    (by decide) selected_cut_05827

theorem selected_cut_05828 : selected 8 ⟨178283, by decide⟩
    (prefixPartial 13 83984) = some ⟨13, 2, 0, 178283, 83984, 3365, 16384⟩ := by
  decide +kernel

theorem context_13_83984_178283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83984 ⟨178283, by decide⟩ :=
  accepted_of_selected 13 83984 ⟨178283, by decide⟩ ⟨13, 2, 0, 178283, 83984, 3365, 16384⟩
    (by decide) selected_cut_05828

theorem selected_cut_05829 : selected 8 ⟨178327, by decide⟩
    (prefixPartial 13 83985) = some ⟨13, 2, 0, 178327, 83985, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_83985_178327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83985 ⟨178327, by decide⟩ :=
  accepted_of_selected 13 83985 ⟨178327, by decide⟩ ⟨13, 2, 0, 178327, 83985, 3245, 16384⟩
    (by decide) selected_cut_05829

theorem selected_cut_05830 : selected 8 ⟨178358, by decide⟩
    (prefixPartial 13 83986) = some ⟨13, 2, 0, 178358, 83986, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_83986_178358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83986 ⟨178358, by decide⟩ :=
  accepted_of_selected 13 83986 ⟨178358, by decide⟩ ⟨13, 2, 0, 178358, 83986, 1829, 16384⟩
    (by decide) selected_cut_05830

theorem selected_cut_05831 : selected 8 ⟨178377, by decide⟩
    (prefixPartial 13 83987) = some ⟨13, 2, 0, 178377, 83987, 981, 16384⟩ := by
  decide +kernel

theorem context_13_83987_178377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83987 ⟨178377, by decide⟩ :=
  accepted_of_selected 13 83987 ⟨178377, by decide⟩ ⟨13, 2, 0, 178377, 83987, 981, 16384⟩
    (by decide) selected_cut_05831

theorem unmarked_context_12_20996_178378 : frontier 9 ⟨178378, by decide⟩
    (prefixCache 12 20996) (prefixPartial 12 20996) = false := by
  decide +kernel

theorem node_context_12_20996_178378 : EJMOriginalGlobalDAGData.nodes 9 ⟨178378, by decide⟩ =
    .split (coordinate 12) (![⟨178283, by decide⟩,⟨178327, by decide⟩,⟨178358, by decide⟩,⟨178377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20996_178378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20996 ⟨178378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20996
    ⟨178378, by decide⟩ (by decide) (![⟨178283, by decide⟩,⟨178327, by decide⟩,⟨178358, by decide⟩,⟨178377, by decide⟩]) unmarked_context_12_20996_178378 node_context_12_20996_178378
  intro a
  fin_cases a
  · exact context_13_83984_178283
  · exact context_13_83985_178327
  · exact context_13_83986_178358
  · exact context_13_83987_178377

theorem selected_cut_05832 : selected 8 ⟨178434, by decide⟩
    (prefixPartial 13 83988) = some ⟨13, 2, 0, 178434, 83988, 3309, 16384⟩ := by
  decide +kernel

theorem context_13_83988_178434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83988 ⟨178434, by decide⟩ :=
  accepted_of_selected 13 83988 ⟨178434, by decide⟩ ⟨13, 2, 0, 178434, 83988, 3309, 16384⟩
    (by decide) selected_cut_05832

theorem selected_cut_05833 : selected 8 ⟨178484, by decide⟩
    (prefixPartial 13 83989) = some ⟨13, 2, 0, 178484, 83989, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_83989_178484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83989 ⟨178484, by decide⟩ :=
  accepted_of_selected 13 83989 ⟨178484, by decide⟩ ⟨13, 2, 0, 178484, 83989, 3457, 16384⟩
    (by decide) selected_cut_05833

theorem selected_cut_05834 : selected 8 ⟨178507, by decide⟩
    (prefixPartial 13 83990) = some ⟨13, 2, 0, 178507, 83990, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_83990_178507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83990 ⟨178507, by decide⟩ :=
  accepted_of_selected 13 83990 ⟨178507, by decide⟩ ⟨13, 2, 0, 178507, 83990, 1881, 16384⟩
    (by decide) selected_cut_05834

theorem selected_cut_05835 : selected 8 ⟨178518, by decide⟩
    (prefixPartial 13 83991) = some ⟨13, 2, 0, 178518, 83991, 997, 16384⟩ := by
  decide +kernel

theorem context_13_83991_178518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83991 ⟨178518, by decide⟩ :=
  accepted_of_selected 13 83991 ⟨178518, by decide⟩ ⟨13, 2, 0, 178518, 83991, 997, 16384⟩
    (by decide) selected_cut_05835

theorem unmarked_context_12_20997_178519 : frontier 9 ⟨178519, by decide⟩
    (prefixCache 12 20997) (prefixPartial 12 20997) = false := by
  decide +kernel

theorem node_context_12_20997_178519 : EJMOriginalGlobalDAGData.nodes 9 ⟨178519, by decide⟩ =
    .split (coordinate 12) (![⟨178434, by decide⟩,⟨178484, by decide⟩,⟨178507, by decide⟩,⟨178518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20997_178519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20997 ⟨178519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20997
    ⟨178519, by decide⟩ (by decide) (![⟨178434, by decide⟩,⟨178484, by decide⟩,⟨178507, by decide⟩,⟨178518, by decide⟩]) unmarked_context_12_20997_178519 node_context_12_20997_178519
  intro a
  fin_cases a
  · exact context_13_83988_178434
  · exact context_13_83989_178484
  · exact context_13_83990_178507
  · exact context_13_83991_178518

theorem selected_cut_05836 : selected 8 ⟨178582, by decide⟩
    (prefixPartial 13 83992) = some ⟨13, 2, 0, 178582, 83992, 3685, 16384⟩ := by
  decide +kernel

theorem context_13_83992_178582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83992 ⟨178582, by decide⟩ :=
  accepted_of_selected 13 83992 ⟨178582, by decide⟩ ⟨13, 2, 0, 178582, 83992, 3685, 16384⟩
    (by decide) selected_cut_05836

theorem selected_cut_05837 : selected 8 ⟨178634, by decide⟩
    (prefixPartial 13 83993) = some ⟨13, 2, 0, 178634, 83993, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_83993_178634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83993 ⟨178634, by decide⟩ :=
  accepted_of_selected 13 83993 ⟨178634, by decide⟩ ⟨13, 2, 0, 178634, 83993, 3441, 16384⟩
    (by decide) selected_cut_05837

theorem selected_cut_05838 : selected 8 ⟨178653, by decide⟩
    (prefixPartial 13 83994) = some ⟨13, 2, 0, 178653, 83994, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_83994_178653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83994 ⟨178653, by decide⟩ :=
  accepted_of_selected 13 83994 ⟨178653, by decide⟩ ⟨13, 2, 0, 178653, 83994, 1857, 16384⟩
    (by decide) selected_cut_05838

theorem selected_cut_05839 : selected 8 ⟨178670, by decide⟩
    (prefixPartial 13 83995) = some ⟨13, 2, 0, 178670, 83995, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_83995_178670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83995 ⟨178670, by decide⟩ :=
  accepted_of_selected 13 83995 ⟨178670, by decide⟩ ⟨13, 2, 0, 178670, 83995, 1077, 16384⟩
    (by decide) selected_cut_05839

theorem unmarked_context_12_20998_178671 : frontier 9 ⟨178671, by decide⟩
    (prefixCache 12 20998) (prefixPartial 12 20998) = false := by
  decide +kernel

theorem node_context_12_20998_178671 : EJMOriginalGlobalDAGData.nodes 9 ⟨178671, by decide⟩ =
    .split (coordinate 12) (![⟨178582, by decide⟩,⟨178634, by decide⟩,⟨178653, by decide⟩,⟨178670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20998_178671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20998 ⟨178671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20998
    ⟨178671, by decide⟩ (by decide) (![⟨178582, by decide⟩,⟨178634, by decide⟩,⟨178653, by decide⟩,⟨178670, by decide⟩]) unmarked_context_12_20998_178671 node_context_12_20998_178671
  intro a
  fin_cases a
  · exact context_13_83992_178582
  · exact context_13_83993_178634
  · exact context_13_83994_178653
  · exact context_13_83995_178670

theorem selected_cut_05840 : selected 8 ⟨178736, by decide⟩
    (prefixPartial 13 83996) = some ⟨13, 2, 0, 178736, 83996, 3957, 16384⟩ := by
  decide +kernel

theorem context_13_83996_178736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83996 ⟨178736, by decide⟩ :=
  accepted_of_selected 13 83996 ⟨178736, by decide⟩ ⟨13, 2, 0, 178736, 83996, 3957, 16384⟩
    (by decide) selected_cut_05840

theorem selected_cut_05841 : selected 8 ⟨178783, by decide⟩
    (prefixPartial 13 83997) = some ⟨13, 2, 0, 178783, 83997, 3485, 16384⟩ := by
  decide +kernel

theorem context_13_83997_178783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83997 ⟨178783, by decide⟩ :=
  accepted_of_selected 13 83997 ⟨178783, by decide⟩ ⟨13, 2, 0, 178783, 83997, 3485, 16384⟩
    (by decide) selected_cut_05841

theorem selected_cut_05842 : selected 8 ⟨178809, by decide⟩
    (prefixPartial 13 83998) = some ⟨13, 2, 0, 178809, 83998, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_83998_178809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83998 ⟨178809, by decide⟩ :=
  accepted_of_selected 13 83998 ⟨178809, by decide⟩ ⟨13, 2, 0, 178809, 83998, 2049, 16384⟩
    (by decide) selected_cut_05842

theorem selected_cut_05843 : selected 8 ⟨178825, by decide⟩
    (prefixPartial 13 83999) = some ⟨13, 2, 0, 178825, 83999, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_83999_178825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83999 ⟨178825, by decide⟩ :=
  accepted_of_selected 13 83999 ⟨178825, by decide⟩ ⟨13, 2, 0, 178825, 83999, 1085, 16384⟩
    (by decide) selected_cut_05843

theorem unmarked_context_12_20999_178826 : frontier 9 ⟨178826, by decide⟩
    (prefixCache 12 20999) (prefixPartial 12 20999) = false := by
  decide +kernel

theorem node_context_12_20999_178826 : EJMOriginalGlobalDAGData.nodes 9 ⟨178826, by decide⟩ =
    .split (coordinate 12) (![⟨178736, by decide⟩,⟨178783, by decide⟩,⟨178809, by decide⟩,⟨178825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20999_178826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20999 ⟨178826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20999
    ⟨178826, by decide⟩ (by decide) (![⟨178736, by decide⟩,⟨178783, by decide⟩,⟨178809, by decide⟩,⟨178825, by decide⟩]) unmarked_context_12_20999_178826 node_context_12_20999_178826
  intro a
  fin_cases a
  · exact context_13_83996_178736
  · exact context_13_83997_178783
  · exact context_13_83998_178809
  · exact context_13_83999_178825

theorem unmarked_context_11_5249_178827 : frontier 10 ⟨178827, by decide⟩
    (prefixCache 11 5249) (prefixPartial 11 5249) = false := by
  decide +kernel

theorem node_context_11_5249_178827 : EJMOriginalGlobalDAGData.nodes 10 ⟨178827, by decide⟩ =
    .split (coordinate 11) (![⟨178378, by decide⟩,⟨178519, by decide⟩,⟨178671, by decide⟩,⟨178826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5249_178827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5249 ⟨178827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5249
    ⟨178827, by decide⟩ (by decide) (![⟨178378, by decide⟩,⟨178519, by decide⟩,⟨178671, by decide⟩,⟨178826, by decide⟩]) unmarked_context_11_5249_178827 node_context_11_5249_178827
  intro a
  fin_cases a
  · exact context_12_20996_178378
  · exact context_12_20997_178519
  · exact context_12_20998_178671
  · exact context_12_20999_178826

theorem selected_cut_05844 : selected 8 ⟨178874, by decide⟩
    (prefixPartial 13 84000) = some ⟨13, 2, 0, 178874, 84000, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_84000_178874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84000 ⟨178874, by decide⟩ :=
  accepted_of_selected 13 84000 ⟨178874, by decide⟩ ⟨13, 2, 0, 178874, 84000, 3089, 16384⟩
    (by decide) selected_cut_05844

theorem selected_cut_05845 : selected 8 ⟨178911, by decide⟩
    (prefixPartial 13 84001) = some ⟨13, 2, 0, 178911, 84001, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_84001_178911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84001 ⟨178911, by decide⟩ :=
  accepted_of_selected 13 84001 ⟨178911, by decide⟩ ⟨13, 2, 0, 178911, 84001, 3049, 16384⟩
    (by decide) selected_cut_05845

theorem selected_cut_05846 : selected 8 ⟨178934, by decide⟩
    (prefixPartial 13 84002) = some ⟨13, 2, 0, 178934, 84002, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_84002_178934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84002 ⟨178934, by decide⟩ :=
  accepted_of_selected 13 84002 ⟨178934, by decide⟩ ⟨13, 2, 0, 178934, 84002, 1921, 16384⟩
    (by decide) selected_cut_05846

theorem selected_cut_05847 : selected 8 ⟨178944, by decide⟩
    (prefixPartial 13 84003) = some ⟨13, 2, 0, 178944, 84003, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_84003_178944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84003 ⟨178944, by decide⟩ :=
  accepted_of_selected 13 84003 ⟨178944, by decide⟩ ⟨13, 2, 0, 178944, 84003, 1061, 16384⟩
    (by decide) selected_cut_05847

theorem unmarked_context_12_21000_178945 : frontier 9 ⟨178945, by decide⟩
    (prefixCache 12 21000) (prefixPartial 12 21000) = false := by
  decide +kernel

theorem node_context_12_21000_178945 : EJMOriginalGlobalDAGData.nodes 9 ⟨178945, by decide⟩ =
    .split (coordinate 12) (![⟨178874, by decide⟩,⟨178911, by decide⟩,⟨178934, by decide⟩,⟨178944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21000_178945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21000 ⟨178945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21000
    ⟨178945, by decide⟩ (by decide) (![⟨178874, by decide⟩,⟨178911, by decide⟩,⟨178934, by decide⟩,⟨178944, by decide⟩]) unmarked_context_12_21000_178945 node_context_12_21000_178945
  intro a
  fin_cases a
  · exact context_13_84000_178874
  · exact context_13_84001_178911
  · exact context_13_84002_178934
  · exact context_13_84003_178944

theorem selected_cut_05848 : selected 8 ⟨179000, by decide⟩
    (prefixPartial 13 84004) = some ⟨13, 2, 0, 179000, 84004, 3449, 16384⟩ := by
  decide +kernel

theorem context_13_84004_179000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84004 ⟨179000, by decide⟩ :=
  accepted_of_selected 13 84004 ⟨179000, by decide⟩ ⟨13, 2, 0, 179000, 84004, 3449, 16384⟩
    (by decide) selected_cut_05848

theorem selected_cut_05849 : selected 8 ⟨179055, by decide⟩
    (prefixPartial 13 84005) = some ⟨13, 2, 0, 179055, 84005, 3625, 16384⟩ := by
  decide +kernel

theorem context_13_84005_179055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84005 ⟨179055, by decide⟩ :=
  accepted_of_selected 13 84005 ⟨179055, by decide⟩ ⟨13, 2, 0, 179055, 84005, 3625, 16384⟩
    (by decide) selected_cut_05849

theorem selected_cut_05850 : selected 8 ⟨179081, by decide⟩
    (prefixPartial 13 84006) = some ⟨13, 2, 0, 179081, 84006, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_84006_179081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84006 ⟨179081, by decide⟩ :=
  accepted_of_selected 13 84006 ⟨179081, by decide⟩ ⟨13, 2, 0, 179081, 84006, 2041, 16384⟩
    (by decide) selected_cut_05850

theorem selected_cut_05851 : selected 8 ⟨179095, by decide⟩
    (prefixPartial 13 84007) = some ⟨13, 2, 0, 179095, 84007, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_84007_179095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84007 ⟨179095, by decide⟩ :=
  accepted_of_selected 13 84007 ⟨179095, by decide⟩ ⟨13, 2, 0, 179095, 84007, 1149, 16384⟩
    (by decide) selected_cut_05851

theorem unmarked_context_12_21001_179096 : frontier 9 ⟨179096, by decide⟩
    (prefixCache 12 21001) (prefixPartial 12 21001) = false := by
  decide +kernel

theorem node_context_12_21001_179096 : EJMOriginalGlobalDAGData.nodes 9 ⟨179096, by decide⟩ =
    .split (coordinate 12) (![⟨179000, by decide⟩,⟨179055, by decide⟩,⟨179081, by decide⟩,⟨179095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21001_179096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21001 ⟨179096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21001
    ⟨179096, by decide⟩ (by decide) (![⟨179000, by decide⟩,⟨179055, by decide⟩,⟨179081, by decide⟩,⟨179095, by decide⟩]) unmarked_context_12_21001_179096 node_context_12_21001_179096
  intro a
  fin_cases a
  · exact context_13_84004_179000
  · exact context_13_84005_179055
  · exact context_13_84006_179081
  · exact context_13_84007_179095

theorem selected_cut_05852 : selected 7 ⟨179114, by decide⟩
    (prefixPartial 14 336032) = some ⟨14, 2, 0, 179114, 336032, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_336032_179114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336032 ⟨179114, by decide⟩ :=
  accepted_of_selected 14 336032 ⟨179114, by decide⟩ ⟨14, 2, 0, 179114, 336032, 1057, 4096⟩
    (by decide) selected_cut_05852

theorem selected_cut_05853 : selected 7 ⟨179139, by decide⟩
    (prefixPartial 14 336033) = some ⟨14, 2, 0, 179139, 336033, 1685, 4096⟩ := by
  decide +kernel

theorem context_14_336033_179139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336033 ⟨179139, by decide⟩ :=
  accepted_of_selected 14 336033 ⟨179139, by decide⟩ ⟨14, 2, 0, 179139, 336033, 1685, 4096⟩
    (by decide) selected_cut_05853

theorem selected_cut_05854 : selected 7 ⟨179164, by decide⟩
    (prefixPartial 14 336034) = some ⟨14, 2, 0, 179164, 336034, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_336034_179164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336034 ⟨179164, by decide⟩ :=
  accepted_of_selected 14 336034 ⟨179164, by decide⟩ ⟨14, 2, 0, 179164, 336034, 1417, 4096⟩
    (by decide) selected_cut_05854

theorem selected_cut_05855 : selected 7 ⟨179189, by decide⟩
    (prefixPartial 14 336035) = some ⟨14, 2, 0, 179189, 336035, 1589, 4096⟩ := by
  decide +kernel

theorem context_14_336035_179189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336035 ⟨179189, by decide⟩ :=
  accepted_of_selected 14 336035 ⟨179189, by decide⟩ ⟨14, 2, 0, 179189, 336035, 1589, 4096⟩
    (by decide) selected_cut_05855

theorem unmarked_context_13_84008_179190 : frontier 8 ⟨179190, by decide⟩
    (prefixCache 13 84008) (prefixPartial 13 84008) = false := by
  decide +kernel

theorem node_context_13_84008_179190 : EJMOriginalGlobalDAGData.nodes 8 ⟨179190, by decide⟩ =
    .split (coordinate 13) (![⟨179114, by decide⟩,⟨179139, by decide⟩,⟨179164, by decide⟩,⟨179189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_84008_179190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84008 ⟨179190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 84008
    ⟨179190, by decide⟩ (by decide) (![⟨179114, by decide⟩,⟨179139, by decide⟩,⟨179164, by decide⟩,⟨179189, by decide⟩]) unmarked_context_13_84008_179190 node_context_13_84008_179190
  intro a
  fin_cases a
  · exact context_14_336032_179114
  · exact context_14_336033_179139
  · exact context_14_336034_179164
  · exact context_14_336035_179189

theorem selected_cut_05856 : selected 7 ⟨179229, by decide⟩
    (prefixPartial 14 336036) = some ⟨14, 2, 0, 179229, 336036, 1757, 4096⟩ := by
  decide +kernel

theorem context_14_336036_179229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336036 ⟨179229, by decide⟩ :=
  accepted_of_selected 14 336036 ⟨179229, by decide⟩ ⟨14, 2, 0, 179229, 336036, 1757, 4096⟩
    (by decide) selected_cut_05856

theorem selected_cut_05857 : selected 7 ⟨179272, by decide⟩
    (prefixPartial 14 336037) = some ⟨14, 2, 0, 179272, 336037, 1753, 4096⟩ := by
  decide +kernel

theorem context_14_336037_179272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336037 ⟨179272, by decide⟩ :=
  accepted_of_selected 14 336037 ⟨179272, by decide⟩ ⟨14, 2, 0, 179272, 336037, 1753, 4096⟩
    (by decide) selected_cut_05857

theorem selected_cut_05858 : selected 7 ⟨179296, by decide⟩
    (prefixPartial 14 336038) = some ⟨14, 2, 0, 179296, 336038, 1365, 4096⟩ := by
  decide +kernel

theorem context_14_336038_179296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336038 ⟨179296, by decide⟩ :=
  accepted_of_selected 14 336038 ⟨179296, by decide⟩ ⟨14, 2, 0, 179296, 336038, 1365, 4096⟩
    (by decide) selected_cut_05858

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
