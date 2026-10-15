/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover047
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04610 : selected 8 ⟨148953, by decide⟩
    (prefixPartial 13 74801) = some ⟨13, 2, 0, 148953, 74801, 3945, 16384⟩ := by
  decide +kernel

theorem context_13_74801_148953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74801 ⟨148953, by decide⟩ :=
  accepted_of_selected 13 74801 ⟨148953, by decide⟩ ⟨13, 2, 0, 148953, 74801, 3945, 16384⟩
    (by decide) selected_cut_04610

theorem selected_cut_04611 : selected 8 ⟨148974, by decide⟩
    (prefixPartial 13 74802) = some ⟨13, 2, 0, 148974, 74802, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_74802_148974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74802 ⟨148974, by decide⟩ :=
  accepted_of_selected 13 74802 ⟨148974, by decide⟩ ⟨13, 2, 0, 148974, 74802, 2145, 16384⟩
    (by decide) selected_cut_04611

theorem selected_cut_04612 : selected 8 ⟨148989, by decide⟩
    (prefixPartial 13 74803) = some ⟨13, 2, 0, 148989, 74803, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_74803_148989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74803 ⟨148989, by decide⟩ :=
  accepted_of_selected 13 74803 ⟨148989, by decide⟩ ⟨13, 2, 0, 148989, 74803, 1269, 16384⟩
    (by decide) selected_cut_04612

theorem unmarked_context_12_18700_148990 : frontier 9 ⟨148990, by decide⟩
    (prefixCache 12 18700) (prefixPartial 12 18700) = false := by
  decide +kernel

theorem node_context_12_18700_148990 : EJMOriginalGlobalDAGData.nodes 9 ⟨148990, by decide⟩ =
    .split (coordinate 12) (![⟨148899, by decide⟩,⟨148953, by decide⟩,⟨148974, by decide⟩,⟨148989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18700_148990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18700 ⟨148990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18700
    ⟨148990, by decide⟩ (by decide) (![⟨148899, by decide⟩,⟨148953, by decide⟩,⟨148974, by decide⟩,⟨148989, by decide⟩]) unmarked_context_12_18700_148990 node_context_12_18700_148990
  intro a
  fin_cases a
  · exact context_13_74800_148899
  · exact context_13_74801_148953
  · exact context_13_74802_148974
  · exact context_13_74803_148989

theorem selected_cut_04613 : selected 8 ⟨149043, by decide⟩
    (prefixPartial 13 74804) = some ⟨13, 2, 0, 149043, 74804, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_74804_149043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74804 ⟨149043, by decide⟩ :=
  accepted_of_selected 13 74804 ⟨149043, by decide⟩ ⟨13, 2, 0, 149043, 74804, 3229, 16384⟩
    (by decide) selected_cut_04613

theorem selected_cut_04614 : selected 8 ⟨149084, by decide⟩
    (prefixPartial 13 74805) = some ⟨13, 2, 0, 149084, 74805, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_74805_149084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74805 ⟨149084, by decide⟩ :=
  accepted_of_selected 13 74805 ⟨149084, by decide⟩ ⟨13, 2, 0, 149084, 74805, 3357, 16384⟩
    (by decide) selected_cut_04614

theorem selected_cut_04615 : selected 8 ⟨149099, by decide⟩
    (prefixPartial 13 74806) = some ⟨13, 2, 0, 149099, 74806, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_74806_149099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74806 ⟨149099, by decide⟩ :=
  accepted_of_selected 13 74806 ⟨149099, by decide⟩ ⟨13, 2, 0, 149099, 74806, 2309, 16384⟩
    (by decide) selected_cut_04615

theorem selected_cut_04616 : selected 8 ⟨149105, by decide⟩
    (prefixPartial 13 74807) = some ⟨13, 2, 0, 149105, 74807, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_74807_149105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74807 ⟨149105, by decide⟩ :=
  accepted_of_selected 13 74807 ⟨149105, by decide⟩ ⟨13, 2, 0, 149105, 74807, 1209, 16384⟩
    (by decide) selected_cut_04616

theorem unmarked_context_12_18701_149106 : frontier 9 ⟨149106, by decide⟩
    (prefixCache 12 18701) (prefixPartial 12 18701) = false := by
  decide +kernel

theorem node_context_12_18701_149106 : EJMOriginalGlobalDAGData.nodes 9 ⟨149106, by decide⟩ =
    .split (coordinate 12) (![⟨149043, by decide⟩,⟨149084, by decide⟩,⟨149099, by decide⟩,⟨149105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18701_149106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18701 ⟨149106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18701
    ⟨149106, by decide⟩ (by decide) (![⟨149043, by decide⟩,⟨149084, by decide⟩,⟨149099, by decide⟩,⟨149105, by decide⟩]) unmarked_context_12_18701_149106 node_context_12_18701_149106
  intro a
  fin_cases a
  · exact context_13_74804_149043
  · exact context_13_74805_149084
  · exact context_13_74806_149099
  · exact context_13_74807_149105

theorem selected_cut_04617 : selected 8 ⟨149172, by decide⟩
    (prefixPartial 13 74808) = some ⟨13, 2, 0, 149172, 74808, 3837, 16384⟩ := by
  decide +kernel

theorem context_13_74808_149172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74808 ⟨149172, by decide⟩ :=
  accepted_of_selected 13 74808 ⟨149172, by decide⟩ ⟨13, 2, 0, 149172, 74808, 3837, 16384⟩
    (by decide) selected_cut_04617

theorem selected_cut_04618 : selected 8 ⟨149231, by decide⟩
    (prefixPartial 13 74809) = some ⟨13, 2, 0, 149231, 74809, 4069, 16384⟩ := by
  decide +kernel

theorem context_13_74809_149231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74809 ⟨149231, by decide⟩ :=
  accepted_of_selected 13 74809 ⟨149231, by decide⟩ ⟨13, 2, 0, 149231, 74809, 4069, 16384⟩
    (by decide) selected_cut_04618

theorem selected_cut_04619 : selected 8 ⟨149261, by decide⟩
    (prefixPartial 13 74810) = some ⟨13, 2, 0, 149261, 74810, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_74810_149261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74810 ⟨149261, by decide⟩ :=
  accepted_of_selected 13 74810 ⟨149261, by decide⟩ ⟨13, 2, 0, 149261, 74810, 2577, 16384⟩
    (by decide) selected_cut_04619

theorem selected_cut_04620 : selected 8 ⟨149273, by decide⟩
    (prefixPartial 13 74811) = some ⟨13, 2, 0, 149273, 74811, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_74811_149273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74811 ⟨149273, by decide⟩ :=
  accepted_of_selected 13 74811 ⟨149273, by decide⟩ ⟨13, 2, 0, 149273, 74811, 1349, 16384⟩
    (by decide) selected_cut_04620

theorem unmarked_context_12_18702_149274 : frontier 9 ⟨149274, by decide⟩
    (prefixCache 12 18702) (prefixPartial 12 18702) = false := by
  decide +kernel

theorem node_context_12_18702_149274 : EJMOriginalGlobalDAGData.nodes 9 ⟨149274, by decide⟩ =
    .split (coordinate 12) (![⟨149172, by decide⟩,⟨149231, by decide⟩,⟨149261, by decide⟩,⟨149273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18702_149274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18702 ⟨149274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18702
    ⟨149274, by decide⟩ (by decide) (![⟨149172, by decide⟩,⟨149231, by decide⟩,⟨149261, by decide⟩,⟨149273, by decide⟩]) unmarked_context_12_18702_149274 node_context_12_18702_149274
  intro a
  fin_cases a
  · exact context_13_74808_149172
  · exact context_13_74809_149231
  · exact context_13_74810_149261
  · exact context_13_74811_149273

theorem selected_cut_04621 : selected 8 ⟨149322, by decide⟩
    (prefixPartial 13 74812) = some ⟨13, 2, 0, 149322, 74812, 3429, 16384⟩ := by
  decide +kernel

theorem context_13_74812_149322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74812 ⟨149322, by decide⟩ :=
  accepted_of_selected 13 74812 ⟨149322, by decide⟩ ⟨13, 2, 0, 149322, 74812, 3429, 16384⟩
    (by decide) selected_cut_04621

theorem selected_cut_04622 : selected 8 ⟨149364, by decide⟩
    (prefixPartial 13 74813) = some ⟨13, 2, 0, 149364, 74813, 3721, 16384⟩ := by
  decide +kernel

theorem context_13_74813_149364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74813 ⟨149364, by decide⟩ :=
  accepted_of_selected 13 74813 ⟨149364, by decide⟩ ⟨13, 2, 0, 149364, 74813, 3721, 16384⟩
    (by decide) selected_cut_04622

theorem selected_cut_04623 : selected 8 ⟨149390, by decide⟩
    (prefixPartial 13 74814) = some ⟨13, 2, 0, 149390, 74814, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_74814_149390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74814 ⟨149390, by decide⟩ :=
  accepted_of_selected 13 74814 ⟨149390, by decide⟩ ⟨13, 2, 0, 149390, 74814, 2321, 16384⟩
    (by decide) selected_cut_04623

theorem selected_cut_04624 : selected 8 ⟨149396, by decide⟩
    (prefixPartial 13 74815) = some ⟨13, 2, 0, 149396, 74815, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_74815_149396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74815 ⟨149396, by decide⟩ :=
  accepted_of_selected 13 74815 ⟨149396, by decide⟩ ⟨13, 2, 0, 149396, 74815, 1205, 16384⟩
    (by decide) selected_cut_04624

theorem unmarked_context_12_18703_149397 : frontier 9 ⟨149397, by decide⟩
    (prefixCache 12 18703) (prefixPartial 12 18703) = false := by
  decide +kernel

theorem node_context_12_18703_149397 : EJMOriginalGlobalDAGData.nodes 9 ⟨149397, by decide⟩ =
    .split (coordinate 12) (![⟨149322, by decide⟩,⟨149364, by decide⟩,⟨149390, by decide⟩,⟨149396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18703_149397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18703 ⟨149397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18703
    ⟨149397, by decide⟩ (by decide) (![⟨149322, by decide⟩,⟨149364, by decide⟩,⟨149390, by decide⟩,⟨149396, by decide⟩]) unmarked_context_12_18703_149397 node_context_12_18703_149397
  intro a
  fin_cases a
  · exact context_13_74812_149322
  · exact context_13_74813_149364
  · exact context_13_74814_149390
  · exact context_13_74815_149396

theorem unmarked_context_11_4675_149398 : frontier 10 ⟨149398, by decide⟩
    (prefixCache 11 4675) (prefixPartial 11 4675) = false := by
  decide +kernel

theorem node_context_11_4675_149398 : EJMOriginalGlobalDAGData.nodes 10 ⟨149398, by decide⟩ =
    .split (coordinate 11) (![⟨148990, by decide⟩,⟨149106, by decide⟩,⟨149274, by decide⟩,⟨149397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4675_149398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4675 ⟨149398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4675
    ⟨149398, by decide⟩ (by decide) (![⟨148990, by decide⟩,⟨149106, by decide⟩,⟨149274, by decide⟩,⟨149397, by decide⟩]) unmarked_context_11_4675_149398 node_context_11_4675_149398
  intro a
  fin_cases a
  · exact context_12_18700_148990
  · exact context_12_18701_149106
  · exact context_12_18702_149274
  · exact context_12_18703_149397

theorem unmarked_context_10_1168_149399 : frontier 11 ⟨149399, by decide⟩
    (prefixCache 10 1168) (prefixPartial 10 1168) = false := by
  decide +kernel

theorem node_context_10_1168_149399 : EJMOriginalGlobalDAGData.nodes 11 ⟨149399, by decide⟩ =
    .split (coordinate 10) (![⟨147487, by decide⟩,⟨148232, by decide⟩,⟨148849, by decide⟩,⟨149398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1168_149399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1168 ⟨149399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1168
    ⟨149399, by decide⟩ (by decide) (![⟨147487, by decide⟩,⟨148232, by decide⟩,⟨148849, by decide⟩,⟨149398, by decide⟩]) unmarked_context_10_1168_149399 node_context_10_1168_149399
  intro a
  fin_cases a
  · exact context_11_4672_147487
  · exact context_11_4673_148232
  · exact context_11_4674_148849
  · exact context_11_4675_149398

theorem selected_cut_04625 : selected 8 ⟨149433, by decide⟩
    (prefixPartial 13 74816) = some ⟨13, 2, 0, 149433, 74816, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_74816_149433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74816 ⟨149433, by decide⟩ :=
  accepted_of_selected 13 74816 ⟨149433, by decide⟩ ⟨13, 2, 0, 149433, 74816, 2313, 16384⟩
    (by decide) selected_cut_04625

theorem selected_cut_04626 : selected 8 ⟨149469, by decide⟩
    (prefixPartial 13 74817) = some ⟨13, 2, 0, 149469, 74817, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_74817_149469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74817 ⟨149469, by decide⟩ :=
  accepted_of_selected 13 74817 ⟨149469, by decide⟩ ⟨13, 2, 0, 149469, 74817, 2525, 16384⟩
    (by decide) selected_cut_04626

theorem selected_cut_04627 : selected 8 ⟨149491, by decide⟩
    (prefixPartial 13 74818) = some ⟨13, 2, 0, 149491, 74818, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_74818_149491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74818 ⟨149491, by decide⟩ :=
  accepted_of_selected 13 74818 ⟨149491, by decide⟩ ⟨13, 2, 0, 149491, 74818, 1521, 16384⟩
    (by decide) selected_cut_04627

theorem selected_cut_04628 : selected 8 ⟨149499, by decide⟩
    (prefixPartial 13 74819) = some ⟨13, 2, 0, 149499, 74819, 945, 16384⟩ := by
  decide +kernel

theorem context_13_74819_149499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74819 ⟨149499, by decide⟩ :=
  accepted_of_selected 13 74819 ⟨149499, by decide⟩ ⟨13, 2, 0, 149499, 74819, 945, 16384⟩
    (by decide) selected_cut_04628

theorem unmarked_context_12_18704_149500 : frontier 9 ⟨149500, by decide⟩
    (prefixCache 12 18704) (prefixPartial 12 18704) = false := by
  decide +kernel

theorem node_context_12_18704_149500 : EJMOriginalGlobalDAGData.nodes 9 ⟨149500, by decide⟩ =
    .split (coordinate 12) (![⟨149433, by decide⟩,⟨149469, by decide⟩,⟨149491, by decide⟩,⟨149499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18704_149500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18704 ⟨149500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18704
    ⟨149500, by decide⟩ (by decide) (![⟨149433, by decide⟩,⟨149469, by decide⟩,⟨149491, by decide⟩,⟨149499, by decide⟩]) unmarked_context_12_18704_149500 node_context_12_18704_149500
  intro a
  fin_cases a
  · exact context_13_74816_149433
  · exact context_13_74817_149469
  · exact context_13_74818_149491
  · exact context_13_74819_149499

theorem selected_cut_04629 : selected 8 ⟨149531, by decide⟩
    (prefixPartial 13 74820) = some ⟨13, 2, 0, 149531, 74820, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_74820_149531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74820 ⟨149531, by decide⟩ :=
  accepted_of_selected 13 74820 ⟨149531, by decide⟩ ⟨13, 2, 0, 149531, 74820, 1973, 16384⟩
    (by decide) selected_cut_04629

theorem selected_cut_04630 : selected 8 ⟨149559, by decide⟩
    (prefixPartial 13 74821) = some ⟨13, 2, 0, 149559, 74821, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_74821_149559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74821 ⟨149559, by decide⟩ :=
  accepted_of_selected 13 74821 ⟨149559, by decide⟩ ⟨13, 2, 0, 149559, 74821, 1597, 16384⟩
    (by decide) selected_cut_04630

theorem selected_cut_04631 : selected 8 ⟨149584, by decide⟩
    (prefixPartial 13 74822) = some ⟨13, 2, 0, 149584, 74822, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_74822_149584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74822 ⟨149584, by decide⟩ :=
  accepted_of_selected 13 74822 ⟨149584, by decide⟩ ⟨13, 2, 0, 149584, 74822, 1489, 16384⟩
    (by decide) selected_cut_04631

theorem selected_cut_04632 : selected 8 ⟨149591, by decide⟩
    (prefixPartial 13 74823) = some ⟨13, 2, 0, 149591, 74823, 873, 16384⟩ := by
  decide +kernel

theorem context_13_74823_149591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74823 ⟨149591, by decide⟩ :=
  accepted_of_selected 13 74823 ⟨149591, by decide⟩ ⟨13, 2, 0, 149591, 74823, 873, 16384⟩
    (by decide) selected_cut_04632

theorem unmarked_context_12_18705_149592 : frontier 9 ⟨149592, by decide⟩
    (prefixCache 12 18705) (prefixPartial 12 18705) = false := by
  decide +kernel

theorem node_context_12_18705_149592 : EJMOriginalGlobalDAGData.nodes 9 ⟨149592, by decide⟩ =
    .split (coordinate 12) (![⟨149531, by decide⟩,⟨149559, by decide⟩,⟨149584, by decide⟩,⟨149591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18705_149592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18705 ⟨149592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18705
    ⟨149592, by decide⟩ (by decide) (![⟨149531, by decide⟩,⟨149559, by decide⟩,⟨149584, by decide⟩,⟨149591, by decide⟩]) unmarked_context_12_18705_149592 node_context_12_18705_149592
  intro a
  fin_cases a
  · exact context_13_74820_149531
  · exact context_13_74821_149559
  · exact context_13_74822_149584
  · exact context_13_74823_149591

theorem selected_cut_04633 : selected 8 ⟨149633, by decide⟩
    (prefixPartial 13 74824) = some ⟨13, 2, 0, 149633, 74824, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_74824_149633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74824 ⟨149633, by decide⟩ :=
  accepted_of_selected 13 74824 ⟨149633, by decide⟩ ⟨13, 2, 0, 149633, 74824, 2505, 16384⟩
    (by decide) selected_cut_04633

theorem selected_cut_04634 : selected 8 ⟨149672, by decide⟩
    (prefixPartial 13 74825) = some ⟨13, 2, 0, 149672, 74825, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_74825_149672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74825 ⟨149672, by decide⟩ :=
  accepted_of_selected 13 74825 ⟨149672, by decide⟩ ⟨13, 2, 0, 149672, 74825, 2321, 16384⟩
    (by decide) selected_cut_04634

theorem selected_cut_04635 : selected 8 ⟨149697, by decide⟩
    (prefixPartial 13 74826) = some ⟨13, 2, 0, 149697, 74826, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_74826_149697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74826 ⟨149697, by decide⟩ :=
  accepted_of_selected 13 74826 ⟨149697, by decide⟩ ⟨13, 2, 0, 149697, 74826, 1817, 16384⟩
    (by decide) selected_cut_04635

theorem selected_cut_04636 : selected 8 ⟨149706, by decide⟩
    (prefixPartial 13 74827) = some ⟨13, 2, 0, 149706, 74827, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_74827_149706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74827 ⟨149706, by decide⟩ :=
  accepted_of_selected 13 74827 ⟨149706, by decide⟩ ⟨13, 2, 0, 149706, 74827, 1057, 16384⟩
    (by decide) selected_cut_04636

theorem unmarked_context_12_18706_149707 : frontier 9 ⟨149707, by decide⟩
    (prefixCache 12 18706) (prefixPartial 12 18706) = false := by
  decide +kernel

theorem node_context_12_18706_149707 : EJMOriginalGlobalDAGData.nodes 9 ⟨149707, by decide⟩ =
    .split (coordinate 12) (![⟨149633, by decide⟩,⟨149672, by decide⟩,⟨149697, by decide⟩,⟨149706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18706_149707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18706 ⟨149707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18706
    ⟨149707, by decide⟩ (by decide) (![⟨149633, by decide⟩,⟨149672, by decide⟩,⟨149697, by decide⟩,⟨149706, by decide⟩]) unmarked_context_12_18706_149707 node_context_12_18706_149707
  intro a
  fin_cases a
  · exact context_13_74824_149633
  · exact context_13_74825_149672
  · exact context_13_74826_149697
  · exact context_13_74827_149706

theorem selected_cut_04637 : selected 8 ⟨149742, by decide⟩
    (prefixPartial 13 74828) = some ⟨13, 2, 0, 149742, 74828, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_74828_149742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74828 ⟨149742, by decide⟩ :=
  accepted_of_selected 13 74828 ⟨149742, by decide⟩ ⟨13, 2, 0, 149742, 74828, 2365, 16384⟩
    (by decide) selected_cut_04637

theorem selected_cut_04638 : selected 8 ⟨149783, by decide⟩
    (prefixPartial 13 74829) = some ⟨13, 2, 0, 149783, 74829, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_74829_149783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74829 ⟨149783, by decide⟩ :=
  accepted_of_selected 13 74829 ⟨149783, by decide⟩ ⟨13, 2, 0, 149783, 74829, 2273, 16384⟩
    (by decide) selected_cut_04638

theorem selected_cut_04639 : selected 8 ⟨149806, by decide⟩
    (prefixPartial 13 74830) = some ⟨13, 2, 0, 149806, 74830, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_74830_149806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74830 ⟨149806, by decide⟩ :=
  accepted_of_selected 13 74830 ⟨149806, by decide⟩ ⟨13, 2, 0, 149806, 74830, 1737, 16384⟩
    (by decide) selected_cut_04639

theorem selected_cut_04640 : selected 8 ⟨149812, by decide⟩
    (prefixPartial 13 74831) = some ⟨13, 2, 0, 149812, 74831, 957, 16384⟩ := by
  decide +kernel

theorem context_13_74831_149812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74831 ⟨149812, by decide⟩ :=
  accepted_of_selected 13 74831 ⟨149812, by decide⟩ ⟨13, 2, 0, 149812, 74831, 957, 16384⟩
    (by decide) selected_cut_04640

theorem unmarked_context_12_18707_149813 : frontier 9 ⟨149813, by decide⟩
    (prefixCache 12 18707) (prefixPartial 12 18707) = false := by
  decide +kernel

theorem node_context_12_18707_149813 : EJMOriginalGlobalDAGData.nodes 9 ⟨149813, by decide⟩ =
    .split (coordinate 12) (![⟨149742, by decide⟩,⟨149783, by decide⟩,⟨149806, by decide⟩,⟨149812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18707_149813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18707 ⟨149813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18707
    ⟨149813, by decide⟩ (by decide) (![⟨149742, by decide⟩,⟨149783, by decide⟩,⟨149806, by decide⟩,⟨149812, by decide⟩]) unmarked_context_12_18707_149813 node_context_12_18707_149813
  intro a
  fin_cases a
  · exact context_13_74828_149742
  · exact context_13_74829_149783
  · exact context_13_74830_149806
  · exact context_13_74831_149812

theorem unmarked_context_11_4676_149814 : frontier 10 ⟨149814, by decide⟩
    (prefixCache 11 4676) (prefixPartial 11 4676) = false := by
  decide +kernel

theorem node_context_11_4676_149814 : EJMOriginalGlobalDAGData.nodes 10 ⟨149814, by decide⟩ =
    .split (coordinate 11) (![⟨149500, by decide⟩,⟨149592, by decide⟩,⟨149707, by decide⟩,⟨149813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4676_149814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4676 ⟨149814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4676
    ⟨149814, by decide⟩ (by decide) (![⟨149500, by decide⟩,⟨149592, by decide⟩,⟨149707, by decide⟩,⟨149813, by decide⟩]) unmarked_context_11_4676_149814 node_context_11_4676_149814
  intro a
  fin_cases a
  · exact context_12_18704_149500
  · exact context_12_18705_149592
  · exact context_12_18706_149707
  · exact context_12_18707_149813

theorem selected_cut_04641 : selected 8 ⟨149836, by decide⟩
    (prefixPartial 13 74832) = some ⟨13, 2, 0, 149836, 74832, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_74832_149836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74832 ⟨149836, by decide⟩ :=
  accepted_of_selected 13 74832 ⟨149836, by decide⟩ ⟨13, 2, 0, 149836, 74832, 1725, 16384⟩
    (by decide) selected_cut_04641

theorem selected_cut_04642 : selected 8 ⟨149865, by decide⟩
    (prefixPartial 13 74833) = some ⟨13, 2, 0, 149865, 74833, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_74833_149865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74833 ⟨149865, by decide⟩ :=
  accepted_of_selected 13 74833 ⟨149865, by decide⟩ ⟨13, 2, 0, 149865, 74833, 1901, 16384⟩
    (by decide) selected_cut_04642

theorem selected_cut_04643 : selected 8 ⟨149882, by decide⟩
    (prefixPartial 13 74834) = some ⟨13, 2, 0, 149882, 74834, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_74834_149882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74834 ⟨149882, by decide⟩ :=
  accepted_of_selected 13 74834 ⟨149882, by decide⟩ ⟨13, 2, 0, 149882, 74834, 1205, 16384⟩
    (by decide) selected_cut_04643

theorem selected_cut_04644 : selected 8 ⟨149889, by decide⟩
    (prefixPartial 13 74835) = some ⟨13, 2, 0, 149889, 74835, 893, 16384⟩ := by
  decide +kernel

theorem context_13_74835_149889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74835 ⟨149889, by decide⟩ :=
  accepted_of_selected 13 74835 ⟨149889, by decide⟩ ⟨13, 2, 0, 149889, 74835, 893, 16384⟩
    (by decide) selected_cut_04644

theorem unmarked_context_12_18708_149890 : frontier 9 ⟨149890, by decide⟩
    (prefixCache 12 18708) (prefixPartial 12 18708) = false := by
  decide +kernel

theorem node_context_12_18708_149890 : EJMOriginalGlobalDAGData.nodes 9 ⟨149890, by decide⟩ =
    .split (coordinate 12) (![⟨149836, by decide⟩,⟨149865, by decide⟩,⟨149882, by decide⟩,⟨149889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18708_149890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18708 ⟨149890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18708
    ⟨149890, by decide⟩ (by decide) (![⟨149836, by decide⟩,⟨149865, by decide⟩,⟨149882, by decide⟩,⟨149889, by decide⟩]) unmarked_context_12_18708_149890 node_context_12_18708_149890
  intro a
  fin_cases a
  · exact context_13_74832_149836
  · exact context_13_74833_149865
  · exact context_13_74834_149882
  · exact context_13_74835_149889

theorem selected_cut_04645 : selected 8 ⟨149922, by decide⟩
    (prefixPartial 13 74836) = some ⟨13, 2, 0, 149922, 74836, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_74836_149922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74836 ⟨149922, by decide⟩ :=
  accepted_of_selected 13 74836 ⟨149922, by decide⟩ ⟨13, 2, 0, 149922, 74836, 2457, 16384⟩
    (by decide) selected_cut_04645

theorem selected_cut_04646 : selected 8 ⟨149954, by decide⟩
    (prefixPartial 13 74837) = some ⟨13, 2, 0, 149954, 74837, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_74837_149954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74837 ⟨149954, by decide⟩ :=
  accepted_of_selected 13 74837 ⟨149954, by decide⟩ ⟨13, 2, 0, 149954, 74837, 2713, 16384⟩
    (by decide) selected_cut_04646

theorem selected_cut_04647 : selected 8 ⟨149975, by decide⟩
    (prefixPartial 13 74838) = some ⟨13, 2, 0, 149975, 74838, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_74838_149975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74838 ⟨149975, by decide⟩ :=
  accepted_of_selected 13 74838 ⟨149975, by decide⟩ ⟨13, 2, 0, 149975, 74838, 1729, 16384⟩
    (by decide) selected_cut_04647

theorem selected_cut_04648 : selected 8 ⟨149980, by decide⟩
    (prefixPartial 13 74839) = some ⟨13, 2, 0, 149980, 74839, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_74839_149980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74839 ⟨149980, by decide⟩ :=
  accepted_of_selected 13 74839 ⟨149980, by decide⟩ ⟨13, 2, 0, 149980, 74839, 1085, 16384⟩
    (by decide) selected_cut_04648

theorem unmarked_context_12_18709_149981 : frontier 9 ⟨149981, by decide⟩
    (prefixCache 12 18709) (prefixPartial 12 18709) = false := by
  decide +kernel

theorem node_context_12_18709_149981 : EJMOriginalGlobalDAGData.nodes 9 ⟨149981, by decide⟩ =
    .split (coordinate 12) (![⟨149922, by decide⟩,⟨149954, by decide⟩,⟨149975, by decide⟩,⟨149980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18709_149981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18709 ⟨149981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18709
    ⟨149981, by decide⟩ (by decide) (![⟨149922, by decide⟩,⟨149954, by decide⟩,⟨149975, by decide⟩,⟨149980, by decide⟩]) unmarked_context_12_18709_149981 node_context_12_18709_149981
  intro a
  fin_cases a
  · exact context_13_74836_149922
  · exact context_13_74837_149954
  · exact context_13_74838_149975
  · exact context_13_74839_149980

theorem selected_cut_04649 : selected 8 ⟨150009, by decide⟩
    (prefixPartial 13 74840) = some ⟨13, 2, 0, 150009, 74840, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_74840_150009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74840 ⟨150009, by decide⟩ :=
  accepted_of_selected 13 74840 ⟨150009, by decide⟩ ⟨13, 2, 0, 150009, 74840, 2089, 16384⟩
    (by decide) selected_cut_04649

theorem selected_cut_04650 : selected 8 ⟨150037, by decide⟩
    (prefixPartial 13 74841) = some ⟨13, 2, 0, 150037, 74841, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_74841_150037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74841 ⟨150037, by decide⟩ :=
  accepted_of_selected 13 74841 ⟨150037, by decide⟩ ⟨13, 2, 0, 150037, 74841, 2285, 16384⟩
    (by decide) selected_cut_04650

theorem selected_cut_04651 : selected 8 ⟨150055, by decide⟩
    (prefixPartial 13 74842) = some ⟨13, 2, 0, 150055, 74842, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_74842_150055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74842 ⟨150055, by decide⟩ :=
  accepted_of_selected 13 74842 ⟨150055, by decide⟩ ⟨13, 2, 0, 150055, 74842, 1525, 16384⟩
    (by decide) selected_cut_04651

theorem selected_cut_04652 : selected 8 ⟨150063, by decide⟩
    (prefixPartial 13 74843) = some ⟨13, 2, 0, 150063, 74843, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_74843_150063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74843 ⟨150063, by decide⟩ :=
  accepted_of_selected 13 74843 ⟨150063, by decide⟩ ⟨13, 2, 0, 150063, 74843, 1045, 16384⟩
    (by decide) selected_cut_04652

theorem unmarked_context_12_18710_150064 : frontier 9 ⟨150064, by decide⟩
    (prefixCache 12 18710) (prefixPartial 12 18710) = false := by
  decide +kernel

theorem node_context_12_18710_150064 : EJMOriginalGlobalDAGData.nodes 9 ⟨150064, by decide⟩ =
    .split (coordinate 12) (![⟨150009, by decide⟩,⟨150037, by decide⟩,⟨150055, by decide⟩,⟨150063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18710_150064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18710 ⟨150064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18710
    ⟨150064, by decide⟩ (by decide) (![⟨150009, by decide⟩,⟨150037, by decide⟩,⟨150055, by decide⟩,⟨150063, by decide⟩]) unmarked_context_12_18710_150064 node_context_12_18710_150064
  intro a
  fin_cases a
  · exact context_13_74840_150009
  · exact context_13_74841_150037
  · exact context_13_74842_150055
  · exact context_13_74843_150063

theorem selected_cut_04653 : selected 8 ⟨150092, by decide⟩
    (prefixPartial 13 74844) = some ⟨13, 2, 0, 150092, 74844, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_74844_150092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74844 ⟨150092, by decide⟩ :=
  accepted_of_selected 13 74844 ⟨150092, by decide⟩ ⟨13, 2, 0, 150092, 74844, 1977, 16384⟩
    (by decide) selected_cut_04653

theorem selected_cut_04654 : selected 8 ⟨150121, by decide⟩
    (prefixPartial 13 74845) = some ⟨13, 2, 0, 150121, 74845, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_74845_150121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74845 ⟨150121, by decide⟩ :=
  accepted_of_selected 13 74845 ⟨150121, by decide⟩ ⟨13, 2, 0, 150121, 74845, 2321, 16384⟩
    (by decide) selected_cut_04654

theorem selected_cut_04655 : selected 8 ⟨150141, by decide⟩
    (prefixPartial 13 74846) = some ⟨13, 2, 0, 150141, 74846, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_74846_150141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74846 ⟨150141, by decide⟩ :=
  accepted_of_selected 13 74846 ⟨150141, by decide⟩ ⟨13, 2, 0, 150141, 74846, 1361, 16384⟩
    (by decide) selected_cut_04655

theorem selected_cut_04656 : selected 8 ⟨150148, by decide⟩
    (prefixPartial 13 74847) = some ⟨13, 2, 0, 150148, 74847, 937, 16384⟩ := by
  decide +kernel

theorem context_13_74847_150148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74847 ⟨150148, by decide⟩ :=
  accepted_of_selected 13 74847 ⟨150148, by decide⟩ ⟨13, 2, 0, 150148, 74847, 937, 16384⟩
    (by decide) selected_cut_04656

theorem unmarked_context_12_18711_150149 : frontier 9 ⟨150149, by decide⟩
    (prefixCache 12 18711) (prefixPartial 12 18711) = false := by
  decide +kernel

theorem node_context_12_18711_150149 : EJMOriginalGlobalDAGData.nodes 9 ⟨150149, by decide⟩ =
    .split (coordinate 12) (![⟨150092, by decide⟩,⟨150121, by decide⟩,⟨150141, by decide⟩,⟨150148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18711_150149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18711 ⟨150149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18711
    ⟨150149, by decide⟩ (by decide) (![⟨150092, by decide⟩,⟨150121, by decide⟩,⟨150141, by decide⟩,⟨150148, by decide⟩]) unmarked_context_12_18711_150149 node_context_12_18711_150149
  intro a
  fin_cases a
  · exact context_13_74844_150092
  · exact context_13_74845_150121
  · exact context_13_74846_150141
  · exact context_13_74847_150148

theorem unmarked_context_11_4677_150150 : frontier 10 ⟨150150, by decide⟩
    (prefixCache 11 4677) (prefixPartial 11 4677) = false := by
  decide +kernel

theorem node_context_11_4677_150150 : EJMOriginalGlobalDAGData.nodes 10 ⟨150150, by decide⟩ =
    .split (coordinate 11) (![⟨149890, by decide⟩,⟨149981, by decide⟩,⟨150064, by decide⟩,⟨150149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4677_150150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4677 ⟨150150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4677
    ⟨150150, by decide⟩ (by decide) (![⟨149890, by decide⟩,⟨149981, by decide⟩,⟨150064, by decide⟩,⟨150149, by decide⟩]) unmarked_context_11_4677_150150 node_context_11_4677_150150
  intro a
  fin_cases a
  · exact context_12_18708_149890
  · exact context_12_18709_149981
  · exact context_12_18710_150064
  · exact context_12_18711_150149

theorem selected_cut_04657 : selected 8 ⟨150167, by decide⟩
    (prefixPartial 13 74848) = some ⟨13, 2, 0, 150167, 74848, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_74848_150167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74848 ⟨150167, by decide⟩ :=
  accepted_of_selected 13 74848 ⟨150167, by decide⟩ ⟨13, 2, 0, 150167, 74848, 1497, 16384⟩
    (by decide) selected_cut_04657

theorem selected_cut_04658 : selected 8 ⟨150191, by decide⟩
    (prefixPartial 13 74849) = some ⟨13, 2, 0, 150191, 74849, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_74849_150191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74849 ⟨150191, by decide⟩ :=
  accepted_of_selected 13 74849 ⟨150191, by decide⟩ ⟨13, 2, 0, 150191, 74849, 2517, 16384⟩
    (by decide) selected_cut_04658

theorem selected_cut_04659 : selected 8 ⟨150213, by decide⟩
    (prefixPartial 13 74850) = some ⟨13, 2, 0, 150213, 74850, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_74850_150213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74850 ⟨150213, by decide⟩ :=
  accepted_of_selected 13 74850 ⟨150213, by decide⟩ ⟨13, 2, 0, 150213, 74850, 1421, 16384⟩
    (by decide) selected_cut_04659

theorem selected_cut_04660 : selected 8 ⟨150221, by decide⟩
    (prefixPartial 13 74851) = some ⟨13, 2, 0, 150221, 74851, 897, 16384⟩ := by
  decide +kernel

theorem context_13_74851_150221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74851 ⟨150221, by decide⟩ :=
  accepted_of_selected 13 74851 ⟨150221, by decide⟩ ⟨13, 2, 0, 150221, 74851, 897, 16384⟩
    (by decide) selected_cut_04660

theorem unmarked_context_12_18712_150222 : frontier 9 ⟨150222, by decide⟩
    (prefixCache 12 18712) (prefixPartial 12 18712) = false := by
  decide +kernel

theorem node_context_12_18712_150222 : EJMOriginalGlobalDAGData.nodes 9 ⟨150222, by decide⟩ =
    .split (coordinate 12) (![⟨150167, by decide⟩,⟨150191, by decide⟩,⟨150213, by decide⟩,⟨150221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18712_150222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18712 ⟨150222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18712
    ⟨150222, by decide⟩ (by decide) (![⟨150167, by decide⟩,⟨150191, by decide⟩,⟨150213, by decide⟩,⟨150221, by decide⟩]) unmarked_context_12_18712_150222 node_context_12_18712_150222
  intro a
  fin_cases a
  · exact context_13_74848_150167
  · exact context_13_74849_150191
  · exact context_13_74850_150213
  · exact context_13_74851_150221

theorem selected_cut_04661 : selected 8 ⟨150249, by decide⟩
    (prefixPartial 13 74852) = some ⟨13, 2, 0, 150249, 74852, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_74852_150249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74852 ⟨150249, by decide⟩ :=
  accepted_of_selected 13 74852 ⟨150249, by decide⟩ ⟨13, 2, 0, 150249, 74852, 1541, 16384⟩
    (by decide) selected_cut_04661

theorem selected_cut_04662 : selected 8 ⟨150275, by decide⟩
    (prefixPartial 13 74853) = some ⟨13, 2, 0, 150275, 74853, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_74853_150275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74853 ⟨150275, by decide⟩ :=
  accepted_of_selected 13 74853 ⟨150275, by decide⟩ ⟨13, 2, 0, 150275, 74853, 1869, 16384⟩
    (by decide) selected_cut_04662

theorem selected_cut_04663 : selected 8 ⟨150301, by decide⟩
    (prefixPartial 13 74854) = some ⟨13, 2, 0, 150301, 74854, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_74854_150301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74854 ⟨150301, by decide⟩ :=
  accepted_of_selected 13 74854 ⟨150301, by decide⟩ ⟨13, 2, 0, 150301, 74854, 1469, 16384⟩
    (by decide) selected_cut_04663

theorem selected_cut_04664 : selected 8 ⟨150312, by decide⟩
    (prefixPartial 13 74855) = some ⟨13, 2, 0, 150312, 74855, 853, 16384⟩ := by
  decide +kernel

theorem context_13_74855_150312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74855 ⟨150312, by decide⟩ :=
  accepted_of_selected 13 74855 ⟨150312, by decide⟩ ⟨13, 2, 0, 150312, 74855, 853, 16384⟩
    (by decide) selected_cut_04664

theorem unmarked_context_12_18713_150313 : frontier 9 ⟨150313, by decide⟩
    (prefixCache 12 18713) (prefixPartial 12 18713) = false := by
  decide +kernel

theorem node_context_12_18713_150313 : EJMOriginalGlobalDAGData.nodes 9 ⟨150313, by decide⟩ =
    .split (coordinate 12) (![⟨150249, by decide⟩,⟨150275, by decide⟩,⟨150301, by decide⟩,⟨150312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18713_150313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18713 ⟨150313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18713
    ⟨150313, by decide⟩ (by decide) (![⟨150249, by decide⟩,⟨150275, by decide⟩,⟨150301, by decide⟩,⟨150312, by decide⟩]) unmarked_context_12_18713_150313 node_context_12_18713_150313
  intro a
  fin_cases a
  · exact context_13_74852_150249
  · exact context_13_74853_150275
  · exact context_13_74854_150301
  · exact context_13_74855_150312

theorem selected_cut_04665 : selected 8 ⟨150337, by decide⟩
    (prefixPartial 13 74856) = some ⟨13, 2, 0, 150337, 74856, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_74856_150337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74856 ⟨150337, by decide⟩ :=
  accepted_of_selected 13 74856 ⟨150337, by decide⟩ ⟨13, 2, 0, 150337, 74856, 1789, 16384⟩
    (by decide) selected_cut_04665

theorem selected_cut_04666 : selected 8 ⟨150364, by decide⟩
    (prefixPartial 13 74857) = some ⟨13, 2, 0, 150364, 74857, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_74857_150364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74857 ⟨150364, by decide⟩ :=
  accepted_of_selected 13 74857 ⟨150364, by decide⟩ ⟨13, 2, 0, 150364, 74857, 2457, 16384⟩
    (by decide) selected_cut_04666

theorem selected_cut_04667 : selected 8 ⟨150386, by decide⟩
    (prefixPartial 13 74858) = some ⟨13, 2, 0, 150386, 74858, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_74858_150386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74858 ⟨150386, by decide⟩ :=
  accepted_of_selected 13 74858 ⟨150386, by decide⟩ ⟨13, 2, 0, 150386, 74858, 1677, 16384⟩
    (by decide) selected_cut_04667

theorem selected_cut_04668 : selected 8 ⟨150394, by decide⟩
    (prefixPartial 13 74859) = some ⟨13, 2, 0, 150394, 74859, 953, 16384⟩ := by
  decide +kernel

theorem context_13_74859_150394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74859 ⟨150394, by decide⟩ :=
  accepted_of_selected 13 74859 ⟨150394, by decide⟩ ⟨13, 2, 0, 150394, 74859, 953, 16384⟩
    (by decide) selected_cut_04668

theorem unmarked_context_12_18714_150395 : frontier 9 ⟨150395, by decide⟩
    (prefixCache 12 18714) (prefixPartial 12 18714) = false := by
  decide +kernel

theorem node_context_12_18714_150395 : EJMOriginalGlobalDAGData.nodes 9 ⟨150395, by decide⟩ =
    .split (coordinate 12) (![⟨150337, by decide⟩,⟨150364, by decide⟩,⟨150386, by decide⟩,⟨150394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18714_150395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18714 ⟨150395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18714
    ⟨150395, by decide⟩ (by decide) (![⟨150337, by decide⟩,⟨150364, by decide⟩,⟨150386, by decide⟩,⟨150394, by decide⟩]) unmarked_context_12_18714_150395 node_context_12_18714_150395
  intro a
  fin_cases a
  · exact context_13_74856_150337
  · exact context_13_74857_150364
  · exact context_13_74858_150386
  · exact context_13_74859_150394

theorem selected_cut_04669 : selected 8 ⟨150422, by decide⟩
    (prefixPartial 13 74860) = some ⟨13, 2, 0, 150422, 74860, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_74860_150422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74860 ⟨150422, by decide⟩ :=
  accepted_of_selected 13 74860 ⟨150422, by decide⟩ ⟨13, 2, 0, 150422, 74860, 1917, 16384⟩
    (by decide) selected_cut_04669

theorem selected_cut_04670 : selected 8 ⟨150472, by decide⟩
    (prefixPartial 13 74861) = some ⟨13, 2, 0, 150472, 74861, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_74861_150472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74861 ⟨150472, by decide⟩ :=
  accepted_of_selected 13 74861 ⟨150472, by decide⟩ ⟨13, 2, 0, 150472, 74861, 2809, 16384⟩
    (by decide) selected_cut_04670

theorem selected_cut_04671 : selected 8 ⟨150499, by decide⟩
    (prefixPartial 13 74862) = some ⟨13, 2, 0, 150499, 74862, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_74862_150499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74862 ⟨150499, by decide⟩ :=
  accepted_of_selected 13 74862 ⟨150499, by decide⟩ ⟨13, 2, 0, 150499, 74862, 1729, 16384⟩
    (by decide) selected_cut_04671

theorem selected_cut_04672 : selected 8 ⟨150506, by decide⟩
    (prefixPartial 13 74863) = some ⟨13, 2, 0, 150506, 74863, 969, 16384⟩ := by
  decide +kernel

theorem context_13_74863_150506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74863 ⟨150506, by decide⟩ :=
  accepted_of_selected 13 74863 ⟨150506, by decide⟩ ⟨13, 2, 0, 150506, 74863, 969, 16384⟩
    (by decide) selected_cut_04672

theorem unmarked_context_12_18715_150507 : frontier 9 ⟨150507, by decide⟩
    (prefixCache 12 18715) (prefixPartial 12 18715) = false := by
  decide +kernel

theorem node_context_12_18715_150507 : EJMOriginalGlobalDAGData.nodes 9 ⟨150507, by decide⟩ =
    .split (coordinate 12) (![⟨150422, by decide⟩,⟨150472, by decide⟩,⟨150499, by decide⟩,⟨150506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18715_150507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18715 ⟨150507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18715
    ⟨150507, by decide⟩ (by decide) (![⟨150422, by decide⟩,⟨150472, by decide⟩,⟨150499, by decide⟩,⟨150506, by decide⟩]) unmarked_context_12_18715_150507 node_context_12_18715_150507
  intro a
  fin_cases a
  · exact context_13_74860_150422
  · exact context_13_74861_150472
  · exact context_13_74862_150499
  · exact context_13_74863_150506

theorem unmarked_context_11_4678_150508 : frontier 10 ⟨150508, by decide⟩
    (prefixCache 11 4678) (prefixPartial 11 4678) = false := by
  decide +kernel

theorem node_context_11_4678_150508 : EJMOriginalGlobalDAGData.nodes 10 ⟨150508, by decide⟩ =
    .split (coordinate 11) (![⟨150222, by decide⟩,⟨150313, by decide⟩,⟨150395, by decide⟩,⟨150507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4678_150508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4678 ⟨150508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4678
    ⟨150508, by decide⟩ (by decide) (![⟨150222, by decide⟩,⟨150313, by decide⟩,⟨150395, by decide⟩,⟨150507, by decide⟩]) unmarked_context_11_4678_150508 node_context_11_4678_150508
  intro a
  fin_cases a
  · exact context_12_18712_150222
  · exact context_12_18713_150313
  · exact context_12_18714_150395
  · exact context_12_18715_150507

theorem selected_cut_04673 : selected 8 ⟨150528, by decide⟩
    (prefixPartial 13 74864) = some ⟨13, 2, 0, 150528, 74864, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_74864_150528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74864 ⟨150528, by decide⟩ :=
  accepted_of_selected 13 74864 ⟨150528, by decide⟩ ⟨13, 2, 0, 150528, 74864, 1577, 16384⟩
    (by decide) selected_cut_04673

theorem selected_cut_04674 : selected 8 ⟨150562, by decide⟩
    (prefixPartial 13 74865) = some ⟨13, 2, 0, 150562, 74865, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_74865_150562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74865 ⟨150562, by decide⟩ :=
  accepted_of_selected 13 74865 ⟨150562, by decide⟩ ⟨13, 2, 0, 150562, 74865, 2489, 16384⟩
    (by decide) selected_cut_04674

theorem selected_cut_04675 : selected 8 ⟨150582, by decide⟩
    (prefixPartial 13 74866) = some ⟨13, 2, 0, 150582, 74866, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_74866_150582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74866 ⟨150582, by decide⟩ :=
  accepted_of_selected 13 74866 ⟨150582, by decide⟩ ⟨13, 2, 0, 150582, 74866, 1337, 16384⟩
    (by decide) selected_cut_04675

theorem selected_cut_04676 : selected 8 ⟨150590, by decide⟩
    (prefixPartial 13 74867) = some ⟨13, 2, 0, 150590, 74867, 937, 16384⟩ := by
  decide +kernel

theorem context_13_74867_150590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74867 ⟨150590, by decide⟩ :=
  accepted_of_selected 13 74867 ⟨150590, by decide⟩ ⟨13, 2, 0, 150590, 74867, 937, 16384⟩
    (by decide) selected_cut_04676

theorem unmarked_context_12_18716_150591 : frontier 9 ⟨150591, by decide⟩
    (prefixCache 12 18716) (prefixPartial 12 18716) = false := by
  decide +kernel

theorem node_context_12_18716_150591 : EJMOriginalGlobalDAGData.nodes 9 ⟨150591, by decide⟩ =
    .split (coordinate 12) (![⟨150528, by decide⟩,⟨150562, by decide⟩,⟨150582, by decide⟩,⟨150590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18716_150591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18716 ⟨150591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18716
    ⟨150591, by decide⟩ (by decide) (![⟨150528, by decide⟩,⟨150562, by decide⟩,⟨150582, by decide⟩,⟨150590, by decide⟩]) unmarked_context_12_18716_150591 node_context_12_18716_150591
  intro a
  fin_cases a
  · exact context_13_74864_150528
  · exact context_13_74865_150562
  · exact context_13_74866_150582
  · exact context_13_74867_150590

theorem selected_cut_04677 : selected 8 ⟨150616, by decide⟩
    (prefixPartial 13 74868) = some ⟨13, 2, 0, 150616, 74868, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_74868_150616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74868 ⟨150616, by decide⟩ :=
  accepted_of_selected 13 74868 ⟨150616, by decide⟩ ⟨13, 2, 0, 150616, 74868, 1585, 16384⟩
    (by decide) selected_cut_04677

theorem selected_cut_04678 : selected 8 ⟨150644, by decide⟩
    (prefixPartial 13 74869) = some ⟨13, 2, 0, 150644, 74869, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_74869_150644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74869 ⟨150644, by decide⟩ :=
  accepted_of_selected 13 74869 ⟨150644, by decide⟩ ⟨13, 2, 0, 150644, 74869, 1837, 16384⟩
    (by decide) selected_cut_04678

theorem selected_cut_04679 : selected 8 ⟨150665, by decide⟩
    (prefixPartial 13 74870) = some ⟨13, 2, 0, 150665, 74870, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_74870_150665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74870 ⟨150665, by decide⟩ :=
  accepted_of_selected 13 74870 ⟨150665, by decide⟩ ⟨13, 2, 0, 150665, 74870, 1433, 16384⟩
    (by decide) selected_cut_04679

theorem selected_cut_04680 : selected 8 ⟨150673, by decide⟩
    (prefixPartial 13 74871) = some ⟨13, 2, 0, 150673, 74871, 821, 16384⟩ := by
  decide +kernel

theorem context_13_74871_150673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74871 ⟨150673, by decide⟩ :=
  accepted_of_selected 13 74871 ⟨150673, by decide⟩ ⟨13, 2, 0, 150673, 74871, 821, 16384⟩
    (by decide) selected_cut_04680

theorem unmarked_context_12_18717_150674 : frontier 9 ⟨150674, by decide⟩
    (prefixCache 12 18717) (prefixPartial 12 18717) = false := by
  decide +kernel

theorem node_context_12_18717_150674 : EJMOriginalGlobalDAGData.nodes 9 ⟨150674, by decide⟩ =
    .split (coordinate 12) (![⟨150616, by decide⟩,⟨150644, by decide⟩,⟨150665, by decide⟩,⟨150673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18717_150674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18717 ⟨150674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18717
    ⟨150674, by decide⟩ (by decide) (![⟨150616, by decide⟩,⟨150644, by decide⟩,⟨150665, by decide⟩,⟨150673, by decide⟩]) unmarked_context_12_18717_150674 node_context_12_18717_150674
  intro a
  fin_cases a
  · exact context_13_74868_150616
  · exact context_13_74869_150644
  · exact context_13_74870_150665
  · exact context_13_74871_150673

theorem selected_cut_04681 : selected 8 ⟨150701, by decide⟩
    (prefixPartial 13 74872) = some ⟨13, 2, 0, 150701, 74872, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_74872_150701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74872 ⟨150701, by decide⟩ :=
  accepted_of_selected 13 74872 ⟨150701, by decide⟩ ⟨13, 2, 0, 150701, 74872, 2033, 16384⟩
    (by decide) selected_cut_04681

theorem selected_cut_04682 : selected 8 ⟨150737, by decide⟩
    (prefixPartial 13 74873) = some ⟨13, 2, 0, 150737, 74873, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_74873_150737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74873 ⟨150737, by decide⟩ :=
  accepted_of_selected 13 74873 ⟨150737, by decide⟩ ⟨13, 2, 0, 150737, 74873, 2737, 16384⟩
    (by decide) selected_cut_04682

theorem selected_cut_04683 : selected 8 ⟨150755, by decide⟩
    (prefixPartial 13 74874) = some ⟨13, 2, 0, 150755, 74874, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_74874_150755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74874 ⟨150755, by decide⟩ :=
  accepted_of_selected 13 74874 ⟨150755, by decide⟩ ⟨13, 2, 0, 150755, 74874, 1793, 16384⟩
    (by decide) selected_cut_04683

theorem selected_cut_04684 : selected 8 ⟨150762, by decide⟩
    (prefixPartial 13 74875) = some ⟨13, 2, 0, 150762, 74875, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_74875_150762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74875 ⟨150762, by decide⟩ :=
  accepted_of_selected 13 74875 ⟨150762, by decide⟩ ⟨13, 2, 0, 150762, 74875, 1021, 16384⟩
    (by decide) selected_cut_04684

theorem unmarked_context_12_18718_150763 : frontier 9 ⟨150763, by decide⟩
    (prefixCache 12 18718) (prefixPartial 12 18718) = false := by
  decide +kernel

theorem node_context_12_18718_150763 : EJMOriginalGlobalDAGData.nodes 9 ⟨150763, by decide⟩ =
    .split (coordinate 12) (![⟨150701, by decide⟩,⟨150737, by decide⟩,⟨150755, by decide⟩,⟨150762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18718_150763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18718 ⟨150763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18718
    ⟨150763, by decide⟩ (by decide) (![⟨150701, by decide⟩,⟨150737, by decide⟩,⟨150755, by decide⟩,⟨150762, by decide⟩]) unmarked_context_12_18718_150763 node_context_12_18718_150763
  intro a
  fin_cases a
  · exact context_13_74872_150701
  · exact context_13_74873_150737
  · exact context_13_74874_150755
  · exact context_13_74875_150762

theorem selected_cut_04685 : selected 8 ⟨150795, by decide⟩
    (prefixPartial 13 74876) = some ⟨13, 2, 0, 150795, 74876, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_74876_150795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74876 ⟨150795, by decide⟩ :=
  accepted_of_selected 13 74876 ⟨150795, by decide⟩ ⟨13, 2, 0, 150795, 74876, 1801, 16384⟩
    (by decide) selected_cut_04685

theorem selected_cut_04686 : selected 8 ⟨150828, by decide⟩
    (prefixPartial 13 74877) = some ⟨13, 2, 0, 150828, 74877, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_74877_150828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74877 ⟨150828, by decide⟩ :=
  accepted_of_selected 13 74877 ⟨150828, by decide⟩ ⟨13, 2, 0, 150828, 74877, 2313, 16384⟩
    (by decide) selected_cut_04686

theorem selected_cut_04687 : selected 8 ⟨150849, by decide⟩
    (prefixPartial 13 74878) = some ⟨13, 2, 0, 150849, 74878, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_74878_150849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74878 ⟨150849, by decide⟩ :=
  accepted_of_selected 13 74878 ⟨150849, by decide⟩ ⟨13, 2, 0, 150849, 74878, 1465, 16384⟩
    (by decide) selected_cut_04687

theorem selected_cut_04688 : selected 8 ⟨150854, by decide⟩
    (prefixPartial 13 74879) = some ⟨13, 2, 0, 150854, 74879, 901, 16384⟩ := by
  decide +kernel

theorem context_13_74879_150854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74879 ⟨150854, by decide⟩ :=
  accepted_of_selected 13 74879 ⟨150854, by decide⟩ ⟨13, 2, 0, 150854, 74879, 901, 16384⟩
    (by decide) selected_cut_04688

theorem unmarked_context_12_18719_150855 : frontier 9 ⟨150855, by decide⟩
    (prefixCache 12 18719) (prefixPartial 12 18719) = false := by
  decide +kernel

theorem node_context_12_18719_150855 : EJMOriginalGlobalDAGData.nodes 9 ⟨150855, by decide⟩ =
    .split (coordinate 12) (![⟨150795, by decide⟩,⟨150828, by decide⟩,⟨150849, by decide⟩,⟨150854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18719_150855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18719 ⟨150855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18719
    ⟨150855, by decide⟩ (by decide) (![⟨150795, by decide⟩,⟨150828, by decide⟩,⟨150849, by decide⟩,⟨150854, by decide⟩]) unmarked_context_12_18719_150855 node_context_12_18719_150855
  intro a
  fin_cases a
  · exact context_13_74876_150795
  · exact context_13_74877_150828
  · exact context_13_74878_150849
  · exact context_13_74879_150854

theorem unmarked_context_11_4679_150856 : frontier 10 ⟨150856, by decide⟩
    (prefixCache 11 4679) (prefixPartial 11 4679) = false := by
  decide +kernel

theorem node_context_11_4679_150856 : EJMOriginalGlobalDAGData.nodes 10 ⟨150856, by decide⟩ =
    .split (coordinate 11) (![⟨150591, by decide⟩,⟨150674, by decide⟩,⟨150763, by decide⟩,⟨150855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4679_150856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4679 ⟨150856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4679
    ⟨150856, by decide⟩ (by decide) (![⟨150591, by decide⟩,⟨150674, by decide⟩,⟨150763, by decide⟩,⟨150855, by decide⟩]) unmarked_context_11_4679_150856 node_context_11_4679_150856
  intro a
  fin_cases a
  · exact context_12_18716_150591
  · exact context_12_18717_150674
  · exact context_12_18718_150763
  · exact context_12_18719_150855

theorem unmarked_context_10_1169_150857 : frontier 11 ⟨150857, by decide⟩
    (prefixCache 10 1169) (prefixPartial 10 1169) = false := by
  decide +kernel

theorem node_context_10_1169_150857 : EJMOriginalGlobalDAGData.nodes 11 ⟨150857, by decide⟩ =
    .split (coordinate 10) (![⟨149814, by decide⟩,⟨150150, by decide⟩,⟨150508, by decide⟩,⟨150856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1169_150857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1169 ⟨150857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1169
    ⟨150857, by decide⟩ (by decide) (![⟨149814, by decide⟩,⟨150150, by decide⟩,⟨150508, by decide⟩,⟨150856, by decide⟩]) unmarked_context_10_1169_150857 node_context_10_1169_150857
  intro a
  fin_cases a
  · exact context_11_4676_149814
  · exact context_11_4677_150150
  · exact context_11_4678_150508
  · exact context_11_4679_150856

theorem selected_cut_04689 : selected 8 ⟨150882, by decide⟩
    (prefixPartial 13 74880) = some ⟨13, 2, 0, 150882, 74880, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_74880_150882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74880 ⟨150882, by decide⟩ :=
  accepted_of_selected 13 74880 ⟨150882, by decide⟩ ⟨13, 2, 0, 150882, 74880, 1729, 16384⟩
    (by decide) selected_cut_04689

theorem selected_cut_04690 : selected 8 ⟨150919, by decide⟩
    (prefixPartial 13 74881) = some ⟨13, 2, 0, 150919, 74881, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_74881_150919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74881 ⟨150919, by decide⟩ :=
  accepted_of_selected 13 74881 ⟨150919, by decide⟩ ⟨13, 2, 0, 150919, 74881, 2889, 16384⟩
    (by decide) selected_cut_04690

theorem selected_cut_04691 : selected 8 ⟨150940, by decide⟩
    (prefixPartial 13 74882) = some ⟨13, 2, 0, 150940, 74882, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_74882_150940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74882 ⟨150940, by decide⟩ :=
  accepted_of_selected 13 74882 ⟨150940, by decide⟩ ⟨13, 2, 0, 150940, 74882, 1593, 16384⟩
    (by decide) selected_cut_04691

theorem selected_cut_04692 : selected 8 ⟨150949, by decide⟩
    (prefixPartial 13 74883) = some ⟨13, 2, 0, 150949, 74883, 957, 16384⟩ := by
  decide +kernel

theorem context_13_74883_150949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74883 ⟨150949, by decide⟩ :=
  accepted_of_selected 13 74883 ⟨150949, by decide⟩ ⟨13, 2, 0, 150949, 74883, 957, 16384⟩
    (by decide) selected_cut_04692

theorem unmarked_context_12_18720_150950 : frontier 9 ⟨150950, by decide⟩
    (prefixCache 12 18720) (prefixPartial 12 18720) = false := by
  decide +kernel

theorem node_context_12_18720_150950 : EJMOriginalGlobalDAGData.nodes 9 ⟨150950, by decide⟩ =
    .split (coordinate 12) (![⟨150882, by decide⟩,⟨150919, by decide⟩,⟨150940, by decide⟩,⟨150949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18720_150950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18720 ⟨150950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18720
    ⟨150950, by decide⟩ (by decide) (![⟨150882, by decide⟩,⟨150919, by decide⟩,⟨150940, by decide⟩,⟨150949, by decide⟩]) unmarked_context_12_18720_150950 node_context_12_18720_150950
  intro a
  fin_cases a
  · exact context_13_74880_150882
  · exact context_13_74881_150919
  · exact context_13_74882_150940
  · exact context_13_74883_150949

theorem selected_cut_04693 : selected 8 ⟨150971, by decide⟩
    (prefixPartial 13 74884) = some ⟨13, 2, 0, 150971, 74884, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_74884_150971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74884 ⟨150971, by decide⟩ :=
  accepted_of_selected 13 74884 ⟨150971, by decide⟩ ⟨13, 2, 0, 150971, 74884, 1429, 16384⟩
    (by decide) selected_cut_04693

theorem selected_cut_04694 : selected 8 ⟨150996, by decide⟩
    (prefixPartial 13 74885) = some ⟨13, 2, 0, 150996, 74885, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_74885_150996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74885 ⟨150996, by decide⟩ :=
  accepted_of_selected 13 74885 ⟨150996, by decide⟩ ⟨13, 2, 0, 150996, 74885, 1881, 16384⟩
    (by decide) selected_cut_04694

theorem selected_cut_04695 : selected 8 ⟨151016, by decide⟩
    (prefixPartial 13 74886) = some ⟨13, 2, 0, 151016, 74886, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_74886_151016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74886 ⟨151016, by decide⟩ :=
  accepted_of_selected 13 74886 ⟨151016, by decide⟩ ⟨13, 2, 0, 151016, 74886, 1581, 16384⟩
    (by decide) selected_cut_04695

theorem selected_cut_04696 : selected 8 ⟨151022, by decide⟩
    (prefixPartial 13 74887) = some ⟨13, 2, 0, 151022, 74887, 869, 16384⟩ := by
  decide +kernel

theorem context_13_74887_151022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74887 ⟨151022, by decide⟩ :=
  accepted_of_selected 13 74887 ⟨151022, by decide⟩ ⟨13, 2, 0, 151022, 74887, 869, 16384⟩
    (by decide) selected_cut_04696

theorem unmarked_context_12_18721_151023 : frontier 9 ⟨151023, by decide⟩
    (prefixCache 12 18721) (prefixPartial 12 18721) = false := by
  decide +kernel

theorem node_context_12_18721_151023 : EJMOriginalGlobalDAGData.nodes 9 ⟨151023, by decide⟩ =
    .split (coordinate 12) (![⟨150971, by decide⟩,⟨150996, by decide⟩,⟨151016, by decide⟩,⟨151022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18721_151023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18721 ⟨151023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18721
    ⟨151023, by decide⟩ (by decide) (![⟨150971, by decide⟩,⟨150996, by decide⟩,⟨151016, by decide⟩,⟨151022, by decide⟩]) unmarked_context_12_18721_151023 node_context_12_18721_151023
  intro a
  fin_cases a
  · exact context_13_74884_150971
  · exact context_13_74885_150996
  · exact context_13_74886_151016
  · exact context_13_74887_151022

theorem selected_cut_04697 : selected 8 ⟨151046, by decide⟩
    (prefixPartial 13 74888) = some ⟨13, 2, 0, 151046, 74888, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_74888_151046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74888 ⟨151046, by decide⟩ :=
  accepted_of_selected 13 74888 ⟨151046, by decide⟩ ⟨13, 2, 0, 151046, 74888, 1757, 16384⟩
    (by decide) selected_cut_04697

theorem selected_cut_04698 : selected 8 ⟨151080, by decide⟩
    (prefixPartial 13 74889) = some ⟨13, 2, 0, 151080, 74889, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_74889_151080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74889 ⟨151080, by decide⟩ :=
  accepted_of_selected 13 74889 ⟨151080, by decide⟩ ⟨13, 2, 0, 151080, 74889, 2457, 16384⟩
    (by decide) selected_cut_04698

theorem selected_cut_04699 : selected 8 ⟨151099, by decide⟩
    (prefixPartial 13 74890) = some ⟨13, 2, 0, 151099, 74890, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_74890_151099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74890 ⟨151099, by decide⟩ :=
  accepted_of_selected 13 74890 ⟨151099, by decide⟩ ⟨13, 2, 0, 151099, 74890, 1721, 16384⟩
    (by decide) selected_cut_04699

theorem selected_cut_04700 : selected 8 ⟨151107, by decide⟩
    (prefixPartial 13 74891) = some ⟨13, 2, 0, 151107, 74891, 977, 16384⟩ := by
  decide +kernel

theorem context_13_74891_151107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74891 ⟨151107, by decide⟩ :=
  accepted_of_selected 13 74891 ⟨151107, by decide⟩ ⟨13, 2, 0, 151107, 74891, 977, 16384⟩
    (by decide) selected_cut_04700

theorem unmarked_context_12_18722_151108 : frontier 9 ⟨151108, by decide⟩
    (prefixCache 12 18722) (prefixPartial 12 18722) = false := by
  decide +kernel

theorem node_context_12_18722_151108 : EJMOriginalGlobalDAGData.nodes 9 ⟨151108, by decide⟩ =
    .split (coordinate 12) (![⟨151046, by decide⟩,⟨151080, by decide⟩,⟨151099, by decide⟩,⟨151107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18722_151108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18722 ⟨151108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18722
    ⟨151108, by decide⟩ (by decide) (![⟨151046, by decide⟩,⟨151080, by decide⟩,⟨151099, by decide⟩,⟨151107, by decide⟩]) unmarked_context_12_18722_151108 node_context_12_18722_151108
  intro a
  fin_cases a
  · exact context_13_74888_151046
  · exact context_13_74889_151080
  · exact context_13_74890_151099
  · exact context_13_74891_151107

theorem selected_cut_04701 : selected 8 ⟨151134, by decide⟩
    (prefixPartial 13 74892) = some ⟨13, 2, 0, 151134, 74892, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_74892_151134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74892 ⟨151134, by decide⟩ :=
  accepted_of_selected 13 74892 ⟨151134, by decide⟩ ⟨13, 2, 0, 151134, 74892, 1769, 16384⟩
    (by decide) selected_cut_04701

theorem selected_cut_04702 : selected 8 ⟨151167, by decide⟩
    (prefixPartial 13 74893) = some ⟨13, 2, 0, 151167, 74893, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_74893_151167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74893 ⟨151167, by decide⟩ :=
  accepted_of_selected 13 74893 ⟨151167, by decide⟩ ⟨13, 2, 0, 151167, 74893, 2401, 16384⟩
    (by decide) selected_cut_04702

theorem selected_cut_04703 : selected 8 ⟨151191, by decide⟩
    (prefixPartial 13 74894) = some ⟨13, 2, 0, 151191, 74894, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_74894_151191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74894 ⟨151191, by decide⟩ :=
  accepted_of_selected 13 74894 ⟨151191, by decide⟩ ⟨13, 2, 0, 151191, 74894, 1809, 16384⟩
    (by decide) selected_cut_04703

theorem selected_cut_04704 : selected 8 ⟨151196, by decide⟩
    (prefixPartial 13 74895) = some ⟨13, 2, 0, 151196, 74895, 969, 16384⟩ := by
  decide +kernel

theorem context_13_74895_151196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74895 ⟨151196, by decide⟩ :=
  accepted_of_selected 13 74895 ⟨151196, by decide⟩ ⟨13, 2, 0, 151196, 74895, 969, 16384⟩
    (by decide) selected_cut_04704

theorem unmarked_context_12_18723_151197 : frontier 9 ⟨151197, by decide⟩
    (prefixCache 12 18723) (prefixPartial 12 18723) = false := by
  decide +kernel

theorem node_context_12_18723_151197 : EJMOriginalGlobalDAGData.nodes 9 ⟨151197, by decide⟩ =
    .split (coordinate 12) (![⟨151134, by decide⟩,⟨151167, by decide⟩,⟨151191, by decide⟩,⟨151196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18723_151197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18723 ⟨151197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18723
    ⟨151197, by decide⟩ (by decide) (![⟨151134, by decide⟩,⟨151167, by decide⟩,⟨151191, by decide⟩,⟨151196, by decide⟩]) unmarked_context_12_18723_151197 node_context_12_18723_151197
  intro a
  fin_cases a
  · exact context_13_74892_151134
  · exact context_13_74893_151167
  · exact context_13_74894_151191
  · exact context_13_74895_151196

theorem unmarked_context_11_4680_151198 : frontier 10 ⟨151198, by decide⟩
    (prefixCache 11 4680) (prefixPartial 11 4680) = false := by
  decide +kernel

theorem node_context_11_4680_151198 : EJMOriginalGlobalDAGData.nodes 10 ⟨151198, by decide⟩ =
    .split (coordinate 11) (![⟨150950, by decide⟩,⟨151023, by decide⟩,⟨151108, by decide⟩,⟨151197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4680_151198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4680 ⟨151198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4680
    ⟨151198, by decide⟩ (by decide) (![⟨150950, by decide⟩,⟨151023, by decide⟩,⟨151108, by decide⟩,⟨151197, by decide⟩]) unmarked_context_11_4680_151198 node_context_11_4680_151198
  intro a
  fin_cases a
  · exact context_12_18720_150950
  · exact context_12_18721_151023
  · exact context_12_18722_151108
  · exact context_12_18723_151197

theorem selected_cut_04705 : selected 8 ⟨151215, by decide⟩
    (prefixPartial 13 74896) = some ⟨13, 2, 0, 151215, 74896, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_74896_151215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74896 ⟨151215, by decide⟩ :=
  accepted_of_selected 13 74896 ⟨151215, by decide⟩ ⟨13, 2, 0, 151215, 74896, 1169, 16384⟩
    (by decide) selected_cut_04705

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
