/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover344
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33124 : selected 10 ⟨853558, by decide⟩
    (prefixPartial 11 27511) = some ⟨11, 2, 0, 853558, 27511, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_27511_853558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27511 ⟨853558, by decide⟩ :=
  accepted_of_selected 11 27511 ⟨853558, by decide⟩ ⟨11, 2, 0, 853558, 27511, 1685, 262144⟩
    (by decide) selected_cut_33124

theorem unmarked_context_10_6877_853559 : frontier 11 ⟨853559, by decide⟩
    (prefixCache 10 6877) (prefixPartial 10 6877) = false := by
  decide +kernel

theorem node_context_10_6877_853559 : EJMOriginalGlobalDAGData.nodes 11 ⟨853559, by decide⟩ =
    .split (coordinate 10) (![⟨853504, by decide⟩,⟨853519, by decide⟩,⟨853539, by decide⟩,⟨853558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6877_853559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6877 ⟨853559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6877
    ⟨853559, by decide⟩ (by decide) (![⟨853504, by decide⟩,⟨853519, by decide⟩,⟨853539, by decide⟩,⟨853558, by decide⟩]) unmarked_context_10_6877_853559 node_context_10_6877_853559
  intro a
  fin_cases a
  · exact context_11_27508_853504
  · exact context_11_27509_853519
  · exact context_11_27510_853539
  · exact context_11_27511_853558

theorem selected_cut_33125 : selected 11 ⟨853616, by decide⟩
    (prefixPartial 10 6878) = some ⟨10, 2, 0, 853616, 6878, 4025, 1048576⟩ := by
  decide +kernel

theorem context_10_6878_853616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6878 ⟨853616, by decide⟩ :=
  accepted_of_selected 10 6878 ⟨853616, by decide⟩ ⟨10, 2, 0, 853616, 6878, 4025, 1048576⟩
    (by decide) selected_cut_33125

theorem selected_cut_33126 : selected 11 ⟨853641, by decide⟩
    (prefixPartial 10 6879) = some ⟨10, 2, 0, 853641, 6879, 853, 1048576⟩ := by
  decide +kernel

theorem context_10_6879_853641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6879 ⟨853641, by decide⟩ :=
  accepted_of_selected 10 6879 ⟨853641, by decide⟩ ⟨10, 2, 0, 853641, 6879, 853, 1048576⟩
    (by decide) selected_cut_33126

theorem unmarked_context_9_1719_853642 : frontier 12 ⟨853642, by decide⟩
    (prefixCache 9 1719) (prefixPartial 9 1719) = false := by
  decide +kernel

theorem node_context_9_1719_853642 : EJMOriginalGlobalDAGData.nodes 12 ⟨853642, by decide⟩ =
    .split (coordinate 9) (![⟨853473, by decide⟩,⟨853559, by decide⟩,⟨853616, by decide⟩,⟨853641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1719_853642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1719 ⟨853642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1719
    ⟨853642, by decide⟩ (by decide) (![⟨853473, by decide⟩,⟨853559, by decide⟩,⟨853616, by decide⟩,⟨853641, by decide⟩]) unmarked_context_9_1719_853642 node_context_9_1719_853642
  intro a
  fin_cases a
  · exact context_10_6876_853473
  · exact context_10_6877_853559
  · exact context_10_6878_853616
  · exact context_10_6879_853641

theorem unmarked_context_8_429_853643 : frontier 13 ⟨853643, by decide⟩
    (prefixCache 8 429) (prefixPartial 8 429) = false := by
  decide +kernel

theorem node_context_8_429_853643 : EJMOriginalGlobalDAGData.nodes 13 ⟨853643, by decide⟩ =
    .split (coordinate 8) (![⟨849273, by decide⟩,⟨852170, by decide⟩,⟨853306, by decide⟩,⟨853642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_429_853643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 429 ⟨853643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 429
    ⟨853643, by decide⟩ (by decide) (![⟨849273, by decide⟩,⟨852170, by decide⟩,⟨853306, by decide⟩,⟨853642, by decide⟩]) unmarked_context_8_429_853643 node_context_8_429_853643
  intro a
  fin_cases a
  · exact context_9_1716_849273
  · exact context_9_1717_852170
  · exact context_9_1718_853306
  · exact context_9_1719_853642

theorem selected_cut_33127 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 27520) = some ⟨11, 1, 0, 434745, 27520, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27520_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27520 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 27520 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 27520, 1, 262144⟩
    (by decide) selected_cut_33127

theorem selected_cut_33128 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 110084) = some ⟨12, 1, 0, 448748, 110084, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110084_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110084 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 110084 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 110084, 1, 65536⟩
    (by decide) selected_cut_33128

theorem selected_cut_33129 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 110085) = some ⟨12, 1, 0, 34034, 110085, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110085_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110085 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 110085 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 110085, 1, 65536⟩
    (by decide) selected_cut_33129

theorem selected_cut_33130 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 110086) = some ⟨12, 1, 0, 763842, 110086, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110086_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110086 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 110086 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 110086, 1, 65536⟩
    (by decide) selected_cut_33130

theorem selected_cut_33131 : selected 8 ⟨853735, by decide⟩
    (prefixPartial 13 440348) = some ⟨13, 2, 0, 853735, 440348, 3817, 16384⟩ := by
  decide +kernel

theorem context_13_440348_853735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440348 ⟨853735, by decide⟩ :=
  accepted_of_selected 13 440348 ⟨853735, by decide⟩ ⟨13, 2, 0, 853735, 440348, 3817, 16384⟩
    (by decide) selected_cut_33131

theorem selected_cut_33132 : selected 7 ⟨853763, by decide⟩
    (prefixPartial 14 1761396) = some ⟨14, 2, 0, 853763, 1761396, 1045, 4096⟩ := by
  decide +kernel

theorem context_14_1761396_853763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1761396 ⟨853763, by decide⟩ :=
  accepted_of_selected 14 1761396 ⟨853763, by decide⟩ ⟨14, 2, 0, 853763, 1761396, 1045, 4096⟩
    (by decide) selected_cut_33132

theorem selected_cut_33133 : selected 7 ⟨853785, by decide⟩
    (prefixPartial 14 1761397) = some ⟨14, 2, 0, 853785, 1761397, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_1761397_853785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1761397 ⟨853785, by decide⟩ :=
  accepted_of_selected 14 1761397 ⟨853785, by decide⟩ ⟨14, 2, 0, 853785, 1761397, 1097, 4096⟩
    (by decide) selected_cut_33133

theorem selected_cut_33134 : selected 7 ⟨853807, by decide⟩
    (prefixPartial 14 1761398) = some ⟨14, 2, 0, 853807, 1761398, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_1761398_853807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1761398 ⟨853807, by decide⟩ :=
  accepted_of_selected 14 1761398 ⟨853807, by decide⟩ ⟨14, 2, 0, 853807, 1761398, 1053, 4096⟩
    (by decide) selected_cut_33134

theorem selected_cut_33135 : selected 7 ⟨853830, by decide⟩
    (prefixPartial 14 1761399) = some ⟨14, 2, 0, 853830, 1761399, 917, 4096⟩ := by
  decide +kernel

theorem context_14_1761399_853830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1761399 ⟨853830, by decide⟩ :=
  accepted_of_selected 14 1761399 ⟨853830, by decide⟩ ⟨14, 2, 0, 853830, 1761399, 917, 4096⟩
    (by decide) selected_cut_33135

theorem unmarked_context_13_440349_853831 : frontier 8 ⟨853831, by decide⟩
    (prefixCache 13 440349) (prefixPartial 13 440349) = false := by
  decide +kernel

theorem node_context_13_440349_853831 : EJMOriginalGlobalDAGData.nodes 8 ⟨853831, by decide⟩ =
    .split (coordinate 13) (![⟨853763, by decide⟩,⟨853785, by decide⟩,⟨853807, by decide⟩,⟨853830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_440349_853831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440349 ⟨853831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 440349
    ⟨853831, by decide⟩ (by decide) (![⟨853763, by decide⟩,⟨853785, by decide⟩,⟨853807, by decide⟩,⟨853830, by decide⟩]) unmarked_context_13_440349_853831 node_context_13_440349_853831
  intro a
  fin_cases a
  · exact context_14_1761396_853763
  · exact context_14_1761397_853785
  · exact context_14_1761398_853807
  · exact context_14_1761399_853830

theorem selected_cut_33136 : selected 8 ⟨853895, by decide⟩
    (prefixPartial 13 440350) = some ⟨13, 2, 0, 853895, 440350, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_440350_853895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440350 ⟨853895, by decide⟩ :=
  accepted_of_selected 13 440350 ⟨853895, by decide⟩ ⟨13, 2, 0, 853895, 440350, 2217, 16384⟩
    (by decide) selected_cut_33136

theorem selected_cut_33137 : selected 8 ⟨853921, by decide⟩
    (prefixPartial 13 440351) = some ⟨13, 2, 0, 853921, 440351, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_440351_853921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440351 ⟨853921, by decide⟩ :=
  accepted_of_selected 13 440351 ⟨853921, by decide⟩ ⟨13, 2, 0, 853921, 440351, 1173, 16384⟩
    (by decide) selected_cut_33137

theorem unmarked_context_12_110087_853922 : frontier 9 ⟨853922, by decide⟩
    (prefixCache 12 110087) (prefixPartial 12 110087) = false := by
  decide +kernel

theorem node_context_12_110087_853922 : EJMOriginalGlobalDAGData.nodes 9 ⟨853922, by decide⟩ =
    .split (coordinate 12) (![⟨853735, by decide⟩,⟨853831, by decide⟩,⟨853895, by decide⟩,⟨853921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110087_853922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110087 ⟨853922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110087
    ⟨853922, by decide⟩ (by decide) (![⟨853735, by decide⟩,⟨853831, by decide⟩,⟨853895, by decide⟩,⟨853921, by decide⟩]) unmarked_context_12_110087_853922 node_context_12_110087_853922
  intro a
  fin_cases a
  · exact context_13_440348_853735
  · exact context_13_440349_853831
  · exact context_13_440350_853895
  · exact context_13_440351_853921

theorem unmarked_context_11_27521_853923 : frontier 10 ⟨853923, by decide⟩
    (prefixCache 11 27521) (prefixPartial 11 27521) = false := by
  decide +kernel

theorem node_context_11_27521_853923 : EJMOriginalGlobalDAGData.nodes 10 ⟨853923, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨853922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27521_853923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27521 ⟨853923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27521
    ⟨853923, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨853922, by decide⟩]) unmarked_context_11_27521_853923 node_context_11_27521_853923
  intro a
  fin_cases a
  · exact context_12_110084_448748
  · exact context_12_110085_34034
  · exact context_12_110086_763842
  · exact context_12_110087_853922

theorem selected_cut_33138 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 110088) = some ⟨12, 1, 0, 448748, 110088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110088_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110088 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 110088 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 110088, 1, 65536⟩
    (by decide) selected_cut_33138

theorem selected_cut_33139 : selected 8 ⟨854008, by decide⟩
    (prefixPartial 13 440356) = some ⟨13, 2, 0, 854008, 440356, 3745, 16384⟩ := by
  decide +kernel

theorem context_13_440356_854008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440356 ⟨854008, by decide⟩ :=
  accepted_of_selected 13 440356 ⟨854008, by decide⟩ ⟨13, 2, 0, 854008, 440356, 3745, 16384⟩
    (by decide) selected_cut_33139

theorem selected_cut_33140 : selected 8 ⟨854071, by decide⟩
    (prefixPartial 13 440357) = some ⟨13, 2, 0, 854071, 440357, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_440357_854071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440357 ⟨854071, by decide⟩ :=
  accepted_of_selected 13 440357 ⟨854071, by decide⟩ ⟨13, 2, 0, 854071, 440357, 3217, 16384⟩
    (by decide) selected_cut_33140

theorem selected_cut_33141 : selected 8 ⟨854114, by decide⟩
    (prefixPartial 13 440358) = some ⟨13, 2, 0, 854114, 440358, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_440358_854114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440358 ⟨854114, by decide⟩ :=
  accepted_of_selected 13 440358 ⟨854114, by decide⟩ ⟨13, 2, 0, 854114, 440358, 1945, 16384⟩
    (by decide) selected_cut_33141

theorem selected_cut_33142 : selected 8 ⟨854124, by decide⟩
    (prefixPartial 13 440359) = some ⟨13, 2, 0, 854124, 440359, 941, 16384⟩ := by
  decide +kernel

theorem context_13_440359_854124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440359 ⟨854124, by decide⟩ :=
  accepted_of_selected 13 440359 ⟨854124, by decide⟩ ⟨13, 2, 0, 854124, 440359, 941, 16384⟩
    (by decide) selected_cut_33142

theorem unmarked_context_12_110089_854125 : frontier 9 ⟨854125, by decide⟩
    (prefixCache 12 110089) (prefixPartial 12 110089) = false := by
  decide +kernel

theorem node_context_12_110089_854125 : EJMOriginalGlobalDAGData.nodes 9 ⟨854125, by decide⟩ =
    .split (coordinate 12) (![⟨854008, by decide⟩,⟨854071, by decide⟩,⟨854114, by decide⟩,⟨854124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110089_854125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110089 ⟨854125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110089
    ⟨854125, by decide⟩ (by decide) (![⟨854008, by decide⟩,⟨854071, by decide⟩,⟨854114, by decide⟩,⟨854124, by decide⟩]) unmarked_context_12_110089_854125 node_context_12_110089_854125
  intro a
  fin_cases a
  · exact context_13_440356_854008
  · exact context_13_440357_854071
  · exact context_13_440358_854114
  · exact context_13_440359_854124

theorem selected_cut_33143 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 110090) = some ⟨12, 1, 0, 763842, 110090, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110090_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110090 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 110090 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 110090, 1, 65536⟩
    (by decide) selected_cut_33143

theorem selected_cut_33144 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 110091) = some ⟨12, 1, 0, 604131, 110091, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110091_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110091 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 110091 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 110091, 1, 65536⟩
    (by decide) selected_cut_33144

theorem unmarked_context_11_27522_854126 : frontier 10 ⟨854126, by decide⟩
    (prefixCache 11 27522) (prefixPartial 11 27522) = false := by
  decide +kernel

theorem node_context_11_27522_854126 : EJMOriginalGlobalDAGData.nodes 10 ⟨854126, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨854125, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27522_854126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27522 ⟨854126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27522
    ⟨854126, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨854125, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_27522_854126 node_context_11_27522_854126
  intro a
  fin_cases a
  · exact context_12_110088_448748
  · exact context_12_110089_854125
  · exact context_12_110090_763842
  · exact context_12_110091_604131

theorem selected_cut_33145 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 27523) = some ⟨11, 1, 0, 789341, 27523, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27523_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27523 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 27523 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 27523, 1, 262144⟩
    (by decide) selected_cut_33145

theorem unmarked_context_10_6880_854127 : frontier 11 ⟨854127, by decide⟩
    (prefixCache 10 6880) (prefixPartial 10 6880) = false := by
  decide +kernel

theorem node_context_10_6880_854127 : EJMOriginalGlobalDAGData.nodes 11 ⟨854127, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨853923, by decide⟩,⟨854126, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6880_854127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6880 ⟨854127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6880
    ⟨854127, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨853923, by decide⟩,⟨854126, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6880_854127 node_context_10_6880_854127
  intro a
  fin_cases a
  · exact context_11_27520_434745
  · exact context_11_27521_853923
  · exact context_11_27522_854126
  · exact context_11_27523_789341

theorem selected_cut_33146 : selected 8 ⟨854163, by decide⟩
    (prefixPartial 13 440384) = some ⟨13, 2, 0, 854163, 440384, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_440384_854163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440384 ⟨854163, by decide⟩ :=
  accepted_of_selected 13 440384 ⟨854163, by decide⟩ ⟨13, 2, 0, 854163, 440384, 2149, 16384⟩
    (by decide) selected_cut_33146

theorem selected_cut_33147 : selected 8 ⟨854191, by decide⟩
    (prefixPartial 13 440385) = some ⟨13, 2, 0, 854191, 440385, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_440385_854191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440385 ⟨854191, by decide⟩ :=
  accepted_of_selected 13 440385 ⟨854191, by decide⟩ ⟨13, 2, 0, 854191, 440385, 2421, 16384⟩
    (by decide) selected_cut_33147

theorem selected_cut_33148 : selected 8 ⟨854208, by decide⟩
    (prefixPartial 13 440386) = some ⟨13, 2, 0, 854208, 440386, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_440386_854208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440386 ⟨854208, by decide⟩ :=
  accepted_of_selected 13 440386 ⟨854208, by decide⟩ ⟨13, 2, 0, 854208, 440386, 1465, 16384⟩
    (by decide) selected_cut_33148

theorem selected_cut_33149 : selected 8 ⟨854217, by decide⟩
    (prefixPartial 13 440387) = some ⟨13, 2, 0, 854217, 440387, 845, 16384⟩ := by
  decide +kernel

theorem context_13_440387_854217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440387 ⟨854217, by decide⟩ :=
  accepted_of_selected 13 440387 ⟨854217, by decide⟩ ⟨13, 2, 0, 854217, 440387, 845, 16384⟩
    (by decide) selected_cut_33149

theorem unmarked_context_12_110096_854218 : frontier 9 ⟨854218, by decide⟩
    (prefixCache 12 110096) (prefixPartial 12 110096) = false := by
  decide +kernel

theorem node_context_12_110096_854218 : EJMOriginalGlobalDAGData.nodes 9 ⟨854218, by decide⟩ =
    .split (coordinate 12) (![⟨854163, by decide⟩,⟨854191, by decide⟩,⟨854208, by decide⟩,⟨854217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110096_854218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110096 ⟨854218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110096
    ⟨854218, by decide⟩ (by decide) (![⟨854163, by decide⟩,⟨854191, by decide⟩,⟨854208, by decide⟩,⟨854217, by decide⟩]) unmarked_context_12_110096_854218 node_context_12_110096_854218
  intro a
  fin_cases a
  · exact context_13_440384_854163
  · exact context_13_440385_854191
  · exact context_13_440386_854208
  · exact context_13_440387_854217

theorem selected_cut_33150 : selected 8 ⟨854268, by decide⟩
    (prefixPartial 13 440388) = some ⟨13, 2, 0, 854268, 440388, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_440388_854268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440388 ⟨854268, by decide⟩ :=
  accepted_of_selected 13 440388 ⟨854268, by decide⟩ ⟨13, 2, 0, 854268, 440388, 2753, 16384⟩
    (by decide) selected_cut_33150

theorem selected_cut_33151 : selected 8 ⟨854313, by decide⟩
    (prefixPartial 13 440389) = some ⟨13, 2, 0, 854313, 440389, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_440389_854313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440389 ⟨854313, by decide⟩ :=
  accepted_of_selected 13 440389 ⟨854313, by decide⟩ ⟨13, 2, 0, 854313, 440389, 2785, 16384⟩
    (by decide) selected_cut_33151

theorem selected_cut_33152 : selected 8 ⟨854337, by decide⟩
    (prefixPartial 13 440390) = some ⟨13, 2, 0, 854337, 440390, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_440390_854337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440390 ⟨854337, by decide⟩ :=
  accepted_of_selected 13 440390 ⟨854337, by decide⟩ ⟨13, 2, 0, 854337, 440390, 1713, 16384⟩
    (by decide) selected_cut_33152

theorem selected_cut_33153 : selected 8 ⟨854347, by decide⟩
    (prefixPartial 13 440391) = some ⟨13, 2, 0, 854347, 440391, 953, 16384⟩ := by
  decide +kernel

theorem context_13_440391_854347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440391 ⟨854347, by decide⟩ :=
  accepted_of_selected 13 440391 ⟨854347, by decide⟩ ⟨13, 2, 0, 854347, 440391, 953, 16384⟩
    (by decide) selected_cut_33153

theorem unmarked_context_12_110097_854348 : frontier 9 ⟨854348, by decide⟩
    (prefixCache 12 110097) (prefixPartial 12 110097) = false := by
  decide +kernel

theorem node_context_12_110097_854348 : EJMOriginalGlobalDAGData.nodes 9 ⟨854348, by decide⟩ =
    .split (coordinate 12) (![⟨854268, by decide⟩,⟨854313, by decide⟩,⟨854337, by decide⟩,⟨854347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110097_854348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110097 ⟨854348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110097
    ⟨854348, by decide⟩ (by decide) (![⟨854268, by decide⟩,⟨854313, by decide⟩,⟨854337, by decide⟩,⟨854347, by decide⟩]) unmarked_context_12_110097_854348 node_context_12_110097_854348
  intro a
  fin_cases a
  · exact context_13_440388_854268
  · exact context_13_440389_854313
  · exact context_13_440390_854337
  · exact context_13_440391_854347

theorem selected_cut_33154 : selected 8 ⟨854376, by decide⟩
    (prefixPartial 13 440392) = some ⟨13, 2, 0, 854376, 440392, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_440392_854376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440392 ⟨854376, by decide⟩ :=
  accepted_of_selected 13 440392 ⟨854376, by decide⟩ ⟨13, 2, 0, 854376, 440392, 1733, 16384⟩
    (by decide) selected_cut_33154

theorem selected_cut_33155 : selected 8 ⟨854402, by decide⟩
    (prefixPartial 13 440393) = some ⟨13, 2, 0, 854402, 440393, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_440393_854402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440393 ⟨854402, by decide⟩ :=
  accepted_of_selected 13 440393 ⟨854402, by decide⟩ ⟨13, 2, 0, 854402, 440393, 2401, 16384⟩
    (by decide) selected_cut_33155

theorem selected_cut_33156 : selected 8 ⟨854419, by decide⟩
    (prefixPartial 13 440394) = some ⟨13, 2, 0, 854419, 440394, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_440394_854419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440394 ⟨854419, by decide⟩ :=
  accepted_of_selected 13 440394 ⟨854419, by decide⟩ ⟨13, 2, 0, 854419, 440394, 1101, 16384⟩
    (by decide) selected_cut_33156

theorem selected_cut_33157 : selected 8 ⟨854428, by decide⟩
    (prefixPartial 13 440395) = some ⟨13, 2, 0, 854428, 440395, 893, 16384⟩ := by
  decide +kernel

theorem context_13_440395_854428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440395 ⟨854428, by decide⟩ :=
  accepted_of_selected 13 440395 ⟨854428, by decide⟩ ⟨13, 2, 0, 854428, 440395, 893, 16384⟩
    (by decide) selected_cut_33157

theorem unmarked_context_12_110098_854429 : frontier 9 ⟨854429, by decide⟩
    (prefixCache 12 110098) (prefixPartial 12 110098) = false := by
  decide +kernel

theorem node_context_12_110098_854429 : EJMOriginalGlobalDAGData.nodes 9 ⟨854429, by decide⟩ =
    .split (coordinate 12) (![⟨854376, by decide⟩,⟨854402, by decide⟩,⟨854419, by decide⟩,⟨854428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110098_854429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110098 ⟨854429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110098
    ⟨854429, by decide⟩ (by decide) (![⟨854376, by decide⟩,⟨854402, by decide⟩,⟨854419, by decide⟩,⟨854428, by decide⟩]) unmarked_context_12_110098_854429 node_context_12_110098_854429
  intro a
  fin_cases a
  · exact context_13_440392_854376
  · exact context_13_440393_854402
  · exact context_13_440394_854419
  · exact context_13_440395_854428

theorem selected_cut_33158 : selected 8 ⟨854470, by decide⟩
    (prefixPartial 13 440396) = some ⟨13, 2, 0, 854470, 440396, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_440396_854470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440396 ⟨854470, by decide⟩ :=
  accepted_of_selected 13 440396 ⟨854470, by decide⟩ ⟨13, 2, 0, 854470, 440396, 2373, 16384⟩
    (by decide) selected_cut_33158

theorem selected_cut_33159 : selected 8 ⟨854511, by decide⟩
    (prefixPartial 13 440397) = some ⟨13, 2, 0, 854511, 440397, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_440397_854511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440397 ⟨854511, by decide⟩ :=
  accepted_of_selected 13 440397 ⟨854511, by decide⟩ ⟨13, 2, 0, 854511, 440397, 3161, 16384⟩
    (by decide) selected_cut_33159

theorem selected_cut_33160 : selected 8 ⟨854538, by decide⟩
    (prefixPartial 13 440398) = some ⟨13, 2, 0, 854538, 440398, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_440398_854538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440398 ⟨854538, by decide⟩ :=
  accepted_of_selected 13 440398 ⟨854538, by decide⟩ ⟨13, 2, 0, 854538, 440398, 1685, 16384⟩
    (by decide) selected_cut_33160

theorem selected_cut_33161 : selected 8 ⟨854544, by decide⟩
    (prefixPartial 13 440399) = some ⟨13, 2, 0, 854544, 440399, 925, 16384⟩ := by
  decide +kernel

theorem context_13_440399_854544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440399 ⟨854544, by decide⟩ :=
  accepted_of_selected 13 440399 ⟨854544, by decide⟩ ⟨13, 2, 0, 854544, 440399, 925, 16384⟩
    (by decide) selected_cut_33161

theorem unmarked_context_12_110099_854545 : frontier 9 ⟨854545, by decide⟩
    (prefixCache 12 110099) (prefixPartial 12 110099) = false := by
  decide +kernel

theorem node_context_12_110099_854545 : EJMOriginalGlobalDAGData.nodes 9 ⟨854545, by decide⟩ =
    .split (coordinate 12) (![⟨854470, by decide⟩,⟨854511, by decide⟩,⟨854538, by decide⟩,⟨854544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110099_854545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110099 ⟨854545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110099
    ⟨854545, by decide⟩ (by decide) (![⟨854470, by decide⟩,⟨854511, by decide⟩,⟨854538, by decide⟩,⟨854544, by decide⟩]) unmarked_context_12_110099_854545 node_context_12_110099_854545
  intro a
  fin_cases a
  · exact context_13_440396_854470
  · exact context_13_440397_854511
  · exact context_13_440398_854538
  · exact context_13_440399_854544

theorem unmarked_context_11_27524_854546 : frontier 10 ⟨854546, by decide⟩
    (prefixCache 11 27524) (prefixPartial 11 27524) = false := by
  decide +kernel

theorem node_context_11_27524_854546 : EJMOriginalGlobalDAGData.nodes 10 ⟨854546, by decide⟩ =
    .split (coordinate 11) (![⟨854218, by decide⟩,⟨854348, by decide⟩,⟨854429, by decide⟩,⟨854545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27524_854546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27524 ⟨854546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27524
    ⟨854546, by decide⟩ (by decide) (![⟨854218, by decide⟩,⟨854348, by decide⟩,⟨854429, by decide⟩,⟨854545, by decide⟩]) unmarked_context_11_27524_854546 node_context_11_27524_854546
  intro a
  fin_cases a
  · exact context_12_110096_854218
  · exact context_12_110097_854348
  · exact context_12_110098_854429
  · exact context_12_110099_854545

theorem selected_cut_33162 : selected 8 ⟨854582, by decide⟩
    (prefixPartial 13 440400) = some ⟨13, 2, 0, 854582, 440400, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_440400_854582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440400 ⟨854582, by decide⟩ :=
  accepted_of_selected 13 440400 ⟨854582, by decide⟩ ⟨13, 2, 0, 854582, 440400, 1913, 16384⟩
    (by decide) selected_cut_33162

theorem selected_cut_33163 : selected 8 ⟨854612, by decide⟩
    (prefixPartial 13 440401) = some ⟨13, 2, 0, 854612, 440401, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_440401_854612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440401 ⟨854612, by decide⟩ :=
  accepted_of_selected 13 440401 ⟨854612, by decide⟩ ⟨13, 2, 0, 854612, 440401, 2485, 16384⟩
    (by decide) selected_cut_33163

theorem selected_cut_33164 : selected 8 ⟨854642, by decide⟩
    (prefixPartial 13 440402) = some ⟨13, 2, 0, 854642, 440402, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_440402_854642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440402 ⟨854642, by decide⟩ :=
  accepted_of_selected 13 440402 ⟨854642, by decide⟩ ⟨13, 2, 0, 854642, 440402, 1489, 16384⟩
    (by decide) selected_cut_33164

theorem selected_cut_33165 : selected 8 ⟨854650, by decide⟩
    (prefixPartial 13 440403) = some ⟨13, 2, 0, 854650, 440403, 837, 16384⟩ := by
  decide +kernel

theorem context_13_440403_854650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440403 ⟨854650, by decide⟩ :=
  accepted_of_selected 13 440403 ⟨854650, by decide⟩ ⟨13, 2, 0, 854650, 440403, 837, 16384⟩
    (by decide) selected_cut_33165

theorem unmarked_context_12_110100_854651 : frontier 9 ⟨854651, by decide⟩
    (prefixCache 12 110100) (prefixPartial 12 110100) = false := by
  decide +kernel

theorem node_context_12_110100_854651 : EJMOriginalGlobalDAGData.nodes 9 ⟨854651, by decide⟩ =
    .split (coordinate 12) (![⟨854582, by decide⟩,⟨854612, by decide⟩,⟨854642, by decide⟩,⟨854650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110100_854651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110100 ⟨854651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110100
    ⟨854651, by decide⟩ (by decide) (![⟨854582, by decide⟩,⟨854612, by decide⟩,⟨854642, by decide⟩,⟨854650, by decide⟩]) unmarked_context_12_110100_854651 node_context_12_110100_854651
  intro a
  fin_cases a
  · exact context_13_440400_854582
  · exact context_13_440401_854612
  · exact context_13_440402_854642
  · exact context_13_440403_854650

theorem selected_cut_33166 : selected 8 ⟨854688, by decide⟩
    (prefixPartial 13 440404) = some ⟨13, 2, 0, 854688, 440404, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_440404_854688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440404 ⟨854688, by decide⟩ :=
  accepted_of_selected 13 440404 ⟨854688, by decide⟩ ⟨13, 2, 0, 854688, 440404, 2397, 16384⟩
    (by decide) selected_cut_33166

theorem selected_cut_33167 : selected 8 ⟨854714, by decide⟩
    (prefixPartial 13 440405) = some ⟨13, 2, 0, 854714, 440405, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_440405_854714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440405 ⟨854714, by decide⟩ :=
  accepted_of_selected 13 440405 ⟨854714, by decide⟩ ⟨13, 2, 0, 854714, 440405, 2501, 16384⟩
    (by decide) selected_cut_33167

theorem selected_cut_33168 : selected 8 ⟨854749, by decide⟩
    (prefixPartial 13 440406) = some ⟨13, 2, 0, 854749, 440406, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_440406_854749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440406 ⟨854749, by decide⟩ :=
  accepted_of_selected 13 440406 ⟨854749, by decide⟩ ⟨13, 2, 0, 854749, 440406, 1777, 16384⟩
    (by decide) selected_cut_33168

theorem selected_cut_33169 : selected 8 ⟨854758, by decide⟩
    (prefixPartial 13 440407) = some ⟨13, 2, 0, 854758, 440407, 889, 16384⟩ := by
  decide +kernel

theorem context_13_440407_854758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440407 ⟨854758, by decide⟩ :=
  accepted_of_selected 13 440407 ⟨854758, by decide⟩ ⟨13, 2, 0, 854758, 440407, 889, 16384⟩
    (by decide) selected_cut_33169

theorem unmarked_context_12_110101_854759 : frontier 9 ⟨854759, by decide⟩
    (prefixCache 12 110101) (prefixPartial 12 110101) = false := by
  decide +kernel

theorem node_context_12_110101_854759 : EJMOriginalGlobalDAGData.nodes 9 ⟨854759, by decide⟩ =
    .split (coordinate 12) (![⟨854688, by decide⟩,⟨854714, by decide⟩,⟨854749, by decide⟩,⟨854758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110101_854759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110101 ⟨854759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110101
    ⟨854759, by decide⟩ (by decide) (![⟨854688, by decide⟩,⟨854714, by decide⟩,⟨854749, by decide⟩,⟨854758, by decide⟩]) unmarked_context_12_110101_854759 node_context_12_110101_854759
  intro a
  fin_cases a
  · exact context_13_440404_854688
  · exact context_13_440405_854714
  · exact context_13_440406_854749
  · exact context_13_440407_854758

theorem selected_cut_33170 : selected 8 ⟨854780, by decide⟩
    (prefixPartial 13 440408) = some ⟨13, 2, 0, 854780, 440408, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_440408_854780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440408 ⟨854780, by decide⟩ :=
  accepted_of_selected 13 440408 ⟨854780, by decide⟩ ⟨13, 2, 0, 854780, 440408, 1469, 16384⟩
    (by decide) selected_cut_33170

theorem selected_cut_33171 : selected 8 ⟨854806, by decide⟩
    (prefixPartial 13 440409) = some ⟨13, 2, 0, 854806, 440409, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_440409_854806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440409 ⟨854806, by decide⟩ :=
  accepted_of_selected 13 440409 ⟨854806, by decide⟩ ⟨13, 2, 0, 854806, 440409, 2293, 16384⟩
    (by decide) selected_cut_33171

theorem selected_cut_33172 : selected 8 ⟨854825, by decide⟩
    (prefixPartial 13 440410) = some ⟨13, 2, 0, 854825, 440410, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_440410_854825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440410 ⟨854825, by decide⟩ :=
  accepted_of_selected 13 440410 ⟨854825, by decide⟩ ⟨13, 2, 0, 854825, 440410, 1241, 16384⟩
    (by decide) selected_cut_33172

theorem selected_cut_33173 : selected 8 ⟨854834, by decide⟩
    (prefixPartial 13 440411) = some ⟨13, 2, 0, 854834, 440411, 829, 16384⟩ := by
  decide +kernel

theorem context_13_440411_854834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440411 ⟨854834, by decide⟩ :=
  accepted_of_selected 13 440411 ⟨854834, by decide⟩ ⟨13, 2, 0, 854834, 440411, 829, 16384⟩
    (by decide) selected_cut_33173

theorem unmarked_context_12_110102_854835 : frontier 9 ⟨854835, by decide⟩
    (prefixCache 12 110102) (prefixPartial 12 110102) = false := by
  decide +kernel

theorem node_context_12_110102_854835 : EJMOriginalGlobalDAGData.nodes 9 ⟨854835, by decide⟩ =
    .split (coordinate 12) (![⟨854780, by decide⟩,⟨854806, by decide⟩,⟨854825, by decide⟩,⟨854834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110102_854835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110102 ⟨854835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110102
    ⟨854835, by decide⟩ (by decide) (![⟨854780, by decide⟩,⟨854806, by decide⟩,⟨854825, by decide⟩,⟨854834, by decide⟩]) unmarked_context_12_110102_854835 node_context_12_110102_854835
  intro a
  fin_cases a
  · exact context_13_440408_854780
  · exact context_13_440409_854806
  · exact context_13_440410_854825
  · exact context_13_440411_854834

theorem selected_cut_33174 : selected 8 ⟨854871, by decide⟩
    (prefixPartial 13 440412) = some ⟨13, 2, 0, 854871, 440412, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_440412_854871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440412 ⟨854871, by decide⟩ :=
  accepted_of_selected 13 440412 ⟨854871, by decide⟩ ⟨13, 2, 0, 854871, 440412, 2213, 16384⟩
    (by decide) selected_cut_33174

theorem selected_cut_33175 : selected 8 ⟨854906, by decide⟩
    (prefixPartial 13 440413) = some ⟨13, 2, 0, 854906, 440413, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_440413_854906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440413 ⟨854906, by decide⟩ :=
  accepted_of_selected 13 440413 ⟨854906, by decide⟩ ⟨13, 2, 0, 854906, 440413, 2881, 16384⟩
    (by decide) selected_cut_33175

theorem selected_cut_33176 : selected 8 ⟨854944, by decide⟩
    (prefixPartial 13 440414) = some ⟨13, 2, 0, 854944, 440414, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_440414_854944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440414 ⟨854944, by decide⟩ :=
  accepted_of_selected 13 440414 ⟨854944, by decide⟩ ⟨13, 2, 0, 854944, 440414, 1881, 16384⟩
    (by decide) selected_cut_33176

theorem selected_cut_33177 : selected 8 ⟨854954, by decide⟩
    (prefixPartial 13 440415) = some ⟨13, 2, 0, 854954, 440415, 889, 16384⟩ := by
  decide +kernel

theorem context_13_440415_854954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440415 ⟨854954, by decide⟩ :=
  accepted_of_selected 13 440415 ⟨854954, by decide⟩ ⟨13, 2, 0, 854954, 440415, 889, 16384⟩
    (by decide) selected_cut_33177

theorem unmarked_context_12_110103_854955 : frontier 9 ⟨854955, by decide⟩
    (prefixCache 12 110103) (prefixPartial 12 110103) = false := by
  decide +kernel

theorem node_context_12_110103_854955 : EJMOriginalGlobalDAGData.nodes 9 ⟨854955, by decide⟩ =
    .split (coordinate 12) (![⟨854871, by decide⟩,⟨854906, by decide⟩,⟨854944, by decide⟩,⟨854954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110103_854955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110103 ⟨854955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110103
    ⟨854955, by decide⟩ (by decide) (![⟨854871, by decide⟩,⟨854906, by decide⟩,⟨854944, by decide⟩,⟨854954, by decide⟩]) unmarked_context_12_110103_854955 node_context_12_110103_854955
  intro a
  fin_cases a
  · exact context_13_440412_854871
  · exact context_13_440413_854906
  · exact context_13_440414_854944
  · exact context_13_440415_854954

theorem unmarked_context_11_27525_854956 : frontier 10 ⟨854956, by decide⟩
    (prefixCache 11 27525) (prefixPartial 11 27525) = false := by
  decide +kernel

theorem node_context_11_27525_854956 : EJMOriginalGlobalDAGData.nodes 10 ⟨854956, by decide⟩ =
    .split (coordinate 11) (![⟨854651, by decide⟩,⟨854759, by decide⟩,⟨854835, by decide⟩,⟨854955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27525_854956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27525 ⟨854956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27525
    ⟨854956, by decide⟩ (by decide) (![⟨854651, by decide⟩,⟨854759, by decide⟩,⟨854835, by decide⟩,⟨854955, by decide⟩]) unmarked_context_11_27525_854956 node_context_11_27525_854956
  intro a
  fin_cases a
  · exact context_12_110100_854651
  · exact context_12_110101_854759
  · exact context_12_110102_854835
  · exact context_12_110103_854955

theorem selected_cut_33178 : selected 8 ⟨854982, by decide⟩
    (prefixPartial 13 440416) = some ⟨13, 2, 0, 854982, 440416, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_440416_854982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440416 ⟨854982, by decide⟩ :=
  accepted_of_selected 13 440416 ⟨854982, by decide⟩ ⟨13, 2, 0, 854982, 440416, 1485, 16384⟩
    (by decide) selected_cut_33178

theorem selected_cut_33179 : selected 8 ⟨855005, by decide⟩
    (prefixPartial 13 440417) = some ⟨13, 2, 0, 855005, 440417, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_440417_855005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440417 ⟨855005, by decide⟩ :=
  accepted_of_selected 13 440417 ⟨855005, by decide⟩ ⟨13, 2, 0, 855005, 440417, 2133, 16384⟩
    (by decide) selected_cut_33179

theorem selected_cut_33180 : selected 8 ⟨855025, by decide⟩
    (prefixPartial 13 440418) = some ⟨13, 2, 0, 855025, 440418, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_440418_855025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440418 ⟨855025, by decide⟩ :=
  accepted_of_selected 13 440418 ⟨855025, by decide⟩ ⟨13, 2, 0, 855025, 440418, 1469, 16384⟩
    (by decide) selected_cut_33180

theorem selected_cut_33181 : selected 8 ⟨855033, by decide⟩
    (prefixPartial 13 440419) = some ⟨13, 2, 0, 855033, 440419, 641, 16384⟩ := by
  decide +kernel

theorem context_13_440419_855033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440419 ⟨855033, by decide⟩ :=
  accepted_of_selected 13 440419 ⟨855033, by decide⟩ ⟨13, 2, 0, 855033, 440419, 641, 16384⟩
    (by decide) selected_cut_33181

theorem unmarked_context_12_110104_855034 : frontier 9 ⟨855034, by decide⟩
    (prefixCache 12 110104) (prefixPartial 12 110104) = false := by
  decide +kernel

theorem node_context_12_110104_855034 : EJMOriginalGlobalDAGData.nodes 9 ⟨855034, by decide⟩ =
    .split (coordinate 12) (![⟨854982, by decide⟩,⟨855005, by decide⟩,⟨855025, by decide⟩,⟨855033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110104_855034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110104 ⟨855034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110104
    ⟨855034, by decide⟩ (by decide) (![⟨854982, by decide⟩,⟨855005, by decide⟩,⟨855025, by decide⟩,⟨855033, by decide⟩]) unmarked_context_12_110104_855034 node_context_12_110104_855034
  intro a
  fin_cases a
  · exact context_13_440416_854982
  · exact context_13_440417_855005
  · exact context_13_440418_855025
  · exact context_13_440419_855033

theorem selected_cut_33182 : selected 8 ⟨855066, by decide⟩
    (prefixPartial 13 440420) = some ⟨13, 2, 0, 855066, 440420, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_440420_855066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440420 ⟨855066, by decide⟩ :=
  accepted_of_selected 13 440420 ⟨855066, by decide⟩ ⟨13, 2, 0, 855066, 440420, 1981, 16384⟩
    (by decide) selected_cut_33182

theorem selected_cut_33183 : selected 8 ⟨855098, by decide⟩
    (prefixPartial 13 440421) = some ⟨13, 2, 0, 855098, 440421, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_440421_855098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440421 ⟨855098, by decide⟩ :=
  accepted_of_selected 13 440421 ⟨855098, by decide⟩ ⟨13, 2, 0, 855098, 440421, 2217, 16384⟩
    (by decide) selected_cut_33183

theorem selected_cut_33184 : selected 8 ⟨855123, by decide⟩
    (prefixPartial 13 440422) = some ⟨13, 2, 0, 855123, 440422, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_440422_855123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440422 ⟨855123, by decide⟩ :=
  accepted_of_selected 13 440422 ⟨855123, by decide⟩ ⟨13, 2, 0, 855123, 440422, 1713, 16384⟩
    (by decide) selected_cut_33184

theorem selected_cut_33185 : selected 8 ⟨855131, by decide⟩
    (prefixPartial 13 440423) = some ⟨13, 2, 0, 855131, 440423, 725, 16384⟩ := by
  decide +kernel

theorem context_13_440423_855131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440423 ⟨855131, by decide⟩ :=
  accepted_of_selected 13 440423 ⟨855131, by decide⟩ ⟨13, 2, 0, 855131, 440423, 725, 16384⟩
    (by decide) selected_cut_33185

theorem unmarked_context_12_110105_855132 : frontier 9 ⟨855132, by decide⟩
    (prefixCache 12 110105) (prefixPartial 12 110105) = false := by
  decide +kernel

theorem node_context_12_110105_855132 : EJMOriginalGlobalDAGData.nodes 9 ⟨855132, by decide⟩ =
    .split (coordinate 12) (![⟨855066, by decide⟩,⟨855098, by decide⟩,⟨855123, by decide⟩,⟨855131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110105_855132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110105 ⟨855132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110105
    ⟨855132, by decide⟩ (by decide) (![⟨855066, by decide⟩,⟨855098, by decide⟩,⟨855123, by decide⟩,⟨855131, by decide⟩]) unmarked_context_12_110105_855132 node_context_12_110105_855132
  intro a
  fin_cases a
  · exact context_13_440420_855066
  · exact context_13_440421_855098
  · exact context_13_440422_855123
  · exact context_13_440423_855131

theorem selected_cut_33186 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 110106) = some ⟨12, 1, 0, 806997, 110106, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110106_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110106 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 110106 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 110106, 1, 65536⟩
    (by decide) selected_cut_33186

theorem selected_cut_33187 : selected 8 ⟨855166, by decide⟩
    (prefixPartial 13 440428) = some ⟨13, 2, 0, 855166, 440428, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_440428_855166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440428 ⟨855166, by decide⟩ :=
  accepted_of_selected 13 440428 ⟨855166, by decide⟩ ⟨13, 2, 0, 855166, 440428, 1701, 16384⟩
    (by decide) selected_cut_33187

theorem selected_cut_33188 : selected 8 ⟨855203, by decide⟩
    (prefixPartial 13 440429) = some ⟨13, 2, 0, 855203, 440429, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_440429_855203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440429 ⟨855203, by decide⟩ :=
  accepted_of_selected 13 440429 ⟨855203, by decide⟩ ⟨13, 2, 0, 855203, 440429, 2657, 16384⟩
    (by decide) selected_cut_33188

theorem selected_cut_33189 : selected 8 ⟨855222, by decide⟩
    (prefixPartial 13 440430) = some ⟨13, 2, 0, 855222, 440430, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_440430_855222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440430 ⟨855222, by decide⟩ :=
  accepted_of_selected 13 440430 ⟨855222, by decide⟩ ⟨13, 2, 0, 855222, 440430, 1573, 16384⟩
    (by decide) selected_cut_33189

theorem selected_cut_33190 : selected 8 ⟨855226, by decide⟩
    (prefixPartial 13 440431) = some ⟨13, 2, 0, 855226, 440431, 601, 16384⟩ := by
  decide +kernel

theorem context_13_440431_855226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440431 ⟨855226, by decide⟩ :=
  accepted_of_selected 13 440431 ⟨855226, by decide⟩ ⟨13, 2, 0, 855226, 440431, 601, 16384⟩
    (by decide) selected_cut_33190

theorem unmarked_context_12_110107_855227 : frontier 9 ⟨855227, by decide⟩
    (prefixCache 12 110107) (prefixPartial 12 110107) = false := by
  decide +kernel

theorem node_context_12_110107_855227 : EJMOriginalGlobalDAGData.nodes 9 ⟨855227, by decide⟩ =
    .split (coordinate 12) (![⟨855166, by decide⟩,⟨855203, by decide⟩,⟨855222, by decide⟩,⟨855226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110107_855227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110107 ⟨855227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110107
    ⟨855227, by decide⟩ (by decide) (![⟨855166, by decide⟩,⟨855203, by decide⟩,⟨855222, by decide⟩,⟨855226, by decide⟩]) unmarked_context_12_110107_855227 node_context_12_110107_855227
  intro a
  fin_cases a
  · exact context_13_440428_855166
  · exact context_13_440429_855203
  · exact context_13_440430_855222
  · exact context_13_440431_855226

theorem unmarked_context_11_27526_855228 : frontier 10 ⟨855228, by decide⟩
    (prefixCache 11 27526) (prefixPartial 11 27526) = false := by
  decide +kernel

theorem node_context_11_27526_855228 : EJMOriginalGlobalDAGData.nodes 10 ⟨855228, by decide⟩ =
    .split (coordinate 11) (![⟨855034, by decide⟩,⟨855132, by decide⟩,⟨806997, by decide⟩,⟨855227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27526_855228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27526 ⟨855228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27526
    ⟨855228, by decide⟩ (by decide) (![⟨855034, by decide⟩,⟨855132, by decide⟩,⟨806997, by decide⟩,⟨855227, by decide⟩]) unmarked_context_11_27526_855228 node_context_11_27526_855228
  intro a
  fin_cases a
  · exact context_12_110104_855034
  · exact context_12_110105_855132
  · exact context_12_110106_806997
  · exact context_12_110107_855227

theorem selected_cut_33191 : selected 8 ⟨855249, by decide⟩
    (prefixPartial 13 440432) = some ⟨13, 2, 0, 855249, 440432, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_440432_855249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440432 ⟨855249, by decide⟩ :=
  accepted_of_selected 13 440432 ⟨855249, by decide⟩ ⟨13, 2, 0, 855249, 440432, 1473, 16384⟩
    (by decide) selected_cut_33191

theorem selected_cut_33192 : selected 8 ⟨855277, by decide⟩
    (prefixPartial 13 440433) = some ⟨13, 2, 0, 855277, 440433, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_440433_855277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440433 ⟨855277, by decide⟩ :=
  accepted_of_selected 13 440433 ⟨855277, by decide⟩ ⟨13, 2, 0, 855277, 440433, 2433, 16384⟩
    (by decide) selected_cut_33192

theorem selected_cut_33193 : selected 8 ⟨855300, by decide⟩
    (prefixPartial 13 440434) = some ⟨13, 2, 0, 855300, 440434, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_440434_855300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440434 ⟨855300, by decide⟩ :=
  accepted_of_selected 13 440434 ⟨855300, by decide⟩ ⟨13, 2, 0, 855300, 440434, 1505, 16384⟩
    (by decide) selected_cut_33193

theorem selected_cut_33194 : selected 8 ⟨855307, by decide⟩
    (prefixPartial 13 440435) = some ⟨13, 2, 0, 855307, 440435, 877, 16384⟩ := by
  decide +kernel

theorem context_13_440435_855307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440435 ⟨855307, by decide⟩ :=
  accepted_of_selected 13 440435 ⟨855307, by decide⟩ ⟨13, 2, 0, 855307, 440435, 877, 16384⟩
    (by decide) selected_cut_33194

theorem unmarked_context_12_110108_855308 : frontier 9 ⟨855308, by decide⟩
    (prefixCache 12 110108) (prefixPartial 12 110108) = false := by
  decide +kernel

theorem node_context_12_110108_855308 : EJMOriginalGlobalDAGData.nodes 9 ⟨855308, by decide⟩ =
    .split (coordinate 12) (![⟨855249, by decide⟩,⟨855277, by decide⟩,⟨855300, by decide⟩,⟨855307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110108_855308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110108 ⟨855308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110108
    ⟨855308, by decide⟩ (by decide) (![⟨855249, by decide⟩,⟨855277, by decide⟩,⟨855300, by decide⟩,⟨855307, by decide⟩]) unmarked_context_12_110108_855308 node_context_12_110108_855308
  intro a
  fin_cases a
  · exact context_13_440432_855249
  · exact context_13_440433_855277
  · exact context_13_440434_855300
  · exact context_13_440435_855307

theorem selected_cut_33195 : selected 8 ⟨855342, by decide⟩
    (prefixPartial 13 440436) = some ⟨13, 2, 0, 855342, 440436, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_440436_855342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440436 ⟨855342, by decide⟩ :=
  accepted_of_selected 13 440436 ⟨855342, by decide⟩ ⟨13, 2, 0, 855342, 440436, 1905, 16384⟩
    (by decide) selected_cut_33195

theorem selected_cut_33196 : selected 8 ⟨855383, by decide⟩
    (prefixPartial 13 440437) = some ⟨13, 2, 0, 855383, 440437, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_440437_855383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440437 ⟨855383, by decide⟩ :=
  accepted_of_selected 13 440437 ⟨855383, by decide⟩ ⟨13, 2, 0, 855383, 440437, 2721, 16384⟩
    (by decide) selected_cut_33196

theorem selected_cut_33197 : selected 8 ⟨855421, by decide⟩
    (prefixPartial 13 440438) = some ⟨13, 2, 0, 855421, 440438, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_440438_855421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440438 ⟨855421, by decide⟩ :=
  accepted_of_selected 13 440438 ⟨855421, by decide⟩ ⟨13, 2, 0, 855421, 440438, 1789, 16384⟩
    (by decide) selected_cut_33197

theorem selected_cut_33198 : selected 8 ⟨855433, by decide⟩
    (prefixPartial 13 440439) = some ⟨13, 2, 0, 855433, 440439, 977, 16384⟩ := by
  decide +kernel

theorem context_13_440439_855433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440439 ⟨855433, by decide⟩ :=
  accepted_of_selected 13 440439 ⟨855433, by decide⟩ ⟨13, 2, 0, 855433, 440439, 977, 16384⟩
    (by decide) selected_cut_33198

theorem unmarked_context_12_110109_855434 : frontier 9 ⟨855434, by decide⟩
    (prefixCache 12 110109) (prefixPartial 12 110109) = false := by
  decide +kernel

theorem node_context_12_110109_855434 : EJMOriginalGlobalDAGData.nodes 9 ⟨855434, by decide⟩ =
    .split (coordinate 12) (![⟨855342, by decide⟩,⟨855383, by decide⟩,⟨855421, by decide⟩,⟨855433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110109_855434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110109 ⟨855434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110109
    ⟨855434, by decide⟩ (by decide) (![⟨855342, by decide⟩,⟨855383, by decide⟩,⟨855421, by decide⟩,⟨855433, by decide⟩]) unmarked_context_12_110109_855434 node_context_12_110109_855434
  intro a
  fin_cases a
  · exact context_13_440436_855342
  · exact context_13_440437_855383
  · exact context_13_440438_855421
  · exact context_13_440439_855433

theorem selected_cut_33199 : selected 8 ⟨855450, by decide⟩
    (prefixPartial 13 440440) = some ⟨13, 2, 0, 855450, 440440, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_440440_855450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440440 ⟨855450, by decide⟩ :=
  accepted_of_selected 13 440440 ⟨855450, by decide⟩ ⟨13, 2, 0, 855450, 440440, 1149, 16384⟩
    (by decide) selected_cut_33199

theorem selected_cut_33200 : selected 8 ⟨855478, by decide⟩
    (prefixPartial 13 440441) = some ⟨13, 2, 0, 855478, 440441, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_440441_855478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440441 ⟨855478, by decide⟩ :=
  accepted_of_selected 13 440441 ⟨855478, by decide⟩ ⟨13, 2, 0, 855478, 440441, 2369, 16384⟩
    (by decide) selected_cut_33200

theorem selected_cut_33201 : selected 8 ⟨855497, by decide⟩
    (prefixPartial 13 440442) = some ⟨13, 2, 0, 855497, 440442, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_440442_855497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440442 ⟨855497, by decide⟩ :=
  accepted_of_selected 13 440442 ⟨855497, by decide⟩ ⟨13, 2, 0, 855497, 440442, 1209, 16384⟩
    (by decide) selected_cut_33201

theorem selected_cut_33202 : selected 8 ⟨855504, by decide⟩
    (prefixPartial 13 440443) = some ⟨13, 2, 0, 855504, 440443, 885, 16384⟩ := by
  decide +kernel

theorem context_13_440443_855504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440443 ⟨855504, by decide⟩ :=
  accepted_of_selected 13 440443 ⟨855504, by decide⟩ ⟨13, 2, 0, 855504, 440443, 885, 16384⟩
    (by decide) selected_cut_33202

theorem unmarked_context_12_110110_855505 : frontier 9 ⟨855505, by decide⟩
    (prefixCache 12 110110) (prefixPartial 12 110110) = false := by
  decide +kernel

theorem node_context_12_110110_855505 : EJMOriginalGlobalDAGData.nodes 9 ⟨855505, by decide⟩ =
    .split (coordinate 12) (![⟨855450, by decide⟩,⟨855478, by decide⟩,⟨855497, by decide⟩,⟨855504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110110_855505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110110 ⟨855505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110110
    ⟨855505, by decide⟩ (by decide) (![⟨855450, by decide⟩,⟨855478, by decide⟩,⟨855497, by decide⟩,⟨855504, by decide⟩]) unmarked_context_12_110110_855505 node_context_12_110110_855505
  intro a
  fin_cases a
  · exact context_13_440440_855450
  · exact context_13_440441_855478
  · exact context_13_440442_855497
  · exact context_13_440443_855504

theorem selected_cut_33203 : selected 8 ⟨855532, by decide⟩
    (prefixPartial 13 440444) = some ⟨13, 2, 0, 855532, 440444, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_440444_855532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440444 ⟨855532, by decide⟩ :=
  accepted_of_selected 13 440444 ⟨855532, by decide⟩ ⟨13, 2, 0, 855532, 440444, 1577, 16384⟩
    (by decide) selected_cut_33203

theorem selected_cut_33204 : selected 8 ⟨855569, by decide⟩
    (prefixPartial 13 440445) = some ⟨13, 2, 0, 855569, 440445, 2845, 16384⟩ := by
  decide +kernel

theorem context_13_440445_855569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440445 ⟨855569, by decide⟩ :=
  accepted_of_selected 13 440445 ⟨855569, by decide⟩ ⟨13, 2, 0, 855569, 440445, 2845, 16384⟩
    (by decide) selected_cut_33204

theorem selected_cut_33205 : selected 8 ⟨855588, by decide⟩
    (prefixPartial 13 440446) = some ⟨13, 2, 0, 855588, 440446, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_440446_855588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440446 ⟨855588, by decide⟩ :=
  accepted_of_selected 13 440446 ⟨855588, by decide⟩ ⟨13, 2, 0, 855588, 440446, 1645, 16384⟩
    (by decide) selected_cut_33205

theorem selected_cut_33206 : selected 8 ⟨855596, by decide⟩
    (prefixPartial 13 440447) = some ⟨13, 2, 0, 855596, 440447, 937, 16384⟩ := by
  decide +kernel

theorem context_13_440447_855596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440447 ⟨855596, by decide⟩ :=
  accepted_of_selected 13 440447 ⟨855596, by decide⟩ ⟨13, 2, 0, 855596, 440447, 937, 16384⟩
    (by decide) selected_cut_33206

theorem unmarked_context_12_110111_855597 : frontier 9 ⟨855597, by decide⟩
    (prefixCache 12 110111) (prefixPartial 12 110111) = false := by
  decide +kernel

theorem node_context_12_110111_855597 : EJMOriginalGlobalDAGData.nodes 9 ⟨855597, by decide⟩ =
    .split (coordinate 12) (![⟨855532, by decide⟩,⟨855569, by decide⟩,⟨855588, by decide⟩,⟨855596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110111_855597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110111 ⟨855597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110111
    ⟨855597, by decide⟩ (by decide) (![⟨855532, by decide⟩,⟨855569, by decide⟩,⟨855588, by decide⟩,⟨855596, by decide⟩]) unmarked_context_12_110111_855597 node_context_12_110111_855597
  intro a
  fin_cases a
  · exact context_13_440444_855532
  · exact context_13_440445_855569
  · exact context_13_440446_855588
  · exact context_13_440447_855596

theorem unmarked_context_11_27527_855598 : frontier 10 ⟨855598, by decide⟩
    (prefixCache 11 27527) (prefixPartial 11 27527) = false := by
  decide +kernel

theorem node_context_11_27527_855598 : EJMOriginalGlobalDAGData.nodes 10 ⟨855598, by decide⟩ =
    .split (coordinate 11) (![⟨855308, by decide⟩,⟨855434, by decide⟩,⟨855505, by decide⟩,⟨855597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27527_855598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27527 ⟨855598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27527
    ⟨855598, by decide⟩ (by decide) (![⟨855308, by decide⟩,⟨855434, by decide⟩,⟨855505, by decide⟩,⟨855597, by decide⟩]) unmarked_context_11_27527_855598 node_context_11_27527_855598
  intro a
  fin_cases a
  · exact context_12_110108_855308
  · exact context_12_110109_855434
  · exact context_12_110110_855505
  · exact context_12_110111_855597

theorem unmarked_context_10_6881_855599 : frontier 11 ⟨855599, by decide⟩
    (prefixCache 10 6881) (prefixPartial 10 6881) = false := by
  decide +kernel

theorem node_context_10_6881_855599 : EJMOriginalGlobalDAGData.nodes 11 ⟨855599, by decide⟩ =
    .split (coordinate 10) (![⟨854546, by decide⟩,⟨854956, by decide⟩,⟨855228, by decide⟩,⟨855598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6881_855599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6881 ⟨855599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6881
    ⟨855599, by decide⟩ (by decide) (![⟨854546, by decide⟩,⟨854956, by decide⟩,⟨855228, by decide⟩,⟨855598, by decide⟩]) unmarked_context_10_6881_855599 node_context_10_6881_855599
  intro a
  fin_cases a
  · exact context_11_27524_854546
  · exact context_11_27525_854956
  · exact context_11_27526_855228
  · exact context_11_27527_855598

theorem selected_cut_33207 : selected 8 ⟨855618, by decide⟩
    (prefixPartial 13 440448) = some ⟨13, 2, 0, 855618, 440448, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_440448_855618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440448 ⟨855618, by decide⟩ :=
  accepted_of_selected 13 440448 ⟨855618, by decide⟩ ⟨13, 2, 0, 855618, 440448, 1257, 16384⟩
    (by decide) selected_cut_33207

theorem selected_cut_33208 : selected 8 ⟨855643, by decide⟩
    (prefixPartial 13 440449) = some ⟨13, 2, 0, 855643, 440449, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_440449_855643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440449 ⟨855643, by decide⟩ :=
  accepted_of_selected 13 440449 ⟨855643, by decide⟩ ⟨13, 2, 0, 855643, 440449, 2101, 16384⟩
    (by decide) selected_cut_33208

theorem selected_cut_33209 : selected 8 ⟨855663, by decide⟩
    (prefixPartial 13 440450) = some ⟨13, 2, 0, 855663, 440450, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_440450_855663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440450 ⟨855663, by decide⟩ :=
  accepted_of_selected 13 440450 ⟨855663, by decide⟩ ⟨13, 2, 0, 855663, 440450, 1301, 16384⟩
    (by decide) selected_cut_33209

theorem selected_cut_33210 : selected 8 ⟨855669, by decide⟩
    (prefixPartial 13 440451) = some ⟨13, 2, 0, 855669, 440451, 593, 16384⟩ := by
  decide +kernel

theorem context_13_440451_855669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440451 ⟨855669, by decide⟩ :=
  accepted_of_selected 13 440451 ⟨855669, by decide⟩ ⟨13, 2, 0, 855669, 440451, 593, 16384⟩
    (by decide) selected_cut_33210

theorem unmarked_context_12_110112_855670 : frontier 9 ⟨855670, by decide⟩
    (prefixCache 12 110112) (prefixPartial 12 110112) = false := by
  decide +kernel

theorem node_context_12_110112_855670 : EJMOriginalGlobalDAGData.nodes 9 ⟨855670, by decide⟩ =
    .split (coordinate 12) (![⟨855618, by decide⟩,⟨855643, by decide⟩,⟨855663, by decide⟩,⟨855669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110112_855670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110112 ⟨855670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110112
    ⟨855670, by decide⟩ (by decide) (![⟨855618, by decide⟩,⟨855643, by decide⟩,⟨855663, by decide⟩,⟨855669, by decide⟩]) unmarked_context_12_110112_855670 node_context_12_110112_855670
  intro a
  fin_cases a
  · exact context_13_440448_855618
  · exact context_13_440449_855643
  · exact context_13_440450_855663
  · exact context_13_440451_855669

theorem selected_cut_33211 : selected 8 ⟨855697, by decide⟩
    (prefixPartial 13 440452) = some ⟨13, 2, 0, 855697, 440452, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_440452_855697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440452 ⟨855697, by decide⟩ :=
  accepted_of_selected 13 440452 ⟨855697, by decide⟩ ⟨13, 2, 0, 855697, 440452, 1361, 16384⟩
    (by decide) selected_cut_33211

theorem selected_cut_33212 : selected 8 ⟨855735, by decide⟩
    (prefixPartial 13 440453) = some ⟨13, 2, 0, 855735, 440453, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_440453_855735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440453 ⟨855735, by decide⟩ :=
  accepted_of_selected 13 440453 ⟨855735, by decide⟩ ⟨13, 2, 0, 855735, 440453, 2509, 16384⟩
    (by decide) selected_cut_33212

theorem selected_cut_33213 : selected 8 ⟨855771, by decide⟩
    (prefixPartial 13 440454) = some ⟨13, 2, 0, 855771, 440454, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_440454_855771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440454 ⟨855771, by decide⟩ :=
  accepted_of_selected 13 440454 ⟨855771, by decide⟩ ⟨13, 2, 0, 855771, 440454, 1517, 16384⟩
    (by decide) selected_cut_33213

theorem selected_cut_33214 : selected 8 ⟨855777, by decide⟩
    (prefixPartial 13 440455) = some ⟨13, 2, 0, 855777, 440455, 613, 16384⟩ := by
  decide +kernel

theorem context_13_440455_855777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440455 ⟨855777, by decide⟩ :=
  accepted_of_selected 13 440455 ⟨855777, by decide⟩ ⟨13, 2, 0, 855777, 440455, 613, 16384⟩
    (by decide) selected_cut_33214

theorem unmarked_context_12_110113_855778 : frontier 9 ⟨855778, by decide⟩
    (prefixCache 12 110113) (prefixPartial 12 110113) = false := by
  decide +kernel

theorem node_context_12_110113_855778 : EJMOriginalGlobalDAGData.nodes 9 ⟨855778, by decide⟩ =
    .split (coordinate 12) (![⟨855697, by decide⟩,⟨855735, by decide⟩,⟨855771, by decide⟩,⟨855777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110113_855778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110113 ⟨855778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110113
    ⟨855778, by decide⟩ (by decide) (![⟨855697, by decide⟩,⟨855735, by decide⟩,⟨855771, by decide⟩,⟨855777, by decide⟩]) unmarked_context_12_110113_855778 node_context_12_110113_855778
  intro a
  fin_cases a
  · exact context_13_440452_855697
  · exact context_13_440453_855735
  · exact context_13_440454_855771
  · exact context_13_440455_855777

theorem selected_cut_33215 : selected 8 ⟨855792, by decide⟩
    (prefixPartial 13 440456) = some ⟨13, 2, 0, 855792, 440456, 933, 16384⟩ := by
  decide +kernel

theorem context_13_440456_855792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440456 ⟨855792, by decide⟩ :=
  accepted_of_selected 13 440456 ⟨855792, by decide⟩ ⟨13, 2, 0, 855792, 440456, 933, 16384⟩
    (by decide) selected_cut_33215

theorem selected_cut_33216 : selected 8 ⟨855815, by decide⟩
    (prefixPartial 13 440457) = some ⟨13, 2, 0, 855815, 440457, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_440457_855815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440457 ⟨855815, by decide⟩ :=
  accepted_of_selected 13 440457 ⟨855815, by decide⟩ ⟨13, 2, 0, 855815, 440457, 1917, 16384⟩
    (by decide) selected_cut_33216

theorem selected_cut_33217 : selected 8 ⟨855830, by decide⟩
    (prefixPartial 13 440458) = some ⟨13, 2, 0, 855830, 440458, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_440458_855830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440458 ⟨855830, by decide⟩ :=
  accepted_of_selected 13 440458 ⟨855830, by decide⟩ ⟨13, 2, 0, 855830, 440458, 1029, 16384⟩
    (by decide) selected_cut_33217

theorem selected_cut_33218 : selected 8 ⟨855839, by decide⟩
    (prefixPartial 13 440459) = some ⟨13, 2, 0, 855839, 440459, 597, 16384⟩ := by
  decide +kernel

theorem context_13_440459_855839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440459 ⟨855839, by decide⟩ :=
  accepted_of_selected 13 440459 ⟨855839, by decide⟩ ⟨13, 2, 0, 855839, 440459, 597, 16384⟩
    (by decide) selected_cut_33218

theorem unmarked_context_12_110114_855840 : frontier 9 ⟨855840, by decide⟩
    (prefixCache 12 110114) (prefixPartial 12 110114) = false := by
  decide +kernel

theorem node_context_12_110114_855840 : EJMOriginalGlobalDAGData.nodes 9 ⟨855840, by decide⟩ =
    .split (coordinate 12) (![⟨855792, by decide⟩,⟨855815, by decide⟩,⟨855830, by decide⟩,⟨855839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110114_855840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110114 ⟨855840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110114
    ⟨855840, by decide⟩ (by decide) (![⟨855792, by decide⟩,⟨855815, by decide⟩,⟨855830, by decide⟩,⟨855839, by decide⟩]) unmarked_context_12_110114_855840 node_context_12_110114_855840
  intro a
  fin_cases a
  · exact context_13_440456_855792
  · exact context_13_440457_855815
  · exact context_13_440458_855830
  · exact context_13_440459_855839

theorem selected_cut_33219 : selected 8 ⟨855856, by decide⟩
    (prefixPartial 13 440460) = some ⟨13, 2, 0, 855856, 440460, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_440460_855856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440460 ⟨855856, by decide⟩ :=
  accepted_of_selected 13 440460 ⟨855856, by decide⟩ ⟨13, 2, 0, 855856, 440460, 1217, 16384⟩
    (by decide) selected_cut_33219

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
