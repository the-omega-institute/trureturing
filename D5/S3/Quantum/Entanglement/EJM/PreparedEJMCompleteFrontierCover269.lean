/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover268
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_25828 : selected 8 ⟨653875, by decide⟩
    (prefixPartial 13 352510) = some ⟨13, 2, 0, 653875, 352510, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_352510_653875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352510 ⟨653875, by decide⟩ :=
  accepted_of_selected 13 352510 ⟨653875, by decide⟩ ⟨13, 2, 0, 653875, 352510, 1689, 16384⟩
    (by decide) selected_cut_25828

theorem selected_cut_25829 : selected 8 ⟨653879, by decide⟩
    (prefixPartial 13 352511) = some ⟨13, 2, 0, 653879, 352511, 685, 16384⟩ := by
  decide +kernel

theorem context_13_352511_653879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352511 ⟨653879, by decide⟩ :=
  accepted_of_selected 13 352511 ⟨653879, by decide⟩ ⟨13, 2, 0, 653879, 352511, 685, 16384⟩
    (by decide) selected_cut_25829

theorem unmarked_context_12_88127_653880 : frontier 9 ⟨653880, by decide⟩
    (prefixCache 12 88127) (prefixPartial 12 88127) = false := by
  decide +kernel

theorem node_context_12_88127_653880 : EJMOriginalGlobalDAGData.nodes 9 ⟨653880, by decide⟩ =
    .split (coordinate 12) (![⟨653793, by decide⟩,⟨653848, by decide⟩,⟨653875, by decide⟩,⟨653879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88127_653880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88127 ⟨653880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88127
    ⟨653880, by decide⟩ (by decide) (![⟨653793, by decide⟩,⟨653848, by decide⟩,⟨653875, by decide⟩,⟨653879, by decide⟩]) unmarked_context_12_88127_653880 node_context_12_88127_653880
  intro a
  fin_cases a
  · exact context_13_352508_653793
  · exact context_13_352509_653848
  · exact context_13_352510_653875
  · exact context_13_352511_653879

theorem unmarked_context_11_22031_653881 : frontier 10 ⟨653881, by decide⟩
    (prefixCache 11 22031) (prefixPartial 11 22031) = false := by
  decide +kernel

theorem node_context_11_22031_653881 : EJMOriginalGlobalDAGData.nodes 10 ⟨653881, by decide⟩ =
    .split (coordinate 11) (![⟨653657, by decide⟩,⟨653724, by decide⟩,⟨653790, by decide⟩,⟨653880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22031_653881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22031 ⟨653881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22031
    ⟨653881, by decide⟩ (by decide) (![⟨653657, by decide⟩,⟨653724, by decide⟩,⟨653790, by decide⟩,⟨653880, by decide⟩]) unmarked_context_11_22031_653881 node_context_11_22031_653881
  intro a
  fin_cases a
  · exact context_12_88124_653657
  · exact context_12_88125_653724
  · exact context_12_88126_653790
  · exact context_12_88127_653880

theorem unmarked_context_10_5507_653882 : frontier 11 ⟨653882, by decide⟩
    (prefixCache 10 5507) (prefixPartial 10 5507) = false := by
  decide +kernel

theorem node_context_10_5507_653882 : EJMOriginalGlobalDAGData.nodes 11 ⟨653882, by decide⟩ =
    .split (coordinate 10) (![⟨653030, by decide⟩,⟨653312, by decide⟩,⟨653586, by decide⟩,⟨653881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5507_653882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5507 ⟨653882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5507
    ⟨653882, by decide⟩ (by decide) (![⟨653030, by decide⟩,⟨653312, by decide⟩,⟨653586, by decide⟩,⟨653881, by decide⟩]) unmarked_context_10_5507_653882 node_context_10_5507_653882
  intro a
  fin_cases a
  · exact context_11_22028_653030
  · exact context_11_22029_653312
  · exact context_11_22030_653586
  · exact context_11_22031_653881

theorem unmarked_context_9_1376_653883 : frontier 12 ⟨653883, by decide⟩
    (prefixCache 9 1376) (prefixPartial 9 1376) = false := by
  decide +kernel

theorem node_context_9_1376_653883 : EJMOriginalGlobalDAGData.nodes 12 ⟨653883, by decide⟩ =
    .split (coordinate 9) (![⟨650185, by decide⟩,⟨651722, by decide⟩,⟨652817, by decide⟩,⟨653882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1376_653883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1376 ⟨653883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1376
    ⟨653883, by decide⟩ (by decide) (![⟨650185, by decide⟩,⟨651722, by decide⟩,⟨652817, by decide⟩,⟨653882, by decide⟩]) unmarked_context_9_1376_653883 node_context_9_1376_653883
  intro a
  fin_cases a
  · exact context_10_5504_650185
  · exact context_10_5505_651722
  · exact context_10_5506_652817
  · exact context_10_5507_653882

theorem selected_cut_25830 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 88128) = some ⟨12, 1, 0, 450982, 88128, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88128_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88128 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 88128 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 88128, 1, 65536⟩
    (by decide) selected_cut_25830

theorem selected_cut_25831 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 88129) = some ⟨12, 1, 0, 126371, 88129, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88129_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88129 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 88129 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 88129, 1, 65536⟩
    (by decide) selected_cut_25831

theorem selected_cut_25832 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352520) = some ⟨13, 1, 0, 3444, 352520, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352520_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352520 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352520 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352520, 1, 16384⟩
    (by decide) selected_cut_25832

theorem selected_cut_25833 : selected 8 ⟨653907, by decide⟩
    (prefixPartial 13 352521) = some ⟨13, 2, 0, 653907, 352521, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_352521_653907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352521 ⟨653907, by decide⟩ :=
  accepted_of_selected 13 352521 ⟨653907, by decide⟩ ⟨13, 2, 0, 653907, 352521, 2157, 16384⟩
    (by decide) selected_cut_25833

theorem selected_cut_25834 : selected 8 ⟨653929, by decide⟩
    (prefixPartial 13 352522) = some ⟨13, 2, 0, 653929, 352522, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_352522_653929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352522 ⟨653929, by decide⟩ :=
  accepted_of_selected 13 352522 ⟨653929, by decide⟩ ⟨13, 2, 0, 653929, 352522, 1193, 16384⟩
    (by decide) selected_cut_25834

theorem selected_cut_25835 : selected 8 ⟨653934, by decide⟩
    (prefixPartial 13 352523) = some ⟨13, 2, 0, 653934, 352523, 781, 16384⟩ := by
  decide +kernel

theorem context_13_352523_653934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352523 ⟨653934, by decide⟩ :=
  accepted_of_selected 13 352523 ⟨653934, by decide⟩ ⟨13, 2, 0, 653934, 352523, 781, 16384⟩
    (by decide) selected_cut_25835

theorem unmarked_context_12_88130_653935 : frontier 9 ⟨653935, by decide⟩
    (prefixCache 12 88130) (prefixPartial 12 88130) = false := by
  decide +kernel

theorem node_context_12_88130_653935 : EJMOriginalGlobalDAGData.nodes 9 ⟨653935, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨653907, by decide⟩,⟨653929, by decide⟩,⟨653934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88130_653935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88130 ⟨653935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88130
    ⟨653935, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨653907, by decide⟩,⟨653929, by decide⟩,⟨653934, by decide⟩]) unmarked_context_12_88130_653935 node_context_12_88130_653935
  intro a
  fin_cases a
  · exact context_13_352520_3444
  · exact context_13_352521_653907
  · exact context_13_352522_653929
  · exact context_13_352523_653934

theorem selected_cut_25836 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352524) = some ⟨13, 1, 0, 3444, 352524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352524, 1, 16384⟩
    (by decide) selected_cut_25836

theorem selected_cut_25837 : selected 8 ⟨653976, by decide⟩
    (prefixPartial 13 352525) = some ⟨13, 2, 0, 653976, 352525, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_352525_653976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352525 ⟨653976, by decide⟩ :=
  accepted_of_selected 13 352525 ⟨653976, by decide⟩ ⟨13, 2, 0, 653976, 352525, 2421, 16384⟩
    (by decide) selected_cut_25837

theorem selected_cut_25838 : selected 8 ⟨653996, by decide⟩
    (prefixPartial 13 352526) = some ⟨13, 2, 0, 653996, 352526, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_352526_653996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352526 ⟨653996, by decide⟩ :=
  accepted_of_selected 13 352526 ⟨653996, by decide⟩ ⟨13, 2, 0, 653996, 352526, 1265, 16384⟩
    (by decide) selected_cut_25838

theorem selected_cut_25839 : selected 8 ⟨654001, by decide⟩
    (prefixPartial 13 352527) = some ⟨13, 2, 0, 654001, 352527, 681, 16384⟩ := by
  decide +kernel

theorem context_13_352527_654001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352527 ⟨654001, by decide⟩ :=
  accepted_of_selected 13 352527 ⟨654001, by decide⟩ ⟨13, 2, 0, 654001, 352527, 681, 16384⟩
    (by decide) selected_cut_25839

theorem unmarked_context_12_88131_654002 : frontier 9 ⟨654002, by decide⟩
    (prefixCache 12 88131) (prefixPartial 12 88131) = false := by
  decide +kernel

theorem node_context_12_88131_654002 : EJMOriginalGlobalDAGData.nodes 9 ⟨654002, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨653976, by decide⟩,⟨653996, by decide⟩,⟨654001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88131_654002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88131 ⟨654002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88131
    ⟨654002, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨653976, by decide⟩,⟨653996, by decide⟩,⟨654001, by decide⟩]) unmarked_context_12_88131_654002 node_context_12_88131_654002
  intro a
  fin_cases a
  · exact context_13_352524_3444
  · exact context_13_352525_653976
  · exact context_13_352526_653996
  · exact context_13_352527_654001

theorem unmarked_context_11_22032_654003 : frontier 10 ⟨654003, by decide⟩
    (prefixCache 11 22032) (prefixPartial 11 22032) = false := by
  decide +kernel

theorem node_context_11_22032_654003 : EJMOriginalGlobalDAGData.nodes 10 ⟨654003, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨126371, by decide⟩,⟨653935, by decide⟩,⟨654002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22032_654003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22032 ⟨654003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22032
    ⟨654003, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨126371, by decide⟩,⟨653935, by decide⟩,⟨654002, by decide⟩]) unmarked_context_11_22032_654003 node_context_11_22032_654003
  intro a
  fin_cases a
  · exact context_12_88128_450982
  · exact context_12_88129_126371
  · exact context_12_88130_653935
  · exact context_12_88131_654002

theorem selected_cut_25840 : selected 9 ⟨654052, by decide⟩
    (prefixPartial 12 88132) = some ⟨12, 2, 0, 654052, 88132, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_88132_654052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88132 ⟨654052, by decide⟩ :=
  accepted_of_selected 12 88132 ⟨654052, by decide⟩ ⟨12, 2, 0, 654052, 88132, 3477, 65536⟩
    (by decide) selected_cut_25840

theorem selected_cut_25841 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 88133) = some ⟨12, 1, 0, 170504, 88133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88133_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88133 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 88133 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 88133, 1, 65536⟩
    (by decide) selected_cut_25841

theorem selected_cut_25842 : selected 9 ⟨654099, by decide⟩
    (prefixPartial 12 88134) = some ⟨12, 2, 0, 654099, 88134, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_88134_654099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88134 ⟨654099, by decide⟩ :=
  accepted_of_selected 12 88134 ⟨654099, by decide⟩ ⟨12, 2, 0, 654099, 88134, 3761, 65536⟩
    (by decide) selected_cut_25842

theorem selected_cut_25843 : selected 9 ⟨654156, by decide⟩
    (prefixPartial 12 88135) = some ⟨12, 2, 0, 654156, 88135, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_88135_654156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88135 ⟨654156, by decide⟩ :=
  accepted_of_selected 12 88135 ⟨654156, by decide⟩ ⟨12, 2, 0, 654156, 88135, 3957, 65536⟩
    (by decide) selected_cut_25843

theorem unmarked_context_11_22033_654157 : frontier 10 ⟨654157, by decide⟩
    (prefixCache 11 22033) (prefixPartial 11 22033) = false := by
  decide +kernel

theorem node_context_11_22033_654157 : EJMOriginalGlobalDAGData.nodes 10 ⟨654157, by decide⟩ =
    .split (coordinate 11) (![⟨654052, by decide⟩,⟨170504, by decide⟩,⟨654099, by decide⟩,⟨654156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22033_654157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22033 ⟨654157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22033
    ⟨654157, by decide⟩ (by decide) (![⟨654052, by decide⟩,⟨170504, by decide⟩,⟨654099, by decide⟩,⟨654156, by decide⟩]) unmarked_context_11_22033_654157 node_context_11_22033_654157
  intro a
  fin_cases a
  · exact context_12_88132_654052
  · exact context_12_88133_170504
  · exact context_12_88134_654099
  · exact context_12_88135_654156

theorem selected_cut_25844 : selected 9 ⟨654200, by decide⟩
    (prefixPartial 12 88136) = some ⟨12, 2, 0, 654200, 88136, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_88136_654200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88136 ⟨654200, by decide⟩ :=
  accepted_of_selected 12 88136 ⟨654200, by decide⟩ ⟨12, 2, 0, 654200, 88136, 3533, 65536⟩
    (by decide) selected_cut_25844

theorem selected_cut_25845 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352548) = some ⟨13, 1, 0, 3444, 352548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352548, 1, 16384⟩
    (by decide) selected_cut_25845

theorem selected_cut_25846 : selected 8 ⟨654245, by decide⟩
    (prefixPartial 13 352549) = some ⟨13, 2, 0, 654245, 352549, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_352549_654245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352549 ⟨654245, by decide⟩ :=
  accepted_of_selected 13 352549 ⟨654245, by decide⟩ ⟨13, 2, 0, 654245, 352549, 2473, 16384⟩
    (by decide) selected_cut_25846

theorem selected_cut_25847 : selected 8 ⟨654272, by decide⟩
    (prefixPartial 13 352550) = some ⟨13, 2, 0, 654272, 352550, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_352550_654272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352550 ⟨654272, by decide⟩ :=
  accepted_of_selected 13 352550 ⟨654272, by decide⟩ ⟨13, 2, 0, 654272, 352550, 1761, 16384⟩
    (by decide) selected_cut_25847

theorem selected_cut_25848 : selected 8 ⟨654279, by decide⟩
    (prefixPartial 13 352551) = some ⟨13, 2, 0, 654279, 352551, 913, 16384⟩ := by
  decide +kernel

theorem context_13_352551_654279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352551 ⟨654279, by decide⟩ :=
  accepted_of_selected 13 352551 ⟨654279, by decide⟩ ⟨13, 2, 0, 654279, 352551, 913, 16384⟩
    (by decide) selected_cut_25848

theorem unmarked_context_12_88137_654280 : frontier 9 ⟨654280, by decide⟩
    (prefixCache 12 88137) (prefixPartial 12 88137) = false := by
  decide +kernel

theorem node_context_12_88137_654280 : EJMOriginalGlobalDAGData.nodes 9 ⟨654280, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨654245, by decide⟩,⟨654272, by decide⟩,⟨654279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88137_654280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88137 ⟨654280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88137
    ⟨654280, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨654245, by decide⟩,⟨654272, by decide⟩,⟨654279, by decide⟩]) unmarked_context_12_88137_654280 node_context_12_88137_654280
  intro a
  fin_cases a
  · exact context_13_352548_3444
  · exact context_13_352549_654245
  · exact context_13_352550_654272
  · exact context_13_352551_654279

theorem selected_cut_25849 : selected 9 ⟨654327, by decide⟩
    (prefixPartial 12 88138) = some ⟨12, 2, 0, 654327, 88138, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_88138_654327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88138 ⟨654327, by decide⟩ :=
  accepted_of_selected 12 88138 ⟨654327, by decide⟩ ⟨12, 2, 0, 654327, 88138, 3477, 65536⟩
    (by decide) selected_cut_25849

theorem selected_cut_25850 : selected 9 ⟨654384, by decide⟩
    (prefixPartial 12 88139) = some ⟨12, 2, 0, 654384, 88139, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_88139_654384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88139 ⟨654384, by decide⟩ :=
  accepted_of_selected 12 88139 ⟨654384, by decide⟩ ⟨12, 2, 0, 654384, 88139, 4005, 65536⟩
    (by decide) selected_cut_25850

theorem unmarked_context_11_22034_654385 : frontier 10 ⟨654385, by decide⟩
    (prefixCache 11 22034) (prefixPartial 11 22034) = false := by
  decide +kernel

theorem node_context_11_22034_654385 : EJMOriginalGlobalDAGData.nodes 10 ⟨654385, by decide⟩ =
    .split (coordinate 11) (![⟨654200, by decide⟩,⟨654280, by decide⟩,⟨654327, by decide⟩,⟨654384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22034_654385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22034 ⟨654385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22034
    ⟨654385, by decide⟩ (by decide) (![⟨654200, by decide⟩,⟨654280, by decide⟩,⟨654327, by decide⟩,⟨654384, by decide⟩]) unmarked_context_11_22034_654385 node_context_11_22034_654385
  intro a
  fin_cases a
  · exact context_12_88136_654200
  · exact context_12_88137_654280
  · exact context_12_88138_654327
  · exact context_12_88139_654384

theorem selected_cut_25851 : selected 9 ⟨654436, by decide⟩
    (prefixPartial 12 88140) = some ⟨12, 2, 0, 654436, 88140, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_88140_654436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88140 ⟨654436, by decide⟩ :=
  accepted_of_selected 12 88140 ⟨654436, by decide⟩ ⟨12, 2, 0, 654436, 88140, 3677, 65536⟩
    (by decide) selected_cut_25851

theorem selected_cut_25852 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352564) = some ⟨13, 1, 0, 3444, 352564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352564, 1, 16384⟩
    (by decide) selected_cut_25852

theorem selected_cut_25853 : selected 8 ⟨654486, by decide⟩
    (prefixPartial 13 352565) = some ⟨13, 2, 0, 654486, 352565, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_352565_654486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352565 ⟨654486, by decide⟩ :=
  accepted_of_selected 13 352565 ⟨654486, by decide⟩ ⟨13, 2, 0, 654486, 352565, 2469, 16384⟩
    (by decide) selected_cut_25853

theorem selected_cut_25854 : selected 8 ⟨654509, by decide⟩
    (prefixPartial 13 352566) = some ⟨13, 2, 0, 654509, 352566, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_352566_654509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352566 ⟨654509, by decide⟩ :=
  accepted_of_selected 13 352566 ⟨654509, by decide⟩ ⟨13, 2, 0, 654509, 352566, 1685, 16384⟩
    (by decide) selected_cut_25854

theorem selected_cut_25855 : selected 8 ⟨654520, by decide⟩
    (prefixPartial 13 352567) = some ⟨13, 2, 0, 654520, 352567, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_352567_654520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352567 ⟨654520, by decide⟩ :=
  accepted_of_selected 13 352567 ⟨654520, by decide⟩ ⟨13, 2, 0, 654520, 352567, 1069, 16384⟩
    (by decide) selected_cut_25855

theorem unmarked_context_12_88141_654521 : frontier 9 ⟨654521, by decide⟩
    (prefixCache 12 88141) (prefixPartial 12 88141) = false := by
  decide +kernel

theorem node_context_12_88141_654521 : EJMOriginalGlobalDAGData.nodes 9 ⟨654521, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨654486, by decide⟩,⟨654509, by decide⟩,⟨654520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88141_654521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88141 ⟨654521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88141
    ⟨654521, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨654486, by decide⟩,⟨654509, by decide⟩,⟨654520, by decide⟩]) unmarked_context_12_88141_654521 node_context_12_88141_654521
  intro a
  fin_cases a
  · exact context_13_352564_3444
  · exact context_13_352565_654486
  · exact context_13_352566_654509
  · exact context_13_352567_654520

theorem selected_cut_25856 : selected 9 ⟨654569, by decide⟩
    (prefixPartial 12 88142) = some ⟨12, 2, 0, 654569, 88142, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_88142_654569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88142 ⟨654569, by decide⟩ :=
  accepted_of_selected 12 88142 ⟨654569, by decide⟩ ⟨12, 2, 0, 654569, 88142, 3933, 65536⟩
    (by decide) selected_cut_25856

theorem selected_cut_25857 : selected 9 ⟨654614, by decide⟩
    (prefixPartial 12 88143) = some ⟨12, 2, 0, 654614, 88143, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_88143_654614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88143 ⟨654614, by decide⟩ :=
  accepted_of_selected 12 88143 ⟨654614, by decide⟩ ⟨12, 2, 0, 654614, 88143, 3841, 65536⟩
    (by decide) selected_cut_25857

theorem unmarked_context_11_22035_654615 : frontier 10 ⟨654615, by decide⟩
    (prefixCache 11 22035) (prefixPartial 11 22035) = false := by
  decide +kernel

theorem node_context_11_22035_654615 : EJMOriginalGlobalDAGData.nodes 10 ⟨654615, by decide⟩ =
    .split (coordinate 11) (![⟨654436, by decide⟩,⟨654521, by decide⟩,⟨654569, by decide⟩,⟨654614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22035_654615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22035 ⟨654615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22035
    ⟨654615, by decide⟩ (by decide) (![⟨654436, by decide⟩,⟨654521, by decide⟩,⟨654569, by decide⟩,⟨654614, by decide⟩]) unmarked_context_11_22035_654615 node_context_11_22035_654615
  intro a
  fin_cases a
  · exact context_12_88140_654436
  · exact context_12_88141_654521
  · exact context_12_88142_654569
  · exact context_12_88143_654614

theorem unmarked_context_10_5508_654616 : frontier 11 ⟨654616, by decide⟩
    (prefixCache 10 5508) (prefixPartial 10 5508) = false := by
  decide +kernel

theorem node_context_10_5508_654616 : EJMOriginalGlobalDAGData.nodes 11 ⟨654616, by decide⟩ =
    .split (coordinate 10) (![⟨654003, by decide⟩,⟨654157, by decide⟩,⟨654385, by decide⟩,⟨654615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5508_654616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5508 ⟨654616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5508
    ⟨654616, by decide⟩ (by decide) (![⟨654003, by decide⟩,⟨654157, by decide⟩,⟨654385, by decide⟩,⟨654615, by decide⟩]) unmarked_context_10_5508_654616 node_context_10_5508_654616
  intro a
  fin_cases a
  · exact context_11_22032_654003
  · exact context_11_22033_654157
  · exact context_11_22034_654385
  · exact context_11_22035_654615

theorem selected_cut_25858 : selected 9 ⟨654741, by decide⟩
    (prefixPartial 12 88144) = some ⟨12, 2, 0, 654741, 88144, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_88144_654741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88144 ⟨654741, by decide⟩ :=
  accepted_of_selected 12 88144 ⟨654741, by decide⟩ ⟨12, 2, 0, 654741, 88144, 3169, 65536⟩
    (by decide) selected_cut_25858

theorem selected_cut_25859 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88145) = some ⟨12, 1, 0, 642341, 88145, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88145_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88145 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88145 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88145, 1, 65536⟩
    (by decide) selected_cut_25859

theorem selected_cut_25860 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352584) = some ⟨13, 1, 0, 3444, 352584, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352584_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352584 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352584 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352584, 1, 16384⟩
    (by decide) selected_cut_25860

theorem selected_cut_25861 : selected 8 ⟨654759, by decide⟩
    (prefixPartial 13 352585) = some ⟨13, 2, 0, 654759, 352585, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_352585_654759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352585 ⟨654759, by decide⟩ :=
  accepted_of_selected 13 352585 ⟨654759, by decide⟩ ⟨13, 2, 0, 654759, 352585, 1697, 16384⟩
    (by decide) selected_cut_25861

theorem selected_cut_25862 : selected 8 ⟨654781, by decide⟩
    (prefixPartial 13 352586) = some ⟨13, 2, 0, 654781, 352586, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_352586_654781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352586 ⟨654781, by decide⟩ :=
  accepted_of_selected 13 352586 ⟨654781, by decide⟩ ⟨13, 2, 0, 654781, 352586, 1545, 16384⟩
    (by decide) selected_cut_25862

theorem selected_cut_25863 : selected 8 ⟨654788, by decide⟩
    (prefixPartial 13 352587) = some ⟨13, 2, 0, 654788, 352587, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_352587_654788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352587 ⟨654788, by decide⟩ :=
  accepted_of_selected 13 352587 ⟨654788, by decide⟩ ⟨13, 2, 0, 654788, 352587, 1041, 16384⟩
    (by decide) selected_cut_25863

theorem unmarked_context_12_88146_654789 : frontier 9 ⟨654789, by decide⟩
    (prefixCache 12 88146) (prefixPartial 12 88146) = false := by
  decide +kernel

theorem node_context_12_88146_654789 : EJMOriginalGlobalDAGData.nodes 9 ⟨654789, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨654759, by decide⟩,⟨654781, by decide⟩,⟨654788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88146_654789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88146 ⟨654789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88146
    ⟨654789, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨654759, by decide⟩,⟨654781, by decide⟩,⟨654788, by decide⟩]) unmarked_context_12_88146_654789 node_context_12_88146_654789
  intro a
  fin_cases a
  · exact context_13_352584_3444
  · exact context_13_352585_654759
  · exact context_13_352586_654781
  · exact context_13_352587_654788

theorem selected_cut_25864 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352588) = some ⟨13, 1, 0, 3444, 352588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352588, 1, 16384⟩
    (by decide) selected_cut_25864

theorem selected_cut_25865 : selected 8 ⟨654814, by decide⟩
    (prefixPartial 13 352589) = some ⟨13, 2, 0, 654814, 352589, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_352589_654814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352589 ⟨654814, by decide⟩ :=
  accepted_of_selected 13 352589 ⟨654814, by decide⟩ ⟨13, 2, 0, 654814, 352589, 1773, 16384⟩
    (by decide) selected_cut_25865

theorem selected_cut_25866 : selected 8 ⟨654835, by decide⟩
    (prefixPartial 13 352590) = some ⟨13, 2, 0, 654835, 352590, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_352590_654835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352590 ⟨654835, by decide⟩ :=
  accepted_of_selected 13 352590 ⟨654835, by decide⟩ ⟨13, 2, 0, 654835, 352590, 1633, 16384⟩
    (by decide) selected_cut_25866

theorem selected_cut_25867 : selected 8 ⟨654839, by decide⟩
    (prefixPartial 13 352591) = some ⟨13, 2, 0, 654839, 352591, 801, 16384⟩ := by
  decide +kernel

theorem context_13_352591_654839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352591 ⟨654839, by decide⟩ :=
  accepted_of_selected 13 352591 ⟨654839, by decide⟩ ⟨13, 2, 0, 654839, 352591, 801, 16384⟩
    (by decide) selected_cut_25867

theorem unmarked_context_12_88147_654840 : frontier 9 ⟨654840, by decide⟩
    (prefixCache 12 88147) (prefixPartial 12 88147) = false := by
  decide +kernel

theorem node_context_12_88147_654840 : EJMOriginalGlobalDAGData.nodes 9 ⟨654840, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨654814, by decide⟩,⟨654835, by decide⟩,⟨654839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88147_654840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88147 ⟨654840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88147
    ⟨654840, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨654814, by decide⟩,⟨654835, by decide⟩,⟨654839, by decide⟩]) unmarked_context_12_88147_654840 node_context_12_88147_654840
  intro a
  fin_cases a
  · exact context_13_352588_3444
  · exact context_13_352589_654814
  · exact context_13_352590_654835
  · exact context_13_352591_654839

theorem unmarked_context_11_22036_654841 : frontier 10 ⟨654841, by decide⟩
    (prefixCache 11 22036) (prefixPartial 11 22036) = false := by
  decide +kernel

theorem node_context_11_22036_654841 : EJMOriginalGlobalDAGData.nodes 10 ⟨654841, by decide⟩ =
    .split (coordinate 11) (![⟨654741, by decide⟩,⟨642341, by decide⟩,⟨654789, by decide⟩,⟨654840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22036_654841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22036 ⟨654841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22036
    ⟨654841, by decide⟩ (by decide) (![⟨654741, by decide⟩,⟨642341, by decide⟩,⟨654789, by decide⟩,⟨654840, by decide⟩]) unmarked_context_11_22036_654841 node_context_11_22036_654841
  intro a
  fin_cases a
  · exact context_12_88144_654741
  · exact context_12_88145_642341
  · exact context_12_88146_654789
  · exact context_12_88147_654840

theorem selected_cut_25868 : selected 9 ⟨654884, by decide⟩
    (prefixPartial 12 88148) = some ⟨12, 2, 0, 654884, 88148, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_88148_654884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88148 ⟨654884, by decide⟩ :=
  accepted_of_selected 12 88148 ⟨654884, by decide⟩ ⟨12, 2, 0, 654884, 88148, 4005, 65536⟩
    (by decide) selected_cut_25868

theorem selected_cut_25869 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88149) = some ⟨12, 1, 0, 642341, 88149, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88149_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88149 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88149 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88149, 1, 65536⟩
    (by decide) selected_cut_25869

theorem selected_cut_25870 : selected 9 ⟨654928, by decide⟩
    (prefixPartial 12 88150) = some ⟨12, 2, 0, 654928, 88150, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_88150_654928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88150 ⟨654928, by decide⟩ :=
  accepted_of_selected 12 88150 ⟨654928, by decide⟩ ⟨12, 2, 0, 654928, 88150, 4057, 65536⟩
    (by decide) selected_cut_25870

theorem selected_cut_25871 : selected 9 ⟨654984, by decide⟩
    (prefixPartial 12 88151) = some ⟨12, 2, 0, 654984, 88151, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_88151_654984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88151 ⟨654984, by decide⟩ :=
  accepted_of_selected 12 88151 ⟨654984, by decide⟩ ⟨12, 2, 0, 654984, 88151, 3953, 65536⟩
    (by decide) selected_cut_25871

theorem unmarked_context_11_22037_654985 : frontier 10 ⟨654985, by decide⟩
    (prefixCache 11 22037) (prefixPartial 11 22037) = false := by
  decide +kernel

theorem node_context_11_22037_654985 : EJMOriginalGlobalDAGData.nodes 10 ⟨654985, by decide⟩ =
    .split (coordinate 11) (![⟨654884, by decide⟩,⟨642341, by decide⟩,⟨654928, by decide⟩,⟨654984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22037_654985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22037 ⟨654985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22037
    ⟨654985, by decide⟩ (by decide) (![⟨654884, by decide⟩,⟨642341, by decide⟩,⟨654928, by decide⟩,⟨654984, by decide⟩]) unmarked_context_11_22037_654985 node_context_11_22037_654985
  intro a
  fin_cases a
  · exact context_12_88148_654884
  · exact context_12_88149_642341
  · exact context_12_88150_654928
  · exact context_12_88151_654984

theorem selected_cut_25872 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352608) = some ⟨13, 1, 0, 3444, 352608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352608, 1, 16384⟩
    (by decide) selected_cut_25872

theorem selected_cut_25873 : selected 8 ⟨655005, by decide⟩
    (prefixPartial 13 352609) = some ⟨13, 2, 0, 655005, 352609, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_352609_655005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352609 ⟨655005, by decide⟩ :=
  accepted_of_selected 13 352609 ⟨655005, by decide⟩ ⟨13, 2, 0, 655005, 352609, 1401, 16384⟩
    (by decide) selected_cut_25873

theorem selected_cut_25874 : selected 8 ⟨655024, by decide⟩
    (prefixPartial 13 352610) = some ⟨13, 2, 0, 655024, 352610, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_352610_655024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352610 ⟨655024, by decide⟩ :=
  accepted_of_selected 13 352610 ⟨655024, by decide⟩ ⟨13, 2, 0, 655024, 352610, 1725, 16384⟩
    (by decide) selected_cut_25874

theorem selected_cut_25875 : selected 8 ⟨655029, by decide⟩
    (prefixPartial 13 352611) = some ⟨13, 2, 0, 655029, 352611, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_352611_655029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352611 ⟨655029, by decide⟩ :=
  accepted_of_selected 13 352611 ⟨655029, by decide⟩ ⟨13, 2, 0, 655029, 352611, 1001, 16384⟩
    (by decide) selected_cut_25875

theorem unmarked_context_12_88152_655030 : frontier 9 ⟨655030, by decide⟩
    (prefixCache 12 88152) (prefixPartial 12 88152) = false := by
  decide +kernel

theorem node_context_12_88152_655030 : EJMOriginalGlobalDAGData.nodes 9 ⟨655030, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655005, by decide⟩,⟨655024, by decide⟩,⟨655029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88152_655030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88152 ⟨655030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88152
    ⟨655030, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655005, by decide⟩,⟨655024, by decide⟩,⟨655029, by decide⟩]) unmarked_context_12_88152_655030 node_context_12_88152_655030
  intro a
  fin_cases a
  · exact context_13_352608_3444
  · exact context_13_352609_655005
  · exact context_13_352610_655024
  · exact context_13_352611_655029

theorem selected_cut_25876 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88153) = some ⟨12, 1, 0, 642341, 88153, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88153_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88153 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88153 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88153, 1, 65536⟩
    (by decide) selected_cut_25876

theorem selected_cut_25877 : selected 9 ⟨655083, by decide⟩
    (prefixPartial 12 88154) = some ⟨12, 2, 0, 655083, 88154, 4049, 65536⟩ := by
  decide +kernel

theorem context_12_88154_655083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88154 ⟨655083, by decide⟩ :=
  accepted_of_selected 12 88154 ⟨655083, by decide⟩ ⟨12, 2, 0, 655083, 88154, 4049, 65536⟩
    (by decide) selected_cut_25877

theorem selected_cut_25878 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352620) = some ⟨13, 1, 0, 3444, 352620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352620, 1, 16384⟩
    (by decide) selected_cut_25878

theorem selected_cut_25879 : selected 8 ⟨655106, by decide⟩
    (prefixPartial 13 352621) = some ⟨13, 2, 0, 655106, 352621, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_352621_655106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352621 ⟨655106, by decide⟩ :=
  accepted_of_selected 13 352621 ⟨655106, by decide⟩ ⟨13, 2, 0, 655106, 352621, 1513, 16384⟩
    (by decide) selected_cut_25879

theorem selected_cut_25880 : selected 8 ⟨655124, by decide⟩
    (prefixPartial 13 352622) = some ⟨13, 2, 0, 655124, 352622, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_352622_655124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352622 ⟨655124, by decide⟩ :=
  accepted_of_selected 13 352622 ⟨655124, by decide⟩ ⟨13, 2, 0, 655124, 352622, 1929, 16384⟩
    (by decide) selected_cut_25880

theorem selected_cut_25881 : selected 8 ⟨655134, by decide⟩
    (prefixPartial 13 352623) = some ⟨13, 2, 0, 655134, 352623, 925, 16384⟩ := by
  decide +kernel

theorem context_13_352623_655134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352623 ⟨655134, by decide⟩ :=
  accepted_of_selected 13 352623 ⟨655134, by decide⟩ ⟨13, 2, 0, 655134, 352623, 925, 16384⟩
    (by decide) selected_cut_25881

theorem unmarked_context_12_88155_655135 : frontier 9 ⟨655135, by decide⟩
    (prefixCache 12 88155) (prefixPartial 12 88155) = false := by
  decide +kernel

theorem node_context_12_88155_655135 : EJMOriginalGlobalDAGData.nodes 9 ⟨655135, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655106, by decide⟩,⟨655124, by decide⟩,⟨655134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88155_655135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88155 ⟨655135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88155
    ⟨655135, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655106, by decide⟩,⟨655124, by decide⟩,⟨655134, by decide⟩]) unmarked_context_12_88155_655135 node_context_12_88155_655135
  intro a
  fin_cases a
  · exact context_13_352620_3444
  · exact context_13_352621_655106
  · exact context_13_352622_655124
  · exact context_13_352623_655134

theorem unmarked_context_11_22038_655136 : frontier 10 ⟨655136, by decide⟩
    (prefixCache 11 22038) (prefixPartial 11 22038) = false := by
  decide +kernel

theorem node_context_11_22038_655136 : EJMOriginalGlobalDAGData.nodes 10 ⟨655136, by decide⟩ =
    .split (coordinate 11) (![⟨655030, by decide⟩,⟨642341, by decide⟩,⟨655083, by decide⟩,⟨655135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22038_655136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22038 ⟨655136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22038
    ⟨655136, by decide⟩ (by decide) (![⟨655030, by decide⟩,⟨642341, by decide⟩,⟨655083, by decide⟩,⟨655135, by decide⟩]) unmarked_context_11_22038_655136 node_context_11_22038_655136
  intro a
  fin_cases a
  · exact context_12_88152_655030
  · exact context_12_88153_642341
  · exact context_12_88154_655083
  · exact context_12_88155_655135

theorem selected_cut_25882 : selected 9 ⟨655178, by decide⟩
    (prefixPartial 12 88156) = some ⟨12, 2, 0, 655178, 88156, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_88156_655178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88156 ⟨655178, by decide⟩ :=
  accepted_of_selected 12 88156 ⟨655178, by decide⟩ ⟨12, 2, 0, 655178, 88156, 4057, 65536⟩
    (by decide) selected_cut_25882

theorem selected_cut_25883 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88157) = some ⟨12, 1, 0, 642341, 88157, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88157_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88157 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88157 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88157, 1, 65536⟩
    (by decide) selected_cut_25883

theorem selected_cut_25884 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352632) = some ⟨13, 1, 0, 3444, 352632, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352632_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352632 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352632 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352632, 1, 16384⟩
    (by decide) selected_cut_25884

theorem selected_cut_25885 : selected 8 ⟨655194, by decide⟩
    (prefixPartial 13 352633) = some ⟨13, 2, 0, 655194, 352633, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_352633_655194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352633 ⟨655194, by decide⟩ :=
  accepted_of_selected 13 352633 ⟨655194, by decide⟩ ⟨13, 2, 0, 655194, 352633, 1357, 16384⟩
    (by decide) selected_cut_25885

theorem selected_cut_25886 : selected 8 ⟨655215, by decide⟩
    (prefixPartial 13 352634) = some ⟨13, 2, 0, 655215, 352634, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_352634_655215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352634 ⟨655215, by decide⟩ :=
  accepted_of_selected 13 352634 ⟨655215, by decide⟩ ⟨13, 2, 0, 655215, 352634, 1909, 16384⟩
    (by decide) selected_cut_25886

theorem selected_cut_25887 : selected 8 ⟨655220, by decide⟩
    (prefixPartial 13 352635) = some ⟨13, 2, 0, 655220, 352635, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_352635_655220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352635 ⟨655220, by decide⟩ :=
  accepted_of_selected 13 352635 ⟨655220, by decide⟩ ⟨13, 2, 0, 655220, 352635, 1041, 16384⟩
    (by decide) selected_cut_25887

theorem unmarked_context_12_88158_655221 : frontier 9 ⟨655221, by decide⟩
    (prefixCache 12 88158) (prefixPartial 12 88158) = false := by
  decide +kernel

theorem node_context_12_88158_655221 : EJMOriginalGlobalDAGData.nodes 9 ⟨655221, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655194, by decide⟩,⟨655215, by decide⟩,⟨655220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88158_655221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88158 ⟨655221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88158
    ⟨655221, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655194, by decide⟩,⟨655215, by decide⟩,⟨655220, by decide⟩]) unmarked_context_12_88158_655221 node_context_12_88158_655221
  intro a
  fin_cases a
  · exact context_13_352632_3444
  · exact context_13_352633_655194
  · exact context_13_352634_655215
  · exact context_13_352635_655220

theorem selected_cut_25888 : selected 9 ⟨655272, by decide⟩
    (prefixPartial 12 88159) = some ⟨12, 2, 0, 655272, 88159, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_88159_655272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88159 ⟨655272, by decide⟩ :=
  accepted_of_selected 12 88159 ⟨655272, by decide⟩ ⟨12, 2, 0, 655272, 88159, 3909, 65536⟩
    (by decide) selected_cut_25888

theorem unmarked_context_11_22039_655273 : frontier 10 ⟨655273, by decide⟩
    (prefixCache 11 22039) (prefixPartial 11 22039) = false := by
  decide +kernel

theorem node_context_11_22039_655273 : EJMOriginalGlobalDAGData.nodes 10 ⟨655273, by decide⟩ =
    .split (coordinate 11) (![⟨655178, by decide⟩,⟨642341, by decide⟩,⟨655221, by decide⟩,⟨655272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22039_655273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22039 ⟨655273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22039
    ⟨655273, by decide⟩ (by decide) (![⟨655178, by decide⟩,⟨642341, by decide⟩,⟨655221, by decide⟩,⟨655272, by decide⟩]) unmarked_context_11_22039_655273 node_context_11_22039_655273
  intro a
  fin_cases a
  · exact context_12_88156_655178
  · exact context_12_88157_642341
  · exact context_12_88158_655221
  · exact context_12_88159_655272

theorem unmarked_context_10_5509_655274 : frontier 11 ⟨655274, by decide⟩
    (prefixCache 10 5509) (prefixPartial 10 5509) = false := by
  decide +kernel

theorem node_context_10_5509_655274 : EJMOriginalGlobalDAGData.nodes 11 ⟨655274, by decide⟩ =
    .split (coordinate 10) (![⟨654841, by decide⟩,⟨654985, by decide⟩,⟨655136, by decide⟩,⟨655273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5509_655274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5509 ⟨655274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5509
    ⟨655274, by decide⟩ (by decide) (![⟨654841, by decide⟩,⟨654985, by decide⟩,⟨655136, by decide⟩,⟨655273, by decide⟩]) unmarked_context_10_5509_655274 node_context_10_5509_655274
  intro a
  fin_cases a
  · exact context_11_22036_654841
  · exact context_11_22037_654985
  · exact context_11_22038_655136
  · exact context_11_22039_655273

theorem selected_cut_25889 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352640) = some ⟨13, 1, 0, 3444, 352640, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352640_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352640 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352640 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352640, 1, 16384⟩
    (by decide) selected_cut_25889

theorem selected_cut_25890 : selected 8 ⟨655311, by decide⟩
    (prefixPartial 13 352641) = some ⟨13, 2, 0, 655311, 352641, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_352641_655311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352641 ⟨655311, by decide⟩ :=
  accepted_of_selected 13 352641 ⟨655311, by decide⟩ ⟨13, 2, 0, 655311, 352641, 1913, 16384⟩
    (by decide) selected_cut_25890

theorem selected_cut_25891 : selected 8 ⟨655336, by decide⟩
    (prefixPartial 13 352642) = some ⟨13, 2, 0, 655336, 352642, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_352642_655336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352642 ⟨655336, by decide⟩ :=
  accepted_of_selected 13 352642 ⟨655336, by decide⟩ ⟨13, 2, 0, 655336, 352642, 2117, 16384⟩
    (by decide) selected_cut_25891

theorem selected_cut_25892 : selected 8 ⟨655353, by decide⟩
    (prefixPartial 13 352643) = some ⟨13, 2, 0, 655353, 352643, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_352643_655353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352643 ⟨655353, by decide⟩ :=
  accepted_of_selected 13 352643 ⟨655353, by decide⟩ ⟨13, 2, 0, 655353, 352643, 1253, 16384⟩
    (by decide) selected_cut_25892

theorem unmarked_context_12_88160_655354 : frontier 9 ⟨655354, by decide⟩
    (prefixCache 12 88160) (prefixPartial 12 88160) = false := by
  decide +kernel

theorem node_context_12_88160_655354 : EJMOriginalGlobalDAGData.nodes 9 ⟨655354, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655311, by decide⟩,⟨655336, by decide⟩,⟨655353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88160_655354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88160 ⟨655354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88160
    ⟨655354, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655311, by decide⟩,⟨655336, by decide⟩,⟨655353, by decide⟩]) unmarked_context_12_88160_655354 node_context_12_88160_655354
  intro a
  fin_cases a
  · exact context_13_352640_3444
  · exact context_13_352641_655311
  · exact context_13_352642_655336
  · exact context_13_352643_655353

theorem selected_cut_25893 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352644) = some ⟨13, 1, 0, 3444, 352644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352644, 1, 16384⟩
    (by decide) selected_cut_25893

theorem selected_cut_25894 : selected 8 ⟨655385, by decide⟩
    (prefixPartial 13 352645) = some ⟨13, 2, 0, 655385, 352645, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_352645_655385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352645 ⟨655385, by decide⟩ :=
  accepted_of_selected 13 352645 ⟨655385, by decide⟩ ⟨13, 2, 0, 655385, 352645, 1713, 16384⟩
    (by decide) selected_cut_25894

theorem selected_cut_25895 : selected 8 ⟨655401, by decide⟩
    (prefixPartial 13 352646) = some ⟨13, 2, 0, 655401, 352646, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_352646_655401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352646 ⟨655401, by decide⟩ :=
  accepted_of_selected 13 352646 ⟨655401, by decide⟩ ⟨13, 2, 0, 655401, 352646, 1509, 16384⟩
    (by decide) selected_cut_25895

theorem selected_cut_25896 : selected 8 ⟨655414, by decide⟩
    (prefixPartial 13 352647) = some ⟨13, 2, 0, 655414, 352647, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_352647_655414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352647 ⟨655414, by decide⟩ :=
  accepted_of_selected 13 352647 ⟨655414, by decide⟩ ⟨13, 2, 0, 655414, 352647, 1089, 16384⟩
    (by decide) selected_cut_25896

theorem unmarked_context_12_88161_655415 : frontier 9 ⟨655415, by decide⟩
    (prefixCache 12 88161) (prefixPartial 12 88161) = false := by
  decide +kernel

theorem node_context_12_88161_655415 : EJMOriginalGlobalDAGData.nodes 9 ⟨655415, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655385, by decide⟩,⟨655401, by decide⟩,⟨655414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88161_655415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88161 ⟨655415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88161
    ⟨655415, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655385, by decide⟩,⟨655401, by decide⟩,⟨655414, by decide⟩]) unmarked_context_12_88161_655415 node_context_12_88161_655415
  intro a
  fin_cases a
  · exact context_13_352644_3444
  · exact context_13_352645_655385
  · exact context_13_352646_655401
  · exact context_13_352647_655414

theorem selected_cut_25897 : selected 9 ⟨655453, by decide⟩
    (prefixPartial 12 88162) = some ⟨12, 2, 0, 655453, 88162, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_88162_655453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88162 ⟨655453, by decide⟩ :=
  accepted_of_selected 12 88162 ⟨655453, by decide⟩ ⟨12, 2, 0, 655453, 88162, 3461, 65536⟩
    (by decide) selected_cut_25897

theorem selected_cut_25898 : selected 9 ⟨655492, by decide⟩
    (prefixPartial 12 88163) = some ⟨12, 2, 0, 655492, 88163, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_88163_655492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88163 ⟨655492, by decide⟩ :=
  accepted_of_selected 12 88163 ⟨655492, by decide⟩ ⟨12, 2, 0, 655492, 88163, 3313, 65536⟩
    (by decide) selected_cut_25898

theorem unmarked_context_11_22040_655493 : frontier 10 ⟨655493, by decide⟩
    (prefixCache 11 22040) (prefixPartial 11 22040) = false := by
  decide +kernel

theorem node_context_11_22040_655493 : EJMOriginalGlobalDAGData.nodes 10 ⟨655493, by decide⟩ =
    .split (coordinate 11) (![⟨655354, by decide⟩,⟨655415, by decide⟩,⟨655453, by decide⟩,⟨655492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22040_655493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22040 ⟨655493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22040
    ⟨655493, by decide⟩ (by decide) (![⟨655354, by decide⟩,⟨655415, by decide⟩,⟨655453, by decide⟩,⟨655492, by decide⟩]) unmarked_context_11_22040_655493 node_context_11_22040_655493
  intro a
  fin_cases a
  · exact context_12_88160_655354
  · exact context_12_88161_655415
  · exact context_12_88162_655453
  · exact context_12_88163_655492

theorem selected_cut_25899 : selected 9 ⟨655532, by decide⟩
    (prefixPartial 12 88164) = some ⟨12, 2, 0, 655532, 88164, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_88164_655532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88164 ⟨655532, by decide⟩ :=
  accepted_of_selected 12 88164 ⟨655532, by decide⟩ ⟨12, 2, 0, 655532, 88164, 3041, 65536⟩
    (by decide) selected_cut_25899

theorem selected_cut_25900 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 88165) = some ⟨12, 1, 0, 642794, 88165, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88165_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88165 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 88165 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 88165, 1, 65536⟩
    (by decide) selected_cut_25900

theorem selected_cut_25901 : selected 9 ⟨655563, by decide⟩
    (prefixPartial 12 88166) = some ⟨12, 2, 0, 655563, 88166, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_88166_655563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88166 ⟨655563, by decide⟩ :=
  accepted_of_selected 12 88166 ⟨655563, by decide⟩ ⟨12, 2, 0, 655563, 88166, 3153, 65536⟩
    (by decide) selected_cut_25901

theorem selected_cut_25902 : selected 9 ⟨655602, by decide⟩
    (prefixPartial 12 88167) = some ⟨12, 2, 0, 655602, 88167, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_88167_655602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88167 ⟨655602, by decide⟩ :=
  accepted_of_selected 12 88167 ⟨655602, by decide⟩ ⟨12, 2, 0, 655602, 88167, 2953, 65536⟩
    (by decide) selected_cut_25902

theorem unmarked_context_11_22041_655603 : frontier 10 ⟨655603, by decide⟩
    (prefixCache 11 22041) (prefixPartial 11 22041) = false := by
  decide +kernel

theorem node_context_11_22041_655603 : EJMOriginalGlobalDAGData.nodes 10 ⟨655603, by decide⟩ =
    .split (coordinate 11) (![⟨655532, by decide⟩,⟨642794, by decide⟩,⟨655563, by decide⟩,⟨655602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22041_655603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22041 ⟨655603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22041
    ⟨655603, by decide⟩ (by decide) (![⟨655532, by decide⟩,⟨642794, by decide⟩,⟨655563, by decide⟩,⟨655602, by decide⟩]) unmarked_context_11_22041_655603 node_context_11_22041_655603
  intro a
  fin_cases a
  · exact context_12_88164_655532
  · exact context_12_88165_642794
  · exact context_12_88166_655563
  · exact context_12_88167_655602

theorem selected_cut_25903 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352672) = some ⟨13, 1, 0, 3444, 352672, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352672_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352672 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352672 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352672, 1, 16384⟩
    (by decide) selected_cut_25903

theorem selected_cut_25904 : selected 8 ⟨655624, by decide⟩
    (prefixPartial 13 352673) = some ⟨13, 2, 0, 655624, 352673, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_352673_655624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352673 ⟨655624, by decide⟩ :=
  accepted_of_selected 13 352673 ⟨655624, by decide⟩ ⟨13, 2, 0, 655624, 352673, 1377, 16384⟩
    (by decide) selected_cut_25904

theorem selected_cut_25905 : selected 8 ⟨655645, by decide⟩
    (prefixPartial 13 352674) = some ⟨13, 2, 0, 655645, 352674, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_352674_655645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352674 ⟨655645, by decide⟩ :=
  accepted_of_selected 13 352674 ⟨655645, by decide⟩ ⟨13, 2, 0, 655645, 352674, 1785, 16384⟩
    (by decide) selected_cut_25905

theorem selected_cut_25906 : selected 8 ⟨655654, by decide⟩
    (prefixPartial 13 352675) = some ⟨13, 2, 0, 655654, 352675, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_352675_655654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352675 ⟨655654, by decide⟩ :=
  accepted_of_selected 13 352675 ⟨655654, by decide⟩ ⟨13, 2, 0, 655654, 352675, 1017, 16384⟩
    (by decide) selected_cut_25906

theorem unmarked_context_12_88168_655655 : frontier 9 ⟨655655, by decide⟩
    (prefixCache 12 88168) (prefixPartial 12 88168) = false := by
  decide +kernel

theorem node_context_12_88168_655655 : EJMOriginalGlobalDAGData.nodes 9 ⟨655655, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655624, by decide⟩,⟨655645, by decide⟩,⟨655654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88168_655655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88168 ⟨655655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88168
    ⟨655655, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655624, by decide⟩,⟨655645, by decide⟩,⟨655654, by decide⟩]) unmarked_context_12_88168_655655 node_context_12_88168_655655
  intro a
  fin_cases a
  · exact context_13_352672_3444
  · exact context_13_352673_655624
  · exact context_13_352674_655645
  · exact context_13_352675_655654

theorem selected_cut_25907 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352676) = some ⟨13, 1, 0, 3444, 352676, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352676_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352676 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352676 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352676, 1, 16384⟩
    (by decide) selected_cut_25907

theorem selected_cut_25908 : selected 8 ⟨655693, by decide⟩
    (prefixPartial 13 352677) = some ⟨13, 2, 0, 655693, 352677, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_352677_655693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352677 ⟨655693, by decide⟩ :=
  accepted_of_selected 13 352677 ⟨655693, by decide⟩ ⟨13, 2, 0, 655693, 352677, 1849, 16384⟩
    (by decide) selected_cut_25908

theorem selected_cut_25909 : selected 8 ⟨655729, by decide⟩
    (prefixPartial 13 352678) = some ⟨13, 2, 0, 655729, 352678, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_352678_655729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352678 ⟨655729, by decide⟩ :=
  accepted_of_selected 13 352678 ⟨655729, by decide⟩ ⟨13, 2, 0, 655729, 352678, 2365, 16384⟩
    (by decide) selected_cut_25909

theorem selected_cut_25910 : selected 8 ⟨655758, by decide⟩
    (prefixPartial 13 352679) = some ⟨13, 2, 0, 655758, 352679, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_352679_655758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352679 ⟨655758, by decide⟩ :=
  accepted_of_selected 13 352679 ⟨655758, by decide⟩ ⟨13, 2, 0, 655758, 352679, 1497, 16384⟩
    (by decide) selected_cut_25910

theorem unmarked_context_12_88169_655759 : frontier 9 ⟨655759, by decide⟩
    (prefixCache 12 88169) (prefixPartial 12 88169) = false := by
  decide +kernel

theorem node_context_12_88169_655759 : EJMOriginalGlobalDAGData.nodes 9 ⟨655759, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655693, by decide⟩,⟨655729, by decide⟩,⟨655758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88169_655759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88169 ⟨655759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88169
    ⟨655759, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655693, by decide⟩,⟨655729, by decide⟩,⟨655758, by decide⟩]) unmarked_context_12_88169_655759 node_context_12_88169_655759
  intro a
  fin_cases a
  · exact context_13_352676_3444
  · exact context_13_352677_655693
  · exact context_13_352678_655729
  · exact context_13_352679_655758

theorem selected_cut_25911 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 88170) = some ⟨12, 1, 0, 474208, 88170, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88170_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88170 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 88170 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 88170, 1, 65536⟩
    (by decide) selected_cut_25911

theorem selected_cut_25912 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352684) = some ⟨13, 1, 0, 3444, 352684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352684, 1, 16384⟩
    (by decide) selected_cut_25912

theorem selected_cut_25913 : selected 8 ⟨655784, by decide⟩
    (prefixPartial 13 352685) = some ⟨13, 2, 0, 655784, 352685, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_352685_655784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352685 ⟨655784, by decide⟩ :=
  accepted_of_selected 13 352685 ⟨655784, by decide⟩ ⟨13, 2, 0, 655784, 352685, 1365, 16384⟩
    (by decide) selected_cut_25913

theorem selected_cut_25914 : selected 8 ⟨655804, by decide⟩
    (prefixPartial 13 352686) = some ⟨13, 2, 0, 655804, 352686, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_352686_655804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352686 ⟨655804, by decide⟩ :=
  accepted_of_selected 13 352686 ⟨655804, by decide⟩ ⟨13, 2, 0, 655804, 352686, 1813, 16384⟩
    (by decide) selected_cut_25914

theorem selected_cut_25915 : selected 8 ⟨655812, by decide⟩
    (prefixPartial 13 352687) = some ⟨13, 2, 0, 655812, 352687, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_352687_655812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352687 ⟨655812, by decide⟩ :=
  accepted_of_selected 13 352687 ⟨655812, by decide⟩ ⟨13, 2, 0, 655812, 352687, 1029, 16384⟩
    (by decide) selected_cut_25915

theorem unmarked_context_12_88171_655813 : frontier 9 ⟨655813, by decide⟩
    (prefixCache 12 88171) (prefixPartial 12 88171) = false := by
  decide +kernel

theorem node_context_12_88171_655813 : EJMOriginalGlobalDAGData.nodes 9 ⟨655813, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655784, by decide⟩,⟨655804, by decide⟩,⟨655812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88171_655813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88171 ⟨655813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88171
    ⟨655813, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655784, by decide⟩,⟨655804, by decide⟩,⟨655812, by decide⟩]) unmarked_context_12_88171_655813 node_context_12_88171_655813
  intro a
  fin_cases a
  · exact context_13_352684_3444
  · exact context_13_352685_655784
  · exact context_13_352686_655804
  · exact context_13_352687_655812

theorem unmarked_context_11_22042_655814 : frontier 10 ⟨655814, by decide⟩
    (prefixCache 11 22042) (prefixPartial 11 22042) = false := by
  decide +kernel

theorem node_context_11_22042_655814 : EJMOriginalGlobalDAGData.nodes 10 ⟨655814, by decide⟩ =
    .split (coordinate 11) (![⟨655655, by decide⟩,⟨655759, by decide⟩,⟨474208, by decide⟩,⟨655813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22042_655814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22042 ⟨655814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22042
    ⟨655814, by decide⟩ (by decide) (![⟨655655, by decide⟩,⟨655759, by decide⟩,⟨474208, by decide⟩,⟨655813, by decide⟩]) unmarked_context_11_22042_655814 node_context_11_22042_655814
  intro a
  fin_cases a
  · exact context_12_88168_655655
  · exact context_12_88169_655759
  · exact context_12_88170_474208
  · exact context_12_88171_655813

theorem selected_cut_25916 : selected 9 ⟨655847, by decide⟩
    (prefixPartial 12 88172) = some ⟨12, 2, 0, 655847, 88172, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_88172_655847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88172 ⟨655847, by decide⟩ :=
  accepted_of_selected 12 88172 ⟨655847, by decide⟩ ⟨12, 2, 0, 655847, 88172, 3257, 65536⟩
    (by decide) selected_cut_25916

theorem selected_cut_25917 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352692) = some ⟨13, 1, 0, 3444, 352692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352692, 1, 16384⟩
    (by decide) selected_cut_25917

theorem selected_cut_25918 : selected 8 ⟨655861, by decide⟩
    (prefixPartial 13 352693) = some ⟨13, 2, 0, 655861, 352693, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_352693_655861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352693 ⟨655861, by decide⟩ :=
  accepted_of_selected 13 352693 ⟨655861, by decide⟩ ⟨13, 2, 0, 655861, 352693, 1069, 16384⟩
    (by decide) selected_cut_25918

theorem selected_cut_25919 : selected 8 ⟨655886, by decide⟩
    (prefixPartial 13 352694) = some ⟨13, 2, 0, 655886, 352694, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_352694_655886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352694 ⟨655886, by decide⟩ :=
  accepted_of_selected 13 352694 ⟨655886, by decide⟩ ⟨13, 2, 0, 655886, 352694, 1937, 16384⟩
    (by decide) selected_cut_25919

theorem selected_cut_25920 : selected 8 ⟨655899, by decide⟩
    (prefixPartial 13 352695) = some ⟨13, 2, 0, 655899, 352695, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_352695_655899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352695 ⟨655899, by decide⟩ :=
  accepted_of_selected 13 352695 ⟨655899, by decide⟩ ⟨13, 2, 0, 655899, 352695, 1173, 16384⟩
    (by decide) selected_cut_25920

theorem unmarked_context_12_88173_655900 : frontier 9 ⟨655900, by decide⟩
    (prefixCache 12 88173) (prefixPartial 12 88173) = false := by
  decide +kernel

theorem node_context_12_88173_655900 : EJMOriginalGlobalDAGData.nodes 9 ⟨655900, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655861, by decide⟩,⟨655886, by decide⟩,⟨655899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88173_655900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88173 ⟨655900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88173
    ⟨655900, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655861, by decide⟩,⟨655886, by decide⟩,⟨655899, by decide⟩]) unmarked_context_12_88173_655900 node_context_12_88173_655900
  intro a
  fin_cases a
  · exact context_13_352692_3444
  · exact context_13_352693_655861
  · exact context_13_352694_655886
  · exact context_13_352695_655899

theorem selected_cut_25921 : selected 9 ⟨655935, by decide⟩
    (prefixPartial 12 88174) = some ⟨12, 2, 0, 655935, 88174, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_88174_655935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88174 ⟨655935, by decide⟩ :=
  accepted_of_selected 12 88174 ⟨655935, by decide⟩ ⟨12, 2, 0, 655935, 88174, 3429, 65536⟩
    (by decide) selected_cut_25921

theorem selected_cut_25922 : selected 9 ⟨655970, by decide⟩
    (prefixPartial 12 88175) = some ⟨12, 2, 0, 655970, 88175, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_88175_655970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88175 ⟨655970, by decide⟩ :=
  accepted_of_selected 12 88175 ⟨655970, by decide⟩ ⟨12, 2, 0, 655970, 88175, 2769, 65536⟩
    (by decide) selected_cut_25922

theorem unmarked_context_11_22043_655971 : frontier 10 ⟨655971, by decide⟩
    (prefixCache 11 22043) (prefixPartial 11 22043) = false := by
  decide +kernel

theorem node_context_11_22043_655971 : EJMOriginalGlobalDAGData.nodes 10 ⟨655971, by decide⟩ =
    .split (coordinate 11) (![⟨655847, by decide⟩,⟨655900, by decide⟩,⟨655935, by decide⟩,⟨655970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22043_655971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22043 ⟨655971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22043
    ⟨655971, by decide⟩ (by decide) (![⟨655847, by decide⟩,⟨655900, by decide⟩,⟨655935, by decide⟩,⟨655970, by decide⟩]) unmarked_context_11_22043_655971 node_context_11_22043_655971
  intro a
  fin_cases a
  · exact context_12_88172_655847
  · exact context_12_88173_655900
  · exact context_12_88174_655935
  · exact context_12_88175_655970

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
