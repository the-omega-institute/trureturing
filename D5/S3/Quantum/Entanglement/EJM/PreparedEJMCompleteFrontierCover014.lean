/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover013
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_4612_49588 : frontier 9 ⟨49588, by decide⟩
    (prefixCache 12 4612) (prefixPartial 12 4612) = false := by
  decide +kernel

theorem node_context_12_4612_49588 : EJMOriginalGlobalDAGData.nodes 9 ⟨49588, by decide⟩ =
    .split (coordinate 12) (![⟨49344, by decide⟩,⟨49471, by decide⟩,⟨49556, by decide⟩,⟨49587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4612_49588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4612 ⟨49588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4612
    ⟨49588, by decide⟩ (by decide) (![⟨49344, by decide⟩,⟨49471, by decide⟩,⟨49556, by decide⟩,⟨49587, by decide⟩]) unmarked_context_12_4612_49588 node_context_12_4612_49588
  intro a
  fin_cases a
  · exact context_13_18448_49344
  · exact context_13_18449_49471
  · exact context_13_18450_49556
  · exact context_13_18451_49587

theorem selected_cut_01346 : selected 8 ⟨49663, by decide⟩
    (prefixPartial 13 18452) = some ⟨13, 2, 0, 49663, 18452, 3889, 16384⟩ := by
  decide +kernel

theorem context_13_18452_49663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18452 ⟨49663, by decide⟩ :=
  accepted_of_selected 13 18452 ⟨49663, by decide⟩ ⟨13, 2, 0, 49663, 18452, 3889, 16384⟩
    (by decide) selected_cut_01346

theorem selected_cut_01347 : selected 7 ⟨49682, by decide⟩
    (prefixPartial 14 73812) = some ⟨14, 2, 0, 49682, 73812, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_73812_49682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73812 ⟨49682, by decide⟩ :=
  accepted_of_selected 14 73812 ⟨49682, by decide⟩ ⟨14, 2, 0, 49682, 73812, 1121, 4096⟩
    (by decide) selected_cut_01347

theorem selected_cut_01348 : selected 7 ⟨49692, by decide⟩
    (prefixPartial 14 73813) = some ⟨14, 2, 0, 49692, 73813, 937, 4096⟩ := by
  decide +kernel

theorem context_14_73813_49692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73813 ⟨49692, by decide⟩ :=
  accepted_of_selected 14 73813 ⟨49692, by decide⟩ ⟨14, 2, 0, 49692, 73813, 937, 4096⟩
    (by decide) selected_cut_01348

theorem selected_cut_01349 : selected 7 ⟨49708, by decide⟩
    (prefixPartial 14 73814) = some ⟨14, 2, 0, 49708, 73814, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_73814_49708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73814 ⟨49708, by decide⟩ :=
  accepted_of_selected 14 73814 ⟨49708, by decide⟩ ⟨14, 2, 0, 49708, 73814, 1093, 4096⟩
    (by decide) selected_cut_01349

theorem selected_cut_01350 : selected 7 ⟨49720, by decide⟩
    (prefixPartial 14 73815) = some ⟨14, 2, 0, 49720, 73815, 985, 4096⟩ := by
  decide +kernel

theorem context_14_73815_49720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73815 ⟨49720, by decide⟩ :=
  accepted_of_selected 14 73815 ⟨49720, by decide⟩ ⟨14, 2, 0, 49720, 73815, 985, 4096⟩
    (by decide) selected_cut_01350

theorem unmarked_context_13_18453_49721 : frontier 8 ⟨49721, by decide⟩
    (prefixCache 13 18453) (prefixPartial 13 18453) = false := by
  decide +kernel

theorem node_context_13_18453_49721 : EJMOriginalGlobalDAGData.nodes 8 ⟨49721, by decide⟩ =
    .split (coordinate 13) (![⟨49682, by decide⟩,⟨49692, by decide⟩,⟨49708, by decide⟩,⟨49720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18453_49721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18453 ⟨49721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18453
    ⟨49721, by decide⟩ (by decide) (![⟨49682, by decide⟩,⟨49692, by decide⟩,⟨49708, by decide⟩,⟨49720, by decide⟩]) unmarked_context_13_18453_49721 node_context_13_18453_49721
  intro a
  fin_cases a
  · exact context_14_73812_49682
  · exact context_14_73813_49692
  · exact context_14_73814_49708
  · exact context_14_73815_49720

theorem selected_cut_01351 : selected 8 ⟨49763, by decide⟩
    (prefixPartial 13 18454) = some ⟨13, 2, 0, 49763, 18454, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_18454_49763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18454 ⟨49763, by decide⟩ :=
  accepted_of_selected 13 18454 ⟨49763, by decide⟩ ⟨13, 2, 0, 49763, 18454, 2525, 16384⟩
    (by decide) selected_cut_01351

theorem selected_cut_01352 : selected 8 ⟨49780, by decide⟩
    (prefixPartial 13 18455) = some ⟨13, 2, 0, 49780, 18455, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_18455_49780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18455 ⟨49780, by decide⟩ :=
  accepted_of_selected 13 18455 ⟨49780, by decide⟩ ⟨13, 2, 0, 49780, 18455, 1241, 16384⟩
    (by decide) selected_cut_01352

theorem unmarked_context_12_4613_49781 : frontier 9 ⟨49781, by decide⟩
    (prefixCache 12 4613) (prefixPartial 12 4613) = false := by
  decide +kernel

theorem node_context_12_4613_49781 : EJMOriginalGlobalDAGData.nodes 9 ⟨49781, by decide⟩ =
    .split (coordinate 12) (![⟨49663, by decide⟩,⟨49721, by decide⟩,⟨49763, by decide⟩,⟨49780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4613_49781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4613 ⟨49781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4613
    ⟨49781, by decide⟩ (by decide) (![⟨49663, by decide⟩,⟨49721, by decide⟩,⟨49763, by decide⟩,⟨49780, by decide⟩]) unmarked_context_12_4613_49781 node_context_12_4613_49781
  intro a
  fin_cases a
  · exact context_13_18452_49663
  · exact context_13_18453_49721
  · exact context_13_18454_49763
  · exact context_13_18455_49780

theorem selected_cut_01353 : selected 8 ⟨49861, by decide⟩
    (prefixPartial 13 18456) = some ⟨13, 2, 0, 49861, 18456, 3889, 16384⟩ := by
  decide +kernel

theorem context_13_18456_49861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18456 ⟨49861, by decide⟩ :=
  accepted_of_selected 13 18456 ⟨49861, by decide⟩ ⟨13, 2, 0, 49861, 18456, 3889, 16384⟩
    (by decide) selected_cut_01353

theorem selected_cut_01354 : selected 8 ⟨49919, by decide⟩
    (prefixPartial 13 18457) = some ⟨13, 2, 0, 49919, 18457, 3909, 16384⟩ := by
  decide +kernel

theorem context_13_18457_49919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18457 ⟨49919, by decide⟩ :=
  accepted_of_selected 13 18457 ⟨49919, by decide⟩ ⟨13, 2, 0, 49919, 18457, 3909, 16384⟩
    (by decide) selected_cut_01354

theorem selected_cut_01355 : selected 8 ⟨49953, by decide⟩
    (prefixPartial 13 18458) = some ⟨13, 2, 0, 49953, 18458, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_18458_49953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18458 ⟨49953, by decide⟩ :=
  accepted_of_selected 13 18458 ⟨49953, by decide⟩ ⟨13, 2, 0, 49953, 18458, 2381, 16384⟩
    (by decide) selected_cut_01355

theorem selected_cut_01356 : selected 8 ⟨49966, by decide⟩
    (prefixPartial 13 18459) = some ⟨13, 2, 0, 49966, 18459, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_18459_49966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18459 ⟨49966, by decide⟩ :=
  accepted_of_selected 13 18459 ⟨49966, by decide⟩ ⟨13, 2, 0, 49966, 18459, 1321, 16384⟩
    (by decide) selected_cut_01356

theorem unmarked_context_12_4614_49967 : frontier 9 ⟨49967, by decide⟩
    (prefixCache 12 4614) (prefixPartial 12 4614) = false := by
  decide +kernel

theorem node_context_12_4614_49967 : EJMOriginalGlobalDAGData.nodes 9 ⟨49967, by decide⟩ =
    .split (coordinate 12) (![⟨49861, by decide⟩,⟨49919, by decide⟩,⟨49953, by decide⟩,⟨49966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4614_49967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4614 ⟨49967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4614
    ⟨49967, by decide⟩ (by decide) (![⟨49861, by decide⟩,⟨49919, by decide⟩,⟨49953, by decide⟩,⟨49966, by decide⟩]) unmarked_context_12_4614_49967 node_context_12_4614_49967
  intro a
  fin_cases a
  · exact context_13_18456_49861
  · exact context_13_18457_49919
  · exact context_13_18458_49953
  · exact context_13_18459_49966

theorem selected_cut_01357 : selected 7 ⟨49985, by decide⟩
    (prefixPartial 14 73840) = some ⟨14, 2, 0, 49985, 73840, 989, 4096⟩ := by
  decide +kernel

theorem context_14_73840_49985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73840 ⟨49985, by decide⟩ :=
  accepted_of_selected 14 73840 ⟨49985, by decide⟩ ⟨14, 2, 0, 49985, 73840, 989, 4096⟩
    (by decide) selected_cut_01357

theorem selected_cut_01358 : selected 7 ⟨50000, by decide⟩
    (prefixPartial 14 73841) = some ⟨14, 2, 0, 50000, 73841, 905, 4096⟩ := by
  decide +kernel

theorem context_14_73841_50000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73841 ⟨50000, by decide⟩ :=
  accepted_of_selected 14 73841 ⟨50000, by decide⟩ ⟨14, 2, 0, 50000, 73841, 905, 4096⟩
    (by decide) selected_cut_01358

theorem selected_cut_01359 : selected 7 ⟨50025, by decide⟩
    (prefixPartial 14 73842) = some ⟨14, 2, 0, 50025, 73842, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_73842_50025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73842 ⟨50025, by decide⟩ :=
  accepted_of_selected 14 73842 ⟨50025, by decide⟩ ⟨14, 2, 0, 50025, 73842, 1181, 4096⟩
    (by decide) selected_cut_01359

theorem selected_cut_01360 : selected 7 ⟨50045, by decide⟩
    (prefixPartial 14 73843) = some ⟨14, 2, 0, 50045, 73843, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_73843_50045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73843 ⟨50045, by decide⟩ :=
  accepted_of_selected 14 73843 ⟨50045, by decide⟩ ⟨14, 2, 0, 50045, 73843, 1229, 4096⟩
    (by decide) selected_cut_01360

theorem unmarked_context_13_18460_50046 : frontier 8 ⟨50046, by decide⟩
    (prefixCache 13 18460) (prefixPartial 13 18460) = false := by
  decide +kernel

theorem node_context_13_18460_50046 : EJMOriginalGlobalDAGData.nodes 8 ⟨50046, by decide⟩ =
    .split (coordinate 13) (![⟨49985, by decide⟩,⟨50000, by decide⟩,⟨50025, by decide⟩,⟨50045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18460_50046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18460 ⟨50046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18460
    ⟨50046, by decide⟩ (by decide) (![⟨49985, by decide⟩,⟨50000, by decide⟩,⟨50025, by decide⟩,⟨50045, by decide⟩]) unmarked_context_13_18460_50046 node_context_13_18460_50046
  intro a
  fin_cases a
  · exact context_14_73840_49985
  · exact context_14_73841_50000
  · exact context_14_73842_50025
  · exact context_14_73843_50045

theorem selected_cut_01361 : selected 7 ⟨50067, by decide⟩
    (prefixPartial 14 73844) = some ⟨14, 2, 0, 50067, 73844, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_73844_50067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73844 ⟨50067, by decide⟩ :=
  accepted_of_selected 14 73844 ⟨50067, by decide⟩ ⟨14, 2, 0, 50067, 73844, 1249, 4096⟩
    (by decide) selected_cut_01361

theorem selected_cut_01362 : selected 7 ⟨50083, by decide⟩
    (prefixPartial 14 73845) = some ⟨14, 2, 0, 50083, 73845, 989, 4096⟩ := by
  decide +kernel

theorem context_14_73845_50083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73845 ⟨50083, by decide⟩ :=
  accepted_of_selected 14 73845 ⟨50083, by decide⟩ ⟨14, 2, 0, 50083, 73845, 989, 4096⟩
    (by decide) selected_cut_01362

theorem selected_cut_01363 : selected 7 ⟨50098, by decide⟩
    (prefixPartial 14 73846) = some ⟨14, 2, 0, 50098, 73846, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_73846_50098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73846 ⟨50098, by decide⟩ :=
  accepted_of_selected 14 73846 ⟨50098, by decide⟩ ⟨14, 2, 0, 50098, 73846, 1049, 4096⟩
    (by decide) selected_cut_01363

theorem selected_cut_01364 : selected 7 ⟨50113, by decide⟩
    (prefixPartial 14 73847) = some ⟨14, 2, 0, 50113, 73847, 961, 4096⟩ := by
  decide +kernel

theorem context_14_73847_50113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73847 ⟨50113, by decide⟩ :=
  accepted_of_selected 14 73847 ⟨50113, by decide⟩ ⟨14, 2, 0, 50113, 73847, 961, 4096⟩
    (by decide) selected_cut_01364

theorem unmarked_context_13_18461_50114 : frontier 8 ⟨50114, by decide⟩
    (prefixCache 13 18461) (prefixPartial 13 18461) = false := by
  decide +kernel

theorem node_context_13_18461_50114 : EJMOriginalGlobalDAGData.nodes 8 ⟨50114, by decide⟩ =
    .split (coordinate 13) (![⟨50067, by decide⟩,⟨50083, by decide⟩,⟨50098, by decide⟩,⟨50113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18461_50114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18461 ⟨50114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18461
    ⟨50114, by decide⟩ (by decide) (![⟨50067, by decide⟩,⟨50083, by decide⟩,⟨50098, by decide⟩,⟨50113, by decide⟩]) unmarked_context_13_18461_50114 node_context_13_18461_50114
  intro a
  fin_cases a
  · exact context_14_73844_50067
  · exact context_14_73845_50083
  · exact context_14_73846_50098
  · exact context_14_73847_50113

theorem selected_cut_01365 : selected 8 ⟨50165, by decide⟩
    (prefixPartial 13 18462) = some ⟨13, 2, 0, 50165, 18462, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_18462_50165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18462 ⟨50165, by decide⟩ :=
  accepted_of_selected 13 18462 ⟨50165, by decide⟩ ⟨13, 2, 0, 50165, 18462, 2785, 16384⟩
    (by decide) selected_cut_01365

theorem selected_cut_01366 : selected 8 ⟨50177, by decide⟩
    (prefixPartial 13 18463) = some ⟨13, 2, 0, 50177, 18463, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_18463_50177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18463 ⟨50177, by decide⟩ :=
  accepted_of_selected 13 18463 ⟨50177, by decide⟩ ⟨13, 2, 0, 50177, 18463, 1265, 16384⟩
    (by decide) selected_cut_01366

theorem unmarked_context_12_4615_50178 : frontier 9 ⟨50178, by decide⟩
    (prefixCache 12 4615) (prefixPartial 12 4615) = false := by
  decide +kernel

theorem node_context_12_4615_50178 : EJMOriginalGlobalDAGData.nodes 9 ⟨50178, by decide⟩ =
    .split (coordinate 12) (![⟨50046, by decide⟩,⟨50114, by decide⟩,⟨50165, by decide⟩,⟨50177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4615_50178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4615 ⟨50178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4615
    ⟨50178, by decide⟩ (by decide) (![⟨50046, by decide⟩,⟨50114, by decide⟩,⟨50165, by decide⟩,⟨50177, by decide⟩]) unmarked_context_12_4615_50178 node_context_12_4615_50178
  intro a
  fin_cases a
  · exact context_13_18460_50046
  · exact context_13_18461_50114
  · exact context_13_18462_50165
  · exact context_13_18463_50177

theorem unmarked_context_11_1153_50179 : frontier 10 ⟨50179, by decide⟩
    (prefixCache 11 1153) (prefixPartial 11 1153) = false := by
  decide +kernel

theorem node_context_11_1153_50179 : EJMOriginalGlobalDAGData.nodes 10 ⟨50179, by decide⟩ =
    .split (coordinate 11) (![⟨49588, by decide⟩,⟨49781, by decide⟩,⟨49967, by decide⟩,⟨50178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1153_50179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1153 ⟨50179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1153
    ⟨50179, by decide⟩ (by decide) (![⟨49588, by decide⟩,⟨49781, by decide⟩,⟨49967, by decide⟩,⟨50178, by decide⟩]) unmarked_context_11_1153_50179 node_context_11_1153_50179
  intro a
  fin_cases a
  · exact context_12_4612_49588
  · exact context_12_4613_49781
  · exact context_12_4614_49967
  · exact context_12_4615_50178

theorem selected_cut_01367 : selected 9 ⟨50180, by decide⟩
    (prefixPartial 12 4616) = some ⟨12, 1, 0, 50180, 4616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4616_50180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4616 ⟨50180, by decide⟩ :=
  accepted_of_selected 12 4616 ⟨50180, by decide⟩ ⟨12, 1, 0, 50180, 4616, 1, 65536⟩
    (by decide) selected_cut_01367

theorem selected_cut_01368 : selected 8 ⟨50252, by decide⟩
    (prefixPartial 13 18468) = some ⟨13, 2, 0, 50252, 18468, 3753, 16384⟩ := by
  decide +kernel

theorem context_13_18468_50252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18468 ⟨50252, by decide⟩ :=
  accepted_of_selected 13 18468 ⟨50252, by decide⟩ ⟨13, 2, 0, 50252, 18468, 3753, 16384⟩
    (by decide) selected_cut_01368

theorem selected_cut_01369 : selected 8 ⟨50309, by decide⟩
    (prefixPartial 13 18469) = some ⟨13, 2, 0, 50309, 18469, 3817, 16384⟩ := by
  decide +kernel

theorem context_13_18469_50309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18469 ⟨50309, by decide⟩ :=
  accepted_of_selected 13 18469 ⟨50309, by decide⟩ ⟨13, 2, 0, 50309, 18469, 3817, 16384⟩
    (by decide) selected_cut_01369

theorem selected_cut_01370 : selected 8 ⟨50344, by decide⟩
    (prefixPartial 13 18470) = some ⟨13, 2, 0, 50344, 18470, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_18470_50344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18470 ⟨50344, by decide⟩ :=
  accepted_of_selected 13 18470 ⟨50344, by decide⟩ ⟨13, 2, 0, 50344, 18470, 2477, 16384⟩
    (by decide) selected_cut_01370

theorem selected_cut_01371 : selected 8 ⟨50359, by decide⟩
    (prefixPartial 13 18471) = some ⟨13, 2, 0, 50359, 18471, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_18471_50359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18471 ⟨50359, by decide⟩ :=
  accepted_of_selected 13 18471 ⟨50359, by decide⟩ ⟨13, 2, 0, 50359, 18471, 1225, 16384⟩
    (by decide) selected_cut_01371

theorem unmarked_context_12_4617_50360 : frontier 9 ⟨50360, by decide⟩
    (prefixCache 12 4617) (prefixPartial 12 4617) = false := by
  decide +kernel

theorem node_context_12_4617_50360 : EJMOriginalGlobalDAGData.nodes 9 ⟨50360, by decide⟩ =
    .split (coordinate 12) (![⟨50252, by decide⟩,⟨50309, by decide⟩,⟨50344, by decide⟩,⟨50359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4617_50360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4617 ⟨50360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4617
    ⟨50360, by decide⟩ (by decide) (![⟨50252, by decide⟩,⟨50309, by decide⟩,⟨50344, by decide⟩,⟨50359, by decide⟩]) unmarked_context_12_4617_50360 node_context_12_4617_50360
  intro a
  fin_cases a
  · exact context_13_18468_50252
  · exact context_13_18469_50309
  · exact context_13_18470_50344
  · exact context_13_18471_50359

theorem selected_cut_01372 : selected 7 ⟨50392, by decide⟩
    (prefixPartial 14 73888) = some ⟨14, 2, 0, 50392, 73888, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_73888_50392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73888 ⟨50392, by decide⟩ :=
  accepted_of_selected 14 73888 ⟨50392, by decide⟩ ⟨14, 2, 0, 50392, 73888, 1009, 4096⟩
    (by decide) selected_cut_01372

theorem selected_cut_01373 : selected 7 ⟨50414, by decide⟩
    (prefixPartial 14 73889) = some ⟨14, 2, 0, 50414, 73889, 1533, 4096⟩ := by
  decide +kernel

theorem context_14_73889_50414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73889 ⟨50414, by decide⟩ :=
  accepted_of_selected 14 73889 ⟨50414, by decide⟩ ⟨14, 2, 0, 50414, 73889, 1533, 4096⟩
    (by decide) selected_cut_01373

theorem selected_cut_01374 : selected 7 ⟨50433, by decide⟩
    (prefixPartial 14 73890) = some ⟨14, 2, 0, 50433, 73890, 1513, 4096⟩ := by
  decide +kernel

theorem context_14_73890_50433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73890 ⟨50433, by decide⟩ :=
  accepted_of_selected 14 73890 ⟨50433, by decide⟩ ⟨14, 2, 0, 50433, 73890, 1513, 4096⟩
    (by decide) selected_cut_01374

theorem selected_cut_01375 : selected 7 ⟨50454, by decide⟩
    (prefixPartial 14 73891) = some ⟨14, 2, 0, 50454, 73891, 1557, 4096⟩ := by
  decide +kernel

theorem context_14_73891_50454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73891 ⟨50454, by decide⟩ :=
  accepted_of_selected 14 73891 ⟨50454, by decide⟩ ⟨14, 2, 0, 50454, 73891, 1557, 4096⟩
    (by decide) selected_cut_01375

theorem unmarked_context_13_18472_50455 : frontier 8 ⟨50455, by decide⟩
    (prefixCache 13 18472) (prefixPartial 13 18472) = false := by
  decide +kernel

theorem node_context_13_18472_50455 : EJMOriginalGlobalDAGData.nodes 8 ⟨50455, by decide⟩ =
    .split (coordinate 13) (![⟨50392, by decide⟩,⟨50414, by decide⟩,⟨50433, by decide⟩,⟨50454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18472_50455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18472 ⟨50455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18472
    ⟨50455, by decide⟩ (by decide) (![⟨50392, by decide⟩,⟨50414, by decide⟩,⟨50433, by decide⟩,⟨50454, by decide⟩]) unmarked_context_13_18472_50455 node_context_13_18472_50455
  intro a
  fin_cases a
  · exact context_14_73888_50392
  · exact context_14_73889_50414
  · exact context_14_73890_50433
  · exact context_14_73891_50454

theorem selected_cut_01376 : selected 7 ⟨50482, by decide⟩
    (prefixPartial 14 73892) = some ⟨14, 2, 0, 50482, 73892, 1657, 4096⟩ := by
  decide +kernel

theorem context_14_73892_50482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73892 ⟨50482, by decide⟩ :=
  accepted_of_selected 14 73892 ⟨50482, by decide⟩ ⟨14, 2, 0, 50482, 73892, 1657, 4096⟩
    (by decide) selected_cut_01376

theorem selected_cut_01377 : selected 7 ⟨50514, by decide⟩
    (prefixPartial 14 73893) = some ⟨14, 2, 0, 50514, 73893, 1597, 4096⟩ := by
  decide +kernel

theorem context_14_73893_50514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73893 ⟨50514, by decide⟩ :=
  accepted_of_selected 14 73893 ⟨50514, by decide⟩ ⟨14, 2, 0, 50514, 73893, 1597, 4096⟩
    (by decide) selected_cut_01377

theorem selected_cut_01378 : selected 7 ⟨50536, by decide⟩
    (prefixPartial 14 73894) = some ⟨14, 2, 0, 50536, 73894, 1465, 4096⟩ := by
  decide +kernel

theorem context_14_73894_50536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73894 ⟨50536, by decide⟩ :=
  accepted_of_selected 14 73894 ⟨50536, by decide⟩ ⟨14, 2, 0, 50536, 73894, 1465, 4096⟩
    (by decide) selected_cut_01378

theorem selected_cut_01379 : selected 7 ⟨50564, by decide⟩
    (prefixPartial 14 73895) = some ⟨14, 2, 0, 50564, 73895, 1445, 4096⟩ := by
  decide +kernel

theorem context_14_73895_50564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73895 ⟨50564, by decide⟩ :=
  accepted_of_selected 14 73895 ⟨50564, by decide⟩ ⟨14, 2, 0, 50564, 73895, 1445, 4096⟩
    (by decide) selected_cut_01379

theorem unmarked_context_13_18473_50565 : frontier 8 ⟨50565, by decide⟩
    (prefixCache 13 18473) (prefixPartial 13 18473) = false := by
  decide +kernel

theorem node_context_13_18473_50565 : EJMOriginalGlobalDAGData.nodes 8 ⟨50565, by decide⟩ =
    .split (coordinate 13) (![⟨50482, by decide⟩,⟨50514, by decide⟩,⟨50536, by decide⟩,⟨50564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18473_50565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18473 ⟨50565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18473
    ⟨50565, by decide⟩ (by decide) (![⟨50482, by decide⟩,⟨50514, by decide⟩,⟨50536, by decide⟩,⟨50564, by decide⟩]) unmarked_context_13_18473_50565 node_context_13_18473_50565
  intro a
  fin_cases a
  · exact context_14_73892_50482
  · exact context_14_73893_50514
  · exact context_14_73894_50536
  · exact context_14_73895_50564

theorem selected_cut_01380 : selected 8 ⟨50654, by decide⟩
    (prefixPartial 13 18474) = some ⟨13, 2, 0, 50654, 18474, 3981, 16384⟩ := by
  decide +kernel

theorem context_13_18474_50654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18474 ⟨50654, by decide⟩ :=
  accepted_of_selected 13 18474 ⟨50654, by decide⟩ ⟨13, 2, 0, 50654, 18474, 3981, 16384⟩
    (by decide) selected_cut_01380

theorem selected_cut_01381 : selected 8 ⟨50705, by decide⟩
    (prefixPartial 13 18475) = some ⟨13, 2, 0, 50705, 18475, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_18475_50705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18475 ⟨50705, by decide⟩ :=
  accepted_of_selected 13 18475 ⟨50705, by decide⟩ ⟨13, 2, 0, 50705, 18475, 1769, 16384⟩
    (by decide) selected_cut_01381

theorem unmarked_context_12_4618_50706 : frontier 9 ⟨50706, by decide⟩
    (prefixCache 12 4618) (prefixPartial 12 4618) = false := by
  decide +kernel

theorem node_context_12_4618_50706 : EJMOriginalGlobalDAGData.nodes 9 ⟨50706, by decide⟩ =
    .split (coordinate 12) (![⟨50455, by decide⟩,⟨50565, by decide⟩,⟨50654, by decide⟩,⟨50705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4618_50706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4618 ⟨50706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4618
    ⟨50706, by decide⟩ (by decide) (![⟨50455, by decide⟩,⟨50565, by decide⟩,⟨50654, by decide⟩,⟨50705, by decide⟩]) unmarked_context_12_4618_50706 node_context_12_4618_50706
  intro a
  fin_cases a
  · exact context_13_18472_50455
  · exact context_13_18473_50565
  · exact context_13_18474_50654
  · exact context_13_18475_50705

theorem selected_cut_01382 : selected 8 ⟨50770, by decide⟩
    (prefixPartial 13 18476) = some ⟨13, 2, 0, 50770, 18476, 3393, 16384⟩ := by
  decide +kernel

theorem context_13_18476_50770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18476 ⟨50770, by decide⟩ :=
  accepted_of_selected 13 18476 ⟨50770, by decide⟩ ⟨13, 2, 0, 50770, 18476, 3393, 16384⟩
    (by decide) selected_cut_01382

theorem selected_cut_01383 : selected 8 ⟨50825, by decide⟩
    (prefixPartial 13 18477) = some ⟨13, 2, 0, 50825, 18477, 4041, 16384⟩ := by
  decide +kernel

theorem context_13_18477_50825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18477 ⟨50825, by decide⟩ :=
  accepted_of_selected 13 18477 ⟨50825, by decide⟩ ⟨13, 2, 0, 50825, 18477, 4041, 16384⟩
    (by decide) selected_cut_01383

theorem selected_cut_01384 : selected 8 ⟨50857, by decide⟩
    (prefixPartial 13 18478) = some ⟨13, 2, 0, 50857, 18478, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_18478_50857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18478 ⟨50857, by decide⟩ :=
  accepted_of_selected 13 18478 ⟨50857, by decide⟩ ⟨13, 2, 0, 50857, 18478, 2445, 16384⟩
    (by decide) selected_cut_01384

theorem selected_cut_01385 : selected 8 ⟨50870, by decide⟩
    (prefixPartial 13 18479) = some ⟨13, 2, 0, 50870, 18479, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_18479_50870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18479 ⟨50870, by decide⟩ :=
  accepted_of_selected 13 18479 ⟨50870, by decide⟩ ⟨13, 2, 0, 50870, 18479, 1217, 16384⟩
    (by decide) selected_cut_01385

theorem unmarked_context_12_4619_50871 : frontier 9 ⟨50871, by decide⟩
    (prefixCache 12 4619) (prefixPartial 12 4619) = false := by
  decide +kernel

theorem node_context_12_4619_50871 : EJMOriginalGlobalDAGData.nodes 9 ⟨50871, by decide⟩ =
    .split (coordinate 12) (![⟨50770, by decide⟩,⟨50825, by decide⟩,⟨50857, by decide⟩,⟨50870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4619_50871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4619 ⟨50871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4619
    ⟨50871, by decide⟩ (by decide) (![⟨50770, by decide⟩,⟨50825, by decide⟩,⟨50857, by decide⟩,⟨50870, by decide⟩]) unmarked_context_12_4619_50871 node_context_12_4619_50871
  intro a
  fin_cases a
  · exact context_13_18476_50770
  · exact context_13_18477_50825
  · exact context_13_18478_50857
  · exact context_13_18479_50870

theorem unmarked_context_11_1154_50872 : frontier 10 ⟨50872, by decide⟩
    (prefixCache 11 1154) (prefixPartial 11 1154) = false := by
  decide +kernel

theorem node_context_11_1154_50872 : EJMOriginalGlobalDAGData.nodes 10 ⟨50872, by decide⟩ =
    .split (coordinate 11) (![⟨50180, by decide⟩,⟨50360, by decide⟩,⟨50706, by decide⟩,⟨50871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1154_50872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1154 ⟨50872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1154
    ⟨50872, by decide⟩ (by decide) (![⟨50180, by decide⟩,⟨50360, by decide⟩,⟨50706, by decide⟩,⟨50871, by decide⟩]) unmarked_context_11_1154_50872 node_context_11_1154_50872
  intro a
  fin_cases a
  · exact context_12_4616_50180
  · exact context_12_4617_50360
  · exact context_12_4618_50706
  · exact context_12_4619_50871

theorem selected_cut_01386 : selected 8 ⟨50923, by decide⟩
    (prefixPartial 13 18480) = some ⟨13, 2, 0, 50923, 18480, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_18480_50923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18480 ⟨50923, by decide⟩ :=
  accepted_of_selected 13 18480 ⟨50923, by decide⟩ ⟨13, 2, 0, 50923, 18480, 1165, 16384⟩
    (by decide) selected_cut_01386

theorem selected_cut_01387 : selected 7 ⟨50983, by decide⟩
    (prefixPartial 14 73924) = some ⟨14, 2, 0, 50983, 73924, 2005, 4096⟩ := by
  decide +kernel

theorem context_14_73924_50983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73924 ⟨50983, by decide⟩ :=
  accepted_of_selected 14 73924 ⟨50983, by decide⟩ ⟨14, 2, 0, 50983, 73924, 2005, 4096⟩
    (by decide) selected_cut_01387

theorem selected_cut_01388 : selected 7 ⟨51017, by decide⟩
    (prefixPartial 14 73925) = some ⟨14, 2, 0, 51017, 73925, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_73925_51017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73925 ⟨51017, by decide⟩ :=
  accepted_of_selected 14 73925 ⟨51017, by decide⟩ ⟨14, 2, 0, 51017, 73925, 1061, 4096⟩
    (by decide) selected_cut_01388

theorem selected_cut_01389 : selected 7 ⟨51046, by decide⟩
    (prefixPartial 14 73926) = some ⟨14, 2, 0, 51046, 73926, 869, 4096⟩ := by
  decide +kernel

theorem context_14_73926_51046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73926 ⟨51046, by decide⟩ :=
  accepted_of_selected 14 73926 ⟨51046, by decide⟩ ⟨14, 2, 0, 51046, 73926, 869, 4096⟩
    (by decide) selected_cut_01389

theorem selected_cut_01390 : selected 7 ⟨51070, by decide⟩
    (prefixPartial 14 73927) = some ⟨14, 2, 0, 51070, 73927, 861, 4096⟩ := by
  decide +kernel

theorem context_14_73927_51070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73927 ⟨51070, by decide⟩ :=
  accepted_of_selected 14 73927 ⟨51070, by decide⟩ ⟨14, 2, 0, 51070, 73927, 861, 4096⟩
    (by decide) selected_cut_01390

theorem unmarked_context_13_18481_51071 : frontier 8 ⟨51071, by decide⟩
    (prefixCache 13 18481) (prefixPartial 13 18481) = false := by
  decide +kernel

theorem node_context_13_18481_51071 : EJMOriginalGlobalDAGData.nodes 8 ⟨51071, by decide⟩ =
    .split (coordinate 13) (![⟨50983, by decide⟩,⟨51017, by decide⟩,⟨51046, by decide⟩,⟨51070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18481_51071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18481 ⟨51071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18481
    ⟨51071, by decide⟩ (by decide) (![⟨50983, by decide⟩,⟨51017, by decide⟩,⟨51046, by decide⟩,⟨51070, by decide⟩]) unmarked_context_13_18481_51071 node_context_13_18481_51071
  intro a
  fin_cases a
  · exact context_14_73924_50983
  · exact context_14_73925_51017
  · exact context_14_73926_51046
  · exact context_14_73927_51070

theorem selected_cut_01391 : selected 8 ⟨51128, by decide⟩
    (prefixPartial 13 18482) = some ⟨13, 2, 0, 51128, 18482, 781, 16384⟩ := by
  decide +kernel

theorem context_13_18482_51128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18482 ⟨51128, by decide⟩ :=
  accepted_of_selected 13 18482 ⟨51128, by decide⟩ ⟨13, 2, 0, 51128, 18482, 781, 16384⟩
    (by decide) selected_cut_01391

theorem selected_cut_01392 : selected 8 ⟨51129, by decide⟩
    (prefixPartial 13 18483) = some ⟨13, 1, 0, 51129, 18483, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18483_51129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18483 ⟨51129, by decide⟩ :=
  accepted_of_selected 13 18483 ⟨51129, by decide⟩ ⟨13, 1, 0, 51129, 18483, 1, 16384⟩
    (by decide) selected_cut_01392

theorem unmarked_context_12_4620_51130 : frontier 9 ⟨51130, by decide⟩
    (prefixCache 12 4620) (prefixPartial 12 4620) = false := by
  decide +kernel

theorem node_context_12_4620_51130 : EJMOriginalGlobalDAGData.nodes 9 ⟨51130, by decide⟩ =
    .split (coordinate 12) (![⟨50923, by decide⟩,⟨51071, by decide⟩,⟨51128, by decide⟩,⟨51129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4620_51130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4620 ⟨51130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4620
    ⟨51130, by decide⟩ (by decide) (![⟨50923, by decide⟩,⟨51071, by decide⟩,⟨51128, by decide⟩,⟨51129, by decide⟩]) unmarked_context_12_4620_51130 node_context_12_4620_51130
  intro a
  fin_cases a
  · exact context_13_18480_50923
  · exact context_13_18481_51071
  · exact context_13_18482_51128
  · exact context_13_18483_51129

theorem selected_cut_01393 : selected 8 ⟨51198, by decide⟩
    (prefixPartial 13 18484) = some ⟨13, 2, 0, 51198, 18484, 3273, 16384⟩ := by
  decide +kernel

theorem context_13_18484_51198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18484 ⟨51198, by decide⟩ :=
  accepted_of_selected 13 18484 ⟨51198, by decide⟩ ⟨13, 2, 0, 51198, 18484, 3273, 16384⟩
    (by decide) selected_cut_01393

theorem selected_cut_01394 : selected 8 ⟨51248, by decide⟩
    (prefixPartial 13 18485) = some ⟨13, 2, 0, 51248, 18485, 3873, 16384⟩ := by
  decide +kernel

theorem context_13_18485_51248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18485 ⟨51248, by decide⟩ :=
  accepted_of_selected 13 18485 ⟨51248, by decide⟩ ⟨13, 2, 0, 51248, 18485, 3873, 16384⟩
    (by decide) selected_cut_01394

theorem selected_cut_01395 : selected 8 ⟨51285, by decide⟩
    (prefixPartial 13 18486) = some ⟨13, 2, 0, 51285, 18486, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_18486_51285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18486 ⟨51285, by decide⟩ :=
  accepted_of_selected 13 18486 ⟨51285, by decide⟩ ⟨13, 2, 0, 51285, 18486, 2581, 16384⟩
    (by decide) selected_cut_01395

theorem selected_cut_01396 : selected 8 ⟨51294, by decide⟩
    (prefixPartial 13 18487) = some ⟨13, 2, 0, 51294, 18487, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_18487_51294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18487 ⟨51294, by decide⟩ :=
  accepted_of_selected 13 18487 ⟨51294, by decide⟩ ⟨13, 2, 0, 51294, 18487, 1217, 16384⟩
    (by decide) selected_cut_01396

theorem unmarked_context_12_4621_51295 : frontier 9 ⟨51295, by decide⟩
    (prefixCache 12 4621) (prefixPartial 12 4621) = false := by
  decide +kernel

theorem node_context_12_4621_51295 : EJMOriginalGlobalDAGData.nodes 9 ⟨51295, by decide⟩ =
    .split (coordinate 12) (![⟨51198, by decide⟩,⟨51248, by decide⟩,⟨51285, by decide⟩,⟨51294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4621_51295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4621 ⟨51295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4621
    ⟨51295, by decide⟩ (by decide) (![⟨51198, by decide⟩,⟨51248, by decide⟩,⟨51285, by decide⟩,⟨51294, by decide⟩]) unmarked_context_12_4621_51295 node_context_12_4621_51295
  intro a
  fin_cases a
  · exact context_13_18484_51198
  · exact context_13_18485_51248
  · exact context_13_18486_51285
  · exact context_13_18487_51294

theorem selected_cut_01397 : selected 8 ⟨51354, by decide⟩
    (prefixPartial 13 18488) = some ⟨13, 2, 0, 51354, 18488, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_18488_51354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18488 ⟨51354, by decide⟩ :=
  accepted_of_selected 13 18488 ⟨51354, by decide⟩ ⟨13, 2, 0, 51354, 18488, 3077, 16384⟩
    (by decide) selected_cut_01397

theorem selected_cut_01398 : selected 8 ⟨51405, by decide⟩
    (prefixPartial 13 18489) = some ⟨13, 2, 0, 51405, 18489, 3893, 16384⟩ := by
  decide +kernel

theorem context_13_18489_51405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18489 ⟨51405, by decide⟩ :=
  accepted_of_selected 13 18489 ⟨51405, by decide⟩ ⟨13, 2, 0, 51405, 18489, 3893, 16384⟩
    (by decide) selected_cut_01398

theorem selected_cut_01399 : selected 8 ⟨51426, by decide⟩
    (prefixPartial 13 18490) = some ⟨13, 2, 0, 51426, 18490, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_18490_51426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18490 ⟨51426, by decide⟩ :=
  accepted_of_selected 13 18490 ⟨51426, by decide⟩ ⟨13, 2, 0, 51426, 18490, 2333, 16384⟩
    (by decide) selected_cut_01399

theorem selected_cut_01400 : selected 8 ⟨51439, by decide⟩
    (prefixPartial 13 18491) = some ⟨13, 2, 0, 51439, 18491, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_18491_51439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18491 ⟨51439, by decide⟩ :=
  accepted_of_selected 13 18491 ⟨51439, by decide⟩ ⟨13, 2, 0, 51439, 18491, 1225, 16384⟩
    (by decide) selected_cut_01400

theorem unmarked_context_12_4622_51440 : frontier 9 ⟨51440, by decide⟩
    (prefixCache 12 4622) (prefixPartial 12 4622) = false := by
  decide +kernel

theorem node_context_12_4622_51440 : EJMOriginalGlobalDAGData.nodes 9 ⟨51440, by decide⟩ =
    .split (coordinate 12) (![⟨51354, by decide⟩,⟨51405, by decide⟩,⟨51426, by decide⟩,⟨51439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4622_51440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4622 ⟨51440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4622
    ⟨51440, by decide⟩ (by decide) (![⟨51354, by decide⟩,⟨51405, by decide⟩,⟨51426, by decide⟩,⟨51439, by decide⟩]) unmarked_context_12_4622_51440 node_context_12_4622_51440
  intro a
  fin_cases a
  · exact context_13_18488_51354
  · exact context_13_18489_51405
  · exact context_13_18490_51426
  · exact context_13_18491_51439

theorem selected_cut_01401 : selected 8 ⟨51494, by decide⟩
    (prefixPartial 13 18492) = some ⟨13, 2, 0, 51494, 18492, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_18492_51494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18492 ⟨51494, by decide⟩ :=
  accepted_of_selected 13 18492 ⟨51494, by decide⟩ ⟨13, 2, 0, 51494, 18492, 3157, 16384⟩
    (by decide) selected_cut_01401

theorem selected_cut_01402 : selected 8 ⟨51541, by decide⟩
    (prefixPartial 13 18493) = some ⟨13, 2, 0, 51541, 18493, 3809, 16384⟩ := by
  decide +kernel

theorem context_13_18493_51541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18493 ⟨51541, by decide⟩ :=
  accepted_of_selected 13 18493 ⟨51541, by decide⟩ ⟨13, 2, 0, 51541, 18493, 3809, 16384⟩
    (by decide) selected_cut_01402

theorem selected_cut_01403 : selected 8 ⟨51568, by decide⟩
    (prefixPartial 13 18494) = some ⟨13, 2, 0, 51568, 18494, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_18494_51568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18494 ⟨51568, by decide⟩ :=
  accepted_of_selected 13 18494 ⟨51568, by decide⟩ ⟨13, 2, 0, 51568, 18494, 2401, 16384⟩
    (by decide) selected_cut_01403

theorem selected_cut_01404 : selected 8 ⟨51582, by decide⟩
    (prefixPartial 13 18495) = some ⟨13, 2, 0, 51582, 18495, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_18495_51582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18495 ⟨51582, by decide⟩ :=
  accepted_of_selected 13 18495 ⟨51582, by decide⟩ ⟨13, 2, 0, 51582, 18495, 1253, 16384⟩
    (by decide) selected_cut_01404

theorem unmarked_context_12_4623_51583 : frontier 9 ⟨51583, by decide⟩
    (prefixCache 12 4623) (prefixPartial 12 4623) = false := by
  decide +kernel

theorem node_context_12_4623_51583 : EJMOriginalGlobalDAGData.nodes 9 ⟨51583, by decide⟩ =
    .split (coordinate 12) (![⟨51494, by decide⟩,⟨51541, by decide⟩,⟨51568, by decide⟩,⟨51582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4623_51583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4623 ⟨51583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4623
    ⟨51583, by decide⟩ (by decide) (![⟨51494, by decide⟩,⟨51541, by decide⟩,⟨51568, by decide⟩,⟨51582, by decide⟩]) unmarked_context_12_4623_51583 node_context_12_4623_51583
  intro a
  fin_cases a
  · exact context_13_18492_51494
  · exact context_13_18493_51541
  · exact context_13_18494_51568
  · exact context_13_18495_51582

theorem unmarked_context_11_1155_51584 : frontier 10 ⟨51584, by decide⟩
    (prefixCache 11 1155) (prefixPartial 11 1155) = false := by
  decide +kernel

theorem node_context_11_1155_51584 : EJMOriginalGlobalDAGData.nodes 10 ⟨51584, by decide⟩ =
    .split (coordinate 11) (![⟨51130, by decide⟩,⟨51295, by decide⟩,⟨51440, by decide⟩,⟨51583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1155_51584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1155 ⟨51584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1155
    ⟨51584, by decide⟩ (by decide) (![⟨51130, by decide⟩,⟨51295, by decide⟩,⟨51440, by decide⟩,⟨51583, by decide⟩]) unmarked_context_11_1155_51584 node_context_11_1155_51584
  intro a
  fin_cases a
  · exact context_12_4620_51130
  · exact context_12_4621_51295
  · exact context_12_4622_51440
  · exact context_12_4623_51583

theorem unmarked_context_10_288_51585 : frontier 11 ⟨51585, by decide⟩
    (prefixCache 10 288) (prefixPartial 10 288) = false := by
  decide +kernel

theorem node_context_10_288_51585 : EJMOriginalGlobalDAGData.nodes 11 ⟨51585, by decide⟩ =
    .split (coordinate 10) (![⟨49254, by decide⟩,⟨50179, by decide⟩,⟨50872, by decide⟩,⟨51584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_288_51585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 288 ⟨51585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 288
    ⟨51585, by decide⟩ (by decide) (![⟨49254, by decide⟩,⟨50179, by decide⟩,⟨50872, by decide⟩,⟨51584, by decide⟩]) unmarked_context_10_288_51585 node_context_10_288_51585
  intro a
  fin_cases a
  · exact context_11_1152_49254
  · exact context_11_1153_50179
  · exact context_11_1154_50872
  · exact context_11_1155_51584

theorem selected_cut_01405 : selected 8 ⟨51616, by decide⟩
    (prefixPartial 13 18496) = some ⟨13, 2, 0, 51616, 18496, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_18496_51616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18496 ⟨51616, by decide⟩ :=
  accepted_of_selected 13 18496 ⟨51616, by decide⟩ ⟨13, 2, 0, 51616, 18496, 1445, 16384⟩
    (by decide) selected_cut_01405

theorem selected_cut_01406 : selected 8 ⟨51644, by decide⟩
    (prefixPartial 13 18497) = some ⟨13, 2, 0, 51644, 18497, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_18497_51644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18497 ⟨51644, by decide⟩ :=
  accepted_of_selected 13 18497 ⟨51644, by decide⟩ ⟨13, 2, 0, 51644, 18497, 2181, 16384⟩
    (by decide) selected_cut_01406

theorem selected_cut_01407 : selected 8 ⟨51668, by decide⟩
    (prefixPartial 13 18498) = some ⟨13, 2, 0, 51668, 18498, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_18498_51668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18498 ⟨51668, by decide⟩ :=
  accepted_of_selected 13 18498 ⟨51668, by decide⟩ ⟨13, 2, 0, 51668, 18498, 1721, 16384⟩
    (by decide) selected_cut_01407

theorem selected_cut_01408 : selected 8 ⟨51677, by decide⟩
    (prefixPartial 13 18499) = some ⟨13, 2, 0, 51677, 18499, 889, 16384⟩ := by
  decide +kernel

theorem context_13_18499_51677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18499 ⟨51677, by decide⟩ :=
  accepted_of_selected 13 18499 ⟨51677, by decide⟩ ⟨13, 2, 0, 51677, 18499, 889, 16384⟩
    (by decide) selected_cut_01408

theorem unmarked_context_12_4624_51678 : frontier 9 ⟨51678, by decide⟩
    (prefixCache 12 4624) (prefixPartial 12 4624) = false := by
  decide +kernel

theorem node_context_12_4624_51678 : EJMOriginalGlobalDAGData.nodes 9 ⟨51678, by decide⟩ =
    .split (coordinate 12) (![⟨51616, by decide⟩,⟨51644, by decide⟩,⟨51668, by decide⟩,⟨51677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4624_51678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4624 ⟨51678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4624
    ⟨51678, by decide⟩ (by decide) (![⟨51616, by decide⟩,⟨51644, by decide⟩,⟨51668, by decide⟩,⟨51677, by decide⟩]) unmarked_context_12_4624_51678 node_context_12_4624_51678
  intro a
  fin_cases a
  · exact context_13_18496_51616
  · exact context_13_18497_51644
  · exact context_13_18498_51668
  · exact context_13_18499_51677

theorem selected_cut_01409 : selected 8 ⟨51710, by decide⟩
    (prefixPartial 13 18500) = some ⟨13, 2, 0, 51710, 18500, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_18500_51710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18500 ⟨51710, by decide⟩ :=
  accepted_of_selected 13 18500 ⟨51710, by decide⟩ ⟨13, 2, 0, 51710, 18500, 1497, 16384⟩
    (by decide) selected_cut_01409

theorem selected_cut_01410 : selected 8 ⟨51731, by decide⟩
    (prefixPartial 13 18501) = some ⟨13, 2, 0, 51731, 18501, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_18501_51731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18501 ⟨51731, by decide⟩ :=
  accepted_of_selected 13 18501 ⟨51731, by decide⟩ ⟨13, 2, 0, 51731, 18501, 1753, 16384⟩
    (by decide) selected_cut_01410

theorem selected_cut_01411 : selected 8 ⟨51757, by decide⟩
    (prefixPartial 13 18502) = some ⟨13, 2, 0, 51757, 18502, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_18502_51757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18502 ⟨51757, by decide⟩ :=
  accepted_of_selected 13 18502 ⟨51757, by decide⟩ ⟨13, 2, 0, 51757, 18502, 1521, 16384⟩
    (by decide) selected_cut_01411

theorem selected_cut_01412 : selected 8 ⟨51768, by decide⟩
    (prefixPartial 13 18503) = some ⟨13, 2, 0, 51768, 18503, 909, 16384⟩ := by
  decide +kernel

theorem context_13_18503_51768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18503 ⟨51768, by decide⟩ :=
  accepted_of_selected 13 18503 ⟨51768, by decide⟩ ⟨13, 2, 0, 51768, 18503, 909, 16384⟩
    (by decide) selected_cut_01412

theorem unmarked_context_12_4625_51769 : frontier 9 ⟨51769, by decide⟩
    (prefixCache 12 4625) (prefixPartial 12 4625) = false := by
  decide +kernel

theorem node_context_12_4625_51769 : EJMOriginalGlobalDAGData.nodes 9 ⟨51769, by decide⟩ =
    .split (coordinate 12) (![⟨51710, by decide⟩,⟨51731, by decide⟩,⟨51757, by decide⟩,⟨51768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4625_51769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4625 ⟨51769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4625
    ⟨51769, by decide⟩ (by decide) (![⟨51710, by decide⟩,⟨51731, by decide⟩,⟨51757, by decide⟩,⟨51768, by decide⟩]) unmarked_context_12_4625_51769 node_context_12_4625_51769
  intro a
  fin_cases a
  · exact context_13_18500_51710
  · exact context_13_18501_51731
  · exact context_13_18502_51757
  · exact context_13_18503_51768

theorem selected_cut_01413 : selected 8 ⟨51796, by decide⟩
    (prefixPartial 13 18504) = some ⟨13, 2, 0, 51796, 18504, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_18504_51796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18504 ⟨51796, by decide⟩ :=
  accepted_of_selected 13 18504 ⟨51796, by decide⟩ ⟨13, 2, 0, 51796, 18504, 1289, 16384⟩
    (by decide) selected_cut_01413

theorem selected_cut_01414 : selected 8 ⟨51830, by decide⟩
    (prefixPartial 13 18505) = some ⟨13, 2, 0, 51830, 18505, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_18505_51830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18505 ⟨51830, by decide⟩ :=
  accepted_of_selected 13 18505 ⟨51830, by decide⟩ ⟨13, 2, 0, 51830, 18505, 1837, 16384⟩
    (by decide) selected_cut_01414

theorem selected_cut_01415 : selected 8 ⟨51851, by decide⟩
    (prefixPartial 13 18506) = some ⟨13, 2, 0, 51851, 18506, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_18506_51851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18506 ⟨51851, by decide⟩ :=
  accepted_of_selected 13 18506 ⟨51851, by decide⟩ ⟨13, 2, 0, 51851, 18506, 1329, 16384⟩
    (by decide) selected_cut_01415

theorem selected_cut_01416 : selected 8 ⟨51863, by decide⟩
    (prefixPartial 13 18507) = some ⟨13, 2, 0, 51863, 18507, 893, 16384⟩ := by
  decide +kernel

theorem context_13_18507_51863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18507 ⟨51863, by decide⟩ :=
  accepted_of_selected 13 18507 ⟨51863, by decide⟩ ⟨13, 2, 0, 51863, 18507, 893, 16384⟩
    (by decide) selected_cut_01416

theorem unmarked_context_12_4626_51864 : frontier 9 ⟨51864, by decide⟩
    (prefixCache 12 4626) (prefixPartial 12 4626) = false := by
  decide +kernel

theorem node_context_12_4626_51864 : EJMOriginalGlobalDAGData.nodes 9 ⟨51864, by decide⟩ =
    .split (coordinate 12) (![⟨51796, by decide⟩,⟨51830, by decide⟩,⟨51851, by decide⟩,⟨51863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4626_51864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4626 ⟨51864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4626
    ⟨51864, by decide⟩ (by decide) (![⟨51796, by decide⟩,⟨51830, by decide⟩,⟨51851, by decide⟩,⟨51863, by decide⟩]) unmarked_context_12_4626_51864 node_context_12_4626_51864
  intro a
  fin_cases a
  · exact context_13_18504_51796
  · exact context_13_18505_51830
  · exact context_13_18506_51851
  · exact context_13_18507_51863

theorem selected_cut_01417 : selected 8 ⟨51897, by decide⟩
    (prefixPartial 13 18508) = some ⟨13, 2, 0, 51897, 18508, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_18508_51897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18508 ⟨51897, by decide⟩ :=
  accepted_of_selected 13 18508 ⟨51897, by decide⟩ ⟨13, 2, 0, 51897, 18508, 1533, 16384⟩
    (by decide) selected_cut_01417

theorem selected_cut_01418 : selected 8 ⟨51928, by decide⟩
    (prefixPartial 13 18509) = some ⟨13, 2, 0, 51928, 18509, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_18509_51928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18509 ⟨51928, by decide⟩ :=
  accepted_of_selected 13 18509 ⟨51928, by decide⟩ ⟨13, 2, 0, 51928, 18509, 1917, 16384⟩
    (by decide) selected_cut_01418

theorem selected_cut_01419 : selected 8 ⟨51952, by decide⟩
    (prefixPartial 13 18510) = some ⟨13, 2, 0, 51952, 18510, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_18510_51952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18510 ⟨51952, by decide⟩ :=
  accepted_of_selected 13 18510 ⟨51952, by decide⟩ ⟨13, 2, 0, 51952, 18510, 1517, 16384⟩
    (by decide) selected_cut_01419

theorem selected_cut_01420 : selected 8 ⟨51962, by decide⟩
    (prefixPartial 13 18511) = some ⟨13, 2, 0, 51962, 18511, 849, 16384⟩ := by
  decide +kernel

theorem context_13_18511_51962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18511 ⟨51962, by decide⟩ :=
  accepted_of_selected 13 18511 ⟨51962, by decide⟩ ⟨13, 2, 0, 51962, 18511, 849, 16384⟩
    (by decide) selected_cut_01420

theorem unmarked_context_12_4627_51963 : frontier 9 ⟨51963, by decide⟩
    (prefixCache 12 4627) (prefixPartial 12 4627) = false := by
  decide +kernel

theorem node_context_12_4627_51963 : EJMOriginalGlobalDAGData.nodes 9 ⟨51963, by decide⟩ =
    .split (coordinate 12) (![⟨51897, by decide⟩,⟨51928, by decide⟩,⟨51952, by decide⟩,⟨51962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4627_51963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4627 ⟨51963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4627
    ⟨51963, by decide⟩ (by decide) (![⟨51897, by decide⟩,⟨51928, by decide⟩,⟨51952, by decide⟩,⟨51962, by decide⟩]) unmarked_context_12_4627_51963 node_context_12_4627_51963
  intro a
  fin_cases a
  · exact context_13_18508_51897
  · exact context_13_18509_51928
  · exact context_13_18510_51952
  · exact context_13_18511_51962

theorem unmarked_context_11_1156_51964 : frontier 10 ⟨51964, by decide⟩
    (prefixCache 11 1156) (prefixPartial 11 1156) = false := by
  decide +kernel

theorem node_context_11_1156_51964 : EJMOriginalGlobalDAGData.nodes 10 ⟨51964, by decide⟩ =
    .split (coordinate 11) (![⟨51678, by decide⟩,⟨51769, by decide⟩,⟨51864, by decide⟩,⟨51963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1156_51964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1156 ⟨51964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1156
    ⟨51964, by decide⟩ (by decide) (![⟨51678, by decide⟩,⟨51769, by decide⟩,⟨51864, by decide⟩,⟨51963, by decide⟩]) unmarked_context_11_1156_51964 node_context_11_1156_51964
  intro a
  fin_cases a
  · exact context_12_4624_51678
  · exact context_12_4625_51769
  · exact context_12_4626_51864
  · exact context_12_4627_51963

theorem selected_cut_01421 : selected 8 ⟨52011, by decide⟩
    (prefixPartial 13 18512) = some ⟨13, 2, 0, 52011, 18512, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_18512_52011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18512 ⟨52011, by decide⟩ :=
  accepted_of_selected 13 18512 ⟨52011, by decide⟩ ⟨13, 2, 0, 52011, 18512, 2025, 16384⟩
    (by decide) selected_cut_01421

theorem selected_cut_01422 : selected 8 ⟨52058, by decide⟩
    (prefixPartial 13 18513) = some ⟨13, 2, 0, 52058, 18513, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_18513_52058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18513 ⟨52058, by decide⟩ :=
  accepted_of_selected 13 18513 ⟨52058, by decide⟩ ⟨13, 2, 0, 52058, 18513, 3185, 16384⟩
    (by decide) selected_cut_01422

theorem selected_cut_01423 : selected 8 ⟨52092, by decide⟩
    (prefixPartial 13 18514) = some ⟨13, 2, 0, 52092, 18514, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_18514_52092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18514 ⟨52092, by decide⟩ :=
  accepted_of_selected 13 18514 ⟨52092, by decide⟩ ⟨13, 2, 0, 52092, 18514, 2165, 16384⟩
    (by decide) selected_cut_01423

theorem selected_cut_01424 : selected 8 ⟨52120, by decide⟩
    (prefixPartial 13 18515) = some ⟨13, 2, 0, 52120, 18515, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_18515_52120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18515 ⟨52120, by decide⟩ :=
  accepted_of_selected 13 18515 ⟨52120, by decide⟩ ⟨13, 2, 0, 52120, 18515, 1225, 16384⟩
    (by decide) selected_cut_01424

theorem unmarked_context_12_4628_52121 : frontier 9 ⟨52121, by decide⟩
    (prefixCache 12 4628) (prefixPartial 12 4628) = false := by
  decide +kernel

theorem node_context_12_4628_52121 : EJMOriginalGlobalDAGData.nodes 9 ⟨52121, by decide⟩ =
    .split (coordinate 12) (![⟨52011, by decide⟩,⟨52058, by decide⟩,⟨52092, by decide⟩,⟨52120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4628_52121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4628 ⟨52121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4628
    ⟨52121, by decide⟩ (by decide) (![⟨52011, by decide⟩,⟨52058, by decide⟩,⟨52092, by decide⟩,⟨52120, by decide⟩]) unmarked_context_12_4628_52121 node_context_12_4628_52121
  intro a
  fin_cases a
  · exact context_13_18512_52011
  · exact context_13_18513_52058
  · exact context_13_18514_52092
  · exact context_13_18515_52120

theorem selected_cut_01425 : selected 8 ⟨52163, by decide⟩
    (prefixPartial 13 18516) = some ⟨13, 2, 0, 52163, 18516, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_18516_52163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18516 ⟨52163, by decide⟩ :=
  accepted_of_selected 13 18516 ⟨52163, by decide⟩ ⟨13, 2, 0, 52163, 18516, 1885, 16384⟩
    (by decide) selected_cut_01425

theorem selected_cut_01426 : selected 8 ⟨52201, by decide⟩
    (prefixPartial 13 18517) = some ⟨13, 2, 0, 52201, 18517, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_18517_52201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18517 ⟨52201, by decide⟩ :=
  accepted_of_selected 13 18517 ⟨52201, by decide⟩ ⟨13, 2, 0, 52201, 18517, 2257, 16384⟩
    (by decide) selected_cut_01426

theorem selected_cut_01427 : selected 8 ⟨52222, by decide⟩
    (prefixPartial 13 18518) = some ⟨13, 2, 0, 52222, 18518, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_18518_52222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18518 ⟨52222, by decide⟩ :=
  accepted_of_selected 13 18518 ⟨52222, by decide⟩ ⟨13, 2, 0, 52222, 18518, 2001, 16384⟩
    (by decide) selected_cut_01427

theorem selected_cut_01428 : selected 8 ⟨52235, by decide⟩
    (prefixPartial 13 18519) = some ⟨13, 2, 0, 52235, 18519, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_18519_52235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18519 ⟨52235, by decide⟩ :=
  accepted_of_selected 13 18519 ⟨52235, by decide⟩ ⟨13, 2, 0, 52235, 18519, 1101, 16384⟩
    (by decide) selected_cut_01428

theorem unmarked_context_12_4629_52236 : frontier 9 ⟨52236, by decide⟩
    (prefixCache 12 4629) (prefixPartial 12 4629) = false := by
  decide +kernel

theorem node_context_12_4629_52236 : EJMOriginalGlobalDAGData.nodes 9 ⟨52236, by decide⟩ =
    .split (coordinate 12) (![⟨52163, by decide⟩,⟨52201, by decide⟩,⟨52222, by decide⟩,⟨52235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4629_52236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4629 ⟨52236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4629
    ⟨52236, by decide⟩ (by decide) (![⟨52163, by decide⟩,⟨52201, by decide⟩,⟨52222, by decide⟩,⟨52235, by decide⟩]) unmarked_context_12_4629_52236 node_context_12_4629_52236
  intro a
  fin_cases a
  · exact context_13_18516_52163
  · exact context_13_18517_52201
  · exact context_13_18518_52222
  · exact context_13_18519_52235

theorem selected_cut_01429 : selected 8 ⟨52276, by decide⟩
    (prefixPartial 13 18520) = some ⟨13, 2, 0, 52276, 18520, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_18520_52276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18520 ⟨52276, by decide⟩ :=
  accepted_of_selected 13 18520 ⟨52276, by decide⟩ ⟨13, 2, 0, 52276, 18520, 1865, 16384⟩
    (by decide) selected_cut_01429

theorem selected_cut_01430 : selected 8 ⟨52309, by decide⟩
    (prefixPartial 13 18521) = some ⟨13, 2, 0, 52309, 18521, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_18521_52309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18521 ⟨52309, by decide⟩ :=
  accepted_of_selected 13 18521 ⟨52309, by decide⟩ ⟨13, 2, 0, 52309, 18521, 2181, 16384⟩
    (by decide) selected_cut_01430

theorem selected_cut_01431 : selected 8 ⟨52330, by decide⟩
    (prefixPartial 13 18522) = some ⟨13, 2, 0, 52330, 18522, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_18522_52330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18522 ⟨52330, by decide⟩ :=
  accepted_of_selected 13 18522 ⟨52330, by decide⟩ ⟨13, 2, 0, 52330, 18522, 1757, 16384⟩
    (by decide) selected_cut_01431

theorem selected_cut_01432 : selected 8 ⟨52340, by decide⟩
    (prefixPartial 13 18523) = some ⟨13, 2, 0, 52340, 18523, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_18523_52340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18523 ⟨52340, by decide⟩ :=
  accepted_of_selected 13 18523 ⟨52340, by decide⟩ ⟨13, 2, 0, 52340, 18523, 1149, 16384⟩
    (by decide) selected_cut_01432

theorem unmarked_context_12_4630_52341 : frontier 9 ⟨52341, by decide⟩
    (prefixCache 12 4630) (prefixPartial 12 4630) = false := by
  decide +kernel

theorem node_context_12_4630_52341 : EJMOriginalGlobalDAGData.nodes 9 ⟨52341, by decide⟩ =
    .split (coordinate 12) (![⟨52276, by decide⟩,⟨52309, by decide⟩,⟨52330, by decide⟩,⟨52340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4630_52341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4630 ⟨52341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4630
    ⟨52341, by decide⟩ (by decide) (![⟨52276, by decide⟩,⟨52309, by decide⟩,⟨52330, by decide⟩,⟨52340, by decide⟩]) unmarked_context_12_4630_52341 node_context_12_4630_52341
  intro a
  fin_cases a
  · exact context_13_18520_52276
  · exact context_13_18521_52309
  · exact context_13_18522_52330
  · exact context_13_18523_52340

theorem selected_cut_01433 : selected 8 ⟨52379, by decide⟩
    (prefixPartial 13 18524) = some ⟨13, 2, 0, 52379, 18524, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_18524_52379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18524 ⟨52379, by decide⟩ :=
  accepted_of_selected 13 18524 ⟨52379, by decide⟩ ⟨13, 2, 0, 52379, 18524, 2213, 16384⟩
    (by decide) selected_cut_01433

theorem selected_cut_01434 : selected 8 ⟨52416, by decide⟩
    (prefixPartial 13 18525) = some ⟨13, 2, 0, 52416, 18525, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_18525_52416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18525 ⟨52416, by decide⟩ :=
  accepted_of_selected 13 18525 ⟨52416, by decide⟩ ⟨13, 2, 0, 52416, 18525, 2329, 16384⟩
    (by decide) selected_cut_01434

theorem selected_cut_01435 : selected 8 ⟨52443, by decide⟩
    (prefixPartial 13 18526) = some ⟨13, 2, 0, 52443, 18526, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_18526_52443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18526 ⟨52443, by decide⟩ :=
  accepted_of_selected 13 18526 ⟨52443, by decide⟩ ⟨13, 2, 0, 52443, 18526, 2201, 16384⟩
    (by decide) selected_cut_01435

theorem selected_cut_01436 : selected 8 ⟨52455, by decide⟩
    (prefixPartial 13 18527) = some ⟨13, 2, 0, 52455, 18527, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_18527_52455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18527 ⟨52455, by decide⟩ :=
  accepted_of_selected 13 18527 ⟨52455, by decide⟩ ⟨13, 2, 0, 52455, 18527, 1049, 16384⟩
    (by decide) selected_cut_01436

theorem unmarked_context_12_4631_52456 : frontier 9 ⟨52456, by decide⟩
    (prefixCache 12 4631) (prefixPartial 12 4631) = false := by
  decide +kernel

theorem node_context_12_4631_52456 : EJMOriginalGlobalDAGData.nodes 9 ⟨52456, by decide⟩ =
    .split (coordinate 12) (![⟨52379, by decide⟩,⟨52416, by decide⟩,⟨52443, by decide⟩,⟨52455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4631_52456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4631 ⟨52456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4631
    ⟨52456, by decide⟩ (by decide) (![⟨52379, by decide⟩,⟨52416, by decide⟩,⟨52443, by decide⟩,⟨52455, by decide⟩]) unmarked_context_12_4631_52456 node_context_12_4631_52456
  intro a
  fin_cases a
  · exact context_13_18524_52379
  · exact context_13_18525_52416
  · exact context_13_18526_52443
  · exact context_13_18527_52455

theorem unmarked_context_11_1157_52457 : frontier 10 ⟨52457, by decide⟩
    (prefixCache 11 1157) (prefixPartial 11 1157) = false := by
  decide +kernel

theorem node_context_11_1157_52457 : EJMOriginalGlobalDAGData.nodes 10 ⟨52457, by decide⟩ =
    .split (coordinate 11) (![⟨52121, by decide⟩,⟨52236, by decide⟩,⟨52341, by decide⟩,⟨52456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1157_52457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1157 ⟨52457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1157
    ⟨52457, by decide⟩ (by decide) (![⟨52121, by decide⟩,⟨52236, by decide⟩,⟨52341, by decide⟩,⟨52456, by decide⟩]) unmarked_context_11_1157_52457 node_context_11_1157_52457
  intro a
  fin_cases a
  · exact context_12_4628_52121
  · exact context_12_4629_52236
  · exact context_12_4630_52341
  · exact context_12_4631_52456

theorem selected_cut_01437 : selected 8 ⟨52494, by decide⟩
    (prefixPartial 13 18528) = some ⟨13, 2, 0, 52494, 18528, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_18528_52494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18528 ⟨52494, by decide⟩ :=
  accepted_of_selected 13 18528 ⟨52494, by decide⟩ ⟨13, 2, 0, 52494, 18528, 1901, 16384⟩
    (by decide) selected_cut_01437

theorem selected_cut_01438 : selected 8 ⟨52543, by decide⟩
    (prefixPartial 13 18529) = some ⟨13, 2, 0, 52543, 18529, 3113, 16384⟩ := by
  decide +kernel

theorem context_13_18529_52543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18529 ⟨52543, by decide⟩ :=
  accepted_of_selected 13 18529 ⟨52543, by decide⟩ ⟨13, 2, 0, 52543, 18529, 3113, 16384⟩
    (by decide) selected_cut_01438

theorem selected_cut_01439 : selected 8 ⟨52575, by decide⟩
    (prefixPartial 13 18530) = some ⟨13, 2, 0, 52575, 18530, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_18530_52575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18530 ⟨52575, by decide⟩ :=
  accepted_of_selected 13 18530 ⟨52575, by decide⟩ ⟨13, 2, 0, 52575, 18530, 2157, 16384⟩
    (by decide) selected_cut_01439

theorem selected_cut_01440 : selected 8 ⟨52591, by decide⟩
    (prefixPartial 13 18531) = some ⟨13, 2, 0, 52591, 18531, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_18531_52591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18531 ⟨52591, by decide⟩ :=
  accepted_of_selected 13 18531 ⟨52591, by decide⟩ ⟨13, 2, 0, 52591, 18531, 1157, 16384⟩
    (by decide) selected_cut_01440

theorem unmarked_context_12_4632_52592 : frontier 9 ⟨52592, by decide⟩
    (prefixCache 12 4632) (prefixPartial 12 4632) = false := by
  decide +kernel

theorem node_context_12_4632_52592 : EJMOriginalGlobalDAGData.nodes 9 ⟨52592, by decide⟩ =
    .split (coordinate 12) (![⟨52494, by decide⟩,⟨52543, by decide⟩,⟨52575, by decide⟩,⟨52591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4632_52592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4632 ⟨52592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4632
    ⟨52592, by decide⟩ (by decide) (![⟨52494, by decide⟩,⟨52543, by decide⟩,⟨52575, by decide⟩,⟨52591, by decide⟩]) unmarked_context_12_4632_52592 node_context_12_4632_52592
  intro a
  fin_cases a
  · exact context_13_18528_52494
  · exact context_13_18529_52543
  · exact context_13_18530_52575
  · exact context_13_18531_52591

theorem selected_cut_01441 : selected 8 ⟨52635, by decide⟩
    (prefixPartial 13 18532) = some ⟨13, 2, 0, 52635, 18532, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_18532_52635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18532 ⟨52635, by decide⟩ :=
  accepted_of_selected 13 18532 ⟨52635, by decide⟩ ⟨13, 2, 0, 52635, 18532, 2049, 16384⟩
    (by decide) selected_cut_01441

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
