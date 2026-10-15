/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover371
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35715 : selected 8 ⟨940107, by decide⟩
    (prefixPartial 13 1148979) = some ⟨13, 2, 0, 940107, 1148979, 689, 16384⟩ := by
  decide +kernel

theorem context_13_1148979_940107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148979 ⟨940107, by decide⟩ :=
  accepted_of_selected 13 1148979 ⟨940107, by decide⟩ ⟨13, 2, 0, 940107, 1148979, 689, 16384⟩
    (by decide) selected_cut_35715

theorem unmarked_context_12_287244_940108 : frontier 9 ⟨940108, by decide⟩
    (prefixCache 12 287244) (prefixPartial 12 287244) = false := by
  decide +kernel

theorem node_context_12_287244_940108 : EJMOriginalGlobalDAGData.nodes 9 ⟨940108, by decide⟩ =
    .split (coordinate 12) (![⟨940059, by decide⟩,⟨940080, by decide⟩,⟨940102, by decide⟩,⟨940107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287244_940108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287244 ⟨940108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287244
    ⟨940108, by decide⟩ (by decide) (![⟨940059, by decide⟩,⟨940080, by decide⟩,⟨940102, by decide⟩,⟨940107, by decide⟩]) unmarked_context_12_287244_940108 node_context_12_287244_940108
  intro a
  fin_cases a
  · exact context_13_1148976_940059
  · exact context_13_1148977_940080
  · exact context_13_1148978_940102
  · exact context_13_1148979_940107

theorem selected_cut_35716 : selected 9 ⟨940165, by decide⟩
    (prefixPartial 12 287245) = some ⟨12, 2, 0, 940165, 287245, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_287245_940165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287245 ⟨940165, by decide⟩ :=
  accepted_of_selected 12 287245 ⟨940165, by decide⟩ ⟨12, 2, 0, 940165, 287245, 3673, 65536⟩
    (by decide) selected_cut_35716

theorem selected_cut_35717 : selected 9 ⟨940222, by decide⟩
    (prefixPartial 12 287246) = some ⟨12, 2, 0, 940222, 287246, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_287246_940222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287246 ⟨940222, by decide⟩ :=
  accepted_of_selected 12 287246 ⟨940222, by decide⟩ ⟨12, 2, 0, 940222, 287246, 3661, 65536⟩
    (by decide) selected_cut_35717

theorem selected_cut_35718 : selected 9 ⟨940273, by decide⟩
    (prefixPartial 12 287247) = some ⟨12, 2, 0, 940273, 287247, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_287247_940273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287247 ⟨940273, by decide⟩ :=
  accepted_of_selected 12 287247 ⟨940273, by decide⟩ ⟨12, 2, 0, 940273, 287247, 3857, 65536⟩
    (by decide) selected_cut_35718

theorem unmarked_context_11_71811_940274 : frontier 10 ⟨940274, by decide⟩
    (prefixCache 11 71811) (prefixPartial 11 71811) = false := by
  decide +kernel

theorem node_context_11_71811_940274 : EJMOriginalGlobalDAGData.nodes 10 ⟨940274, by decide⟩ =
    .split (coordinate 11) (![⟨940108, by decide⟩,⟨940165, by decide⟩,⟨940222, by decide⟩,⟨940273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71811_940274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71811 ⟨940274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71811
    ⟨940274, by decide⟩ (by decide) (![⟨940108, by decide⟩,⟨940165, by decide⟩,⟨940222, by decide⟩,⟨940273, by decide⟩]) unmarked_context_11_71811_940274 node_context_11_71811_940274
  intro a
  fin_cases a
  · exact context_12_287244_940108
  · exact context_12_287245_940165
  · exact context_12_287246_940222
  · exact context_12_287247_940273

theorem unmarked_context_10_17952_940275 : frontier 11 ⟨940275, by decide⟩
    (prefixCache 10 17952) (prefixPartial 10 17952) = false := by
  decide +kernel

theorem node_context_10_17952_940275 : EJMOriginalGlobalDAGData.nodes 11 ⟨940275, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨939745, by decide⟩,⟨940025, by decide⟩,⟨940274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17952_940275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17952 ⟨940275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17952
    ⟨940275, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨939745, by decide⟩,⟨940025, by decide⟩,⟨940274, by decide⟩]) unmarked_context_10_17952_940275 node_context_10_17952_940275
  intro a
  fin_cases a
  · exact context_11_71808_167448
  · exact context_11_71809_939745
  · exact context_11_71810_940025
  · exact context_11_71811_940274

theorem selected_cut_35719 : selected 9 ⟨940338, by decide⟩
    (prefixPartial 12 287248) = some ⟨12, 2, 0, 940338, 287248, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_287248_940338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287248 ⟨940338, by decide⟩ :=
  accepted_of_selected 12 287248 ⟨940338, by decide⟩ ⟨12, 2, 0, 940338, 287248, 3673, 65536⟩
    (by decide) selected_cut_35719

theorem selected_cut_35720 : selected 9 ⟨940380, by decide⟩
    (prefixPartial 12 287249) = some ⟨12, 2, 0, 940380, 287249, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_287249_940380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287249 ⟨940380, by decide⟩ :=
  accepted_of_selected 12 287249 ⟨940380, by decide⟩ ⟨12, 2, 0, 940380, 287249, 3313, 65536⟩
    (by decide) selected_cut_35720

theorem selected_cut_35721 : selected 9 ⟨940426, by decide⟩
    (prefixPartial 12 287250) = some ⟨12, 2, 0, 940426, 287250, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_287250_940426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287250 ⟨940426, by decide⟩ :=
  accepted_of_selected 12 287250 ⟨940426, by decide⟩ ⟨12, 2, 0, 940426, 287250, 3065, 65536⟩
    (by decide) selected_cut_35721

theorem selected_cut_35722 : selected 9 ⟨940489, by decide⟩
    (prefixPartial 12 287251) = some ⟨12, 2, 0, 940489, 287251, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_287251_940489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287251 ⟨940489, by decide⟩ :=
  accepted_of_selected 12 287251 ⟨940489, by decide⟩ ⟨12, 2, 0, 940489, 287251, 3901, 65536⟩
    (by decide) selected_cut_35722

theorem unmarked_context_11_71812_940490 : frontier 10 ⟨940490, by decide⟩
    (prefixCache 11 71812) (prefixPartial 11 71812) = false := by
  decide +kernel

theorem node_context_11_71812_940490 : EJMOriginalGlobalDAGData.nodes 10 ⟨940490, by decide⟩ =
    .split (coordinate 11) (![⟨940338, by decide⟩,⟨940380, by decide⟩,⟨940426, by decide⟩,⟨940489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71812_940490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71812 ⟨940490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71812
    ⟨940490, by decide⟩ (by decide) (![⟨940338, by decide⟩,⟨940380, by decide⟩,⟨940426, by decide⟩,⟨940489, by decide⟩]) unmarked_context_11_71812_940490 node_context_11_71812_940490
  intro a
  fin_cases a
  · exact context_12_287248_940338
  · exact context_12_287249_940380
  · exact context_12_287250_940426
  · exact context_12_287251_940489

theorem selected_cut_35723 : selected 9 ⟨940542, by decide⟩
    (prefixPartial 12 287252) = some ⟨12, 2, 0, 940542, 287252, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_287252_940542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287252 ⟨940542, by decide⟩ :=
  accepted_of_selected 12 287252 ⟨940542, by decide⟩ ⟨12, 2, 0, 940542, 287252, 3909, 65536⟩
    (by decide) selected_cut_35723

theorem selected_cut_35724 : selected 9 ⟨940596, by decide⟩
    (prefixPartial 12 287253) = some ⟨12, 2, 0, 940596, 287253, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_287253_940596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287253 ⟨940596, by decide⟩ :=
  accepted_of_selected 12 287253 ⟨940596, by decide⟩ ⟨12, 2, 0, 940596, 287253, 3401, 65536⟩
    (by decide) selected_cut_35724

theorem selected_cut_35725 : selected 9 ⟨940638, by decide⟩
    (prefixPartial 12 287254) = some ⟨12, 2, 0, 940638, 287254, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_287254_940638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287254 ⟨940638, by decide⟩ :=
  accepted_of_selected 12 287254 ⟨940638, by decide⟩ ⟨12, 2, 0, 940638, 287254, 3137, 65536⟩
    (by decide) selected_cut_35725

theorem selected_cut_35726 : selected 9 ⟨940704, by decide⟩
    (prefixPartial 12 287255) = some ⟨12, 2, 0, 940704, 287255, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_287255_940704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287255 ⟨940704, by decide⟩ :=
  accepted_of_selected 12 287255 ⟨940704, by decide⟩ ⟨12, 2, 0, 940704, 287255, 3889, 65536⟩
    (by decide) selected_cut_35726

theorem unmarked_context_11_71813_940705 : frontier 10 ⟨940705, by decide⟩
    (prefixCache 11 71813) (prefixPartial 11 71813) = false := by
  decide +kernel

theorem node_context_11_71813_940705 : EJMOriginalGlobalDAGData.nodes 10 ⟨940705, by decide⟩ =
    .split (coordinate 11) (![⟨940542, by decide⟩,⟨940596, by decide⟩,⟨940638, by decide⟩,⟨940704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71813_940705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71813 ⟨940705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71813
    ⟨940705, by decide⟩ (by decide) (![⟨940542, by decide⟩,⟨940596, by decide⟩,⟨940638, by decide⟩,⟨940704, by decide⟩]) unmarked_context_11_71813_940705 node_context_11_71813_940705
  intro a
  fin_cases a
  · exact context_12_287252_940542
  · exact context_12_287253_940596
  · exact context_12_287254_940638
  · exact context_12_287255_940704

theorem selected_cut_35727 : selected 8 ⟨940732, by decide⟩
    (prefixPartial 13 1149024) = some ⟨13, 2, 0, 940732, 1149024, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_1149024_940732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149024 ⟨940732, by decide⟩ :=
  accepted_of_selected 13 1149024 ⟨940732, by decide⟩ ⟨13, 2, 0, 940732, 1149024, 1469, 16384⟩
    (by decide) selected_cut_35727

theorem selected_cut_35728 : selected 8 ⟨940752, by decide⟩
    (prefixPartial 13 1149025) = some ⟨13, 2, 0, 940752, 1149025, 873, 16384⟩ := by
  decide +kernel

theorem context_13_1149025_940752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149025 ⟨940752, by decide⟩ :=
  accepted_of_selected 13 1149025 ⟨940752, by decide⟩ ⟨13, 2, 0, 940752, 1149025, 873, 16384⟩
    (by decide) selected_cut_35728

theorem selected_cut_35729 : selected 8 ⟨940769, by decide⟩
    (prefixPartial 13 1149026) = some ⟨13, 2, 0, 940769, 1149026, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_1149026_940769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149026 ⟨940769, by decide⟩ :=
  accepted_of_selected 13 1149026 ⟨940769, by decide⟩ ⟨13, 2, 0, 940769, 1149026, 1165, 16384⟩
    (by decide) selected_cut_35729

theorem selected_cut_35730 : selected 8 ⟨940776, by decide⟩
    (prefixPartial 13 1149027) = some ⟨13, 2, 0, 940776, 1149027, 661, 16384⟩ := by
  decide +kernel

theorem context_13_1149027_940776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149027 ⟨940776, by decide⟩ :=
  accepted_of_selected 13 1149027 ⟨940776, by decide⟩ ⟨13, 2, 0, 940776, 1149027, 661, 16384⟩
    (by decide) selected_cut_35730

theorem unmarked_context_12_287256_940777 : frontier 9 ⟨940777, by decide⟩
    (prefixCache 12 287256) (prefixPartial 12 287256) = false := by
  decide +kernel

theorem node_context_12_287256_940777 : EJMOriginalGlobalDAGData.nodes 9 ⟨940777, by decide⟩ =
    .split (coordinate 12) (![⟨940732, by decide⟩,⟨940752, by decide⟩,⟨940769, by decide⟩,⟨940776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287256_940777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287256 ⟨940777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287256
    ⟨940777, by decide⟩ (by decide) (![⟨940732, by decide⟩,⟨940752, by decide⟩,⟨940769, by decide⟩,⟨940776, by decide⟩]) unmarked_context_12_287256_940777 node_context_12_287256_940777
  intro a
  fin_cases a
  · exact context_13_1149024_940732
  · exact context_13_1149025_940752
  · exact context_13_1149026_940769
  · exact context_13_1149027_940776

theorem selected_cut_35731 : selected 9 ⟨940834, by decide⟩
    (prefixPartial 12 287257) = some ⟨12, 2, 0, 940834, 287257, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_287257_940834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287257 ⟨940834, by decide⟩ :=
  accepted_of_selected 12 287257 ⟨940834, by decide⟩ ⟨12, 2, 0, 940834, 287257, 3641, 65536⟩
    (by decide) selected_cut_35731

theorem selected_cut_35732 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 287258) = some ⟨12, 1, 0, 893903, 287258, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287258_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287258 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 287258 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 287258, 1, 65536⟩
    (by decide) selected_cut_35732

theorem selected_cut_35733 : selected 9 ⟨940905, by decide⟩
    (prefixPartial 12 287259) = some ⟨12, 2, 0, 940905, 287259, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_287259_940905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287259 ⟨940905, by decide⟩ :=
  accepted_of_selected 12 287259 ⟨940905, by decide⟩ ⟨12, 2, 0, 940905, 287259, 4021, 65536⟩
    (by decide) selected_cut_35733

theorem unmarked_context_11_71814_940906 : frontier 10 ⟨940906, by decide⟩
    (prefixCache 11 71814) (prefixPartial 11 71814) = false := by
  decide +kernel

theorem node_context_11_71814_940906 : EJMOriginalGlobalDAGData.nodes 10 ⟨940906, by decide⟩ =
    .split (coordinate 11) (![⟨940777, by decide⟩,⟨940834, by decide⟩,⟨893903, by decide⟩,⟨940905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71814_940906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71814 ⟨940906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71814
    ⟨940906, by decide⟩ (by decide) (![⟨940777, by decide⟩,⟨940834, by decide⟩,⟨893903, by decide⟩,⟨940905, by decide⟩]) unmarked_context_11_71814_940906 node_context_11_71814_940906
  intro a
  fin_cases a
  · exact context_12_287256_940777
  · exact context_12_287257_940834
  · exact context_12_287258_893903
  · exact context_12_287259_940905

theorem selected_cut_35734 : selected 8 ⟨940940, by decide⟩
    (prefixPartial 13 1149040) = some ⟨13, 2, 0, 940940, 1149040, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_1149040_940940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149040 ⟨940940, by decide⟩ :=
  accepted_of_selected 13 1149040 ⟨940940, by decide⟩ ⟨13, 2, 0, 940940, 1149040, 1657, 16384⟩
    (by decide) selected_cut_35734

theorem selected_cut_35735 : selected 8 ⟨940954, by decide⟩
    (prefixPartial 13 1149041) = some ⟨13, 2, 0, 940954, 1149041, 721, 16384⟩ := by
  decide +kernel

theorem context_13_1149041_940954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149041 ⟨940954, by decide⟩ :=
  accepted_of_selected 13 1149041 ⟨940954, by decide⟩ ⟨13, 2, 0, 940954, 1149041, 721, 16384⟩
    (by decide) selected_cut_35735

theorem selected_cut_35736 : selected 8 ⟨940971, by decide⟩
    (prefixPartial 13 1149042) = some ⟨13, 2, 0, 940971, 1149042, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1149042_940971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149042 ⟨940971, by decide⟩ :=
  accepted_of_selected 13 1149042 ⟨940971, by decide⟩ ⟨13, 2, 0, 940971, 1149042, 1113, 16384⟩
    (by decide) selected_cut_35736

theorem selected_cut_35737 : selected 8 ⟨940979, by decide⟩
    (prefixPartial 13 1149043) = some ⟨13, 2, 0, 940979, 1149043, 629, 16384⟩ := by
  decide +kernel

theorem context_13_1149043_940979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149043 ⟨940979, by decide⟩ :=
  accepted_of_selected 13 1149043 ⟨940979, by decide⟩ ⟨13, 2, 0, 940979, 1149043, 629, 16384⟩
    (by decide) selected_cut_35737

theorem unmarked_context_12_287260_940980 : frontier 9 ⟨940980, by decide⟩
    (prefixCache 12 287260) (prefixPartial 12 287260) = false := by
  decide +kernel

theorem node_context_12_287260_940980 : EJMOriginalGlobalDAGData.nodes 9 ⟨940980, by decide⟩ =
    .split (coordinate 12) (![⟨940940, by decide⟩,⟨940954, by decide⟩,⟨940971, by decide⟩,⟨940979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287260_940980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287260 ⟨940980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287260
    ⟨940980, by decide⟩ (by decide) (![⟨940940, by decide⟩,⟨940954, by decide⟩,⟨940971, by decide⟩,⟨940979, by decide⟩]) unmarked_context_12_287260_940980 node_context_12_287260_940980
  intro a
  fin_cases a
  · exact context_13_1149040_940940
  · exact context_13_1149041_940954
  · exact context_13_1149042_940971
  · exact context_13_1149043_940979

theorem selected_cut_35738 : selected 9 ⟨941035, by decide⟩
    (prefixPartial 12 287261) = some ⟨12, 2, 0, 941035, 287261, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_287261_941035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287261 ⟨941035, by decide⟩ :=
  accepted_of_selected 12 287261 ⟨941035, by decide⟩ ⟨12, 2, 0, 941035, 287261, 3609, 65536⟩
    (by decide) selected_cut_35738

theorem selected_cut_35739 : selected 9 ⟨941089, by decide⟩
    (prefixPartial 12 287262) = some ⟨12, 2, 0, 941089, 287262, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_287262_941089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287262 ⟨941089, by decide⟩ :=
  accepted_of_selected 12 287262 ⟨941089, by decide⟩ ⟨12, 2, 0, 941089, 287262, 3357, 65536⟩
    (by decide) selected_cut_35739

theorem selected_cut_35740 : selected 9 ⟨941140, by decide⟩
    (prefixPartial 12 287263) = some ⟨12, 2, 0, 941140, 287263, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_287263_941140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287263 ⟨941140, by decide⟩ :=
  accepted_of_selected 12 287263 ⟨941140, by decide⟩ ⟨12, 2, 0, 941140, 287263, 3805, 65536⟩
    (by decide) selected_cut_35740

theorem unmarked_context_11_71815_941141 : frontier 10 ⟨941141, by decide⟩
    (prefixCache 11 71815) (prefixPartial 11 71815) = false := by
  decide +kernel

theorem node_context_11_71815_941141 : EJMOriginalGlobalDAGData.nodes 10 ⟨941141, by decide⟩ =
    .split (coordinate 11) (![⟨940980, by decide⟩,⟨941035, by decide⟩,⟨941089, by decide⟩,⟨941140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71815_941141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71815 ⟨941141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71815
    ⟨941141, by decide⟩ (by decide) (![⟨940980, by decide⟩,⟨941035, by decide⟩,⟨941089, by decide⟩,⟨941140, by decide⟩]) unmarked_context_11_71815_941141 node_context_11_71815_941141
  intro a
  fin_cases a
  · exact context_12_287260_940980
  · exact context_12_287261_941035
  · exact context_12_287262_941089
  · exact context_12_287263_941140

theorem unmarked_context_10_17953_941142 : frontier 11 ⟨941142, by decide⟩
    (prefixCache 10 17953) (prefixPartial 10 17953) = false := by
  decide +kernel

theorem node_context_10_17953_941142 : EJMOriginalGlobalDAGData.nodes 11 ⟨941142, by decide⟩ =
    .split (coordinate 10) (![⟨940490, by decide⟩,⟨940705, by decide⟩,⟨940906, by decide⟩,⟨941141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17953_941142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17953 ⟨941142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17953
    ⟨941142, by decide⟩ (by decide) (![⟨940490, by decide⟩,⟨940705, by decide⟩,⟨940906, by decide⟩,⟨941141, by decide⟩]) unmarked_context_10_17953_941142 node_context_10_17953_941142
  intro a
  fin_cases a
  · exact context_11_71812_940490
  · exact context_11_71813_940705
  · exact context_11_71814_940906
  · exact context_11_71815_941141

theorem selected_cut_35741 : selected 9 ⟨941197, by decide⟩
    (prefixPartial 12 287264) = some ⟨12, 2, 0, 941197, 287264, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_287264_941197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287264 ⟨941197, by decide⟩ :=
  accepted_of_selected 12 287264 ⟨941197, by decide⟩ ⟨12, 2, 0, 941197, 287264, 3169, 65536⟩
    (by decide) selected_cut_35741

theorem selected_cut_35742 : selected 9 ⟨941240, by decide⟩
    (prefixPartial 12 287265) = some ⟨12, 2, 0, 941240, 287265, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_287265_941240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287265 ⟨941240, by decide⟩ :=
  accepted_of_selected 12 287265 ⟨941240, by decide⟩ ⟨12, 2, 0, 941240, 287265, 2825, 65536⟩
    (by decide) selected_cut_35742

theorem selected_cut_35743 : selected 9 ⟨941288, by decide⟩
    (prefixPartial 12 287266) = some ⟨12, 2, 0, 941288, 287266, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_287266_941288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287266 ⟨941288, by decide⟩ :=
  accepted_of_selected 12 287266 ⟨941288, by decide⟩ ⟨12, 2, 0, 941288, 287266, 2793, 65536⟩
    (by decide) selected_cut_35743

theorem selected_cut_35744 : selected 9 ⟨941342, by decide⟩
    (prefixPartial 12 287267) = some ⟨12, 2, 0, 941342, 287267, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_287267_941342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287267 ⟨941342, by decide⟩ :=
  accepted_of_selected 12 287267 ⟨941342, by decide⟩ ⟨12, 2, 0, 941342, 287267, 3289, 65536⟩
    (by decide) selected_cut_35744

theorem unmarked_context_11_71816_941343 : frontier 10 ⟨941343, by decide⟩
    (prefixCache 11 71816) (prefixPartial 11 71816) = false := by
  decide +kernel

theorem node_context_11_71816_941343 : EJMOriginalGlobalDAGData.nodes 10 ⟨941343, by decide⟩ =
    .split (coordinate 11) (![⟨941197, by decide⟩,⟨941240, by decide⟩,⟨941288, by decide⟩,⟨941342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71816_941343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71816 ⟨941343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71816
    ⟨941343, by decide⟩ (by decide) (![⟨941197, by decide⟩,⟨941240, by decide⟩,⟨941288, by decide⟩,⟨941342, by decide⟩]) unmarked_context_11_71816_941343 node_context_11_71816_941343
  intro a
  fin_cases a
  · exact context_12_287264_941197
  · exact context_12_287265_941240
  · exact context_12_287266_941288
  · exact context_12_287267_941342

theorem selected_cut_35745 : selected 9 ⟨941396, by decide⟩
    (prefixPartial 12 287268) = some ⟨12, 2, 0, 941396, 287268, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_287268_941396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287268 ⟨941396, by decide⟩ :=
  accepted_of_selected 12 287268 ⟨941396, by decide⟩ ⟨12, 2, 0, 941396, 287268, 3289, 65536⟩
    (by decide) selected_cut_35745

theorem selected_cut_35746 : selected 9 ⟨941444, by decide⟩
    (prefixPartial 12 287269) = some ⟨12, 2, 0, 941444, 287269, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_287269_941444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287269 ⟨941444, by decide⟩ :=
  accepted_of_selected 12 287269 ⟨941444, by decide⟩ ⟨12, 2, 0, 941444, 287269, 3045, 65536⟩
    (by decide) selected_cut_35746

theorem selected_cut_35747 : selected 9 ⟨941492, by decide⟩
    (prefixPartial 12 287270) = some ⟨12, 2, 0, 941492, 287270, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_287270_941492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287270 ⟨941492, by decide⟩ :=
  accepted_of_selected 12 287270 ⟨941492, by decide⟩ ⟨12, 2, 0, 941492, 287270, 2909, 65536⟩
    (by decide) selected_cut_35747

theorem selected_cut_35748 : selected 9 ⟨941543, by decide⟩
    (prefixPartial 12 287271) = some ⟨12, 2, 0, 941543, 287271, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_287271_941543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287271 ⟨941543, by decide⟩ :=
  accepted_of_selected 12 287271 ⟨941543, by decide⟩ ⟨12, 2, 0, 941543, 287271, 3193, 65536⟩
    (by decide) selected_cut_35748

theorem unmarked_context_11_71817_941544 : frontier 10 ⟨941544, by decide⟩
    (prefixCache 11 71817) (prefixPartial 11 71817) = false := by
  decide +kernel

theorem node_context_11_71817_941544 : EJMOriginalGlobalDAGData.nodes 10 ⟨941544, by decide⟩ =
    .split (coordinate 11) (![⟨941396, by decide⟩,⟨941444, by decide⟩,⟨941492, by decide⟩,⟨941543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71817_941544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71817 ⟨941544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71817
    ⟨941544, by decide⟩ (by decide) (![⟨941396, by decide⟩,⟨941444, by decide⟩,⟨941492, by decide⟩,⟨941543, by decide⟩]) unmarked_context_11_71817_941544 node_context_11_71817_941544
  intro a
  fin_cases a
  · exact context_12_287268_941396
  · exact context_12_287269_941444
  · exact context_12_287270_941492
  · exact context_12_287271_941543

theorem selected_cut_35749 : selected 9 ⟨941607, by decide⟩
    (prefixPartial 12 287272) = some ⟨12, 2, 0, 941607, 287272, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_287272_941607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287272 ⟨941607, by decide⟩ :=
  accepted_of_selected 12 287272 ⟨941607, by decide⟩ ⟨12, 2, 0, 941607, 287272, 3581, 65536⟩
    (by decide) selected_cut_35749

theorem selected_cut_35750 : selected 9 ⟨941657, by decide⟩
    (prefixPartial 12 287273) = some ⟨12, 2, 0, 941657, 287273, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_287273_941657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287273 ⟨941657, by decide⟩ :=
  accepted_of_selected 12 287273 ⟨941657, by decide⟩ ⟨12, 2, 0, 941657, 287273, 3141, 65536⟩
    (by decide) selected_cut_35750

theorem selected_cut_35751 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 287274) = some ⟨12, 1, 0, 242157, 287274, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287274_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287274 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 287274 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 287274, 1, 65536⟩
    (by decide) selected_cut_35751

theorem selected_cut_35752 : selected 9 ⟨941709, by decide⟩
    (prefixPartial 12 287275) = some ⟨12, 2, 0, 941709, 287275, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_287275_941709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287275 ⟨941709, by decide⟩ :=
  accepted_of_selected 12 287275 ⟨941709, by decide⟩ ⟨12, 2, 0, 941709, 287275, 3337, 65536⟩
    (by decide) selected_cut_35752

theorem unmarked_context_11_71818_941710 : frontier 10 ⟨941710, by decide⟩
    (prefixCache 11 71818) (prefixPartial 11 71818) = false := by
  decide +kernel

theorem node_context_11_71818_941710 : EJMOriginalGlobalDAGData.nodes 10 ⟨941710, by decide⟩ =
    .split (coordinate 11) (![⟨941607, by decide⟩,⟨941657, by decide⟩,⟨242157, by decide⟩,⟨941709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71818_941710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71818 ⟨941710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71818
    ⟨941710, by decide⟩ (by decide) (![⟨941607, by decide⟩,⟨941657, by decide⟩,⟨242157, by decide⟩,⟨941709, by decide⟩]) unmarked_context_11_71818_941710 node_context_11_71818_941710
  intro a
  fin_cases a
  · exact context_12_287272_941607
  · exact context_12_287273_941657
  · exact context_12_287274_242157
  · exact context_12_287275_941709

theorem selected_cut_35753 : selected 9 ⟨941776, by decide⟩
    (prefixPartial 12 287276) = some ⟨12, 2, 0, 941776, 287276, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_287276_941776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287276 ⟨941776, by decide⟩ :=
  accepted_of_selected 12 287276 ⟨941776, by decide⟩ ⟨12, 2, 0, 941776, 287276, 3689, 65536⟩
    (by decide) selected_cut_35753

theorem selected_cut_35754 : selected 9 ⟨941828, by decide⟩
    (prefixPartial 12 287277) = some ⟨12, 2, 0, 941828, 287277, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_287277_941828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287277 ⟨941828, by decide⟩ :=
  accepted_of_selected 12 287277 ⟨941828, by decide⟩ ⟨12, 2, 0, 941828, 287277, 3249, 65536⟩
    (by decide) selected_cut_35754

theorem selected_cut_35755 : selected 9 ⟨941889, by decide⟩
    (prefixPartial 12 287278) = some ⟨12, 2, 0, 941889, 287278, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_287278_941889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287278 ⟨941889, by decide⟩ :=
  accepted_of_selected 12 287278 ⟨941889, by decide⟩ ⟨12, 2, 0, 941889, 287278, 3293, 65536⟩
    (by decide) selected_cut_35755

theorem selected_cut_35756 : selected 9 ⟨941948, by decide⟩
    (prefixPartial 12 287279) = some ⟨12, 2, 0, 941948, 287279, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_287279_941948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287279 ⟨941948, by decide⟩ :=
  accepted_of_selected 12 287279 ⟨941948, by decide⟩ ⟨12, 2, 0, 941948, 287279, 3265, 65536⟩
    (by decide) selected_cut_35756

theorem unmarked_context_11_71819_941949 : frontier 10 ⟨941949, by decide⟩
    (prefixCache 11 71819) (prefixPartial 11 71819) = false := by
  decide +kernel

theorem node_context_11_71819_941949 : EJMOriginalGlobalDAGData.nodes 10 ⟨941949, by decide⟩ =
    .split (coordinate 11) (![⟨941776, by decide⟩,⟨941828, by decide⟩,⟨941889, by decide⟩,⟨941948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71819_941949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71819 ⟨941949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71819
    ⟨941949, by decide⟩ (by decide) (![⟨941776, by decide⟩,⟨941828, by decide⟩,⟨941889, by decide⟩,⟨941948, by decide⟩]) unmarked_context_11_71819_941949 node_context_11_71819_941949
  intro a
  fin_cases a
  · exact context_12_287276_941776
  · exact context_12_287277_941828
  · exact context_12_287278_941889
  · exact context_12_287279_941948

theorem unmarked_context_10_17954_941950 : frontier 11 ⟨941950, by decide⟩
    (prefixCache 10 17954) (prefixPartial 10 17954) = false := by
  decide +kernel

theorem node_context_10_17954_941950 : EJMOriginalGlobalDAGData.nodes 11 ⟨941950, by decide⟩ =
    .split (coordinate 10) (![⟨941343, by decide⟩,⟨941544, by decide⟩,⟨941710, by decide⟩,⟨941949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17954_941950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17954 ⟨941950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17954
    ⟨941950, by decide⟩ (by decide) (![⟨941343, by decide⟩,⟨941544, by decide⟩,⟨941710, by decide⟩,⟨941949, by decide⟩]) unmarked_context_10_17954_941950 node_context_10_17954_941950
  intro a
  fin_cases a
  · exact context_11_71816_941343
  · exact context_11_71817_941544
  · exact context_11_71818_941710
  · exact context_11_71819_941949

theorem selected_cut_35757 : selected 9 ⟨941981, by decide⟩
    (prefixPartial 12 287280) = some ⟨12, 2, 0, 941981, 287280, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_287280_941981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287280 ⟨941981, by decide⟩ :=
  accepted_of_selected 12 287280 ⟨941981, by decide⟩ ⟨12, 2, 0, 941981, 287280, 2677, 65536⟩
    (by decide) selected_cut_35757

theorem selected_cut_35758 : selected 9 ⟨942013, by decide⟩
    (prefixPartial 12 287281) = some ⟨12, 2, 0, 942013, 287281, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_287281_942013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287281 ⟨942013, by decide⟩ :=
  accepted_of_selected 12 287281 ⟨942013, by decide⟩ ⟨12, 2, 0, 942013, 287281, 2429, 65536⟩
    (by decide) selected_cut_35758

theorem selected_cut_35759 : selected 9 ⟨942045, by decide⟩
    (prefixPartial 12 287282) = some ⟨12, 2, 0, 942045, 287282, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_287282_942045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287282 ⟨942045, by decide⟩ :=
  accepted_of_selected 12 287282 ⟨942045, by decide⟩ ⟨12, 2, 0, 942045, 287282, 2305, 65536⟩
    (by decide) selected_cut_35759

theorem selected_cut_35760 : selected 9 ⟨942095, by decide⟩
    (prefixPartial 12 287283) = some ⟨12, 2, 0, 942095, 287283, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_287283_942095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287283 ⟨942095, by decide⟩ :=
  accepted_of_selected 12 287283 ⟨942095, by decide⟩ ⟨12, 2, 0, 942095, 287283, 2965, 65536⟩
    (by decide) selected_cut_35760

theorem unmarked_context_11_71820_942096 : frontier 10 ⟨942096, by decide⟩
    (prefixCache 11 71820) (prefixPartial 11 71820) = false := by
  decide +kernel

theorem node_context_11_71820_942096 : EJMOriginalGlobalDAGData.nodes 10 ⟨942096, by decide⟩ =
    .split (coordinate 11) (![⟨941981, by decide⟩,⟨942013, by decide⟩,⟨942045, by decide⟩,⟨942095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71820_942096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71820 ⟨942096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71820
    ⟨942096, by decide⟩ (by decide) (![⟨941981, by decide⟩,⟨942013, by decide⟩,⟨942045, by decide⟩,⟨942095, by decide⟩]) unmarked_context_11_71820_942096 node_context_11_71820_942096
  intro a
  fin_cases a
  · exact context_12_287280_941981
  · exact context_12_287281_942013
  · exact context_12_287282_942045
  · exact context_12_287283_942095

theorem selected_cut_35761 : selected 9 ⟨942139, by decide⟩
    (prefixPartial 12 287284) = some ⟨12, 2, 0, 942139, 287284, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_287284_942139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287284 ⟨942139, by decide⟩ :=
  accepted_of_selected 12 287284 ⟨942139, by decide⟩ ⟨12, 2, 0, 942139, 287284, 2865, 65536⟩
    (by decide) selected_cut_35761

theorem selected_cut_35762 : selected 9 ⟨942182, by decide⟩
    (prefixPartial 12 287285) = some ⟨12, 2, 0, 942182, 287285, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_287285_942182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287285 ⟨942182, by decide⟩ :=
  accepted_of_selected 12 287285 ⟨942182, by decide⟩ ⟨12, 2, 0, 942182, 287285, 2565, 65536⟩
    (by decide) selected_cut_35762

theorem selected_cut_35763 : selected 9 ⟨942214, by decide⟩
    (prefixPartial 12 287286) = some ⟨12, 2, 0, 942214, 287286, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_287286_942214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287286 ⟨942214, by decide⟩ :=
  accepted_of_selected 12 287286 ⟨942214, by decide⟩ ⟨12, 2, 0, 942214, 287286, 2333, 65536⟩
    (by decide) selected_cut_35763

theorem selected_cut_35764 : selected 9 ⟨942261, by decide⟩
    (prefixPartial 12 287287) = some ⟨12, 2, 0, 942261, 287287, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_287287_942261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287287 ⟨942261, by decide⟩ :=
  accepted_of_selected 12 287287 ⟨942261, by decide⟩ ⟨12, 2, 0, 942261, 287287, 2745, 65536⟩
    (by decide) selected_cut_35764

theorem unmarked_context_11_71821_942262 : frontier 10 ⟨942262, by decide⟩
    (prefixCache 11 71821) (prefixPartial 11 71821) = false := by
  decide +kernel

theorem node_context_11_71821_942262 : EJMOriginalGlobalDAGData.nodes 10 ⟨942262, by decide⟩ =
    .split (coordinate 11) (![⟨942139, by decide⟩,⟨942182, by decide⟩,⟨942214, by decide⟩,⟨942261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71821_942262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71821 ⟨942262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71821
    ⟨942262, by decide⟩ (by decide) (![⟨942139, by decide⟩,⟨942182, by decide⟩,⟨942214, by decide⟩,⟨942261, by decide⟩]) unmarked_context_11_71821_942262 node_context_11_71821_942262
  intro a
  fin_cases a
  · exact context_12_287284_942139
  · exact context_12_287285_942182
  · exact context_12_287286_942214
  · exact context_12_287287_942261

theorem selected_cut_35765 : selected 9 ⟨942327, by decide⟩
    (prefixPartial 12 287288) = some ⟨12, 2, 0, 942327, 287288, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_287288_942327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287288 ⟨942327, by decide⟩ :=
  accepted_of_selected 12 287288 ⟨942327, by decide⟩ ⟨12, 2, 0, 942327, 287288, 3261, 65536⟩
    (by decide) selected_cut_35765

theorem selected_cut_35766 : selected 9 ⟨942372, by decide⟩
    (prefixPartial 12 287289) = some ⟨12, 2, 0, 942372, 287289, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_287289_942372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287289 ⟨942372, by decide⟩ :=
  accepted_of_selected 12 287289 ⟨942372, by decide⟩ ⟨12, 2, 0, 942372, 287289, 2785, 65536⟩
    (by decide) selected_cut_35766

theorem selected_cut_35767 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 287290) = some ⟨12, 1, 0, 893903, 287290, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287290_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287290 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 287290 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 287290, 1, 65536⟩
    (by decide) selected_cut_35767

theorem selected_cut_35768 : selected 9 ⟨942432, by decide⟩
    (prefixPartial 12 287291) = some ⟨12, 2, 0, 942432, 287291, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_287291_942432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287291 ⟨942432, by decide⟩ :=
  accepted_of_selected 12 287291 ⟨942432, by decide⟩ ⟨12, 2, 0, 942432, 287291, 3025, 65536⟩
    (by decide) selected_cut_35768

theorem unmarked_context_11_71822_942433 : frontier 10 ⟨942433, by decide⟩
    (prefixCache 11 71822) (prefixPartial 11 71822) = false := by
  decide +kernel

theorem node_context_11_71822_942433 : EJMOriginalGlobalDAGData.nodes 10 ⟨942433, by decide⟩ =
    .split (coordinate 11) (![⟨942327, by decide⟩,⟨942372, by decide⟩,⟨893903, by decide⟩,⟨942432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71822_942433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71822 ⟨942433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71822
    ⟨942433, by decide⟩ (by decide) (![⟨942327, by decide⟩,⟨942372, by decide⟩,⟨893903, by decide⟩,⟨942432, by decide⟩]) unmarked_context_11_71822_942433 node_context_11_71822_942433
  intro a
  fin_cases a
  · exact context_12_287288_942327
  · exact context_12_287289_942372
  · exact context_12_287290_893903
  · exact context_12_287291_942432

theorem selected_cut_35769 : selected 9 ⟨942467, by decide⟩
    (prefixPartial 12 287292) = some ⟨12, 2, 0, 942467, 287292, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_287292_942467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287292 ⟨942467, by decide⟩ :=
  accepted_of_selected 12 287292 ⟨942467, by decide⟩ ⟨12, 2, 0, 942467, 287292, 2605, 65536⟩
    (by decide) selected_cut_35769

theorem selected_cut_35770 : selected 9 ⟨942502, by decide⟩
    (prefixPartial 12 287293) = some ⟨12, 2, 0, 942502, 287293, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_287293_942502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287293 ⟨942502, by decide⟩ :=
  accepted_of_selected 12 287293 ⟨942502, by decide⟩ ⟨12, 2, 0, 942502, 287293, 2381, 65536⟩
    (by decide) selected_cut_35770

theorem selected_cut_35771 : selected 9 ⟨942541, by decide⟩
    (prefixPartial 12 287294) = some ⟨12, 2, 0, 942541, 287294, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_287294_942541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287294 ⟨942541, by decide⟩ :=
  accepted_of_selected 12 287294 ⟨942541, by decide⟩ ⟨12, 2, 0, 942541, 287294, 2345, 65536⟩
    (by decide) selected_cut_35771

theorem selected_cut_35772 : selected 9 ⟨942583, by decide⟩
    (prefixPartial 12 287295) = some ⟨12, 2, 0, 942583, 287295, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_287295_942583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287295 ⟨942583, by decide⟩ :=
  accepted_of_selected 12 287295 ⟨942583, by decide⟩ ⟨12, 2, 0, 942583, 287295, 2537, 65536⟩
    (by decide) selected_cut_35772

theorem unmarked_context_11_71823_942584 : frontier 10 ⟨942584, by decide⟩
    (prefixCache 11 71823) (prefixPartial 11 71823) = false := by
  decide +kernel

theorem node_context_11_71823_942584 : EJMOriginalGlobalDAGData.nodes 10 ⟨942584, by decide⟩ =
    .split (coordinate 11) (![⟨942467, by decide⟩,⟨942502, by decide⟩,⟨942541, by decide⟩,⟨942583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71823_942584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71823 ⟨942584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71823
    ⟨942584, by decide⟩ (by decide) (![⟨942467, by decide⟩,⟨942502, by decide⟩,⟨942541, by decide⟩,⟨942583, by decide⟩]) unmarked_context_11_71823_942584 node_context_11_71823_942584
  intro a
  fin_cases a
  · exact context_12_287292_942467
  · exact context_12_287293_942502
  · exact context_12_287294_942541
  · exact context_12_287295_942583

theorem unmarked_context_10_17955_942585 : frontier 11 ⟨942585, by decide⟩
    (prefixCache 10 17955) (prefixPartial 10 17955) = false := by
  decide +kernel

theorem node_context_10_17955_942585 : EJMOriginalGlobalDAGData.nodes 11 ⟨942585, by decide⟩ =
    .split (coordinate 10) (![⟨942096, by decide⟩,⟨942262, by decide⟩,⟨942433, by decide⟩,⟨942584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17955_942585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17955 ⟨942585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17955
    ⟨942585, by decide⟩ (by decide) (![⟨942096, by decide⟩,⟨942262, by decide⟩,⟨942433, by decide⟩,⟨942584, by decide⟩]) unmarked_context_10_17955_942585 node_context_10_17955_942585
  intro a
  fin_cases a
  · exact context_11_71820_942096
  · exact context_11_71821_942262
  · exact context_11_71822_942433
  · exact context_11_71823_942584

theorem unmarked_context_9_4488_942586 : frontier 12 ⟨942586, by decide⟩
    (prefixCache 9 4488) (prefixPartial 9 4488) = false := by
  decide +kernel

theorem node_context_9_4488_942586 : EJMOriginalGlobalDAGData.nodes 12 ⟨942586, by decide⟩ =
    .split (coordinate 9) (![⟨940275, by decide⟩,⟨941142, by decide⟩,⟨941950, by decide⟩,⟨942585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4488_942586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4488 ⟨942586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4488
    ⟨942586, by decide⟩ (by decide) (![⟨940275, by decide⟩,⟨941142, by decide⟩,⟨941950, by decide⟩,⟨942585, by decide⟩]) unmarked_context_9_4488_942586 node_context_9_4488_942586
  intro a
  fin_cases a
  · exact context_10_17952_940275
  · exact context_10_17953_941142
  · exact context_10_17954_941950
  · exact context_10_17955_942585

theorem selected_cut_35773 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71824) = some ⟨11, 1, 0, 907917, 71824, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71824_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71824 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71824 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71824, 1, 262144⟩
    (by decide) selected_cut_35773

theorem selected_cut_35774 : selected 9 ⟨942623, by decide⟩
    (prefixPartial 12 287300) = some ⟨12, 2, 0, 942623, 287300, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_287300_942623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287300 ⟨942623, by decide⟩ :=
  accepted_of_selected 12 287300 ⟨942623, by decide⟩ ⟨12, 2, 0, 942623, 287300, 2329, 65536⟩
    (by decide) selected_cut_35774

theorem selected_cut_35775 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287301) = some ⟨12, 1, 0, 896706, 287301, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287301_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287301 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287301 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287301, 1, 65536⟩
    (by decide) selected_cut_35775

theorem selected_cut_35776 : selected 9 ⟨942652, by decide⟩
    (prefixPartial 12 287302) = some ⟨12, 2, 0, 942652, 287302, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_287302_942652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287302 ⟨942652, by decide⟩ :=
  accepted_of_selected 12 287302 ⟨942652, by decide⟩ ⟨12, 2, 0, 942652, 287302, 2097, 65536⟩
    (by decide) selected_cut_35776

theorem selected_cut_35777 : selected 9 ⟨942685, by decide⟩
    (prefixPartial 12 287303) = some ⟨12, 2, 0, 942685, 287303, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_287303_942685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287303 ⟨942685, by decide⟩ :=
  accepted_of_selected 12 287303 ⟨942685, by decide⟩ ⟨12, 2, 0, 942685, 287303, 2301, 65536⟩
    (by decide) selected_cut_35777

theorem unmarked_context_11_71825_942686 : frontier 10 ⟨942686, by decide⟩
    (prefixCache 11 71825) (prefixPartial 11 71825) = false := by
  decide +kernel

theorem node_context_11_71825_942686 : EJMOriginalGlobalDAGData.nodes 10 ⟨942686, by decide⟩ =
    .split (coordinate 11) (![⟨942623, by decide⟩,⟨896706, by decide⟩,⟨942652, by decide⟩,⟨942685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71825_942686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71825 ⟨942686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71825
    ⟨942686, by decide⟩ (by decide) (![⟨942623, by decide⟩,⟨896706, by decide⟩,⟨942652, by decide⟩,⟨942685, by decide⟩]) unmarked_context_11_71825_942686 node_context_11_71825_942686
  intro a
  fin_cases a
  · exact context_12_287300_942623
  · exact context_12_287301_896706
  · exact context_12_287302_942652
  · exact context_12_287303_942685

theorem selected_cut_35778 : selected 9 ⟨942728, by decide⟩
    (prefixPartial 12 287304) = some ⟨12, 2, 0, 942728, 287304, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_287304_942728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287304 ⟨942728, by decide⟩ :=
  accepted_of_selected 12 287304 ⟨942728, by decide⟩ ⟨12, 2, 0, 942728, 287304, 2581, 65536⟩
    (by decide) selected_cut_35778

theorem selected_cut_35779 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287305) = some ⟨12, 1, 0, 896706, 287305, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287305_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287305 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287305 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287305, 1, 65536⟩
    (by decide) selected_cut_35779

theorem selected_cut_35780 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 287306) = some ⟨12, 1, 0, 893903, 287306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287306_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287306 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 287306 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 287306, 1, 65536⟩
    (by decide) selected_cut_35780

theorem selected_cut_35781 : selected 9 ⟨942773, by decide⟩
    (prefixPartial 12 287307) = some ⟨12, 2, 0, 942773, 287307, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_287307_942773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287307 ⟨942773, by decide⟩ :=
  accepted_of_selected 12 287307 ⟨942773, by decide⟩ ⟨12, 2, 0, 942773, 287307, 2545, 65536⟩
    (by decide) selected_cut_35781

theorem unmarked_context_11_71826_942774 : frontier 10 ⟨942774, by decide⟩
    (prefixCache 11 71826) (prefixPartial 11 71826) = false := by
  decide +kernel

theorem node_context_11_71826_942774 : EJMOriginalGlobalDAGData.nodes 10 ⟨942774, by decide⟩ =
    .split (coordinate 11) (![⟨942728, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨942773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71826_942774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71826 ⟨942774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71826
    ⟨942774, by decide⟩ (by decide) (![⟨942728, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨942773, by decide⟩]) unmarked_context_11_71826_942774 node_context_11_71826_942774
  intro a
  fin_cases a
  · exact context_12_287304_942728
  · exact context_12_287305_896706
  · exact context_12_287306_893903
  · exact context_12_287307_942773

theorem selected_cut_35782 : selected 9 ⟨942815, by decide⟩
    (prefixPartial 12 287308) = some ⟨12, 2, 0, 942815, 287308, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_287308_942815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287308 ⟨942815, by decide⟩ :=
  accepted_of_selected 12 287308 ⟨942815, by decide⟩ ⟨12, 2, 0, 942815, 287308, 2473, 65536⟩
    (by decide) selected_cut_35782

theorem selected_cut_35783 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287309) = some ⟨12, 1, 0, 896706, 287309, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287309_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287309 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287309 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287309, 1, 65536⟩
    (by decide) selected_cut_35783

theorem selected_cut_35784 : selected 9 ⟨942849, by decide⟩
    (prefixPartial 12 287310) = some ⟨12, 2, 0, 942849, 287310, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_287310_942849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287310 ⟨942849, by decide⟩ :=
  accepted_of_selected 12 287310 ⟨942849, by decide⟩ ⟨12, 2, 0, 942849, 287310, 2117, 65536⟩
    (by decide) selected_cut_35784

theorem selected_cut_35785 : selected 9 ⟨942883, by decide⟩
    (prefixPartial 12 287311) = some ⟨12, 2, 0, 942883, 287311, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_287311_942883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287311 ⟨942883, by decide⟩ :=
  accepted_of_selected 12 287311 ⟨942883, by decide⟩ ⟨12, 2, 0, 942883, 287311, 2345, 65536⟩
    (by decide) selected_cut_35785

theorem unmarked_context_11_71827_942884 : frontier 10 ⟨942884, by decide⟩
    (prefixCache 11 71827) (prefixPartial 11 71827) = false := by
  decide +kernel

theorem node_context_11_71827_942884 : EJMOriginalGlobalDAGData.nodes 10 ⟨942884, by decide⟩ =
    .split (coordinate 11) (![⟨942815, by decide⟩,⟨896706, by decide⟩,⟨942849, by decide⟩,⟨942883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71827_942884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71827 ⟨942884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71827
    ⟨942884, by decide⟩ (by decide) (![⟨942815, by decide⟩,⟨896706, by decide⟩,⟨942849, by decide⟩,⟨942883, by decide⟩]) unmarked_context_11_71827_942884 node_context_11_71827_942884
  intro a
  fin_cases a
  · exact context_12_287308_942815
  · exact context_12_287309_896706
  · exact context_12_287310_942849
  · exact context_12_287311_942883

theorem unmarked_context_10_17956_942885 : frontier 11 ⟨942885, by decide⟩
    (prefixCache 10 17956) (prefixPartial 10 17956) = false := by
  decide +kernel

theorem node_context_10_17956_942885 : EJMOriginalGlobalDAGData.nodes 11 ⟨942885, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨942686, by decide⟩,⟨942774, by decide⟩,⟨942884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17956_942885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17956 ⟨942885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17956
    ⟨942885, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨942686, by decide⟩,⟨942774, by decide⟩,⟨942884, by decide⟩]) unmarked_context_10_17956_942885 node_context_10_17956_942885
  intro a
  fin_cases a
  · exact context_11_71824_907917
  · exact context_11_71825_942686
  · exact context_11_71826_942774
  · exact context_11_71827_942884

theorem selected_cut_35786 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17957) = some ⟨10, 1, 0, 893098, 17957, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17957_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17957 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17957 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17957, 1, 1048576⟩
    (by decide) selected_cut_35786

theorem selected_cut_35787 : selected 9 ⟨942910, by decide⟩
    (prefixPartial 12 287328) = some ⟨12, 2, 0, 942910, 287328, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_287328_942910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287328 ⟨942910, by decide⟩ :=
  accepted_of_selected 12 287328 ⟨942910, by decide⟩ ⟨12, 2, 0, 942910, 287328, 1753, 65536⟩
    (by decide) selected_cut_35787

theorem selected_cut_35788 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287329) = some ⟨12, 1, 0, 896706, 287329, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287329_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287329 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287329 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287329, 1, 65536⟩
    (by decide) selected_cut_35788

theorem selected_cut_35789 : selected 9 ⟨942933, by decide⟩
    (prefixPartial 12 287330) = some ⟨12, 2, 0, 942933, 287330, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_287330_942933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287330 ⟨942933, by decide⟩ :=
  accepted_of_selected 12 287330 ⟨942933, by decide⟩ ⟨12, 2, 0, 942933, 287330, 1733, 65536⟩
    (by decide) selected_cut_35789

theorem selected_cut_35790 : selected 9 ⟨942965, by decide⟩
    (prefixPartial 12 287331) = some ⟨12, 2, 0, 942965, 287331, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_287331_942965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287331 ⟨942965, by decide⟩ :=
  accepted_of_selected 12 287331 ⟨942965, by decide⟩ ⟨12, 2, 0, 942965, 287331, 2045, 65536⟩
    (by decide) selected_cut_35790

theorem unmarked_context_11_71832_942966 : frontier 10 ⟨942966, by decide⟩
    (prefixCache 11 71832) (prefixPartial 11 71832) = false := by
  decide +kernel

theorem node_context_11_71832_942966 : EJMOriginalGlobalDAGData.nodes 10 ⟨942966, by decide⟩ =
    .split (coordinate 11) (![⟨942910, by decide⟩,⟨896706, by decide⟩,⟨942933, by decide⟩,⟨942965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71832_942966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71832 ⟨942966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71832
    ⟨942966, by decide⟩ (by decide) (![⟨942910, by decide⟩,⟨896706, by decide⟩,⟨942933, by decide⟩,⟨942965, by decide⟩]) unmarked_context_11_71832_942966 node_context_11_71832_942966
  intro a
  fin_cases a
  · exact context_12_287328_942910
  · exact context_12_287329_896706
  · exact context_12_287330_942933
  · exact context_12_287331_942965

theorem selected_cut_35791 : selected 9 ⟨942986, by decide⟩
    (prefixPartial 12 287332) = some ⟨12, 2, 0, 942986, 287332, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_287332_942986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287332 ⟨942986, by decide⟩ :=
  accepted_of_selected 12 287332 ⟨942986, by decide⟩ ⟨12, 2, 0, 942986, 287332, 1865, 65536⟩
    (by decide) selected_cut_35791

theorem selected_cut_35792 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287333) = some ⟨12, 1, 0, 896706, 287333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287333_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287333 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287333 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287333, 1, 65536⟩
    (by decide) selected_cut_35792

theorem selected_cut_35793 : selected 9 ⟨943010, by decide⟩
    (prefixPartial 12 287334) = some ⟨12, 2, 0, 943010, 287334, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_287334_943010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287334 ⟨943010, by decide⟩ :=
  accepted_of_selected 12 287334 ⟨943010, by decide⟩ ⟨12, 2, 0, 943010, 287334, 1861, 65536⟩
    (by decide) selected_cut_35793

theorem selected_cut_35794 : selected 9 ⟨943037, by decide⟩
    (prefixPartial 12 287335) = some ⟨12, 2, 0, 943037, 287335, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_287335_943037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287335 ⟨943037, by decide⟩ :=
  accepted_of_selected 12 287335 ⟨943037, by decide⟩ ⟨12, 2, 0, 943037, 287335, 1877, 65536⟩
    (by decide) selected_cut_35794

theorem unmarked_context_11_71833_943038 : frontier 10 ⟨943038, by decide⟩
    (prefixCache 11 71833) (prefixPartial 11 71833) = false := by
  decide +kernel

theorem node_context_11_71833_943038 : EJMOriginalGlobalDAGData.nodes 10 ⟨943038, by decide⟩ =
    .split (coordinate 11) (![⟨942986, by decide⟩,⟨896706, by decide⟩,⟨943010, by decide⟩,⟨943037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71833_943038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71833 ⟨943038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71833
    ⟨943038, by decide⟩ (by decide) (![⟨942986, by decide⟩,⟨896706, by decide⟩,⟨943010, by decide⟩,⟨943037, by decide⟩]) unmarked_context_11_71833_943038 node_context_11_71833_943038
  intro a
  fin_cases a
  · exact context_12_287332_942986
  · exact context_12_287333_896706
  · exact context_12_287334_943010
  · exact context_12_287335_943037

theorem selected_cut_35795 : selected 10 ⟨943092, by decide⟩
    (prefixPartial 11 71834) = some ⟨11, 2, 0, 943092, 71834, 3789, 262144⟩ := by
  decide +kernel

theorem context_11_71834_943092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71834 ⟨943092, by decide⟩ :=
  accepted_of_selected 11 71834 ⟨943092, by decide⟩ ⟨11, 2, 0, 943092, 71834, 3789, 262144⟩
    (by decide) selected_cut_35795

theorem selected_cut_35796 : selected 9 ⟨943124, by decide⟩
    (prefixPartial 12 287340) = some ⟨12, 2, 0, 943124, 287340, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_287340_943124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287340 ⟨943124, by decide⟩ :=
  accepted_of_selected 12 287340 ⟨943124, by decide⟩ ⟨12, 2, 0, 943124, 287340, 2061, 65536⟩
    (by decide) selected_cut_35796

theorem selected_cut_35797 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287341) = some ⟨12, 1, 0, 896706, 287341, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287341_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287341 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287341 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287341, 1, 65536⟩
    (by decide) selected_cut_35797

theorem selected_cut_35798 : selected 9 ⟨943161, by decide⟩
    (prefixPartial 12 287342) = some ⟨12, 2, 0, 943161, 287342, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_287342_943161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287342 ⟨943161, by decide⟩ :=
  accepted_of_selected 12 287342 ⟨943161, by decide⟩ ⟨12, 2, 0, 943161, 287342, 2025, 65536⟩
    (by decide) selected_cut_35798

theorem selected_cut_35799 : selected 9 ⟨943196, by decide⟩
    (prefixPartial 12 287343) = some ⟨12, 2, 0, 943196, 287343, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_287343_943196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287343 ⟨943196, by decide⟩ :=
  accepted_of_selected 12 287343 ⟨943196, by decide⟩ ⟨12, 2, 0, 943196, 287343, 2073, 65536⟩
    (by decide) selected_cut_35799

theorem unmarked_context_11_71835_943197 : frontier 10 ⟨943197, by decide⟩
    (prefixCache 11 71835) (prefixPartial 11 71835) = false := by
  decide +kernel

theorem node_context_11_71835_943197 : EJMOriginalGlobalDAGData.nodes 10 ⟨943197, by decide⟩ =
    .split (coordinate 11) (![⟨943124, by decide⟩,⟨896706, by decide⟩,⟨943161, by decide⟩,⟨943196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71835_943197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71835 ⟨943197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71835
    ⟨943197, by decide⟩ (by decide) (![⟨943124, by decide⟩,⟨896706, by decide⟩,⟨943161, by decide⟩,⟨943196, by decide⟩]) unmarked_context_11_71835_943197 node_context_11_71835_943197
  intro a
  fin_cases a
  · exact context_12_287340_943124
  · exact context_12_287341_896706
  · exact context_12_287342_943161
  · exact context_12_287343_943196

theorem unmarked_context_10_17958_943198 : frontier 11 ⟨943198, by decide⟩
    (prefixCache 10 17958) (prefixPartial 10 17958) = false := by
  decide +kernel

theorem node_context_10_17958_943198 : EJMOriginalGlobalDAGData.nodes 11 ⟨943198, by decide⟩ =
    .split (coordinate 10) (![⟨942966, by decide⟩,⟨943038, by decide⟩,⟨943092, by decide⟩,⟨943197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17958_943198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17958 ⟨943198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17958
    ⟨943198, by decide⟩ (by decide) (![⟨942966, by decide⟩,⟨943038, by decide⟩,⟨943092, by decide⟩,⟨943197, by decide⟩]) unmarked_context_10_17958_943198 node_context_10_17958_943198
  intro a
  fin_cases a
  · exact context_11_71832_942966
  · exact context_11_71833_943038
  · exact context_11_71834_943092
  · exact context_11_71835_943197

theorem selected_cut_35800 : selected 9 ⟨943212, by decide⟩
    (prefixPartial 12 287344) = some ⟨12, 2, 0, 943212, 287344, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_287344_943212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287344 ⟨943212, by decide⟩ :=
  accepted_of_selected 12 287344 ⟨943212, by decide⟩ ⟨12, 2, 0, 943212, 287344, 1549, 65536⟩
    (by decide) selected_cut_35800

theorem selected_cut_35801 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287345) = some ⟨12, 1, 0, 896706, 287345, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287345_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287345 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287345 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287345, 1, 65536⟩
    (by decide) selected_cut_35801

theorem selected_cut_35802 : selected 9 ⟨943233, by decide⟩
    (prefixPartial 12 287346) = some ⟨12, 2, 0, 943233, 287346, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_287346_943233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287346 ⟨943233, by decide⟩ :=
  accepted_of_selected 12 287346 ⟨943233, by decide⟩ ⟨12, 2, 0, 943233, 287346, 1477, 65536⟩
    (by decide) selected_cut_35802

theorem selected_cut_35803 : selected 9 ⟨943263, by decide⟩
    (prefixPartial 12 287347) = some ⟨12, 2, 0, 943263, 287347, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_287347_943263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287347 ⟨943263, by decide⟩ :=
  accepted_of_selected 12 287347 ⟨943263, by decide⟩ ⟨12, 2, 0, 943263, 287347, 1969, 65536⟩
    (by decide) selected_cut_35803

theorem unmarked_context_11_71836_943264 : frontier 10 ⟨943264, by decide⟩
    (prefixCache 11 71836) (prefixPartial 11 71836) = false := by
  decide +kernel

theorem node_context_11_71836_943264 : EJMOriginalGlobalDAGData.nodes 10 ⟨943264, by decide⟩ =
    .split (coordinate 11) (![⟨943212, by decide⟩,⟨896706, by decide⟩,⟨943233, by decide⟩,⟨943263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71836_943264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71836 ⟨943264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71836
    ⟨943264, by decide⟩ (by decide) (![⟨943212, by decide⟩,⟨896706, by decide⟩,⟨943233, by decide⟩,⟨943263, by decide⟩]) unmarked_context_11_71836_943264 node_context_11_71836_943264
  intro a
  fin_cases a
  · exact context_12_287344_943212
  · exact context_12_287345_896706
  · exact context_12_287346_943233
  · exact context_12_287347_943263

theorem selected_cut_35804 : selected 9 ⟨943284, by decide⟩
    (prefixPartial 12 287348) = some ⟨12, 2, 0, 943284, 287348, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_287348_943284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287348 ⟨943284, by decide⟩ :=
  accepted_of_selected 12 287348 ⟨943284, by decide⟩ ⟨12, 2, 0, 943284, 287348, 1577, 65536⟩
    (by decide) selected_cut_35804

theorem selected_cut_35805 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287349) = some ⟨12, 1, 0, 896706, 287349, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287349_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287349 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287349 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287349, 1, 65536⟩
    (by decide) selected_cut_35805

theorem selected_cut_35806 : selected 9 ⟨943301, by decide⟩
    (prefixPartial 12 287350) = some ⟨12, 2, 0, 943301, 287350, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_287350_943301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287350 ⟨943301, by decide⟩ :=
  accepted_of_selected 12 287350 ⟨943301, by decide⟩ ⟨12, 2, 0, 943301, 287350, 1433, 65536⟩
    (by decide) selected_cut_35806

theorem selected_cut_35807 : selected 9 ⟨943333, by decide⟩
    (prefixPartial 12 287351) = some ⟨12, 2, 0, 943333, 287351, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_287351_943333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287351 ⟨943333, by decide⟩ :=
  accepted_of_selected 12 287351 ⟨943333, by decide⟩ ⟨12, 2, 0, 943333, 287351, 1813, 65536⟩
    (by decide) selected_cut_35807

theorem unmarked_context_11_71837_943334 : frontier 10 ⟨943334, by decide⟩
    (prefixCache 11 71837) (prefixPartial 11 71837) = false := by
  decide +kernel

theorem node_context_11_71837_943334 : EJMOriginalGlobalDAGData.nodes 10 ⟨943334, by decide⟩ =
    .split (coordinate 11) (![⟨943284, by decide⟩,⟨896706, by decide⟩,⟨943301, by decide⟩,⟨943333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71837_943334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71837 ⟨943334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71837
    ⟨943334, by decide⟩ (by decide) (![⟨943284, by decide⟩,⟨896706, by decide⟩,⟨943301, by decide⟩,⟨943333, by decide⟩]) unmarked_context_11_71837_943334 node_context_11_71837_943334
  intro a
  fin_cases a
  · exact context_12_287348_943284
  · exact context_12_287349_896706
  · exact context_12_287350_943301
  · exact context_12_287351_943333

theorem selected_cut_35808 : selected 10 ⟨943387, by decide⟩
    (prefixPartial 11 71838) = some ⟨11, 2, 0, 943387, 71838, 3529, 262144⟩ := by
  decide +kernel

theorem context_11_71838_943387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71838 ⟨943387, by decide⟩ :=
  accepted_of_selected 11 71838 ⟨943387, by decide⟩ ⟨11, 2, 0, 943387, 71838, 3529, 262144⟩
    (by decide) selected_cut_35808

theorem selected_cut_35809 : selected 9 ⟨943409, by decide⟩
    (prefixPartial 12 287356) = some ⟨12, 2, 0, 943409, 287356, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_287356_943409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287356 ⟨943409, by decide⟩ :=
  accepted_of_selected 12 287356 ⟨943409, by decide⟩ ⟨12, 2, 0, 943409, 287356, 1597, 65536⟩
    (by decide) selected_cut_35809

theorem selected_cut_35810 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287357) = some ⟨12, 1, 0, 896706, 287357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287357_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287357 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287357 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287357, 1, 65536⟩
    (by decide) selected_cut_35810

theorem selected_cut_35811 : selected 9 ⟨943431, by decide⟩
    (prefixPartial 12 287358) = some ⟨12, 2, 0, 943431, 287358, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_287358_943431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287358 ⟨943431, by decide⟩ :=
  accepted_of_selected 12 287358 ⟨943431, by decide⟩ ⟨12, 2, 0, 943431, 287358, 1469, 65536⟩
    (by decide) selected_cut_35811

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
