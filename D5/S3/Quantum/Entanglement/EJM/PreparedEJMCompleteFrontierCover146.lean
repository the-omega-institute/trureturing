/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover145
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_26979_364256 : frontier 9 ⟨364256, by decide⟩
    (prefixCache 12 26979) (prefixPartial 12 26979) = false := by
  decide +kernel

theorem node_context_12_26979_364256 : EJMOriginalGlobalDAGData.nodes 9 ⟨364256, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364224, by decide⟩,⟨364247, by decide⟩,⟨364255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26979_364256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26979 ⟨364256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26979
    ⟨364256, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364224, by decide⟩,⟨364247, by decide⟩,⟨364255, by decide⟩]) unmarked_context_12_26979_364256 node_context_12_26979_364256
  intro a
  fin_cases a
  · exact context_13_107916_3444
  · exact context_13_107917_364224
  · exact context_13_107918_364247
  · exact context_13_107919_364255

theorem unmarked_context_11_6744_364257 : frontier 10 ⟨364257, by decide⟩
    (prefixCache 11 6744) (prefixPartial 11 6744) = false := by
  decide +kernel

theorem node_context_11_6744_364257 : EJMOriginalGlobalDAGData.nodes 10 ⟨364257, by decide⟩ =
    .split (coordinate 11) (![⟨364100, by decide⟩,⟨364154, by decide⟩,⟨364209, by decide⟩,⟨364256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6744_364257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6744 ⟨364257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6744
    ⟨364257, by decide⟩ (by decide) (![⟨364100, by decide⟩,⟨364154, by decide⟩,⟨364209, by decide⟩,⟨364256, by decide⟩]) unmarked_context_11_6744_364257 node_context_11_6744_364257
  intro a
  fin_cases a
  · exact context_12_26976_364100
  · exact context_12_26977_364154
  · exact context_12_26978_364209
  · exact context_12_26979_364256

theorem selected_cut_14020 : selected 9 ⟨364290, by decide⟩
    (prefixPartial 12 26980) = some ⟨12, 2, 0, 364290, 26980, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_26980_364290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26980 ⟨364290, by decide⟩ :=
  accepted_of_selected 12 26980 ⟨364290, by decide⟩ ⟨12, 2, 0, 364290, 26980, 3465, 65536⟩
    (by decide) selected_cut_14020

theorem selected_cut_14021 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 26981) = some ⟨12, 1, 0, 126884, 26981, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26981_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26981 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 26981 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 26981, 1, 65536⟩
    (by decide) selected_cut_14021

theorem selected_cut_14022 : selected 9 ⟨364330, by decide⟩
    (prefixPartial 12 26982) = some ⟨12, 2, 0, 364330, 26982, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_26982_364330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26982 ⟨364330, by decide⟩ :=
  accepted_of_selected 12 26982 ⟨364330, by decide⟩ ⟨12, 2, 0, 364330, 26982, 3773, 65536⟩
    (by decide) selected_cut_14022

theorem selected_cut_14023 : selected 9 ⟨364368, by decide⟩
    (prefixPartial 12 26983) = some ⟨12, 2, 0, 364368, 26983, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_26983_364368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26983 ⟨364368, by decide⟩ :=
  accepted_of_selected 12 26983 ⟨364368, by decide⟩ ⟨12, 2, 0, 364368, 26983, 4085, 65536⟩
    (by decide) selected_cut_14023

theorem unmarked_context_11_6745_364369 : frontier 10 ⟨364369, by decide⟩
    (prefixCache 11 6745) (prefixPartial 11 6745) = false := by
  decide +kernel

theorem node_context_11_6745_364369 : EJMOriginalGlobalDAGData.nodes 10 ⟨364369, by decide⟩ =
    .split (coordinate 11) (![⟨364290, by decide⟩,⟨126884, by decide⟩,⟨364330, by decide⟩,⟨364368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6745_364369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6745 ⟨364369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6745
    ⟨364369, by decide⟩ (by decide) (![⟨364290, by decide⟩,⟨126884, by decide⟩,⟨364330, by decide⟩,⟨364368, by decide⟩]) unmarked_context_11_6745_364369 node_context_11_6745_364369
  intro a
  fin_cases a
  · exact context_12_26980_364290
  · exact context_12_26981_126884
  · exact context_12_26982_364330
  · exact context_12_26983_364368

theorem selected_cut_14024 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107936) = some ⟨13, 1, 0, 3444, 107936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107936, 1, 16384⟩
    (by decide) selected_cut_14024

theorem selected_cut_14025 : selected 8 ⟨364399, by decide⟩
    (prefixPartial 13 107937) = some ⟨13, 2, 0, 364399, 107937, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_107937_364399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107937 ⟨364399, by decide⟩ :=
  accepted_of_selected 13 107937 ⟨364399, by decide⟩ ⟨13, 2, 0, 364399, 107937, 1609, 16384⟩
    (by decide) selected_cut_14025

theorem selected_cut_14026 : selected 8 ⟨364428, by decide⟩
    (prefixPartial 13 107938) = some ⟨13, 2, 0, 364428, 107938, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_107938_364428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107938 ⟨364428, by decide⟩ :=
  accepted_of_selected 13 107938 ⟨364428, by decide⟩ ⟨13, 2, 0, 364428, 107938, 2361, 16384⟩
    (by decide) selected_cut_14026

theorem selected_cut_14027 : selected 8 ⟨364444, by decide⟩
    (prefixPartial 13 107939) = some ⟨13, 2, 0, 364444, 107939, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_107939_364444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107939 ⟨364444, by decide⟩ :=
  accepted_of_selected 13 107939 ⟨364444, by decide⟩ ⟨13, 2, 0, 364444, 107939, 1249, 16384⟩
    (by decide) selected_cut_14027

theorem unmarked_context_12_26984_364445 : frontier 9 ⟨364445, by decide⟩
    (prefixCache 12 26984) (prefixPartial 12 26984) = false := by
  decide +kernel

theorem node_context_12_26984_364445 : EJMOriginalGlobalDAGData.nodes 9 ⟨364445, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364399, by decide⟩,⟨364428, by decide⟩,⟨364444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26984_364445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26984 ⟨364445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26984
    ⟨364445, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364399, by decide⟩,⟨364428, by decide⟩,⟨364444, by decide⟩]) unmarked_context_12_26984_364445 node_context_12_26984_364445
  intro a
  fin_cases a
  · exact context_13_107936_3444
  · exact context_13_107937_364399
  · exact context_13_107938_364428
  · exact context_13_107939_364444

theorem selected_cut_14028 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107940) = some ⟨13, 1, 0, 3444, 107940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107940, 1, 16384⟩
    (by decide) selected_cut_14028

theorem selected_cut_14029 : selected 8 ⟨364475, by decide⟩
    (prefixPartial 13 107941) = some ⟨13, 2, 0, 364475, 107941, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_107941_364475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107941 ⟨364475, by decide⟩ :=
  accepted_of_selected 13 107941 ⟨364475, by decide⟩ ⟨13, 2, 0, 364475, 107941, 1753, 16384⟩
    (by decide) selected_cut_14029

theorem selected_cut_14030 : selected 8 ⟨364526, by decide⟩
    (prefixPartial 13 107942) = some ⟨13, 2, 0, 364526, 107942, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_107942_364526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107942 ⟨364526, by decide⟩ :=
  accepted_of_selected 13 107942 ⟨364526, by decide⟩ ⟨13, 2, 0, 364526, 107942, 3009, 16384⟩
    (by decide) selected_cut_14030

theorem selected_cut_14031 : selected 8 ⟨364558, by decide⟩
    (prefixPartial 13 107943) = some ⟨13, 2, 0, 364558, 107943, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_107943_364558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107943 ⟨364558, by decide⟩ :=
  accepted_of_selected 13 107943 ⟨364558, by decide⟩ ⟨13, 2, 0, 364558, 107943, 1737, 16384⟩
    (by decide) selected_cut_14031

theorem unmarked_context_12_26985_364559 : frontier 9 ⟨364559, by decide⟩
    (prefixCache 12 26985) (prefixPartial 12 26985) = false := by
  decide +kernel

theorem node_context_12_26985_364559 : EJMOriginalGlobalDAGData.nodes 9 ⟨364559, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364475, by decide⟩,⟨364526, by decide⟩,⟨364558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26985_364559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26985 ⟨364559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26985
    ⟨364559, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364475, by decide⟩,⟨364526, by decide⟩,⟨364558, by decide⟩]) unmarked_context_12_26985_364559 node_context_12_26985_364559
  intro a
  fin_cases a
  · exact context_13_107940_3444
  · exact context_13_107941_364475
  · exact context_13_107942_364526
  · exact context_13_107943_364558

theorem selected_cut_14032 : selected 9 ⟨364560, by decide⟩
    (prefixPartial 12 26986) = some ⟨12, 1, 0, 364560, 26986, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26986_364560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26986 ⟨364560, by decide⟩ :=
  accepted_of_selected 12 26986 ⟨364560, by decide⟩ ⟨12, 1, 0, 364560, 26986, 1, 65536⟩
    (by decide) selected_cut_14032

theorem selected_cut_14033 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107948) = some ⟨13, 1, 0, 3444, 107948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107948, 1, 16384⟩
    (by decide) selected_cut_14033

theorem selected_cut_14034 : selected 8 ⟨364590, by decide⟩
    (prefixPartial 13 107949) = some ⟨13, 2, 0, 364590, 107949, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_107949_364590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107949 ⟨364590, by decide⟩ :=
  accepted_of_selected 13 107949 ⟨364590, by decide⟩ ⟨13, 2, 0, 364590, 107949, 1449, 16384⟩
    (by decide) selected_cut_14034

theorem selected_cut_14035 : selected 8 ⟨364623, by decide⟩
    (prefixPartial 13 107950) = some ⟨13, 2, 0, 364623, 107950, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_107950_364623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107950 ⟨364623, by decide⟩ :=
  accepted_of_selected 13 107950 ⟨364623, by decide⟩ ⟨13, 2, 0, 364623, 107950, 2649, 16384⟩
    (by decide) selected_cut_14035

theorem selected_cut_14036 : selected 8 ⟨364635, by decide⟩
    (prefixPartial 13 107951) = some ⟨13, 2, 0, 364635, 107951, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_107951_364635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107951 ⟨364635, by decide⟩ :=
  accepted_of_selected 13 107951 ⟨364635, by decide⟩ ⟨13, 2, 0, 364635, 107951, 1337, 16384⟩
    (by decide) selected_cut_14036

theorem unmarked_context_12_26987_364636 : frontier 9 ⟨364636, by decide⟩
    (prefixCache 12 26987) (prefixPartial 12 26987) = false := by
  decide +kernel

theorem node_context_12_26987_364636 : EJMOriginalGlobalDAGData.nodes 9 ⟨364636, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364590, by decide⟩,⟨364623, by decide⟩,⟨364635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26987_364636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26987 ⟨364636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26987
    ⟨364636, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364590, by decide⟩,⟨364623, by decide⟩,⟨364635, by decide⟩]) unmarked_context_12_26987_364636 node_context_12_26987_364636
  intro a
  fin_cases a
  · exact context_13_107948_3444
  · exact context_13_107949_364590
  · exact context_13_107950_364623
  · exact context_13_107951_364635

theorem unmarked_context_11_6746_364637 : frontier 10 ⟨364637, by decide⟩
    (prefixCache 11 6746) (prefixPartial 11 6746) = false := by
  decide +kernel

theorem node_context_11_6746_364637 : EJMOriginalGlobalDAGData.nodes 10 ⟨364637, by decide⟩ =
    .split (coordinate 11) (![⟨364445, by decide⟩,⟨364559, by decide⟩,⟨364560, by decide⟩,⟨364636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6746_364637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6746 ⟨364637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6746
    ⟨364637, by decide⟩ (by decide) (![⟨364445, by decide⟩,⟨364559, by decide⟩,⟨364560, by decide⟩,⟨364636, by decide⟩]) unmarked_context_11_6746_364637 node_context_11_6746_364637
  intro a
  fin_cases a
  · exact context_12_26984_364445
  · exact context_12_26985_364559
  · exact context_12_26986_364560
  · exact context_12_26987_364636

theorem selected_cut_14037 : selected 9 ⟨364677, by decide⟩
    (prefixPartial 12 26988) = some ⟨12, 2, 0, 364677, 26988, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_26988_364677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26988 ⟨364677, by decide⟩ :=
  accepted_of_selected 12 26988 ⟨364677, by decide⟩ ⟨12, 2, 0, 364677, 26988, 3897, 65536⟩
    (by decide) selected_cut_14037

theorem selected_cut_14038 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107956) = some ⟨13, 1, 0, 3444, 107956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107956, 1, 16384⟩
    (by decide) selected_cut_14038

theorem selected_cut_14039 : selected 8 ⟨364690, by decide⟩
    (prefixPartial 13 107957) = some ⟨13, 2, 0, 364690, 107957, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_107957_364690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107957 ⟨364690, by decide⟩ :=
  accepted_of_selected 13 107957 ⟨364690, by decide⟩ ⟨13, 2, 0, 364690, 107957, 1017, 16384⟩
    (by decide) selected_cut_14039

theorem selected_cut_14040 : selected 8 ⟨364713, by decide⟩
    (prefixPartial 13 107958) = some ⟨13, 2, 0, 364713, 107958, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_107958_364713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107958 ⟨364713, by decide⟩ :=
  accepted_of_selected 13 107958 ⟨364713, by decide⟩ ⟨13, 2, 0, 364713, 107958, 2297, 16384⟩
    (by decide) selected_cut_14040

theorem selected_cut_14041 : selected 8 ⟨364736, by decide⟩
    (prefixPartial 13 107959) = some ⟨13, 2, 0, 364736, 107959, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_107959_364736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107959 ⟨364736, by decide⟩ :=
  accepted_of_selected 13 107959 ⟨364736, by decide⟩ ⟨13, 2, 0, 364736, 107959, 1333, 16384⟩
    (by decide) selected_cut_14041

theorem unmarked_context_12_26989_364737 : frontier 9 ⟨364737, by decide⟩
    (prefixCache 12 26989) (prefixPartial 12 26989) = false := by
  decide +kernel

theorem node_context_12_26989_364737 : EJMOriginalGlobalDAGData.nodes 9 ⟨364737, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364690, by decide⟩,⟨364713, by decide⟩,⟨364736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26989_364737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26989 ⟨364737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26989
    ⟨364737, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364690, by decide⟩,⟨364713, by decide⟩,⟨364736, by decide⟩]) unmarked_context_12_26989_364737 node_context_12_26989_364737
  intro a
  fin_cases a
  · exact context_13_107956_3444
  · exact context_13_107957_364690
  · exact context_13_107958_364713
  · exact context_13_107959_364736

theorem selected_cut_14042 : selected 9 ⟨364775, by decide⟩
    (prefixPartial 12 26990) = some ⟨12, 2, 0, 364775, 26990, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_26990_364775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26990 ⟨364775, by decide⟩ :=
  accepted_of_selected 12 26990 ⟨364775, by decide⟩ ⟨12, 2, 0, 364775, 26990, 3785, 65536⟩
    (by decide) selected_cut_14042

theorem selected_cut_14043 : selected 9 ⟨364809, by decide⟩
    (prefixPartial 12 26991) = some ⟨12, 2, 0, 364809, 26991, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_26991_364809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26991 ⟨364809, by decide⟩ :=
  accepted_of_selected 12 26991 ⟨364809, by decide⟩ ⟨12, 2, 0, 364809, 26991, 4045, 65536⟩
    (by decide) selected_cut_14043

theorem unmarked_context_11_6747_364810 : frontier 10 ⟨364810, by decide⟩
    (prefixCache 11 6747) (prefixPartial 11 6747) = false := by
  decide +kernel

theorem node_context_11_6747_364810 : EJMOriginalGlobalDAGData.nodes 10 ⟨364810, by decide⟩ =
    .split (coordinate 11) (![⟨364677, by decide⟩,⟨364737, by decide⟩,⟨364775, by decide⟩,⟨364809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6747_364810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6747 ⟨364810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6747
    ⟨364810, by decide⟩ (by decide) (![⟨364677, by decide⟩,⟨364737, by decide⟩,⟨364775, by decide⟩,⟨364809, by decide⟩]) unmarked_context_11_6747_364810 node_context_11_6747_364810
  intro a
  fin_cases a
  · exact context_12_26988_364677
  · exact context_12_26989_364737
  · exact context_12_26990_364775
  · exact context_12_26991_364809

theorem unmarked_context_10_1686_364811 : frontier 11 ⟨364811, by decide⟩
    (prefixCache 10 1686) (prefixPartial 10 1686) = false := by
  decide +kernel

theorem node_context_10_1686_364811 : EJMOriginalGlobalDAGData.nodes 11 ⟨364811, by decide⟩ =
    .split (coordinate 10) (![⟨364257, by decide⟩,⟨364369, by decide⟩,⟨364637, by decide⟩,⟨364810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1686_364811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1686 ⟨364811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1686
    ⟨364811, by decide⟩ (by decide) (![⟨364257, by decide⟩,⟨364369, by decide⟩,⟨364637, by decide⟩,⟨364810, by decide⟩]) unmarked_context_10_1686_364811 node_context_10_1686_364811
  intro a
  fin_cases a
  · exact context_11_6744_364257
  · exact context_11_6745_364369
  · exact context_11_6746_364637
  · exact context_11_6747_364810

theorem selected_cut_14044 : selected 9 ⟨364837, by decide⟩
    (prefixPartial 12 26992) = some ⟨12, 2, 0, 364837, 26992, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_26992_364837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26992 ⟨364837, by decide⟩ :=
  accepted_of_selected 12 26992 ⟨364837, by decide⟩ ⟨12, 2, 0, 364837, 26992, 3685, 65536⟩
    (by decide) selected_cut_14044

theorem selected_cut_14045 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107972) = some ⟨13, 1, 0, 3444, 107972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107972, 1, 16384⟩
    (by decide) selected_cut_14045

theorem selected_cut_14046 : selected 8 ⟨364846, by decide⟩
    (prefixPartial 13 107973) = some ⟨13, 2, 0, 364846, 107973, 805, 16384⟩ := by
  decide +kernel

theorem context_13_107973_364846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107973 ⟨364846, by decide⟩ :=
  accepted_of_selected 13 107973 ⟨364846, by decide⟩ ⟨13, 2, 0, 364846, 107973, 805, 16384⟩
    (by decide) selected_cut_14046

theorem selected_cut_14047 : selected 8 ⟨364874, by decide⟩
    (prefixPartial 13 107974) = some ⟨13, 2, 0, 364874, 107974, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_107974_364874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107974 ⟨364874, by decide⟩ :=
  accepted_of_selected 13 107974 ⟨364874, by decide⟩ ⟨13, 2, 0, 364874, 107974, 2609, 16384⟩
    (by decide) selected_cut_14047

theorem selected_cut_14048 : selected 8 ⟨364888, by decide⟩
    (prefixPartial 13 107975) = some ⟨13, 2, 0, 364888, 107975, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_107975_364888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107975 ⟨364888, by decide⟩ :=
  accepted_of_selected 13 107975 ⟨364888, by decide⟩ ⟨13, 2, 0, 364888, 107975, 1261, 16384⟩
    (by decide) selected_cut_14048

theorem unmarked_context_12_26993_364889 : frontier 9 ⟨364889, by decide⟩
    (prefixCache 12 26993) (prefixPartial 12 26993) = false := by
  decide +kernel

theorem node_context_12_26993_364889 : EJMOriginalGlobalDAGData.nodes 9 ⟨364889, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364846, by decide⟩,⟨364874, by decide⟩,⟨364888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26993_364889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26993 ⟨364889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26993
    ⟨364889, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364846, by decide⟩,⟨364874, by decide⟩,⟨364888, by decide⟩]) unmarked_context_12_26993_364889 node_context_12_26993_364889
  intro a
  fin_cases a
  · exact context_13_107972_3444
  · exact context_13_107973_364846
  · exact context_13_107974_364874
  · exact context_13_107975_364888

theorem selected_cut_14049 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107976) = some ⟨13, 1, 0, 3444, 107976, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107976_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107976 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107976 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107976, 1, 16384⟩
    (by decide) selected_cut_14049

theorem selected_cut_14050 : selected 8 ⟨364898, by decide⟩
    (prefixPartial 13 107977) = some ⟨13, 2, 0, 364898, 107977, 737, 16384⟩ := by
  decide +kernel

theorem context_13_107977_364898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107977 ⟨364898, by decide⟩ :=
  accepted_of_selected 13 107977 ⟨364898, by decide⟩ ⟨13, 2, 0, 364898, 107977, 737, 16384⟩
    (by decide) selected_cut_14050

theorem selected_cut_14051 : selected 8 ⟨364928, by decide⟩
    (prefixPartial 13 107978) = some ⟨13, 2, 0, 364928, 107978, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_107978_364928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107978 ⟨364928, by decide⟩ :=
  accepted_of_selected 13 107978 ⟨364928, by decide⟩ ⟨13, 2, 0, 364928, 107978, 2449, 16384⟩
    (by decide) selected_cut_14051

theorem selected_cut_14052 : selected 8 ⟨364936, by decide⟩
    (prefixPartial 13 107979) = some ⟨13, 2, 0, 364936, 107979, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_107979_364936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107979 ⟨364936, by decide⟩ :=
  accepted_of_selected 13 107979 ⟨364936, by decide⟩ ⟨13, 2, 0, 364936, 107979, 1097, 16384⟩
    (by decide) selected_cut_14052

theorem unmarked_context_12_26994_364937 : frontier 9 ⟨364937, by decide⟩
    (prefixCache 12 26994) (prefixPartial 12 26994) = false := by
  decide +kernel

theorem node_context_12_26994_364937 : EJMOriginalGlobalDAGData.nodes 9 ⟨364937, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364898, by decide⟩,⟨364928, by decide⟩,⟨364936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26994_364937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26994 ⟨364937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26994
    ⟨364937, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364898, by decide⟩,⟨364928, by decide⟩,⟨364936, by decide⟩]) unmarked_context_12_26994_364937 node_context_12_26994_364937
  intro a
  fin_cases a
  · exact context_13_107976_3444
  · exact context_13_107977_364898
  · exact context_13_107978_364928
  · exact context_13_107979_364936

theorem selected_cut_14053 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107980) = some ⟨13, 1, 0, 3444, 107980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107980, 1, 16384⟩
    (by decide) selected_cut_14053

theorem selected_cut_14054 : selected 8 ⟨364945, by decide⟩
    (prefixPartial 13 107981) = some ⟨13, 2, 0, 364945, 107981, 677, 16384⟩ := by
  decide +kernel

theorem context_13_107981_364945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107981 ⟨364945, by decide⟩ :=
  accepted_of_selected 13 107981 ⟨364945, by decide⟩ ⟨13, 2, 0, 364945, 107981, 677, 16384⟩
    (by decide) selected_cut_14054

theorem selected_cut_14055 : selected 8 ⟨364979, by decide⟩
    (prefixPartial 13 107982) = some ⟨13, 2, 0, 364979, 107982, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_107982_364979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107982 ⟨364979, by decide⟩ :=
  accepted_of_selected 13 107982 ⟨364979, by decide⟩ ⟨13, 2, 0, 364979, 107982, 2653, 16384⟩
    (by decide) selected_cut_14055

theorem selected_cut_14056 : selected 8 ⟨364987, by decide⟩
    (prefixPartial 13 107983) = some ⟨13, 2, 0, 364987, 107983, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_107983_364987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107983 ⟨364987, by decide⟩ :=
  accepted_of_selected 13 107983 ⟨364987, by decide⟩ ⟨13, 2, 0, 364987, 107983, 1081, 16384⟩
    (by decide) selected_cut_14056

theorem unmarked_context_12_26995_364988 : frontier 9 ⟨364988, by decide⟩
    (prefixCache 12 26995) (prefixPartial 12 26995) = false := by
  decide +kernel

theorem node_context_12_26995_364988 : EJMOriginalGlobalDAGData.nodes 9 ⟨364988, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364945, by decide⟩,⟨364979, by decide⟩,⟨364987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26995_364988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26995 ⟨364988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26995
    ⟨364988, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364945, by decide⟩,⟨364979, by decide⟩,⟨364987, by decide⟩]) unmarked_context_12_26995_364988 node_context_12_26995_364988
  intro a
  fin_cases a
  · exact context_13_107980_3444
  · exact context_13_107981_364945
  · exact context_13_107982_364979
  · exact context_13_107983_364987

theorem unmarked_context_11_6748_364989 : frontier 10 ⟨364989, by decide⟩
    (prefixCache 11 6748) (prefixPartial 11 6748) = false := by
  decide +kernel

theorem node_context_11_6748_364989 : EJMOriginalGlobalDAGData.nodes 10 ⟨364989, by decide⟩ =
    .split (coordinate 11) (![⟨364837, by decide⟩,⟨364889, by decide⟩,⟨364937, by decide⟩,⟨364988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6748_364989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6748 ⟨364989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6748
    ⟨364989, by decide⟩ (by decide) (![⟨364837, by decide⟩,⟨364889, by decide⟩,⟨364937, by decide⟩,⟨364988, by decide⟩]) unmarked_context_11_6748_364989 node_context_11_6748_364989
  intro a
  fin_cases a
  · exact context_12_26992_364837
  · exact context_12_26993_364889
  · exact context_12_26994_364937
  · exact context_12_26995_364988

theorem selected_cut_14057 : selected 9 ⟨365020, by decide⟩
    (prefixPartial 12 26996) = some ⟨12, 2, 0, 365020, 26996, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_26996_365020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26996 ⟨365020, by decide⟩ :=
  accepted_of_selected 12 26996 ⟨365020, by decide⟩ ⟨12, 2, 0, 365020, 26996, 3069, 65536⟩
    (by decide) selected_cut_14057

theorem selected_cut_14058 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 26997) = some ⟨12, 1, 0, 126884, 26997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26997_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26997 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 26997 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 26997, 1, 65536⟩
    (by decide) selected_cut_14058

theorem selected_cut_14059 : selected 9 ⟨365055, by decide⟩
    (prefixPartial 12 26998) = some ⟨12, 2, 0, 365055, 26998, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_26998_365055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26998 ⟨365055, by decide⟩ :=
  accepted_of_selected 12 26998 ⟨365055, by decide⟩ ⟨12, 2, 0, 365055, 26998, 3545, 65536⟩
    (by decide) selected_cut_14059

theorem selected_cut_14060 : selected 9 ⟨365087, by decide⟩
    (prefixPartial 12 26999) = some ⟨12, 2, 0, 365087, 26999, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_26999_365087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26999 ⟨365087, by decide⟩ :=
  accepted_of_selected 12 26999 ⟨365087, by decide⟩ ⟨12, 2, 0, 365087, 26999, 3593, 65536⟩
    (by decide) selected_cut_14060

theorem unmarked_context_11_6749_365088 : frontier 10 ⟨365088, by decide⟩
    (prefixCache 11 6749) (prefixPartial 11 6749) = false := by
  decide +kernel

theorem node_context_11_6749_365088 : EJMOriginalGlobalDAGData.nodes 10 ⟨365088, by decide⟩ =
    .split (coordinate 11) (![⟨365020, by decide⟩,⟨126884, by decide⟩,⟨365055, by decide⟩,⟨365087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6749_365088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6749 ⟨365088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6749
    ⟨365088, by decide⟩ (by decide) (![⟨365020, by decide⟩,⟨126884, by decide⟩,⟨365055, by decide⟩,⟨365087, by decide⟩]) unmarked_context_11_6749_365088 node_context_11_6749_365088
  intro a
  fin_cases a
  · exact context_12_26996_365020
  · exact context_12_26997_126884
  · exact context_12_26998_365055
  · exact context_12_26999_365087

theorem selected_cut_14061 : selected 9 ⟨365117, by decide⟩
    (prefixPartial 12 27000) = some ⟨12, 2, 0, 365117, 27000, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_27000_365117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27000 ⟨365117, by decide⟩ :=
  accepted_of_selected 12 27000 ⟨365117, by decide⟩ ⟨12, 2, 0, 365117, 27000, 3513, 65536⟩
    (by decide) selected_cut_14061

theorem selected_cut_14062 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108004) = some ⟨13, 1, 0, 3444, 108004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108004, 1, 16384⟩
    (by decide) selected_cut_14062

theorem selected_cut_14063 : selected 8 ⟨365120, by decide⟩
    (prefixPartial 13 108005) = some ⟨13, 2, 0, 365120, 108005, 377, 16384⟩ := by
  decide +kernel

theorem context_13_108005_365120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108005 ⟨365120, by decide⟩ :=
  accepted_of_selected 13 108005 ⟨365120, by decide⟩ ⟨13, 2, 0, 365120, 108005, 377, 16384⟩
    (by decide) selected_cut_14063

theorem selected_cut_14064 : selected 8 ⟨365143, by decide⟩
    (prefixPartial 13 108006) = some ⟨13, 2, 0, 365143, 108006, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_108006_365143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108006 ⟨365143, by decide⟩ :=
  accepted_of_selected 13 108006 ⟨365143, by decide⟩ ⟨13, 2, 0, 365143, 108006, 2493, 16384⟩
    (by decide) selected_cut_14064

theorem selected_cut_14065 : selected 8 ⟨365162, by decide⟩
    (prefixPartial 13 108007) = some ⟨13, 2, 0, 365162, 108007, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_108007_365162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108007 ⟨365162, by decide⟩ :=
  accepted_of_selected 13 108007 ⟨365162, by decide⟩ ⟨13, 2, 0, 365162, 108007, 1365, 16384⟩
    (by decide) selected_cut_14065

theorem unmarked_context_12_27001_365163 : frontier 9 ⟨365163, by decide⟩
    (prefixCache 12 27001) (prefixPartial 12 27001) = false := by
  decide +kernel

theorem node_context_12_27001_365163 : EJMOriginalGlobalDAGData.nodes 9 ⟨365163, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨365120, by decide⟩,⟨365143, by decide⟩,⟨365162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27001_365163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27001 ⟨365163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27001
    ⟨365163, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨365120, by decide⟩,⟨365143, by decide⟩,⟨365162, by decide⟩]) unmarked_context_12_27001_365163 node_context_12_27001_365163
  intro a
  fin_cases a
  · exact context_13_108004_3444
  · exact context_13_108005_365120
  · exact context_13_108006_365143
  · exact context_13_108007_365162

theorem selected_cut_14066 : selected 9 ⟨365200, by decide⟩
    (prefixPartial 12 27002) = some ⟨12, 2, 0, 365200, 27002, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_27002_365200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27002 ⟨365200, by decide⟩ :=
  accepted_of_selected 12 27002 ⟨365200, by decide⟩ ⟨12, 2, 0, 365200, 27002, 3777, 65536⟩
    (by decide) selected_cut_14066

theorem selected_cut_14067 : selected 9 ⟨365236, by decide⟩
    (prefixPartial 12 27003) = some ⟨12, 2, 0, 365236, 27003, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_27003_365236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27003 ⟨365236, by decide⟩ :=
  accepted_of_selected 12 27003 ⟨365236, by decide⟩ ⟨12, 2, 0, 365236, 27003, 3789, 65536⟩
    (by decide) selected_cut_14067

theorem unmarked_context_11_6750_365237 : frontier 10 ⟨365237, by decide⟩
    (prefixCache 11 6750) (prefixPartial 11 6750) = false := by
  decide +kernel

theorem node_context_11_6750_365237 : EJMOriginalGlobalDAGData.nodes 10 ⟨365237, by decide⟩ =
    .split (coordinate 11) (![⟨365117, by decide⟩,⟨365163, by decide⟩,⟨365200, by decide⟩,⟨365236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6750_365237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6750 ⟨365237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6750
    ⟨365237, by decide⟩ (by decide) (![⟨365117, by decide⟩,⟨365163, by decide⟩,⟨365200, by decide⟩,⟨365236, by decide⟩]) unmarked_context_11_6750_365237 node_context_11_6750_365237
  intro a
  fin_cases a
  · exact context_12_27000_365117
  · exact context_12_27001_365163
  · exact context_12_27002_365200
  · exact context_12_27003_365236

theorem selected_cut_14068 : selected 9 ⟨365266, by decide⟩
    (prefixPartial 12 27004) = some ⟨12, 2, 0, 365266, 27004, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_27004_365266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27004 ⟨365266, by decide⟩ :=
  accepted_of_selected 12 27004 ⟨365266, by decide⟩ ⟨12, 2, 0, 365266, 27004, 3181, 65536⟩
    (by decide) selected_cut_14068

theorem selected_cut_14069 : selected 9 ⟨365304, by decide⟩
    (prefixPartial 12 27005) = some ⟨12, 2, 0, 365304, 27005, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_27005_365304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27005 ⟨365304, by decide⟩ :=
  accepted_of_selected 12 27005 ⟨365304, by decide⟩ ⟨12, 2, 0, 365304, 27005, 3897, 65536⟩
    (by decide) selected_cut_14069

theorem selected_cut_14070 : selected 9 ⟨365333, by decide⟩
    (prefixPartial 12 27006) = some ⟨12, 2, 0, 365333, 27006, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_27006_365333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27006 ⟨365333, by decide⟩ :=
  accepted_of_selected 12 27006 ⟨365333, by decide⟩ ⟨12, 2, 0, 365333, 27006, 3301, 65536⟩
    (by decide) selected_cut_14070

theorem selected_cut_14071 : selected 9 ⟨365364, by decide⟩
    (prefixPartial 12 27007) = some ⟨12, 2, 0, 365364, 27007, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_27007_365364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27007 ⟨365364, by decide⟩ :=
  accepted_of_selected 12 27007 ⟨365364, by decide⟩ ⟨12, 2, 0, 365364, 27007, 3513, 65536⟩
    (by decide) selected_cut_14071

theorem unmarked_context_11_6751_365365 : frontier 10 ⟨365365, by decide⟩
    (prefixCache 11 6751) (prefixPartial 11 6751) = false := by
  decide +kernel

theorem node_context_11_6751_365365 : EJMOriginalGlobalDAGData.nodes 10 ⟨365365, by decide⟩ =
    .split (coordinate 11) (![⟨365266, by decide⟩,⟨365304, by decide⟩,⟨365333, by decide⟩,⟨365364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6751_365365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6751 ⟨365365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6751
    ⟨365365, by decide⟩ (by decide) (![⟨365266, by decide⟩,⟨365304, by decide⟩,⟨365333, by decide⟩,⟨365364, by decide⟩]) unmarked_context_11_6751_365365 node_context_11_6751_365365
  intro a
  fin_cases a
  · exact context_12_27004_365266
  · exact context_12_27005_365304
  · exact context_12_27006_365333
  · exact context_12_27007_365364

theorem unmarked_context_10_1687_365366 : frontier 11 ⟨365366, by decide⟩
    (prefixCache 10 1687) (prefixPartial 10 1687) = false := by
  decide +kernel

theorem node_context_10_1687_365366 : EJMOriginalGlobalDAGData.nodes 11 ⟨365366, by decide⟩ =
    .split (coordinate 10) (![⟨364989, by decide⟩,⟨365088, by decide⟩,⟨365237, by decide⟩,⟨365365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1687_365366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1687 ⟨365366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1687
    ⟨365366, by decide⟩ (by decide) (![⟨364989, by decide⟩,⟨365088, by decide⟩,⟨365237, by decide⟩,⟨365365, by decide⟩]) unmarked_context_10_1687_365366 node_context_10_1687_365366
  intro a
  fin_cases a
  · exact context_11_6748_364989
  · exact context_11_6749_365088
  · exact context_11_6750_365237
  · exact context_11_6751_365365

theorem unmarked_context_9_421_365367 : frontier 12 ⟨365367, by decide⟩
    (prefixCache 9 421) (prefixPartial 9 421) = false := by
  decide +kernel

theorem node_context_9_421_365367 : EJMOriginalGlobalDAGData.nodes 12 ⟨365367, by decide⟩ =
    .split (coordinate 9) (![⟨363518, by decide⟩,⟨364066, by decide⟩,⟨364811, by decide⟩,⟨365366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_421_365367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 421 ⟨365367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 421
    ⟨365367, by decide⟩ (by decide) (![⟨363518, by decide⟩,⟨364066, by decide⟩,⟨364811, by decide⟩,⟨365366, by decide⟩]) unmarked_context_9_421_365367 node_context_9_421_365367
  intro a
  fin_cases a
  · exact context_10_1684_363518
  · exact context_10_1685_364066
  · exact context_10_1686_364811
  · exact context_10_1687_365366

theorem selected_cut_14072 : selected 9 ⟨365395, by decide⟩
    (prefixPartial 12 27008) = some ⟨12, 2, 0, 365395, 27008, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_27008_365395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27008 ⟨365395, by decide⟩ :=
  accepted_of_selected 12 27008 ⟨365395, by decide⟩ ⟨12, 2, 0, 365395, 27008, 2673, 65536⟩
    (by decide) selected_cut_14072

theorem selected_cut_14073 : selected 9 ⟨365424, by decide⟩
    (prefixPartial 12 27009) = some ⟨12, 2, 0, 365424, 27009, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_27009_365424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27009 ⟨365424, by decide⟩ :=
  accepted_of_selected 12 27009 ⟨365424, by decide⟩ ⟨12, 2, 0, 365424, 27009, 2777, 65536⟩
    (by decide) selected_cut_14073

theorem selected_cut_14074 : selected 9 ⟨365449, by decide⟩
    (prefixPartial 12 27010) = some ⟨12, 2, 0, 365449, 27010, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_27010_365449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27010 ⟨365449, by decide⟩ :=
  accepted_of_selected 12 27010 ⟨365449, by decide⟩ ⟨12, 2, 0, 365449, 27010, 2889, 65536⟩
    (by decide) selected_cut_14074

theorem selected_cut_14075 : selected 9 ⟨365473, by decide⟩
    (prefixPartial 12 27011) = some ⟨12, 2, 0, 365473, 27011, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_27011_365473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27011 ⟨365473, by decide⟩ :=
  accepted_of_selected 12 27011 ⟨365473, by decide⟩ ⟨12, 2, 0, 365473, 27011, 2825, 65536⟩
    (by decide) selected_cut_14075

theorem unmarked_context_11_6752_365474 : frontier 10 ⟨365474, by decide⟩
    (prefixCache 11 6752) (prefixPartial 11 6752) = false := by
  decide +kernel

theorem node_context_11_6752_365474 : EJMOriginalGlobalDAGData.nodes 10 ⟨365474, by decide⟩ =
    .split (coordinate 11) (![⟨365395, by decide⟩,⟨365424, by decide⟩,⟨365449, by decide⟩,⟨365473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6752_365474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6752 ⟨365474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6752
    ⟨365474, by decide⟩ (by decide) (![⟨365395, by decide⟩,⟨365424, by decide⟩,⟨365449, by decide⟩,⟨365473, by decide⟩]) unmarked_context_11_6752_365474 node_context_11_6752_365474
  intro a
  fin_cases a
  · exact context_12_27008_365395
  · exact context_12_27009_365424
  · exact context_12_27010_365449
  · exact context_12_27011_365473

theorem selected_cut_14076 : selected 9 ⟨365501, by decide⟩
    (prefixPartial 12 27012) = some ⟨12, 2, 0, 365501, 27012, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_27012_365501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27012 ⟨365501, by decide⟩ :=
  accepted_of_selected 12 27012 ⟨365501, by decide⟩ ⟨12, 2, 0, 365501, 27012, 2637, 65536⟩
    (by decide) selected_cut_14076

theorem selected_cut_14077 : selected 9 ⟨365535, by decide⟩
    (prefixPartial 12 27013) = some ⟨12, 2, 0, 365535, 27013, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_27013_365535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27013 ⟨365535, by decide⟩ :=
  accepted_of_selected 12 27013 ⟨365535, by decide⟩ ⟨12, 2, 0, 365535, 27013, 3405, 65536⟩
    (by decide) selected_cut_14077

theorem selected_cut_14078 : selected 9 ⟨365562, by decide⟩
    (prefixPartial 12 27014) = some ⟨12, 2, 0, 365562, 27014, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_27014_365562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27014 ⟨365562, by decide⟩ :=
  accepted_of_selected 12 27014 ⟨365562, by decide⟩ ⟨12, 2, 0, 365562, 27014, 2705, 65536⟩
    (by decide) selected_cut_14078

theorem selected_cut_14079 : selected 9 ⟨365587, by decide⟩
    (prefixPartial 12 27015) = some ⟨12, 2, 0, 365587, 27015, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_27015_365587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27015 ⟨365587, by decide⟩ :=
  accepted_of_selected 12 27015 ⟨365587, by decide⟩ ⟨12, 2, 0, 365587, 27015, 2585, 65536⟩
    (by decide) selected_cut_14079

theorem unmarked_context_11_6753_365588 : frontier 10 ⟨365588, by decide⟩
    (prefixCache 11 6753) (prefixPartial 11 6753) = false := by
  decide +kernel

theorem node_context_11_6753_365588 : EJMOriginalGlobalDAGData.nodes 10 ⟨365588, by decide⟩ =
    .split (coordinate 11) (![⟨365501, by decide⟩,⟨365535, by decide⟩,⟨365562, by decide⟩,⟨365587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6753_365588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6753 ⟨365588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6753
    ⟨365588, by decide⟩ (by decide) (![⟨365501, by decide⟩,⟨365535, by decide⟩,⟨365562, by decide⟩,⟨365587, by decide⟩]) unmarked_context_11_6753_365588 node_context_11_6753_365588
  intro a
  fin_cases a
  · exact context_12_27012_365501
  · exact context_12_27013_365535
  · exact context_12_27014_365562
  · exact context_12_27015_365587

theorem selected_cut_14080 : selected 9 ⟨365610, by decide⟩
    (prefixPartial 12 27016) = some ⟨12, 2, 0, 365610, 27016, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_27016_365610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27016 ⟨365610, by decide⟩ :=
  accepted_of_selected 12 27016 ⟨365610, by decide⟩ ⟨12, 2, 0, 365610, 27016, 2621, 65536⟩
    (by decide) selected_cut_14080

theorem selected_cut_14081 : selected 9 ⟨365635, by decide⟩
    (prefixPartial 12 27017) = some ⟨12, 2, 0, 365635, 27017, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_27017_365635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27017 ⟨365635, by decide⟩ :=
  accepted_of_selected 12 27017 ⟨365635, by decide⟩ ⟨12, 2, 0, 365635, 27017, 2469, 65536⟩
    (by decide) selected_cut_14081

theorem selected_cut_14082 : selected 9 ⟨365660, by decide⟩
    (prefixPartial 12 27018) = some ⟨12, 2, 0, 365660, 27018, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_27018_365660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27018 ⟨365660, by decide⟩ :=
  accepted_of_selected 12 27018 ⟨365660, by decide⟩ ⟨12, 2, 0, 365660, 27018, 2537, 65536⟩
    (by decide) selected_cut_14082

theorem selected_cut_14083 : selected 9 ⟨365685, by decide⟩
    (prefixPartial 12 27019) = some ⟨12, 2, 0, 365685, 27019, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_27019_365685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27019 ⟨365685, by decide⟩ :=
  accepted_of_selected 12 27019 ⟨365685, by decide⟩ ⟨12, 2, 0, 365685, 27019, 2365, 65536⟩
    (by decide) selected_cut_14083

theorem unmarked_context_11_6754_365686 : frontier 10 ⟨365686, by decide⟩
    (prefixCache 11 6754) (prefixPartial 11 6754) = false := by
  decide +kernel

theorem node_context_11_6754_365686 : EJMOriginalGlobalDAGData.nodes 10 ⟨365686, by decide⟩ =
    .split (coordinate 11) (![⟨365610, by decide⟩,⟨365635, by decide⟩,⟨365660, by decide⟩,⟨365685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6754_365686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6754 ⟨365686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6754
    ⟨365686, by decide⟩ (by decide) (![⟨365610, by decide⟩,⟨365635, by decide⟩,⟨365660, by decide⟩,⟨365685, by decide⟩]) unmarked_context_11_6754_365686 node_context_11_6754_365686
  intro a
  fin_cases a
  · exact context_12_27016_365610
  · exact context_12_27017_365635
  · exact context_12_27018_365660
  · exact context_12_27019_365685

theorem selected_cut_14084 : selected 9 ⟨365706, by decide⟩
    (prefixPartial 12 27020) = some ⟨12, 2, 0, 365706, 27020, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_27020_365706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27020 ⟨365706, by decide⟩ :=
  accepted_of_selected 12 27020 ⟨365706, by decide⟩ ⟨12, 2, 0, 365706, 27020, 2521, 65536⟩
    (by decide) selected_cut_14084

theorem selected_cut_14085 : selected 9 ⟨365737, by decide⟩
    (prefixPartial 12 27021) = some ⟨12, 2, 0, 365737, 27021, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_27021_365737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27021 ⟨365737, by decide⟩ :=
  accepted_of_selected 12 27021 ⟨365737, by decide⟩ ⟨12, 2, 0, 365737, 27021, 2369, 65536⟩
    (by decide) selected_cut_14085

theorem selected_cut_14086 : selected 9 ⟨365764, by decide⟩
    (prefixPartial 12 27022) = some ⟨12, 2, 0, 365764, 27022, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_27022_365764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27022 ⟨365764, by decide⟩ :=
  accepted_of_selected 12 27022 ⟨365764, by decide⟩ ⟨12, 2, 0, 365764, 27022, 2417, 65536⟩
    (by decide) selected_cut_14086

theorem selected_cut_14087 : selected 9 ⟨365791, by decide⟩
    (prefixPartial 12 27023) = some ⟨12, 2, 0, 365791, 27023, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_27023_365791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27023 ⟨365791, by decide⟩ :=
  accepted_of_selected 12 27023 ⟨365791, by decide⟩ ⟨12, 2, 0, 365791, 27023, 2313, 65536⟩
    (by decide) selected_cut_14087

theorem unmarked_context_11_6755_365792 : frontier 10 ⟨365792, by decide⟩
    (prefixCache 11 6755) (prefixPartial 11 6755) = false := by
  decide +kernel

theorem node_context_11_6755_365792 : EJMOriginalGlobalDAGData.nodes 10 ⟨365792, by decide⟩ =
    .split (coordinate 11) (![⟨365706, by decide⟩,⟨365737, by decide⟩,⟨365764, by decide⟩,⟨365791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6755_365792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6755 ⟨365792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6755
    ⟨365792, by decide⟩ (by decide) (![⟨365706, by decide⟩,⟨365737, by decide⟩,⟨365764, by decide⟩,⟨365791, by decide⟩]) unmarked_context_11_6755_365792 node_context_11_6755_365792
  intro a
  fin_cases a
  · exact context_12_27020_365706
  · exact context_12_27021_365737
  · exact context_12_27022_365764
  · exact context_12_27023_365791

theorem unmarked_context_10_1688_365793 : frontier 11 ⟨365793, by decide⟩
    (prefixCache 10 1688) (prefixPartial 10 1688) = false := by
  decide +kernel

theorem node_context_10_1688_365793 : EJMOriginalGlobalDAGData.nodes 11 ⟨365793, by decide⟩ =
    .split (coordinate 10) (![⟨365474, by decide⟩,⟨365588, by decide⟩,⟨365686, by decide⟩,⟨365792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1688_365793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1688 ⟨365793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1688
    ⟨365793, by decide⟩ (by decide) (![⟨365474, by decide⟩,⟨365588, by decide⟩,⟨365686, by decide⟩,⟨365792, by decide⟩]) unmarked_context_10_1688_365793 node_context_10_1688_365793
  intro a
  fin_cases a
  · exact context_11_6752_365474
  · exact context_11_6753_365588
  · exact context_11_6754_365686
  · exact context_11_6755_365792

theorem selected_cut_14088 : selected 9 ⟨365816, by decide⟩
    (prefixPartial 12 27024) = some ⟨12, 2, 0, 365816, 27024, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_27024_365816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27024 ⟨365816, by decide⟩ :=
  accepted_of_selected 12 27024 ⟨365816, by decide⟩ ⟨12, 2, 0, 365816, 27024, 2041, 65536⟩
    (by decide) selected_cut_14088

theorem selected_cut_14089 : selected 9 ⟨365837, by decide⟩
    (prefixPartial 12 27025) = some ⟨12, 2, 0, 365837, 27025, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_27025_365837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27025 ⟨365837, by decide⟩ :=
  accepted_of_selected 12 27025 ⟨365837, by decide⟩ ⟨12, 2, 0, 365837, 27025, 2097, 65536⟩
    (by decide) selected_cut_14089

theorem selected_cut_14090 : selected 9 ⟨365864, by decide⟩
    (prefixPartial 12 27026) = some ⟨12, 2, 0, 365864, 27026, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_27026_365864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27026 ⟨365864, by decide⟩ :=
  accepted_of_selected 12 27026 ⟨365864, by decide⟩ ⟨12, 2, 0, 365864, 27026, 2325, 65536⟩
    (by decide) selected_cut_14090

theorem selected_cut_14091 : selected 9 ⟨365887, by decide⟩
    (prefixPartial 12 27027) = some ⟨12, 2, 0, 365887, 27027, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_27027_365887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27027 ⟨365887, by decide⟩ :=
  accepted_of_selected 12 27027 ⟨365887, by decide⟩ ⟨12, 2, 0, 365887, 27027, 2181, 65536⟩
    (by decide) selected_cut_14091

theorem unmarked_context_11_6756_365888 : frontier 10 ⟨365888, by decide⟩
    (prefixCache 11 6756) (prefixPartial 11 6756) = false := by
  decide +kernel

theorem node_context_11_6756_365888 : EJMOriginalGlobalDAGData.nodes 10 ⟨365888, by decide⟩ =
    .split (coordinate 11) (![⟨365816, by decide⟩,⟨365837, by decide⟩,⟨365864, by decide⟩,⟨365887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6756_365888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6756 ⟨365888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6756
    ⟨365888, by decide⟩ (by decide) (![⟨365816, by decide⟩,⟨365837, by decide⟩,⟨365864, by decide⟩,⟨365887, by decide⟩]) unmarked_context_11_6756_365888 node_context_11_6756_365888
  intro a
  fin_cases a
  · exact context_12_27024_365816
  · exact context_12_27025_365837
  · exact context_12_27026_365864
  · exact context_12_27027_365887

theorem selected_cut_14092 : selected 9 ⟨365906, by decide⟩
    (prefixPartial 12 27028) = some ⟨12, 2, 0, 365906, 27028, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_27028_365906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27028 ⟨365906, by decide⟩ :=
  accepted_of_selected 12 27028 ⟨365906, by decide⟩ ⟨12, 2, 0, 365906, 27028, 1845, 65536⟩
    (by decide) selected_cut_14092

theorem selected_cut_14093 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 27029) = some ⟨12, 1, 0, 365907, 27029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27029_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27029 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 27029 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 27029, 1, 65536⟩
    (by decide) selected_cut_14093

theorem selected_cut_14094 : selected 9 ⟨365924, by decide⟩
    (prefixPartial 12 27030) = some ⟨12, 2, 0, 365924, 27030, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_27030_365924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27030 ⟨365924, by decide⟩ :=
  accepted_of_selected 12 27030 ⟨365924, by decide⟩ ⟨12, 2, 0, 365924, 27030, 2033, 65536⟩
    (by decide) selected_cut_14094

theorem selected_cut_14095 : selected 9 ⟨365944, by decide⟩
    (prefixPartial 12 27031) = some ⟨12, 2, 0, 365944, 27031, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_27031_365944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27031 ⟨365944, by decide⟩ :=
  accepted_of_selected 12 27031 ⟨365944, by decide⟩ ⟨12, 2, 0, 365944, 27031, 1909, 65536⟩
    (by decide) selected_cut_14095

theorem unmarked_context_11_6757_365945 : frontier 10 ⟨365945, by decide⟩
    (prefixCache 11 6757) (prefixPartial 11 6757) = false := by
  decide +kernel

theorem node_context_11_6757_365945 : EJMOriginalGlobalDAGData.nodes 10 ⟨365945, by decide⟩ =
    .split (coordinate 11) (![⟨365906, by decide⟩,⟨365907, by decide⟩,⟨365924, by decide⟩,⟨365944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6757_365945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6757 ⟨365945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6757
    ⟨365945, by decide⟩ (by decide) (![⟨365906, by decide⟩,⟨365907, by decide⟩,⟨365924, by decide⟩,⟨365944, by decide⟩]) unmarked_context_11_6757_365945 node_context_11_6757_365945
  intro a
  fin_cases a
  · exact context_12_27028_365906
  · exact context_12_27029_365907
  · exact context_12_27030_365924
  · exact context_12_27031_365944

theorem selected_cut_14096 : selected 9 ⟨365966, by decide⟩
    (prefixPartial 12 27032) = some ⟨12, 2, 0, 365966, 27032, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_27032_365966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27032 ⟨365966, by decide⟩ :=
  accepted_of_selected 12 27032 ⟨365966, by decide⟩ ⟨12, 2, 0, 365966, 27032, 1833, 65536⟩
    (by decide) selected_cut_14096

theorem selected_cut_14097 : selected 9 ⟨365987, by decide⟩
    (prefixPartial 12 27033) = some ⟨12, 2, 0, 365987, 27033, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_27033_365987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27033 ⟨365987, by decide⟩ :=
  accepted_of_selected 12 27033 ⟨365987, by decide⟩ ⟨12, 2, 0, 365987, 27033, 1733, 65536⟩
    (by decide) selected_cut_14097

theorem selected_cut_14098 : selected 9 ⟨366008, by decide⟩
    (prefixPartial 12 27034) = some ⟨12, 2, 0, 366008, 27034, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_27034_366008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27034 ⟨366008, by decide⟩ :=
  accepted_of_selected 12 27034 ⟨366008, by decide⟩ ⟨12, 2, 0, 366008, 27034, 1861, 65536⟩
    (by decide) selected_cut_14098

theorem selected_cut_14099 : selected 9 ⟨366029, by decide⟩
    (prefixPartial 12 27035) = some ⟨12, 2, 0, 366029, 27035, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_27035_366029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27035 ⟨366029, by decide⟩ :=
  accepted_of_selected 12 27035 ⟨366029, by decide⟩ ⟨12, 2, 0, 366029, 27035, 1725, 65536⟩
    (by decide) selected_cut_14099

theorem unmarked_context_11_6758_366030 : frontier 10 ⟨366030, by decide⟩
    (prefixCache 11 6758) (prefixPartial 11 6758) = false := by
  decide +kernel

theorem node_context_11_6758_366030 : EJMOriginalGlobalDAGData.nodes 10 ⟨366030, by decide⟩ =
    .split (coordinate 11) (![⟨365966, by decide⟩,⟨365987, by decide⟩,⟨366008, by decide⟩,⟨366029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6758_366030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6758 ⟨366030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6758
    ⟨366030, by decide⟩ (by decide) (![⟨365966, by decide⟩,⟨365987, by decide⟩,⟨366008, by decide⟩,⟨366029, by decide⟩]) unmarked_context_11_6758_366030 node_context_11_6758_366030
  intro a
  fin_cases a
  · exact context_12_27032_365966
  · exact context_12_27033_365987
  · exact context_12_27034_366008
  · exact context_12_27035_366029

theorem selected_cut_14100 : selected 9 ⟨366047, by decide⟩
    (prefixPartial 12 27036) = some ⟨12, 2, 0, 366047, 27036, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_27036_366047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27036 ⟨366047, by decide⟩ :=
  accepted_of_selected 12 27036 ⟨366047, by decide⟩ ⟨12, 2, 0, 366047, 27036, 1773, 65536⟩
    (by decide) selected_cut_14100

theorem selected_cut_14101 : selected 9 ⟨366067, by decide⟩
    (prefixPartial 12 27037) = some ⟨12, 2, 0, 366067, 27037, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_27037_366067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27037 ⟨366067, by decide⟩ :=
  accepted_of_selected 12 27037 ⟨366067, by decide⟩ ⟨12, 2, 0, 366067, 27037, 1645, 65536⟩
    (by decide) selected_cut_14101

theorem selected_cut_14102 : selected 9 ⟨366086, by decide⟩
    (prefixPartial 12 27038) = some ⟨12, 2, 0, 366086, 27038, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_27038_366086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27038 ⟨366086, by decide⟩ :=
  accepted_of_selected 12 27038 ⟨366086, by decide⟩ ⟨12, 2, 0, 366086, 27038, 1781, 65536⟩
    (by decide) selected_cut_14102

theorem selected_cut_14103 : selected 9 ⟨366107, by decide⟩
    (prefixPartial 12 27039) = some ⟨12, 2, 0, 366107, 27039, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_27039_366107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27039 ⟨366107, by decide⟩ :=
  accepted_of_selected 12 27039 ⟨366107, by decide⟩ ⟨12, 2, 0, 366107, 27039, 1713, 65536⟩
    (by decide) selected_cut_14103

theorem unmarked_context_11_6759_366108 : frontier 10 ⟨366108, by decide⟩
    (prefixCache 11 6759) (prefixPartial 11 6759) = false := by
  decide +kernel

theorem node_context_11_6759_366108 : EJMOriginalGlobalDAGData.nodes 10 ⟨366108, by decide⟩ =
    .split (coordinate 11) (![⟨366047, by decide⟩,⟨366067, by decide⟩,⟨366086, by decide⟩,⟨366107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6759_366108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6759 ⟨366108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6759
    ⟨366108, by decide⟩ (by decide) (![⟨366047, by decide⟩,⟨366067, by decide⟩,⟨366086, by decide⟩,⟨366107, by decide⟩]) unmarked_context_11_6759_366108 node_context_11_6759_366108
  intro a
  fin_cases a
  · exact context_12_27036_366047
  · exact context_12_27037_366067
  · exact context_12_27038_366086
  · exact context_12_27039_366107

theorem unmarked_context_10_1689_366109 : frontier 11 ⟨366109, by decide⟩
    (prefixCache 10 1689) (prefixPartial 10 1689) = false := by
  decide +kernel

theorem node_context_10_1689_366109 : EJMOriginalGlobalDAGData.nodes 11 ⟨366109, by decide⟩ =
    .split (coordinate 10) (![⟨365888, by decide⟩,⟨365945, by decide⟩,⟨366030, by decide⟩,⟨366108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1689_366109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1689 ⟨366109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1689
    ⟨366109, by decide⟩ (by decide) (![⟨365888, by decide⟩,⟨365945, by decide⟩,⟨366030, by decide⟩,⟨366108, by decide⟩]) unmarked_context_10_1689_366109 node_context_10_1689_366109
  intro a
  fin_cases a
  · exact context_11_6756_365888
  · exact context_11_6757_365945
  · exact context_11_6758_366030
  · exact context_11_6759_366108

theorem selected_cut_14104 : selected 9 ⟨366125, by decide⟩
    (prefixPartial 12 27040) = some ⟨12, 2, 0, 366125, 27040, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_27040_366125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27040 ⟨366125, by decide⟩ :=
  accepted_of_selected 12 27040 ⟨366125, by decide⟩ ⟨12, 2, 0, 366125, 27040, 1541, 65536⟩
    (by decide) selected_cut_14104

theorem selected_cut_14105 : selected 9 ⟨366148, by decide⟩
    (prefixPartial 12 27041) = some ⟨12, 2, 0, 366148, 27041, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_27041_366148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27041 ⟨366148, by decide⟩ :=
  accepted_of_selected 12 27041 ⟨366148, by decide⟩ ⟨12, 2, 0, 366148, 27041, 1657, 65536⟩
    (by decide) selected_cut_14105

theorem selected_cut_14106 : selected 9 ⟨366169, by decide⟩
    (prefixPartial 12 27042) = some ⟨12, 2, 0, 366169, 27042, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_27042_366169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27042 ⟨366169, by decide⟩ :=
  accepted_of_selected 12 27042 ⟨366169, by decide⟩ ⟨12, 2, 0, 366169, 27042, 1625, 65536⟩
    (by decide) selected_cut_14106

theorem selected_cut_14107 : selected 9 ⟨366188, by decide⟩
    (prefixPartial 12 27043) = some ⟨12, 2, 0, 366188, 27043, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_27043_366188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27043 ⟨366188, by decide⟩ :=
  accepted_of_selected 12 27043 ⟨366188, by decide⟩ ⟨12, 2, 0, 366188, 27043, 1629, 65536⟩
    (by decide) selected_cut_14107

theorem unmarked_context_11_6760_366189 : frontier 10 ⟨366189, by decide⟩
    (prefixCache 11 6760) (prefixPartial 11 6760) = false := by
  decide +kernel

theorem node_context_11_6760_366189 : EJMOriginalGlobalDAGData.nodes 10 ⟨366189, by decide⟩ =
    .split (coordinate 11) (![⟨366125, by decide⟩,⟨366148, by decide⟩,⟨366169, by decide⟩,⟨366188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6760_366189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6760 ⟨366189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6760
    ⟨366189, by decide⟩ (by decide) (![⟨366125, by decide⟩,⟨366148, by decide⟩,⟨366169, by decide⟩,⟨366188, by decide⟩]) unmarked_context_11_6760_366189 node_context_11_6760_366189
  intro a
  fin_cases a
  · exact context_12_27040_366125
  · exact context_12_27041_366148
  · exact context_12_27042_366169
  · exact context_12_27043_366188

theorem selected_cut_14108 : selected 9 ⟨366205, by decide⟩
    (prefixPartial 12 27044) = some ⟨12, 2, 0, 366205, 27044, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_27044_366205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27044 ⟨366205, by decide⟩ :=
  accepted_of_selected 12 27044 ⟨366205, by decide⟩ ⟨12, 2, 0, 366205, 27044, 1525, 65536⟩
    (by decide) selected_cut_14108

theorem selected_cut_14109 : selected 9 ⟨366225, by decide⟩
    (prefixPartial 12 27045) = some ⟨12, 2, 0, 366225, 27045, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_27045_366225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27045 ⟨366225, by decide⟩ :=
  accepted_of_selected 12 27045 ⟨366225, by decide⟩ ⟨12, 2, 0, 366225, 27045, 2129, 65536⟩
    (by decide) selected_cut_14109

theorem selected_cut_14110 : selected 9 ⟨366242, by decide⟩
    (prefixPartial 12 27046) = some ⟨12, 2, 0, 366242, 27046, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_27046_366242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27046 ⟨366242, by decide⟩ :=
  accepted_of_selected 12 27046 ⟨366242, by decide⟩ ⟨12, 2, 0, 366242, 27046, 1477, 65536⟩
    (by decide) selected_cut_14110

theorem selected_cut_14111 : selected 9 ⟨366260, by decide⟩
    (prefixPartial 12 27047) = some ⟨12, 2, 0, 366260, 27047, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_27047_366260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27047 ⟨366260, by decide⟩ :=
  accepted_of_selected 12 27047 ⟨366260, by decide⟩ ⟨12, 2, 0, 366260, 27047, 1489, 65536⟩
    (by decide) selected_cut_14111

theorem unmarked_context_11_6761_366261 : frontier 10 ⟨366261, by decide⟩
    (prefixCache 11 6761) (prefixPartial 11 6761) = false := by
  decide +kernel

theorem node_context_11_6761_366261 : EJMOriginalGlobalDAGData.nodes 10 ⟨366261, by decide⟩ =
    .split (coordinate 11) (![⟨366205, by decide⟩,⟨366225, by decide⟩,⟨366242, by decide⟩,⟨366260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6761_366261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6761 ⟨366261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6761
    ⟨366261, by decide⟩ (by decide) (![⟨366205, by decide⟩,⟨366225, by decide⟩,⟨366242, by decide⟩,⟨366260, by decide⟩]) unmarked_context_11_6761_366261 node_context_11_6761_366261
  intro a
  fin_cases a
  · exact context_12_27044_366205
  · exact context_12_27045_366225
  · exact context_12_27046_366242
  · exact context_12_27047_366260

theorem selected_cut_14112 : selected 10 ⟨366301, by decide⟩
    (prefixPartial 11 6762) = some ⟨11, 2, 0, 366301, 6762, 3697, 262144⟩ := by
  decide +kernel

theorem context_11_6762_366301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6762 ⟨366301, by decide⟩ :=
  accepted_of_selected 11 6762 ⟨366301, by decide⟩ ⟨11, 2, 0, 366301, 6762, 3697, 262144⟩
    (by decide) selected_cut_14112

theorem selected_cut_14113 : selected 9 ⟨366313, by decide⟩
    (prefixPartial 12 27052) = some ⟨12, 2, 0, 366313, 27052, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_27052_366313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27052 ⟨366313, by decide⟩ :=
  accepted_of_selected 12 27052 ⟨366313, by decide⟩ ⟨12, 2, 0, 366313, 27052, 1537, 65536⟩
    (by decide) selected_cut_14113

theorem selected_cut_14114 : selected 9 ⟨366330, by decide⟩
    (prefixPartial 12 27053) = some ⟨12, 2, 0, 366330, 27053, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_27053_366330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27053 ⟨366330, by decide⟩ :=
  accepted_of_selected 12 27053 ⟨366330, by decide⟩ ⟨12, 2, 0, 366330, 27053, 1421, 65536⟩
    (by decide) selected_cut_14114

theorem selected_cut_14115 : selected 9 ⟨366345, by decide⟩
    (prefixPartial 12 27054) = some ⟨12, 2, 0, 366345, 27054, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_27054_366345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27054 ⟨366345, by decide⟩ :=
  accepted_of_selected 12 27054 ⟨366345, by decide⟩ ⟨12, 2, 0, 366345, 27054, 1369, 65536⟩
    (by decide) selected_cut_14115

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
