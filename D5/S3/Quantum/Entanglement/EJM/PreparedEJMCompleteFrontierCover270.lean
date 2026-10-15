/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover269
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_5510_655972 : frontier 11 ⟨655972, by decide⟩
    (prefixCache 10 5510) (prefixPartial 10 5510) = false := by
  decide +kernel

theorem node_context_10_5510_655972 : EJMOriginalGlobalDAGData.nodes 11 ⟨655972, by decide⟩ =
    .split (coordinate 10) (![⟨655493, by decide⟩,⟨655603, by decide⟩,⟨655814, by decide⟩,⟨655971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5510_655972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5510 ⟨655972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5510
    ⟨655972, by decide⟩ (by decide) (![⟨655493, by decide⟩,⟨655603, by decide⟩,⟨655814, by decide⟩,⟨655971, by decide⟩]) unmarked_context_10_5510_655972 node_context_10_5510_655972
  intro a
  fin_cases a
  · exact context_11_22040_655493
  · exact context_11_22041_655603
  · exact context_11_22042_655814
  · exact context_11_22043_655971

theorem selected_cut_25923 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 352704) = some ⟨13, 1, 0, 3444, 352704, 1, 16384⟩ := by
  decide +kernel

theorem context_13_352704_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352704 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 352704 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 352704, 1, 16384⟩
    (by decide) selected_cut_25923

theorem selected_cut_25924 : selected 8 ⟨655989, by decide⟩
    (prefixPartial 13 352705) = some ⟨13, 2, 0, 655989, 352705, 933, 16384⟩ := by
  decide +kernel

theorem context_13_352705_655989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352705 ⟨655989, by decide⟩ :=
  accepted_of_selected 13 352705 ⟨655989, by decide⟩ ⟨13, 2, 0, 655989, 352705, 933, 16384⟩
    (by decide) selected_cut_25924

theorem selected_cut_25925 : selected 8 ⟨656031, by decide⟩
    (prefixPartial 13 352706) = some ⟨13, 2, 0, 656031, 352706, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_352706_656031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352706 ⟨656031, by decide⟩ :=
  accepted_of_selected 13 352706 ⟨656031, by decide⟩ ⟨13, 2, 0, 656031, 352706, 2369, 16384⟩
    (by decide) selected_cut_25925

theorem selected_cut_25926 : selected 8 ⟨656048, by decide⟩
    (prefixPartial 13 352707) = some ⟨13, 2, 0, 656048, 352707, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_352707_656048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 352707 ⟨656048, by decide⟩ :=
  accepted_of_selected 13 352707 ⟨656048, by decide⟩ ⟨13, 2, 0, 656048, 352707, 1229, 16384⟩
    (by decide) selected_cut_25926

theorem unmarked_context_12_88176_656049 : frontier 9 ⟨656049, by decide⟩
    (prefixCache 12 88176) (prefixPartial 12 88176) = false := by
  decide +kernel

theorem node_context_12_88176_656049 : EJMOriginalGlobalDAGData.nodes 9 ⟨656049, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨655989, by decide⟩,⟨656031, by decide⟩,⟨656048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88176_656049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88176 ⟨656049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88176
    ⟨656049, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨655989, by decide⟩,⟨656031, by decide⟩,⟨656048, by decide⟩]) unmarked_context_12_88176_656049 node_context_12_88176_656049
  intro a
  fin_cases a
  · exact context_13_352704_3444
  · exact context_13_352705_655989
  · exact context_13_352706_656031
  · exact context_13_352707_656048

theorem selected_cut_25927 : selected 9 ⟨656089, by decide⟩
    (prefixPartial 12 88177) = some ⟨12, 2, 0, 656089, 88177, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_88177_656089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88177 ⟨656089, by decide⟩ :=
  accepted_of_selected 12 88177 ⟨656089, by decide⟩ ⟨12, 2, 0, 656089, 88177, 3513, 65536⟩
    (by decide) selected_cut_25927

theorem selected_cut_25928 : selected 9 ⟨656121, by decide⟩
    (prefixPartial 12 88178) = some ⟨12, 2, 0, 656121, 88178, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_88178_656121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88178 ⟨656121, by decide⟩ :=
  accepted_of_selected 12 88178 ⟨656121, by decide⟩ ⟨12, 2, 0, 656121, 88178, 2797, 65536⟩
    (by decide) selected_cut_25928

theorem selected_cut_25929 : selected 9 ⟨656160, by decide⟩
    (prefixPartial 12 88179) = some ⟨12, 2, 0, 656160, 88179, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_88179_656160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88179 ⟨656160, by decide⟩ :=
  accepted_of_selected 12 88179 ⟨656160, by decide⟩ ⟨12, 2, 0, 656160, 88179, 2993, 65536⟩
    (by decide) selected_cut_25929

theorem unmarked_context_11_22044_656161 : frontier 10 ⟨656161, by decide⟩
    (prefixCache 11 22044) (prefixPartial 11 22044) = false := by
  decide +kernel

theorem node_context_11_22044_656161 : EJMOriginalGlobalDAGData.nodes 10 ⟨656161, by decide⟩ =
    .split (coordinate 11) (![⟨656049, by decide⟩,⟨656089, by decide⟩,⟨656121, by decide⟩,⟨656160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22044_656161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22044 ⟨656161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22044
    ⟨656161, by decide⟩ (by decide) (![⟨656049, by decide⟩,⟨656089, by decide⟩,⟨656121, by decide⟩,⟨656160, by decide⟩]) unmarked_context_11_22044_656161 node_context_11_22044_656161
  intro a
  fin_cases a
  · exact context_12_88176_656049
  · exact context_12_88177_656089
  · exact context_12_88178_656121
  · exact context_12_88179_656160

theorem selected_cut_25930 : selected 9 ⟨656194, by decide⟩
    (prefixPartial 12 88180) = some ⟨12, 2, 0, 656194, 88180, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_88180_656194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88180 ⟨656194, by decide⟩ :=
  accepted_of_selected 12 88180 ⟨656194, by decide⟩ ⟨12, 2, 0, 656194, 88180, 2649, 65536⟩
    (by decide) selected_cut_25930

theorem selected_cut_25931 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 88181) = some ⟨12, 1, 0, 642794, 88181, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88181_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88181 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 88181 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 88181, 1, 65536⟩
    (by decide) selected_cut_25931

theorem selected_cut_25932 : selected 9 ⟨656221, by decide⟩
    (prefixPartial 12 88182) = some ⟨12, 2, 0, 656221, 88182, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_88182_656221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88182 ⟨656221, by decide⟩ :=
  accepted_of_selected 12 88182 ⟨656221, by decide⟩ ⟨12, 2, 0, 656221, 88182, 2585, 65536⟩
    (by decide) selected_cut_25932

theorem selected_cut_25933 : selected 9 ⟨656256, by decide⟩
    (prefixPartial 12 88183) = some ⟨12, 2, 0, 656256, 88183, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_88183_656256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88183 ⟨656256, by decide⟩ :=
  accepted_of_selected 12 88183 ⟨656256, by decide⟩ ⟨12, 2, 0, 656256, 88183, 2657, 65536⟩
    (by decide) selected_cut_25933

theorem unmarked_context_11_22045_656257 : frontier 10 ⟨656257, by decide⟩
    (prefixCache 11 22045) (prefixPartial 11 22045) = false := by
  decide +kernel

theorem node_context_11_22045_656257 : EJMOriginalGlobalDAGData.nodes 10 ⟨656257, by decide⟩ =
    .split (coordinate 11) (![⟨656194, by decide⟩,⟨642794, by decide⟩,⟨656221, by decide⟩,⟨656256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22045_656257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22045 ⟨656257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22045
    ⟨656257, by decide⟩ (by decide) (![⟨656194, by decide⟩,⟨642794, by decide⟩,⟨656221, by decide⟩,⟨656256, by decide⟩]) unmarked_context_11_22045_656257 node_context_11_22045_656257
  intro a
  fin_cases a
  · exact context_12_88180_656194
  · exact context_12_88181_642794
  · exact context_12_88182_656221
  · exact context_12_88183_656256

theorem selected_cut_25934 : selected 9 ⟨656288, by decide⟩
    (prefixPartial 12 88184) = some ⟨12, 2, 0, 656288, 88184, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_88184_656288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88184 ⟨656288, by decide⟩ :=
  accepted_of_selected 12 88184 ⟨656288, by decide⟩ ⟨12, 2, 0, 656288, 88184, 2849, 65536⟩
    (by decide) selected_cut_25934

theorem selected_cut_25935 : selected 9 ⟨656336, by decide⟩
    (prefixPartial 12 88185) = some ⟨12, 2, 0, 656336, 88185, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_88185_656336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88185 ⟨656336, by decide⟩ :=
  accepted_of_selected 12 88185 ⟨656336, by decide⟩ ⟨12, 2, 0, 656336, 88185, 3629, 65536⟩
    (by decide) selected_cut_25935

theorem selected_cut_25936 : selected 9 ⟨656364, by decide⟩
    (prefixPartial 12 88186) = some ⟨12, 2, 0, 656364, 88186, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_88186_656364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88186 ⟨656364, by decide⟩ :=
  accepted_of_selected 12 88186 ⟨656364, by decide⟩ ⟨12, 2, 0, 656364, 88186, 2521, 65536⟩
    (by decide) selected_cut_25936

theorem selected_cut_25937 : selected 9 ⟨656396, by decide⟩
    (prefixPartial 12 88187) = some ⟨12, 2, 0, 656396, 88187, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_88187_656396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88187 ⟨656396, by decide⟩ :=
  accepted_of_selected 12 88187 ⟨656396, by decide⟩ ⟨12, 2, 0, 656396, 88187, 2845, 65536⟩
    (by decide) selected_cut_25937

theorem unmarked_context_11_22046_656397 : frontier 10 ⟨656397, by decide⟩
    (prefixCache 11 22046) (prefixPartial 11 22046) = false := by
  decide +kernel

theorem node_context_11_22046_656397 : EJMOriginalGlobalDAGData.nodes 10 ⟨656397, by decide⟩ =
    .split (coordinate 11) (![⟨656288, by decide⟩,⟨656336, by decide⟩,⟨656364, by decide⟩,⟨656396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22046_656397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22046 ⟨656397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22046
    ⟨656397, by decide⟩ (by decide) (![⟨656288, by decide⟩,⟨656336, by decide⟩,⟨656364, by decide⟩,⟨656396, by decide⟩]) unmarked_context_11_22046_656397 node_context_11_22046_656397
  intro a
  fin_cases a
  · exact context_12_88184_656288
  · exact context_12_88185_656336
  · exact context_12_88186_656364
  · exact context_12_88187_656396

theorem selected_cut_25938 : selected 9 ⟨656426, by decide⟩
    (prefixPartial 12 88188) = some ⟨12, 2, 0, 656426, 88188, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_88188_656426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88188 ⟨656426, by decide⟩ :=
  accepted_of_selected 12 88188 ⟨656426, by decide⟩ ⟨12, 2, 0, 656426, 88188, 2609, 65536⟩
    (by decide) selected_cut_25938

theorem selected_cut_25939 : selected 9 ⟨656471, by decide⟩
    (prefixPartial 12 88189) = some ⟨12, 2, 0, 656471, 88189, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_88189_656471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88189 ⟨656471, by decide⟩ :=
  accepted_of_selected 12 88189 ⟨656471, by decide⟩ ⟨12, 2, 0, 656471, 88189, 3261, 65536⟩
    (by decide) selected_cut_25939

theorem selected_cut_25940 : selected 9 ⟨656497, by decide⟩
    (prefixPartial 12 88190) = some ⟨12, 2, 0, 656497, 88190, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_88190_656497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88190 ⟨656497, by decide⟩ :=
  accepted_of_selected 12 88190 ⟨656497, by decide⟩ ⟨12, 2, 0, 656497, 88190, 2621, 65536⟩
    (by decide) selected_cut_25940

theorem selected_cut_25941 : selected 9 ⟨656523, by decide⟩
    (prefixPartial 12 88191) = some ⟨12, 2, 0, 656523, 88191, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_88191_656523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88191 ⟨656523, by decide⟩ :=
  accepted_of_selected 12 88191 ⟨656523, by decide⟩ ⟨12, 2, 0, 656523, 88191, 2341, 65536⟩
    (by decide) selected_cut_25941

theorem unmarked_context_11_22047_656524 : frontier 10 ⟨656524, by decide⟩
    (prefixCache 11 22047) (prefixPartial 11 22047) = false := by
  decide +kernel

theorem node_context_11_22047_656524 : EJMOriginalGlobalDAGData.nodes 10 ⟨656524, by decide⟩ =
    .split (coordinate 11) (![⟨656426, by decide⟩,⟨656471, by decide⟩,⟨656497, by decide⟩,⟨656523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22047_656524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22047 ⟨656524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22047
    ⟨656524, by decide⟩ (by decide) (![⟨656426, by decide⟩,⟨656471, by decide⟩,⟨656497, by decide⟩,⟨656523, by decide⟩]) unmarked_context_11_22047_656524 node_context_11_22047_656524
  intro a
  fin_cases a
  · exact context_12_88188_656426
  · exact context_12_88189_656471
  · exact context_12_88190_656497
  · exact context_12_88191_656523

theorem unmarked_context_10_5511_656525 : frontier 11 ⟨656525, by decide⟩
    (prefixCache 10 5511) (prefixPartial 10 5511) = false := by
  decide +kernel

theorem node_context_10_5511_656525 : EJMOriginalGlobalDAGData.nodes 11 ⟨656525, by decide⟩ =
    .split (coordinate 10) (![⟨656161, by decide⟩,⟨656257, by decide⟩,⟨656397, by decide⟩,⟨656524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5511_656525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5511 ⟨656525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5511
    ⟨656525, by decide⟩ (by decide) (![⟨656161, by decide⟩,⟨656257, by decide⟩,⟨656397, by decide⟩,⟨656524, by decide⟩]) unmarked_context_10_5511_656525 node_context_10_5511_656525
  intro a
  fin_cases a
  · exact context_11_22044_656161
  · exact context_11_22045_656257
  · exact context_11_22046_656397
  · exact context_11_22047_656524

theorem unmarked_context_9_1377_656526 : frontier 12 ⟨656526, by decide⟩
    (prefixCache 9 1377) (prefixPartial 9 1377) = false := by
  decide +kernel

theorem node_context_9_1377_656526 : EJMOriginalGlobalDAGData.nodes 12 ⟨656526, by decide⟩ =
    .split (coordinate 9) (![⟨654616, by decide⟩,⟨655274, by decide⟩,⟨655972, by decide⟩,⟨656525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1377_656526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1377 ⟨656526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1377
    ⟨656526, by decide⟩ (by decide) (![⟨654616, by decide⟩,⟨655274, by decide⟩,⟨655972, by decide⟩,⟨656525, by decide⟩]) unmarked_context_9_1377_656526 node_context_9_1377_656526
  intro a
  fin_cases a
  · exact context_10_5508_654616
  · exact context_10_5509_655274
  · exact context_10_5510_655972
  · exact context_10_5511_656525

theorem selected_cut_25942 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 88192) = some ⟨12, 1, 0, 450982, 88192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88192_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88192 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 88192 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 88192, 1, 65536⟩
    (by decide) selected_cut_25942

theorem selected_cut_25943 : selected 9 ⟨656545, by decide⟩
    (prefixPartial 12 88193) = some ⟨12, 2, 0, 656545, 88193, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_88193_656545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88193 ⟨656545, by decide⟩ :=
  accepted_of_selected 12 88193 ⟨656545, by decide⟩ ⟨12, 2, 0, 656545, 88193, 1985, 65536⟩
    (by decide) selected_cut_25943

theorem selected_cut_25944 : selected 9 ⟨656576, by decide⟩
    (prefixPartial 12 88194) = some ⟨12, 2, 0, 656576, 88194, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_88194_656576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88194 ⟨656576, by decide⟩ :=
  accepted_of_selected 12 88194 ⟨656576, by decide⟩ ⟨12, 2, 0, 656576, 88194, 2285, 65536⟩
    (by decide) selected_cut_25944

theorem selected_cut_25945 : selected 9 ⟨656599, by decide⟩
    (prefixPartial 12 88195) = some ⟨12, 2, 0, 656599, 88195, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_88195_656599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88195 ⟨656599, by decide⟩ :=
  accepted_of_selected 12 88195 ⟨656599, by decide⟩ ⟨12, 2, 0, 656599, 88195, 2173, 65536⟩
    (by decide) selected_cut_25945

theorem unmarked_context_11_22048_656600 : frontier 10 ⟨656600, by decide⟩
    (prefixCache 11 22048) (prefixPartial 11 22048) = false := by
  decide +kernel

theorem node_context_11_22048_656600 : EJMOriginalGlobalDAGData.nodes 10 ⟨656600, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨656545, by decide⟩,⟨656576, by decide⟩,⟨656599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22048_656600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22048 ⟨656600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22048
    ⟨656600, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨656545, by decide⟩,⟨656576, by decide⟩,⟨656599, by decide⟩]) unmarked_context_11_22048_656600 node_context_11_22048_656600
  intro a
  fin_cases a
  · exact context_12_88192_450982
  · exact context_12_88193_656545
  · exact context_12_88194_656576
  · exact context_12_88195_656599

theorem selected_cut_25946 : selected 9 ⟨656624, by decide⟩
    (prefixPartial 12 88196) = some ⟨12, 2, 0, 656624, 88196, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_88196_656624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88196 ⟨656624, by decide⟩ :=
  accepted_of_selected 12 88196 ⟨656624, by decide⟩ ⟨12, 2, 0, 656624, 88196, 1925, 65536⟩
    (by decide) selected_cut_25946

theorem selected_cut_25947 : selected 9 ⟨656650, by decide⟩
    (prefixPartial 12 88197) = some ⟨12, 2, 0, 656650, 88197, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_88197_656650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88197 ⟨656650, by decide⟩ :=
  accepted_of_selected 12 88197 ⟨656650, by decide⟩ ⟨12, 2, 0, 656650, 88197, 1701, 65536⟩
    (by decide) selected_cut_25947

theorem selected_cut_25948 : selected 9 ⟨656672, by decide⟩
    (prefixPartial 12 88198) = some ⟨12, 2, 0, 656672, 88198, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_88198_656672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88198 ⟨656672, by decide⟩ :=
  accepted_of_selected 12 88198 ⟨656672, by decide⟩ ⟨12, 2, 0, 656672, 88198, 2029, 65536⟩
    (by decide) selected_cut_25948

theorem selected_cut_25949 : selected 9 ⟨656695, by decide⟩
    (prefixPartial 12 88199) = some ⟨12, 2, 0, 656695, 88199, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_88199_656695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88199 ⟨656695, by decide⟩ :=
  accepted_of_selected 12 88199 ⟨656695, by decide⟩ ⟨12, 2, 0, 656695, 88199, 1881, 65536⟩
    (by decide) selected_cut_25949

theorem unmarked_context_11_22049_656696 : frontier 10 ⟨656696, by decide⟩
    (prefixCache 11 22049) (prefixPartial 11 22049) = false := by
  decide +kernel

theorem node_context_11_22049_656696 : EJMOriginalGlobalDAGData.nodes 10 ⟨656696, by decide⟩ =
    .split (coordinate 11) (![⟨656624, by decide⟩,⟨656650, by decide⟩,⟨656672, by decide⟩,⟨656695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22049_656696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22049 ⟨656696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22049
    ⟨656696, by decide⟩ (by decide) (![⟨656624, by decide⟩,⟨656650, by decide⟩,⟨656672, by decide⟩,⟨656695, by decide⟩]) unmarked_context_11_22049_656696 node_context_11_22049_656696
  intro a
  fin_cases a
  · exact context_12_88196_656624
  · exact context_12_88197_656650
  · exact context_12_88198_656672
  · exact context_12_88199_656695

theorem selected_cut_25950 : selected 9 ⟨656719, by decide⟩
    (prefixPartial 12 88200) = some ⟨12, 2, 0, 656719, 88200, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_88200_656719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88200 ⟨656719, by decide⟩ :=
  accepted_of_selected 12 88200 ⟨656719, by decide⟩ ⟨12, 2, 0, 656719, 88200, 1889, 65536⟩
    (by decide) selected_cut_25950

theorem selected_cut_25951 : selected 9 ⟨656744, by decide⟩
    (prefixPartial 12 88201) = some ⟨12, 2, 0, 656744, 88201, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_88201_656744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88201 ⟨656744, by decide⟩ :=
  accepted_of_selected 12 88201 ⟨656744, by decide⟩ ⟨12, 2, 0, 656744, 88201, 2045, 65536⟩
    (by decide) selected_cut_25951

theorem selected_cut_25952 : selected 9 ⟨656770, by decide⟩
    (prefixPartial 12 88202) = some ⟨12, 2, 0, 656770, 88202, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_88202_656770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88202 ⟨656770, by decide⟩ :=
  accepted_of_selected 12 88202 ⟨656770, by decide⟩ ⟨12, 2, 0, 656770, 88202, 1997, 65536⟩
    (by decide) selected_cut_25952

theorem selected_cut_25953 : selected 9 ⟨656794, by decide⟩
    (prefixPartial 12 88203) = some ⟨12, 2, 0, 656794, 88203, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_88203_656794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88203 ⟨656794, by decide⟩ :=
  accepted_of_selected 12 88203 ⟨656794, by decide⟩ ⟨12, 2, 0, 656794, 88203, 1949, 65536⟩
    (by decide) selected_cut_25953

theorem unmarked_context_11_22050_656795 : frontier 10 ⟨656795, by decide⟩
    (prefixCache 11 22050) (prefixPartial 11 22050) = false := by
  decide +kernel

theorem node_context_11_22050_656795 : EJMOriginalGlobalDAGData.nodes 10 ⟨656795, by decide⟩ =
    .split (coordinate 11) (![⟨656719, by decide⟩,⟨656744, by decide⟩,⟨656770, by decide⟩,⟨656794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22050_656795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22050 ⟨656795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22050
    ⟨656795, by decide⟩ (by decide) (![⟨656719, by decide⟩,⟨656744, by decide⟩,⟨656770, by decide⟩,⟨656794, by decide⟩]) unmarked_context_11_22050_656795 node_context_11_22050_656795
  intro a
  fin_cases a
  · exact context_12_88200_656719
  · exact context_12_88201_656744
  · exact context_12_88202_656770
  · exact context_12_88203_656794

theorem selected_cut_25954 : selected 9 ⟨656819, by decide⟩
    (prefixPartial 12 88204) = some ⟨12, 2, 0, 656819, 88204, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_88204_656819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88204 ⟨656819, by decide⟩ :=
  accepted_of_selected 12 88204 ⟨656819, by decide⟩ ⟨12, 2, 0, 656819, 88204, 1889, 65536⟩
    (by decide) selected_cut_25954

theorem selected_cut_25955 : selected 9 ⟨656845, by decide⟩
    (prefixPartial 12 88205) = some ⟨12, 2, 0, 656845, 88205, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_88205_656845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88205 ⟨656845, by decide⟩ :=
  accepted_of_selected 12 88205 ⟨656845, by decide⟩ ⟨12, 2, 0, 656845, 88205, 1997, 65536⟩
    (by decide) selected_cut_25955

theorem selected_cut_25956 : selected 9 ⟨656873, by decide⟩
    (prefixPartial 12 88206) = some ⟨12, 2, 0, 656873, 88206, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_88206_656873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88206 ⟨656873, by decide⟩ :=
  accepted_of_selected 12 88206 ⟨656873, by decide⟩ ⟨12, 2, 0, 656873, 88206, 2217, 65536⟩
    (by decide) selected_cut_25956

theorem selected_cut_25957 : selected 9 ⟨656893, by decide⟩
    (prefixPartial 12 88207) = some ⟨12, 2, 0, 656893, 88207, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_88207_656893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88207 ⟨656893, by decide⟩ :=
  accepted_of_selected 12 88207 ⟨656893, by decide⟩ ⟨12, 2, 0, 656893, 88207, 1821, 65536⟩
    (by decide) selected_cut_25957

theorem unmarked_context_11_22051_656894 : frontier 10 ⟨656894, by decide⟩
    (prefixCache 11 22051) (prefixPartial 11 22051) = false := by
  decide +kernel

theorem node_context_11_22051_656894 : EJMOriginalGlobalDAGData.nodes 10 ⟨656894, by decide⟩ =
    .split (coordinate 11) (![⟨656819, by decide⟩,⟨656845, by decide⟩,⟨656873, by decide⟩,⟨656893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22051_656894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22051 ⟨656894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22051
    ⟨656894, by decide⟩ (by decide) (![⟨656819, by decide⟩,⟨656845, by decide⟩,⟨656873, by decide⟩,⟨656893, by decide⟩]) unmarked_context_11_22051_656894 node_context_11_22051_656894
  intro a
  fin_cases a
  · exact context_12_88204_656819
  · exact context_12_88205_656845
  · exact context_12_88206_656873
  · exact context_12_88207_656893

theorem unmarked_context_10_5512_656895 : frontier 11 ⟨656895, by decide⟩
    (prefixCache 10 5512) (prefixPartial 10 5512) = false := by
  decide +kernel

theorem node_context_10_5512_656895 : EJMOriginalGlobalDAGData.nodes 11 ⟨656895, by decide⟩ =
    .split (coordinate 10) (![⟨656600, by decide⟩,⟨656696, by decide⟩,⟨656795, by decide⟩,⟨656894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5512_656895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5512 ⟨656895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5512
    ⟨656895, by decide⟩ (by decide) (![⟨656600, by decide⟩,⟨656696, by decide⟩,⟨656795, by decide⟩,⟨656894, by decide⟩]) unmarked_context_10_5512_656895 node_context_10_5512_656895
  intro a
  fin_cases a
  · exact context_11_22048_656600
  · exact context_11_22049_656696
  · exact context_11_22050_656795
  · exact context_11_22051_656894

theorem selected_cut_25958 : selected 9 ⟨656949, by decide⟩
    (prefixPartial 12 88208) = some ⟨12, 2, 0, 656949, 88208, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_88208_656949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88208 ⟨656949, by decide⟩ :=
  accepted_of_selected 12 88208 ⟨656949, by decide⟩ ⟨12, 2, 0, 656949, 88208, 3353, 65536⟩
    (by decide) selected_cut_25958

theorem selected_cut_25959 : selected 9 ⟨656971, by decide⟩
    (prefixPartial 12 88209) = some ⟨12, 2, 0, 656971, 88209, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_88209_656971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88209 ⟨656971, by decide⟩ :=
  accepted_of_selected 12 88209 ⟨656971, by decide⟩ ⟨12, 2, 0, 656971, 88209, 2273, 65536⟩
    (by decide) selected_cut_25959

theorem selected_cut_25960 : selected 9 ⟨657001, by decide⟩
    (prefixPartial 12 88210) = some ⟨12, 2, 0, 657001, 88210, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_88210_657001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88210 ⟨657001, by decide⟩ :=
  accepted_of_selected 12 88210 ⟨657001, by decide⟩ ⟨12, 2, 0, 657001, 88210, 2453, 65536⟩
    (by decide) selected_cut_25960

theorem selected_cut_25961 : selected 9 ⟨657022, by decide⟩
    (prefixPartial 12 88211) = some ⟨12, 2, 0, 657022, 88211, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_88211_657022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88211 ⟨657022, by decide⟩ :=
  accepted_of_selected 12 88211 ⟨657022, by decide⟩ ⟨12, 2, 0, 657022, 88211, 2081, 65536⟩
    (by decide) selected_cut_25961

theorem unmarked_context_11_22052_657023 : frontier 10 ⟨657023, by decide⟩
    (prefixCache 11 22052) (prefixPartial 11 22052) = false := by
  decide +kernel

theorem node_context_11_22052_657023 : EJMOriginalGlobalDAGData.nodes 10 ⟨657023, by decide⟩ =
    .split (coordinate 11) (![⟨656949, by decide⟩,⟨656971, by decide⟩,⟨657001, by decide⟩,⟨657022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22052_657023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22052 ⟨657023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22052
    ⟨657023, by decide⟩ (by decide) (![⟨656949, by decide⟩,⟨656971, by decide⟩,⟨657001, by decide⟩,⟨657022, by decide⟩]) unmarked_context_11_22052_657023 node_context_11_22052_657023
  intro a
  fin_cases a
  · exact context_12_88208_656949
  · exact context_12_88209_656971
  · exact context_12_88210_657001
  · exact context_12_88211_657022

theorem selected_cut_25962 : selected 9 ⟨657041, by decide⟩
    (prefixPartial 12 88212) = some ⟨12, 2, 0, 657041, 88212, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_88212_657041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88212 ⟨657041, by decide⟩ :=
  accepted_of_selected 12 88212 ⟨657041, by decide⟩ ⟨12, 2, 0, 657041, 88212, 2029, 65536⟩
    (by decide) selected_cut_25962

theorem selected_cut_25963 : selected 9 ⟨657062, by decide⟩
    (prefixPartial 12 88213) = some ⟨12, 2, 0, 657062, 88213, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_88213_657062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88213 ⟨657062, by decide⟩ :=
  accepted_of_selected 12 88213 ⟨657062, by decide⟩ ⟨12, 2, 0, 657062, 88213, 1889, 65536⟩
    (by decide) selected_cut_25963

theorem selected_cut_25964 : selected 9 ⟨657090, by decide⟩
    (prefixPartial 12 88214) = some ⟨12, 2, 0, 657090, 88214, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_88214_657090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88214 ⟨657090, by decide⟩ :=
  accepted_of_selected 12 88214 ⟨657090, by decide⟩ ⟨12, 2, 0, 657090, 88214, 2141, 65536⟩
    (by decide) selected_cut_25964

theorem selected_cut_25965 : selected 9 ⟨657107, by decide⟩
    (prefixPartial 12 88215) = some ⟨12, 2, 0, 657107, 88215, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_88215_657107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88215 ⟨657107, by decide⟩ :=
  accepted_of_selected 12 88215 ⟨657107, by decide⟩ ⟨12, 2, 0, 657107, 88215, 1933, 65536⟩
    (by decide) selected_cut_25965

theorem unmarked_context_11_22053_657108 : frontier 10 ⟨657108, by decide⟩
    (prefixCache 11 22053) (prefixPartial 11 22053) = false := by
  decide +kernel

theorem node_context_11_22053_657108 : EJMOriginalGlobalDAGData.nodes 10 ⟨657108, by decide⟩ =
    .split (coordinate 11) (![⟨657041, by decide⟩,⟨657062, by decide⟩,⟨657090, by decide⟩,⟨657107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22053_657108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22053 ⟨657108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22053
    ⟨657108, by decide⟩ (by decide) (![⟨657041, by decide⟩,⟨657062, by decide⟩,⟨657090, by decide⟩,⟨657107, by decide⟩]) unmarked_context_11_22053_657108 node_context_11_22053_657108
  intro a
  fin_cases a
  · exact context_12_88212_657041
  · exact context_12_88213_657062
  · exact context_12_88214_657090
  · exact context_12_88215_657107

theorem selected_cut_25966 : selected 9 ⟨657127, by decide⟩
    (prefixPartial 12 88216) = some ⟨12, 2, 0, 657127, 88216, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_88216_657127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88216 ⟨657127, by decide⟩ :=
  accepted_of_selected 12 88216 ⟨657127, by decide⟩ ⟨12, 2, 0, 657127, 88216, 2117, 65536⟩
    (by decide) selected_cut_25966

theorem selected_cut_25967 : selected 9 ⟨657147, by decide⟩
    (prefixPartial 12 88217) = some ⟨12, 2, 0, 657147, 88217, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_88217_657147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88217 ⟨657147, by decide⟩ :=
  accepted_of_selected 12 88217 ⟨657147, by decide⟩ ⟨12, 2, 0, 657147, 88217, 2221, 65536⟩
    (by decide) selected_cut_25967

theorem selected_cut_25968 : selected 9 ⟨657170, by decide⟩
    (prefixPartial 12 88218) = some ⟨12, 2, 0, 657170, 88218, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_88218_657170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88218 ⟨657170, by decide⟩ :=
  accepted_of_selected 12 88218 ⟨657170, by decide⟩ ⟨12, 2, 0, 657170, 88218, 2137, 65536⟩
    (by decide) selected_cut_25968

theorem selected_cut_25969 : selected 9 ⟨657190, by decide⟩
    (prefixPartial 12 88219) = some ⟨12, 2, 0, 657190, 88219, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_88219_657190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88219 ⟨657190, by decide⟩ :=
  accepted_of_selected 12 88219 ⟨657190, by decide⟩ ⟨12, 2, 0, 657190, 88219, 1977, 65536⟩
    (by decide) selected_cut_25969

theorem unmarked_context_11_22054_657191 : frontier 10 ⟨657191, by decide⟩
    (prefixCache 11 22054) (prefixPartial 11 22054) = false := by
  decide +kernel

theorem node_context_11_22054_657191 : EJMOriginalGlobalDAGData.nodes 10 ⟨657191, by decide⟩ =
    .split (coordinate 11) (![⟨657127, by decide⟩,⟨657147, by decide⟩,⟨657170, by decide⟩,⟨657190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22054_657191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22054 ⟨657191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22054
    ⟨657191, by decide⟩ (by decide) (![⟨657127, by decide⟩,⟨657147, by decide⟩,⟨657170, by decide⟩,⟨657190, by decide⟩]) unmarked_context_11_22054_657191 node_context_11_22054_657191
  intro a
  fin_cases a
  · exact context_12_88216_657127
  · exact context_12_88217_657147
  · exact context_12_88218_657170
  · exact context_12_88219_657190

theorem selected_cut_25970 : selected 9 ⟨657212, by decide⟩
    (prefixPartial 12 88220) = some ⟨12, 2, 0, 657212, 88220, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_88220_657212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88220 ⟨657212, by decide⟩ :=
  accepted_of_selected 12 88220 ⟨657212, by decide⟩ ⟨12, 2, 0, 657212, 88220, 1957, 65536⟩
    (by decide) selected_cut_25970

theorem selected_cut_25971 : selected 9 ⟨657228, by decide⟩
    (prefixPartial 12 88221) = some ⟨12, 2, 0, 657228, 88221, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_88221_657228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88221 ⟨657228, by decide⟩ :=
  accepted_of_selected 12 88221 ⟨657228, by decide⟩ ⟨12, 2, 0, 657228, 88221, 2097, 65536⟩
    (by decide) selected_cut_25971

theorem selected_cut_25972 : selected 9 ⟨657251, by decide⟩
    (prefixPartial 12 88222) = some ⟨12, 2, 0, 657251, 88222, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_88222_657251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88222 ⟨657251, by decide⟩ :=
  accepted_of_selected 12 88222 ⟨657251, by decide⟩ ⟨12, 2, 0, 657251, 88222, 2161, 65536⟩
    (by decide) selected_cut_25972

theorem selected_cut_25973 : selected 9 ⟨657271, by decide⟩
    (prefixPartial 12 88223) = some ⟨12, 2, 0, 657271, 88223, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_88223_657271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88223 ⟨657271, by decide⟩ :=
  accepted_of_selected 12 88223 ⟨657271, by decide⟩ ⟨12, 2, 0, 657271, 88223, 1745, 65536⟩
    (by decide) selected_cut_25973

theorem unmarked_context_11_22055_657272 : frontier 10 ⟨657272, by decide⟩
    (prefixCache 11 22055) (prefixPartial 11 22055) = false := by
  decide +kernel

theorem node_context_11_22055_657272 : EJMOriginalGlobalDAGData.nodes 10 ⟨657272, by decide⟩ =
    .split (coordinate 11) (![⟨657212, by decide⟩,⟨657228, by decide⟩,⟨657251, by decide⟩,⟨657271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22055_657272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22055 ⟨657272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22055
    ⟨657272, by decide⟩ (by decide) (![⟨657212, by decide⟩,⟨657228, by decide⟩,⟨657251, by decide⟩,⟨657271, by decide⟩]) unmarked_context_11_22055_657272 node_context_11_22055_657272
  intro a
  fin_cases a
  · exact context_12_88220_657212
  · exact context_12_88221_657228
  · exact context_12_88222_657251
  · exact context_12_88223_657271

theorem unmarked_context_10_5513_657273 : frontier 11 ⟨657273, by decide⟩
    (prefixCache 10 5513) (prefixPartial 10 5513) = false := by
  decide +kernel

theorem node_context_10_5513_657273 : EJMOriginalGlobalDAGData.nodes 11 ⟨657273, by decide⟩ =
    .split (coordinate 10) (![⟨657023, by decide⟩,⟨657108, by decide⟩,⟨657191, by decide⟩,⟨657272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5513_657273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5513 ⟨657273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5513
    ⟨657273, by decide⟩ (by decide) (![⟨657023, by decide⟩,⟨657108, by decide⟩,⟨657191, by decide⟩,⟨657272, by decide⟩]) unmarked_context_10_5513_657273 node_context_10_5513_657273
  intro a
  fin_cases a
  · exact context_11_22052_657023
  · exact context_11_22053_657108
  · exact context_11_22054_657191
  · exact context_11_22055_657272

theorem selected_cut_25974 : selected 9 ⟨657287, by decide⟩
    (prefixPartial 12 88224) = some ⟨12, 2, 0, 657287, 88224, 593, 65536⟩ := by
  decide +kernel

theorem context_12_88224_657287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88224 ⟨657287, by decide⟩ :=
  accepted_of_selected 12 88224 ⟨657287, by decide⟩ ⟨12, 2, 0, 657287, 88224, 593, 65536⟩
    (by decide) selected_cut_25974

theorem selected_cut_25975 : selected 9 ⟨657303, by decide⟩
    (prefixPartial 12 88225) = some ⟨12, 2, 0, 657303, 88225, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_88225_657303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88225 ⟨657303, by decide⟩ :=
  accepted_of_selected 12 88225 ⟨657303, by decide⟩ ⟨12, 2, 0, 657303, 88225, 1441, 65536⟩
    (by decide) selected_cut_25975

theorem selected_cut_25976 : selected 9 ⟨657322, by decide⟩
    (prefixPartial 12 88226) = some ⟨12, 2, 0, 657322, 88226, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_88226_657322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88226 ⟨657322, by decide⟩ :=
  accepted_of_selected 12 88226 ⟨657322, by decide⟩ ⟨12, 2, 0, 657322, 88226, 1577, 65536⟩
    (by decide) selected_cut_25976

theorem selected_cut_25977 : selected 9 ⟨657331, by decide⟩
    (prefixPartial 12 88227) = some ⟨12, 2, 0, 657331, 88227, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_88227_657331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88227 ⟨657331, by decide⟩ :=
  accepted_of_selected 12 88227 ⟨657331, by decide⟩ ⟨12, 2, 0, 657331, 88227, 1285, 65536⟩
    (by decide) selected_cut_25977

theorem unmarked_context_11_22056_657332 : frontier 10 ⟨657332, by decide⟩
    (prefixCache 11 22056) (prefixPartial 11 22056) = false := by
  decide +kernel

theorem node_context_11_22056_657332 : EJMOriginalGlobalDAGData.nodes 10 ⟨657332, by decide⟩ =
    .split (coordinate 11) (![⟨657287, by decide⟩,⟨657303, by decide⟩,⟨657322, by decide⟩,⟨657331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22056_657332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22056 ⟨657332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22056
    ⟨657332, by decide⟩ (by decide) (![⟨657287, by decide⟩,⟨657303, by decide⟩,⟨657322, by decide⟩,⟨657331, by decide⟩]) unmarked_context_11_22056_657332 node_context_11_22056_657332
  intro a
  fin_cases a
  · exact context_12_88224_657287
  · exact context_12_88225_657303
  · exact context_12_88226_657322
  · exact context_12_88227_657331

theorem selected_cut_25978 : selected 9 ⟨657347, by decide⟩
    (prefixPartial 12 88228) = some ⟨12, 2, 0, 657347, 88228, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_88228_657347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88228 ⟨657347, by decide⟩ :=
  accepted_of_selected 12 88228 ⟨657347, by decide⟩ ⟨12, 2, 0, 657347, 88228, 1301, 65536⟩
    (by decide) selected_cut_25978

theorem selected_cut_25979 : selected 9 ⟨657362, by decide⟩
    (prefixPartial 12 88229) = some ⟨12, 2, 0, 657362, 88229, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_88229_657362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88229 ⟨657362, by decide⟩ :=
  accepted_of_selected 12 88229 ⟨657362, by decide⟩ ⟨12, 2, 0, 657362, 88229, 1205, 65536⟩
    (by decide) selected_cut_25979

theorem selected_cut_25980 : selected 9 ⟨657380, by decide⟩
    (prefixPartial 12 88230) = some ⟨12, 2, 0, 657380, 88230, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_88230_657380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88230 ⟨657380, by decide⟩ :=
  accepted_of_selected 12 88230 ⟨657380, by decide⟩ ⟨12, 2, 0, 657380, 88230, 1397, 65536⟩
    (by decide) selected_cut_25980

theorem selected_cut_25981 : selected 9 ⟨657395, by decide⟩
    (prefixPartial 12 88231) = some ⟨12, 2, 0, 657395, 88231, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_88231_657395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88231 ⟨657395, by decide⟩ :=
  accepted_of_selected 12 88231 ⟨657395, by decide⟩ ⟨12, 2, 0, 657395, 88231, 1241, 65536⟩
    (by decide) selected_cut_25981

theorem unmarked_context_11_22057_657396 : frontier 10 ⟨657396, by decide⟩
    (prefixCache 11 22057) (prefixPartial 11 22057) = false := by
  decide +kernel

theorem node_context_11_22057_657396 : EJMOriginalGlobalDAGData.nodes 10 ⟨657396, by decide⟩ =
    .split (coordinate 11) (![⟨657347, by decide⟩,⟨657362, by decide⟩,⟨657380, by decide⟩,⟨657395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22057_657396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22057 ⟨657396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22057
    ⟨657396, by decide⟩ (by decide) (![⟨657347, by decide⟩,⟨657362, by decide⟩,⟨657380, by decide⟩,⟨657395, by decide⟩]) unmarked_context_11_22057_657396 node_context_11_22057_657396
  intro a
  fin_cases a
  · exact context_12_88228_657347
  · exact context_12_88229_657362
  · exact context_12_88230_657380
  · exact context_12_88231_657395

theorem selected_cut_25982 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 22058) = some ⟨11, 1, 0, 479708, 22058, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22058_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22058 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 22058 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 22058, 1, 262144⟩
    (by decide) selected_cut_25982

theorem selected_cut_25983 : selected 9 ⟨657411, by decide⟩
    (prefixPartial 12 88236) = some ⟨12, 2, 0, 657411, 88236, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_88236_657411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88236 ⟨657411, by decide⟩ :=
  accepted_of_selected 12 88236 ⟨657411, by decide⟩ ⟨12, 2, 0, 657411, 88236, 1385, 65536⟩
    (by decide) selected_cut_25983

theorem selected_cut_25984 : selected 9 ⟨657426, by decide⟩
    (prefixPartial 12 88237) = some ⟨12, 2, 0, 657426, 88237, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_88237_657426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88237 ⟨657426, by decide⟩ :=
  accepted_of_selected 12 88237 ⟨657426, by decide⟩ ⟨12, 2, 0, 657426, 88237, 1449, 65536⟩
    (by decide) selected_cut_25984

theorem selected_cut_25985 : selected 9 ⟨657441, by decide⟩
    (prefixPartial 12 88238) = some ⟨12, 2, 0, 657441, 88238, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_88238_657441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88238 ⟨657441, by decide⟩ :=
  accepted_of_selected 12 88238 ⟨657441, by decide⟩ ⟨12, 2, 0, 657441, 88238, 1453, 65536⟩
    (by decide) selected_cut_25985

theorem selected_cut_25986 : selected 9 ⟨657452, by decide⟩
    (prefixPartial 12 88239) = some ⟨12, 2, 0, 657452, 88239, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_88239_657452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88239 ⟨657452, by decide⟩ :=
  accepted_of_selected 12 88239 ⟨657452, by decide⟩ ⟨12, 2, 0, 657452, 88239, 1173, 65536⟩
    (by decide) selected_cut_25986

theorem unmarked_context_11_22059_657453 : frontier 10 ⟨657453, by decide⟩
    (prefixCache 11 22059) (prefixPartial 11 22059) = false := by
  decide +kernel

theorem node_context_11_22059_657453 : EJMOriginalGlobalDAGData.nodes 10 ⟨657453, by decide⟩ =
    .split (coordinate 11) (![⟨657411, by decide⟩,⟨657426, by decide⟩,⟨657441, by decide⟩,⟨657452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22059_657453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22059 ⟨657453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22059
    ⟨657453, by decide⟩ (by decide) (![⟨657411, by decide⟩,⟨657426, by decide⟩,⟨657441, by decide⟩,⟨657452, by decide⟩]) unmarked_context_11_22059_657453 node_context_11_22059_657453
  intro a
  fin_cases a
  · exact context_12_88236_657411
  · exact context_12_88237_657426
  · exact context_12_88238_657441
  · exact context_12_88239_657452

theorem unmarked_context_10_5514_657454 : frontier 11 ⟨657454, by decide⟩
    (prefixCache 10 5514) (prefixPartial 10 5514) = false := by
  decide +kernel

theorem node_context_10_5514_657454 : EJMOriginalGlobalDAGData.nodes 11 ⟨657454, by decide⟩ =
    .split (coordinate 10) (![⟨657332, by decide⟩,⟨657396, by decide⟩,⟨479708, by decide⟩,⟨657453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5514_657454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5514 ⟨657454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5514
    ⟨657454, by decide⟩ (by decide) (![⟨657332, by decide⟩,⟨657396, by decide⟩,⟨479708, by decide⟩,⟨657453, by decide⟩]) unmarked_context_10_5514_657454 node_context_10_5514_657454
  intro a
  fin_cases a
  · exact context_11_22056_657332
  · exact context_11_22057_657396
  · exact context_11_22058_479708
  · exact context_11_22059_657453

theorem selected_cut_25987 : selected 9 ⟨657482, by decide⟩
    (prefixPartial 12 88240) = some ⟨12, 2, 0, 657482, 88240, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_88240_657482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88240 ⟨657482, by decide⟩ :=
  accepted_of_selected 12 88240 ⟨657482, by decide⟩ ⟨12, 2, 0, 657482, 88240, 1969, 65536⟩
    (by decide) selected_cut_25987

theorem selected_cut_25988 : selected 9 ⟨657492, by decide⟩
    (prefixPartial 12 88241) = some ⟨12, 2, 0, 657492, 88241, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_88241_657492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88241 ⟨657492, by decide⟩ :=
  accepted_of_selected 12 88241 ⟨657492, by decide⟩ ⟨12, 2, 0, 657492, 88241, 1321, 65536⟩
    (by decide) selected_cut_25988

theorem selected_cut_25989 : selected 9 ⟨657508, by decide⟩
    (prefixPartial 12 88242) = some ⟨12, 2, 0, 657508, 88242, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_88242_657508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88242 ⟨657508, by decide⟩ :=
  accepted_of_selected 12 88242 ⟨657508, by decide⟩ ⟨12, 2, 0, 657508, 88242, 1361, 65536⟩
    (by decide) selected_cut_25989

theorem selected_cut_25990 : selected 9 ⟨657519, by decide⟩
    (prefixPartial 12 88243) = some ⟨12, 2, 0, 657519, 88243, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_88243_657519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88243 ⟨657519, by decide⟩ :=
  accepted_of_selected 12 88243 ⟨657519, by decide⟩ ⟨12, 2, 0, 657519, 88243, 1217, 65536⟩
    (by decide) selected_cut_25990

theorem unmarked_context_11_22060_657520 : frontier 10 ⟨657520, by decide⟩
    (prefixCache 11 22060) (prefixPartial 11 22060) = false := by
  decide +kernel

theorem node_context_11_22060_657520 : EJMOriginalGlobalDAGData.nodes 10 ⟨657520, by decide⟩ =
    .split (coordinate 11) (![⟨657482, by decide⟩,⟨657492, by decide⟩,⟨657508, by decide⟩,⟨657519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22060_657520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22060 ⟨657520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22060
    ⟨657520, by decide⟩ (by decide) (![⟨657482, by decide⟩,⟨657492, by decide⟩,⟨657508, by decide⟩,⟨657519, by decide⟩]) unmarked_context_11_22060_657520 node_context_11_22060_657520
  intro a
  fin_cases a
  · exact context_12_88240_657482
  · exact context_12_88241_657492
  · exact context_12_88242_657508
  · exact context_12_88243_657519

theorem selected_cut_25991 : selected 9 ⟨657534, by decide⟩
    (prefixPartial 12 88244) = some ⟨12, 2, 0, 657534, 88244, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_88244_657534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88244 ⟨657534, by decide⟩ :=
  accepted_of_selected 12 88244 ⟨657534, by decide⟩ ⟨12, 2, 0, 657534, 88244, 1241, 65536⟩
    (by decide) selected_cut_25991

theorem selected_cut_25992 : selected 9 ⟨657547, by decide⟩
    (prefixPartial 12 88245) = some ⟨12, 2, 0, 657547, 88245, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_88245_657547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88245 ⟨657547, by decide⟩ :=
  accepted_of_selected 12 88245 ⟨657547, by decide⟩ ⟨12, 2, 0, 657547, 88245, 1157, 65536⟩
    (by decide) selected_cut_25992

theorem selected_cut_25993 : selected 9 ⟨657559, by decide⟩
    (prefixPartial 12 88246) = some ⟨12, 2, 0, 657559, 88246, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_88246_657559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88246 ⟨657559, by decide⟩ :=
  accepted_of_selected 12 88246 ⟨657559, by decide⟩ ⟨12, 2, 0, 657559, 88246, 1133, 65536⟩
    (by decide) selected_cut_25993

theorem selected_cut_25994 : selected 9 ⟨657571, by decide⟩
    (prefixPartial 12 88247) = some ⟨12, 2, 0, 657571, 88247, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_88247_657571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88247 ⟨657571, by decide⟩ :=
  accepted_of_selected 12 88247 ⟨657571, by decide⟩ ⟨12, 2, 0, 657571, 88247, 1101, 65536⟩
    (by decide) selected_cut_25994

theorem unmarked_context_11_22061_657572 : frontier 10 ⟨657572, by decide⟩
    (prefixCache 11 22061) (prefixPartial 11 22061) = false := by
  decide +kernel

theorem node_context_11_22061_657572 : EJMOriginalGlobalDAGData.nodes 10 ⟨657572, by decide⟩ =
    .split (coordinate 11) (![⟨657534, by decide⟩,⟨657547, by decide⟩,⟨657559, by decide⟩,⟨657571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22061_657572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22061 ⟨657572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22061
    ⟨657572, by decide⟩ (by decide) (![⟨657534, by decide⟩,⟨657547, by decide⟩,⟨657559, by decide⟩,⟨657571, by decide⟩]) unmarked_context_11_22061_657572 node_context_11_22061_657572
  intro a
  fin_cases a
  · exact context_12_88244_657534
  · exact context_12_88245_657547
  · exact context_12_88246_657559
  · exact context_12_88247_657571

theorem selected_cut_25995 : selected 9 ⟨657585, by decide⟩
    (prefixPartial 12 88248) = some ⟨12, 2, 0, 657585, 88248, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_88248_657585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88248 ⟨657585, by decide⟩ :=
  accepted_of_selected 12 88248 ⟨657585, by decide⟩ ⟨12, 2, 0, 657585, 88248, 1173, 65536⟩
    (by decide) selected_cut_25995

theorem selected_cut_25996 : selected 9 ⟨657599, by decide⟩
    (prefixPartial 12 88249) = some ⟨12, 2, 0, 657599, 88249, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_88249_657599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88249 ⟨657599, by decide⟩ :=
  accepted_of_selected 12 88249 ⟨657599, by decide⟩ ⟨12, 2, 0, 657599, 88249, 1261, 65536⟩
    (by decide) selected_cut_25996

theorem selected_cut_25997 : selected 9 ⟨657610, by decide⟩
    (prefixPartial 12 88250) = some ⟨12, 2, 0, 657610, 88250, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_88250_657610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88250 ⟨657610, by decide⟩ :=
  accepted_of_selected 12 88250 ⟨657610, by decide⟩ ⟨12, 2, 0, 657610, 88250, 1041, 65536⟩
    (by decide) selected_cut_25997

theorem selected_cut_25998 : selected 9 ⟨657621, by decide⟩
    (prefixPartial 12 88251) = some ⟨12, 2, 0, 657621, 88251, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_88251_657621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88251 ⟨657621, by decide⟩ :=
  accepted_of_selected 12 88251 ⟨657621, by decide⟩ ⟨12, 2, 0, 657621, 88251, 1037, 65536⟩
    (by decide) selected_cut_25998

theorem unmarked_context_11_22062_657622 : frontier 10 ⟨657622, by decide⟩
    (prefixCache 11 22062) (prefixPartial 11 22062) = false := by
  decide +kernel

theorem node_context_11_22062_657622 : EJMOriginalGlobalDAGData.nodes 10 ⟨657622, by decide⟩ =
    .split (coordinate 11) (![⟨657585, by decide⟩,⟨657599, by decide⟩,⟨657610, by decide⟩,⟨657621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22062_657622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22062 ⟨657622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22062
    ⟨657622, by decide⟩ (by decide) (![⟨657585, by decide⟩,⟨657599, by decide⟩,⟨657610, by decide⟩,⟨657621, by decide⟩]) unmarked_context_11_22062_657622 node_context_11_22062_657622
  intro a
  fin_cases a
  · exact context_12_88248_657585
  · exact context_12_88249_657599
  · exact context_12_88250_657610
  · exact context_12_88251_657621

theorem selected_cut_25999 : selected 10 ⟨657662, by decide⟩
    (prefixPartial 11 22063) = some ⟨11, 2, 0, 657662, 22063, 3913, 262144⟩ := by
  decide +kernel

theorem context_11_22063_657662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22063 ⟨657662, by decide⟩ :=
  accepted_of_selected 11 22063 ⟨657662, by decide⟩ ⟨11, 2, 0, 657662, 22063, 3913, 262144⟩
    (by decide) selected_cut_25999

theorem unmarked_context_10_5515_657663 : frontier 11 ⟨657663, by decide⟩
    (prefixCache 10 5515) (prefixPartial 10 5515) = false := by
  decide +kernel

theorem node_context_10_5515_657663 : EJMOriginalGlobalDAGData.nodes 11 ⟨657663, by decide⟩ =
    .split (coordinate 10) (![⟨657520, by decide⟩,⟨657572, by decide⟩,⟨657622, by decide⟩,⟨657662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5515_657663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5515 ⟨657663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5515
    ⟨657663, by decide⟩ (by decide) (![⟨657520, by decide⟩,⟨657572, by decide⟩,⟨657622, by decide⟩,⟨657662, by decide⟩]) unmarked_context_10_5515_657663 node_context_10_5515_657663
  intro a
  fin_cases a
  · exact context_11_22060_657520
  · exact context_11_22061_657572
  · exact context_11_22062_657622
  · exact context_11_22063_657662

theorem unmarked_context_9_1378_657664 : frontier 12 ⟨657664, by decide⟩
    (prefixCache 9 1378) (prefixPartial 9 1378) = false := by
  decide +kernel

theorem node_context_9_1378_657664 : EJMOriginalGlobalDAGData.nodes 12 ⟨657664, by decide⟩ =
    .split (coordinate 9) (![⟨656895, by decide⟩,⟨657273, by decide⟩,⟨657454, by decide⟩,⟨657663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1378_657664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1378 ⟨657664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1378
    ⟨657664, by decide⟩ (by decide) (![⟨656895, by decide⟩,⟨657273, by decide⟩,⟨657454, by decide⟩,⟨657663, by decide⟩]) unmarked_context_9_1378_657664 node_context_9_1378_657664
  intro a
  fin_cases a
  · exact context_10_5512_656895
  · exact context_10_5513_657273
  · exact context_10_5514_657454
  · exact context_10_5515_657663

theorem selected_cut_26000 : selected 10 ⟨657694, by decide⟩
    (prefixPartial 11 22064) = some ⟨11, 2, 0, 657694, 22064, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_22064_657694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22064 ⟨657694, by decide⟩ :=
  accepted_of_selected 11 22064 ⟨657694, by decide⟩ ⟨11, 2, 0, 657694, 22064, 2645, 262144⟩
    (by decide) selected_cut_26000

theorem selected_cut_26001 : selected 10 ⟨657730, by decide⟩
    (prefixPartial 11 22065) = some ⟨11, 2, 0, 657730, 22065, 3413, 262144⟩ := by
  decide +kernel

theorem context_11_22065_657730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22065 ⟨657730, by decide⟩ :=
  accepted_of_selected 11 22065 ⟨657730, by decide⟩ ⟨11, 2, 0, 657730, 22065, 3413, 262144⟩
    (by decide) selected_cut_26001

theorem selected_cut_26002 : selected 10 ⟨657757, by decide⟩
    (prefixPartial 11 22066) = some ⟨11, 2, 0, 657757, 22066, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_22066_657757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22066 ⟨657757, by decide⟩ :=
  accepted_of_selected 11 22066 ⟨657757, by decide⟩ ⟨11, 2, 0, 657757, 22066, 2973, 262144⟩
    (by decide) selected_cut_26002

theorem selected_cut_26003 : selected 10 ⟨657793, by decide⟩
    (prefixPartial 11 22067) = some ⟨11, 2, 0, 657793, 22067, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_22067_657793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22067 ⟨657793, by decide⟩ :=
  accepted_of_selected 11 22067 ⟨657793, by decide⟩ ⟨11, 2, 0, 657793, 22067, 3357, 262144⟩
    (by decide) selected_cut_26003

theorem unmarked_context_10_5516_657794 : frontier 11 ⟨657794, by decide⟩
    (prefixCache 10 5516) (prefixPartial 10 5516) = false := by
  decide +kernel

theorem node_context_10_5516_657794 : EJMOriginalGlobalDAGData.nodes 11 ⟨657794, by decide⟩ =
    .split (coordinate 10) (![⟨657694, by decide⟩,⟨657730, by decide⟩,⟨657757, by decide⟩,⟨657793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5516_657794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5516 ⟨657794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5516
    ⟨657794, by decide⟩ (by decide) (![⟨657694, by decide⟩,⟨657730, by decide⟩,⟨657757, by decide⟩,⟨657793, by decide⟩]) unmarked_context_10_5516_657794 node_context_10_5516_657794
  intro a
  fin_cases a
  · exact context_11_22064_657694
  · exact context_11_22065_657730
  · exact context_11_22066_657757
  · exact context_11_22067_657793

theorem selected_cut_26004 : selected 10 ⟨657858, by decide⟩
    (prefixPartial 11 22068) = some ⟨11, 2, 0, 657858, 22068, 3393, 262144⟩ := by
  decide +kernel

theorem context_11_22068_657858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22068 ⟨657858, by decide⟩ :=
  accepted_of_selected 11 22068 ⟨657858, by decide⟩ ⟨11, 2, 0, 657858, 22068, 3393, 262144⟩
    (by decide) selected_cut_26004

theorem selected_cut_26005 : selected 10 ⟨657878, by decide⟩
    (prefixPartial 11 22069) = some ⟨11, 2, 0, 657878, 22069, 2601, 262144⟩ := by
  decide +kernel

theorem context_11_22069_657878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22069 ⟨657878, by decide⟩ :=
  accepted_of_selected 11 22069 ⟨657878, by decide⟩ ⟨11, 2, 0, 657878, 22069, 2601, 262144⟩
    (by decide) selected_cut_26005

theorem selected_cut_26006 : selected 10 ⟨657900, by decide⟩
    (prefixPartial 11 22070) = some ⟨11, 2, 0, 657900, 22070, 2353, 262144⟩ := by
  decide +kernel

theorem context_11_22070_657900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22070 ⟨657900, by decide⟩ :=
  accepted_of_selected 11 22070 ⟨657900, by decide⟩ ⟨11, 2, 0, 657900, 22070, 2353, 262144⟩
    (by decide) selected_cut_26006

theorem selected_cut_26007 : selected 10 ⟨657922, by decide⟩
    (prefixPartial 11 22071) = some ⟨11, 2, 0, 657922, 22071, 2177, 262144⟩ := by
  decide +kernel

theorem context_11_22071_657922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22071 ⟨657922, by decide⟩ :=
  accepted_of_selected 11 22071 ⟨657922, by decide⟩ ⟨11, 2, 0, 657922, 22071, 2177, 262144⟩
    (by decide) selected_cut_26007

theorem unmarked_context_10_5517_657923 : frontier 11 ⟨657923, by decide⟩
    (prefixCache 10 5517) (prefixPartial 10 5517) = false := by
  decide +kernel

theorem node_context_10_5517_657923 : EJMOriginalGlobalDAGData.nodes 11 ⟨657923, by decide⟩ =
    .split (coordinate 10) (![⟨657858, by decide⟩,⟨657878, by decide⟩,⟨657900, by decide⟩,⟨657922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5517_657923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5517 ⟨657923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5517
    ⟨657923, by decide⟩ (by decide) (![⟨657858, by decide⟩,⟨657878, by decide⟩,⟨657900, by decide⟩,⟨657922, by decide⟩]) unmarked_context_10_5517_657923 node_context_10_5517_657923
  intro a
  fin_cases a
  · exact context_11_22068_657858
  · exact context_11_22069_657878
  · exact context_11_22070_657900
  · exact context_11_22071_657922

theorem selected_cut_26008 : selected 10 ⟨657947, by decide⟩
    (prefixPartial 11 22072) = some ⟨11, 2, 0, 657947, 22072, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_22072_657947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22072 ⟨657947, by decide⟩ :=
  accepted_of_selected 11 22072 ⟨657947, by decide⟩ ⟨11, 2, 0, 657947, 22072, 1729, 262144⟩
    (by decide) selected_cut_26008

theorem selected_cut_26009 : selected 10 ⟨657960, by decide⟩
    (prefixPartial 11 22073) = some ⟨11, 2, 0, 657960, 22073, 1269, 262144⟩ := by
  decide +kernel

theorem context_11_22073_657960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22073 ⟨657960, by decide⟩ :=
  accepted_of_selected 11 22073 ⟨657960, by decide⟩ ⟨11, 2, 0, 657960, 22073, 1269, 262144⟩
    (by decide) selected_cut_26009

theorem selected_cut_26010 : selected 10 ⟨657973, by decide⟩
    (prefixPartial 11 22074) = some ⟨11, 2, 0, 657973, 22074, 949, 262144⟩ := by
  decide +kernel

theorem context_11_22074_657973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22074 ⟨657973, by decide⟩ :=
  accepted_of_selected 11 22074 ⟨657973, by decide⟩ ⟨11, 2, 0, 657973, 22074, 949, 262144⟩
    (by decide) selected_cut_26010

theorem selected_cut_26011 : selected 10 ⟨657987, by decide⟩
    (prefixPartial 11 22075) = some ⟨11, 2, 0, 657987, 22075, 929, 262144⟩ := by
  decide +kernel

theorem context_11_22075_657987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22075 ⟨657987, by decide⟩ :=
  accepted_of_selected 11 22075 ⟨657987, by decide⟩ ⟨11, 2, 0, 657987, 22075, 929, 262144⟩
    (by decide) selected_cut_26011

theorem unmarked_context_10_5518_657988 : frontier 11 ⟨657988, by decide⟩
    (prefixCache 10 5518) (prefixPartial 10 5518) = false := by
  decide +kernel

theorem node_context_10_5518_657988 : EJMOriginalGlobalDAGData.nodes 11 ⟨657988, by decide⟩ =
    .split (coordinate 10) (![⟨657947, by decide⟩,⟨657960, by decide⟩,⟨657973, by decide⟩,⟨657987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5518_657988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5518 ⟨657988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5518
    ⟨657988, by decide⟩ (by decide) (![⟨657947, by decide⟩,⟨657960, by decide⟩,⟨657973, by decide⟩,⟨657987, by decide⟩]) unmarked_context_10_5518_657988 node_context_10_5518_657988
  intro a
  fin_cases a
  · exact context_11_22072_657947
  · exact context_11_22073_657960
  · exact context_11_22074_657973
  · exact context_11_22075_657987

theorem selected_cut_26012 : selected 11 ⟨657996, by decide⟩
    (prefixPartial 10 5519) = some ⟨10, 2, 0, 657996, 5519, 1505, 1048576⟩ := by
  decide +kernel

theorem context_10_5519_657996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5519 ⟨657996, by decide⟩ :=
  accepted_of_selected 10 5519 ⟨657996, by decide⟩ ⟨10, 2, 0, 657996, 5519, 1505, 1048576⟩
    (by decide) selected_cut_26012

theorem unmarked_context_9_1379_657997 : frontier 12 ⟨657997, by decide⟩
    (prefixCache 9 1379) (prefixPartial 9 1379) = false := by
  decide +kernel

theorem node_context_9_1379_657997 : EJMOriginalGlobalDAGData.nodes 12 ⟨657997, by decide⟩ =
    .split (coordinate 9) (![⟨657794, by decide⟩,⟨657923, by decide⟩,⟨657988, by decide⟩,⟨657996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1379_657997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1379 ⟨657997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1379
    ⟨657997, by decide⟩ (by decide) (![⟨657794, by decide⟩,⟨657923, by decide⟩,⟨657988, by decide⟩,⟨657996, by decide⟩]) unmarked_context_9_1379_657997 node_context_9_1379_657997
  intro a
  fin_cases a
  · exact context_10_5516_657794
  · exact context_10_5517_657923
  · exact context_10_5518_657988
  · exact context_10_5519_657996

theorem unmarked_context_8_344_657998 : frontier 13 ⟨657998, by decide⟩
    (prefixCache 8 344) (prefixPartial 8 344) = false := by
  decide +kernel

theorem node_context_8_344_657998 : EJMOriginalGlobalDAGData.nodes 13 ⟨657998, by decide⟩ =
    .split (coordinate 8) (![⟨653883, by decide⟩,⟨656526, by decide⟩,⟨657664, by decide⟩,⟨657997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_344_657998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 344 ⟨657998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 344
    ⟨657998, by decide⟩ (by decide) (![⟨653883, by decide⟩,⟨656526, by decide⟩,⟨657664, by decide⟩,⟨657997, by decide⟩]) unmarked_context_8_344_657998 node_context_8_344_657998
  intro a
  fin_cases a
  · exact context_9_1376_653883
  · exact context_9_1377_656526
  · exact context_9_1378_657664
  · exact context_9_1379_657997

theorem selected_cut_26013 : selected 13 ⟨643294, by decide⟩
    (prefixPartial 8 345) = some ⟨8, 1, 0, 643294, 345, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_345_643294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 345 ⟨643294, by decide⟩ :=
  accepted_of_selected 8 345 ⟨643294, by decide⟩ ⟨8, 1, 0, 643294, 345, 1, 16777216⟩
    (by decide) selected_cut_26013

theorem selected_cut_26014 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 22144) = some ⟨11, 1, 0, 434745, 22144, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22144_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22144 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 22144 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 22144, 1, 262144⟩
    (by decide) selected_cut_26014

theorem selected_cut_26015 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88580) = some ⟨12, 1, 0, 448748, 88580, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88580_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88580 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88580 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88580, 1, 65536⟩
    (by decide) selected_cut_26015

theorem selected_cut_26016 : selected 8 ⟨658119, by decide⟩
    (prefixPartial 13 354324) = some ⟨13, 2, 0, 658119, 354324, 3785, 16384⟩ := by
  decide +kernel

theorem context_13_354324_658119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354324 ⟨658119, by decide⟩ :=
  accepted_of_selected 13 354324 ⟨658119, by decide⟩ ⟨13, 2, 0, 658119, 354324, 3785, 16384⟩
    (by decide) selected_cut_26016

theorem selected_cut_26017 : selected 8 ⟨658204, by decide⟩
    (prefixPartial 13 354325) = some ⟨13, 2, 0, 658204, 354325, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_354325_658204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354325 ⟨658204, by decide⟩ :=
  accepted_of_selected 13 354325 ⟨658204, by decide⟩ ⟨13, 2, 0, 658204, 354325, 2489, 16384⟩
    (by decide) selected_cut_26017

theorem selected_cut_26018 : selected 8 ⟨658224, by decide⟩
    (prefixPartial 13 354326) = some ⟨13, 2, 0, 658224, 354326, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_354326_658224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354326 ⟨658224, by decide⟩ :=
  accepted_of_selected 13 354326 ⟨658224, by decide⟩ ⟨13, 2, 0, 658224, 354326, 1413, 16384⟩
    (by decide) selected_cut_26018

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
