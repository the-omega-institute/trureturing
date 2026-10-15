/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover019
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_01922 : selected 7 ⟨63956, by decide⟩
    (prefixPartial 14 86051) = some ⟨14, 2, 0, 63956, 86051, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_86051_63956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86051 ⟨63956, by decide⟩ :=
  accepted_of_selected 14 86051 ⟨63956, by decide⟩ ⟨14, 2, 0, 63956, 86051, 1181, 4096⟩
    (by decide) selected_cut_01922

theorem unmarked_context_13_21512_63957 : frontier 8 ⟨63957, by decide⟩
    (prefixCache 13 21512) (prefixPartial 13 21512) = false := by
  decide +kernel

theorem node_context_13_21512_63957 : EJMOriginalGlobalDAGData.nodes 8 ⟨63957, by decide⟩ =
    .split (coordinate 13) (![⟨63889, by decide⟩,⟨63910, by decide⟩,⟨63935, by decide⟩,⟨63956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_21512_63957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21512 ⟨63957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 21512
    ⟨63957, by decide⟩ (by decide) (![⟨63889, by decide⟩,⟨63910, by decide⟩,⟨63935, by decide⟩,⟨63956, by decide⟩]) unmarked_context_13_21512_63957 node_context_13_21512_63957
  intro a
  fin_cases a
  · exact context_14_86048_63889
  · exact context_14_86049_63910
  · exact context_14_86050_63935
  · exact context_14_86051_63956

theorem selected_cut_01923 : selected 8 ⟨64007, by decide⟩
    (prefixPartial 13 21513) = some ⟨13, 2, 0, 64007, 21513, 3449, 16384⟩ := by
  decide +kernel

theorem context_13_21513_64007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21513 ⟨64007, by decide⟩ :=
  accepted_of_selected 13 21513 ⟨64007, by decide⟩ ⟨13, 2, 0, 64007, 21513, 3449, 16384⟩
    (by decide) selected_cut_01923

theorem selected_cut_01924 : selected 8 ⟨64043, by decide⟩
    (prefixPartial 13 21514) = some ⟨13, 2, 0, 64043, 21514, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_21514_64043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21514 ⟨64043, by decide⟩ :=
  accepted_of_selected 13 21514 ⟨64043, by decide⟩ ⟨13, 2, 0, 64043, 21514, 2757, 16384⟩
    (by decide) selected_cut_01924

theorem selected_cut_01925 : selected 8 ⟨64064, by decide⟩
    (prefixPartial 13 21515) = some ⟨13, 2, 0, 64064, 21515, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_21515_64064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21515 ⟨64064, by decide⟩ :=
  accepted_of_selected 13 21515 ⟨64064, by decide⟩ ⟨13, 2, 0, 64064, 21515, 1445, 16384⟩
    (by decide) selected_cut_01925

theorem unmarked_context_12_5378_64065 : frontier 9 ⟨64065, by decide⟩
    (prefixCache 12 5378) (prefixPartial 12 5378) = false := by
  decide +kernel

theorem node_context_12_5378_64065 : EJMOriginalGlobalDAGData.nodes 9 ⟨64065, by decide⟩ =
    .split (coordinate 12) (![⟨63957, by decide⟩,⟨64007, by decide⟩,⟨64043, by decide⟩,⟨64064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5378_64065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5378 ⟨64065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5378
    ⟨64065, by decide⟩ (by decide) (![⟨63957, by decide⟩,⟨64007, by decide⟩,⟨64043, by decide⟩,⟨64064, by decide⟩]) unmarked_context_12_5378_64065 node_context_12_5378_64065
  intro a
  fin_cases a
  · exact context_13_21512_63957
  · exact context_13_21513_64007
  · exact context_13_21514_64043
  · exact context_13_21515_64064

theorem selected_cut_01926 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5379) = some ⟨12, 1, 0, 893, 5379, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5379_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5379 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5379 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5379, 1, 65536⟩
    (by decide) selected_cut_01926

theorem unmarked_context_11_1344_64066 : frontier 10 ⟨64066, by decide⟩
    (prefixCache 11 1344) (prefixPartial 11 1344) = false := by
  decide +kernel

theorem node_context_11_1344_64066 : EJMOriginalGlobalDAGData.nodes 10 ⟨64066, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨63853, by decide⟩,⟨64065, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1344_64066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1344 ⟨64066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1344
    ⟨64066, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨63853, by decide⟩,⟨64065, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1344_64066 node_context_11_1344_64066
  intro a
  fin_cases a
  · exact context_12_5376_34034
  · exact context_12_5377_63853
  · exact context_12_5378_64065
  · exact context_12_5379_893

theorem selected_cut_01927 : selected 8 ⟨64137, by decide⟩
    (prefixPartial 13 21520) = some ⟨13, 2, 0, 64137, 21520, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_21520_64137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21520 ⟨64137, by decide⟩ :=
  accepted_of_selected 13 21520 ⟨64137, by decide⟩ ⟨13, 2, 0, 64137, 21520, 2261, 16384⟩
    (by decide) selected_cut_01927

theorem selected_cut_01928 : selected 8 ⟨64172, by decide⟩
    (prefixPartial 13 21521) = some ⟨13, 2, 0, 64172, 21521, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_21521_64172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21521 ⟨64172, by decide⟩ :=
  accepted_of_selected 13 21521 ⟨64172, by decide⟩ ⟨13, 2, 0, 64172, 21521, 1465, 16384⟩
    (by decide) selected_cut_01928

theorem selected_cut_01929 : selected 8 ⟨64246, by decide⟩
    (prefixPartial 13 21522) = some ⟨13, 2, 0, 64246, 21522, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_21522_64246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21522 ⟨64246, by decide⟩ :=
  accepted_of_selected 13 21522 ⟨64246, by decide⟩ ⟨13, 2, 0, 64246, 21522, 1993, 16384⟩
    (by decide) selected_cut_01929

theorem selected_cut_01930 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 21523) = some ⟨13, 1, 0, 414, 21523, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21523_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21523 ⟨414, by decide⟩ :=
  accepted_of_selected 13 21523 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 21523, 1, 16384⟩
    (by decide) selected_cut_01930

theorem unmarked_context_12_5380_64247 : frontier 9 ⟨64247, by decide⟩
    (prefixCache 12 5380) (prefixPartial 12 5380) = false := by
  decide +kernel

theorem node_context_12_5380_64247 : EJMOriginalGlobalDAGData.nodes 9 ⟨64247, by decide⟩ =
    .split (coordinate 12) (![⟨64137, by decide⟩,⟨64172, by decide⟩,⟨64246, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5380_64247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5380 ⟨64247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5380
    ⟨64247, by decide⟩ (by decide) (![⟨64137, by decide⟩,⟨64172, by decide⟩,⟨64246, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_5380_64247 node_context_12_5380_64247
  intro a
  fin_cases a
  · exact context_13_21520_64137
  · exact context_13_21521_64172
  · exact context_13_21522_64246
  · exact context_13_21523_414

theorem selected_cut_01931 : selected 7 ⟨64271, by decide⟩
    (prefixPartial 14 86096) = some ⟨14, 2, 0, 64271, 86096, 1317, 4096⟩ := by
  decide +kernel

theorem context_14_86096_64271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86096 ⟨64271, by decide⟩ :=
  accepted_of_selected 14 86096 ⟨64271, by decide⟩ ⟨14, 2, 0, 64271, 86096, 1317, 4096⟩
    (by decide) selected_cut_01931

theorem selected_cut_01932 : selected 7 ⟨64302, by decide⟩
    (prefixPartial 14 86097) = some ⟨14, 2, 0, 64302, 86097, 957, 4096⟩ := by
  decide +kernel

theorem context_14_86097_64302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86097 ⟨64302, by decide⟩ :=
  accepted_of_selected 14 86097 ⟨64302, by decide⟩ ⟨14, 2, 0, 64302, 86097, 957, 4096⟩
    (by decide) selected_cut_01932

theorem selected_cut_01933 : selected 7 ⟨64337, by decide⟩
    (prefixPartial 14 86098) = some ⟨14, 2, 0, 64337, 86098, 1901, 4096⟩ := by
  decide +kernel

theorem context_14_86098_64337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86098 ⟨64337, by decide⟩ :=
  accepted_of_selected 14 86098 ⟨64337, by decide⟩ ⟨14, 2, 0, 64337, 86098, 1901, 4096⟩
    (by decide) selected_cut_01933

theorem selected_cut_01934 : selected 7 ⟨291, by decide⟩
    (prefixPartial 14 86099) = some ⟨14, 1, 0, 291, 86099, 1, 4096⟩ := by
  decide +kernel

theorem context_14_86099_291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86099 ⟨291, by decide⟩ :=
  accepted_of_selected 14 86099 ⟨291, by decide⟩ ⟨14, 1, 0, 291, 86099, 1, 4096⟩
    (by decide) selected_cut_01934

theorem unmarked_context_13_21524_64338 : frontier 8 ⟨64338, by decide⟩
    (prefixCache 13 21524) (prefixPartial 13 21524) = false := by
  decide +kernel

theorem node_context_13_21524_64338 : EJMOriginalGlobalDAGData.nodes 8 ⟨64338, by decide⟩ =
    .split (coordinate 13) (![⟨64271, by decide⟩,⟨64302, by decide⟩,⟨64337, by decide⟩,⟨291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_21524_64338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21524 ⟨64338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 21524
    ⟨64338, by decide⟩ (by decide) (![⟨64271, by decide⟩,⟨64302, by decide⟩,⟨64337, by decide⟩,⟨291, by decide⟩]) unmarked_context_13_21524_64338 node_context_13_21524_64338
  intro a
  fin_cases a
  · exact context_14_86096_64271
  · exact context_14_86097_64302
  · exact context_14_86098_64337
  · exact context_14_86099_291

theorem selected_cut_01935 : selected 8 ⟨64406, by decide⟩
    (prefixPartial 13 21525) = some ⟨13, 2, 0, 64406, 21525, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_21525_64406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21525 ⟨64406, by decide⟩ :=
  accepted_of_selected 13 21525 ⟨64406, by decide⟩ ⟨13, 2, 0, 64406, 21525, 2957, 16384⟩
    (by decide) selected_cut_01935

theorem selected_cut_01936 : selected 8 ⟨64479, by decide⟩
    (prefixPartial 13 21526) = some ⟨13, 2, 0, 64479, 21526, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_21526_64479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21526 ⟨64479, by decide⟩ :=
  accepted_of_selected 13 21526 ⟨64479, by decide⟩ ⟨13, 2, 0, 64479, 21526, 3077, 16384⟩
    (by decide) selected_cut_01936

theorem selected_cut_01937 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 21527) = some ⟨13, 1, 0, 414, 21527, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21527_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21527 ⟨414, by decide⟩ :=
  accepted_of_selected 13 21527 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 21527, 1, 16384⟩
    (by decide) selected_cut_01937

theorem unmarked_context_12_5381_64480 : frontier 9 ⟨64480, by decide⟩
    (prefixCache 12 5381) (prefixPartial 12 5381) = false := by
  decide +kernel

theorem node_context_12_5381_64480 : EJMOriginalGlobalDAGData.nodes 9 ⟨64480, by decide⟩ =
    .split (coordinate 12) (![⟨64338, by decide⟩,⟨64406, by decide⟩,⟨64479, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5381_64480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5381 ⟨64480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5381
    ⟨64480, by decide⟩ (by decide) (![⟨64338, by decide⟩,⟨64406, by decide⟩,⟨64479, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_5381_64480 node_context_12_5381_64480
  intro a
  fin_cases a
  · exact context_13_21524_64338
  · exact context_13_21525_64406
  · exact context_13_21526_64479
  · exact context_13_21527_414

theorem selected_cut_01938 : selected 7 ⟨64503, by decide⟩
    (prefixPartial 14 86112) = some ⟨14, 2, 0, 64503, 86112, 1257, 4096⟩ := by
  decide +kernel

theorem context_14_86112_64503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86112 ⟨64503, by decide⟩ :=
  accepted_of_selected 14 86112 ⟨64503, by decide⟩ ⟨14, 2, 0, 64503, 86112, 1257, 4096⟩
    (by decide) selected_cut_01938

theorem selected_cut_01939 : selected 7 ⟨64534, by decide⟩
    (prefixPartial 14 86113) = some ⟨14, 2, 0, 64534, 86113, 1233, 4096⟩ := by
  decide +kernel

theorem context_14_86113_64534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86113 ⟨64534, by decide⟩ :=
  accepted_of_selected 14 86113 ⟨64534, by decide⟩ ⟨14, 2, 0, 64534, 86113, 1233, 4096⟩
    (by decide) selected_cut_01939

theorem selected_cut_01940 : selected 7 ⟨64566, by decide⟩
    (prefixPartial 14 86114) = some ⟨14, 2, 0, 64566, 86114, 1489, 4096⟩ := by
  decide +kernel

theorem context_14_86114_64566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86114 ⟨64566, by decide⟩ :=
  accepted_of_selected 14 86114 ⟨64566, by decide⟩ ⟨14, 2, 0, 64566, 86114, 1489, 4096⟩
    (by decide) selected_cut_01940

theorem selected_cut_01941 : selected 7 ⟨64588, by decide⟩
    (prefixPartial 14 86115) = some ⟨14, 2, 0, 64588, 86115, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_86115_64588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86115 ⟨64588, by decide⟩ :=
  accepted_of_selected 14 86115 ⟨64588, by decide⟩ ⟨14, 2, 0, 64588, 86115, 1189, 4096⟩
    (by decide) selected_cut_01941

theorem unmarked_context_13_21528_64589 : frontier 8 ⟨64589, by decide⟩
    (prefixCache 13 21528) (prefixPartial 13 21528) = false := by
  decide +kernel

theorem node_context_13_21528_64589 : EJMOriginalGlobalDAGData.nodes 8 ⟨64589, by decide⟩ =
    .split (coordinate 13) (![⟨64503, by decide⟩,⟨64534, by decide⟩,⟨64566, by decide⟩,⟨64588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_21528_64589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21528 ⟨64589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 21528
    ⟨64589, by decide⟩ (by decide) (![⟨64503, by decide⟩,⟨64534, by decide⟩,⟨64566, by decide⟩,⟨64588, by decide⟩]) unmarked_context_13_21528_64589 node_context_13_21528_64589
  intro a
  fin_cases a
  · exact context_14_86112_64503
  · exact context_14_86113_64534
  · exact context_14_86114_64566
  · exact context_14_86115_64588

theorem selected_cut_01942 : selected 8 ⟨64641, by decide⟩
    (prefixPartial 13 21529) = some ⟨13, 2, 0, 64641, 21529, 3301, 16384⟩ := by
  decide +kernel

theorem context_13_21529_64641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21529 ⟨64641, by decide⟩ :=
  accepted_of_selected 13 21529 ⟨64641, by decide⟩ ⟨13, 2, 0, 64641, 21529, 3301, 16384⟩
    (by decide) selected_cut_01942

theorem selected_cut_01943 : selected 8 ⟨64681, by decide⟩
    (prefixPartial 13 21530) = some ⟨13, 2, 0, 64681, 21530, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_21530_64681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21530 ⟨64681, by decide⟩ :=
  accepted_of_selected 13 21530 ⟨64681, by decide⟩ ⟨13, 2, 0, 64681, 21530, 2665, 16384⟩
    (by decide) selected_cut_01943

theorem selected_cut_01944 : selected 8 ⟨64703, by decide⟩
    (prefixPartial 13 21531) = some ⟨13, 2, 0, 64703, 21531, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_21531_64703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21531 ⟨64703, by decide⟩ :=
  accepted_of_selected 13 21531 ⟨64703, by decide⟩ ⟨13, 2, 0, 64703, 21531, 1429, 16384⟩
    (by decide) selected_cut_01944

theorem unmarked_context_12_5382_64704 : frontier 9 ⟨64704, by decide⟩
    (prefixCache 12 5382) (prefixPartial 12 5382) = false := by
  decide +kernel

theorem node_context_12_5382_64704 : EJMOriginalGlobalDAGData.nodes 9 ⟨64704, by decide⟩ =
    .split (coordinate 12) (![⟨64589, by decide⟩,⟨64641, by decide⟩,⟨64681, by decide⟩,⟨64703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5382_64704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5382 ⟨64704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5382
    ⟨64704, by decide⟩ (by decide) (![⟨64589, by decide⟩,⟨64641, by decide⟩,⟨64681, by decide⟩,⟨64703, by decide⟩]) unmarked_context_12_5382_64704 node_context_12_5382_64704
  intro a
  fin_cases a
  · exact context_13_21528_64589
  · exact context_13_21529_64641
  · exact context_13_21530_64681
  · exact context_13_21531_64703

theorem selected_cut_01945 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5383) = some ⟨12, 1, 0, 893, 5383, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5383_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5383 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5383 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5383, 1, 65536⟩
    (by decide) selected_cut_01945

theorem unmarked_context_11_1345_64705 : frontier 10 ⟨64705, by decide⟩
    (prefixCache 11 1345) (prefixPartial 11 1345) = false := by
  decide +kernel

theorem node_context_11_1345_64705 : EJMOriginalGlobalDAGData.nodes 10 ⟨64705, by decide⟩ =
    .split (coordinate 11) (![⟨64247, by decide⟩,⟨64480, by decide⟩,⟨64704, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1345_64705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1345 ⟨64705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1345
    ⟨64705, by decide⟩ (by decide) (![⟨64247, by decide⟩,⟨64480, by decide⟩,⟨64704, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1345_64705 node_context_11_1345_64705
  intro a
  fin_cases a
  · exact context_12_5380_64247
  · exact context_12_5381_64480
  · exact context_12_5382_64704
  · exact context_12_5383_893

theorem selected_cut_01946 : selected 8 ⟨64790, by decide⟩
    (prefixPartial 13 21536) = some ⟨13, 2, 0, 64790, 21536, 3637, 16384⟩ := by
  decide +kernel

theorem context_13_21536_64790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21536 ⟨64790, by decide⟩ :=
  accepted_of_selected 13 21536 ⟨64790, by decide⟩ ⟨13, 2, 0, 64790, 21536, 3637, 16384⟩
    (by decide) selected_cut_01946

theorem selected_cut_01947 : selected 8 ⟨64878, by decide⟩
    (prefixPartial 13 21537) = some ⟨13, 2, 0, 64878, 21537, 3625, 16384⟩ := by
  decide +kernel

theorem context_13_21537_64878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21537 ⟨64878, by decide⟩ :=
  accepted_of_selected 13 21537 ⟨64878, by decide⟩ ⟨13, 2, 0, 64878, 21537, 3625, 16384⟩
    (by decide) selected_cut_01947

theorem selected_cut_01948 : selected 8 ⟨64959, by decide⟩
    (prefixPartial 13 21538) = some ⟨13, 2, 0, 64959, 21538, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_21538_64959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21538 ⟨64959, by decide⟩ :=
  accepted_of_selected 13 21538 ⟨64959, by decide⟩ ⟨13, 2, 0, 64959, 21538, 2757, 16384⟩
    (by decide) selected_cut_01948

theorem selected_cut_01949 : selected 8 ⟨65002, by decide⟩
    (prefixPartial 13 21539) = some ⟨13, 2, 0, 65002, 21539, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_21539_65002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21539 ⟨65002, by decide⟩ :=
  accepted_of_selected 13 21539 ⟨65002, by decide⟩ ⟨13, 2, 0, 65002, 21539, 1285, 16384⟩
    (by decide) selected_cut_01949

theorem unmarked_context_12_5384_65003 : frontier 9 ⟨65003, by decide⟩
    (prefixCache 12 5384) (prefixPartial 12 5384) = false := by
  decide +kernel

theorem node_context_12_5384_65003 : EJMOriginalGlobalDAGData.nodes 9 ⟨65003, by decide⟩ =
    .split (coordinate 12) (![⟨64790, by decide⟩,⟨64878, by decide⟩,⟨64959, by decide⟩,⟨65002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5384_65003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5384 ⟨65003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5384
    ⟨65003, by decide⟩ (by decide) (![⟨64790, by decide⟩,⟨64878, by decide⟩,⟨64959, by decide⟩,⟨65002, by decide⟩]) unmarked_context_12_5384_65003 node_context_12_5384_65003
  intro a
  fin_cases a
  · exact context_13_21536_64790
  · exact context_13_21537_64878
  · exact context_13_21538_64959
  · exact context_13_21539_65002

theorem selected_cut_01950 : selected 8 ⟨65088, by decide⟩
    (prefixPartial 13 21540) = some ⟨13, 2, 0, 65088, 21540, 3913, 16384⟩ := by
  decide +kernel

theorem context_13_21540_65088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21540 ⟨65088, by decide⟩ :=
  accepted_of_selected 13 21540 ⟨65088, by decide⟩ ⟨13, 2, 0, 65088, 21540, 3913, 16384⟩
    (by decide) selected_cut_01950

theorem selected_cut_01951 : selected 8 ⟨65156, by decide⟩
    (prefixPartial 13 21541) = some ⟨13, 2, 0, 65156, 21541, 3673, 16384⟩ := by
  decide +kernel

theorem context_13_21541_65156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21541 ⟨65156, by decide⟩ :=
  accepted_of_selected 13 21541 ⟨65156, by decide⟩ ⟨13, 2, 0, 65156, 21541, 3673, 16384⟩
    (by decide) selected_cut_01951

theorem selected_cut_01952 : selected 8 ⟨65192, by decide⟩
    (prefixPartial 13 21542) = some ⟨13, 2, 0, 65192, 21542, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_21542_65192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21542 ⟨65192, by decide⟩ :=
  accepted_of_selected 13 21542 ⟨65192, by decide⟩ ⟨13, 2, 0, 65192, 21542, 2697, 16384⟩
    (by decide) selected_cut_01952

theorem selected_cut_01953 : selected 8 ⟨65210, by decide⟩
    (prefixPartial 13 21543) = some ⟨13, 2, 0, 65210, 21543, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_21543_65210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21543 ⟨65210, by decide⟩ :=
  accepted_of_selected 13 21543 ⟨65210, by decide⟩ ⟨13, 2, 0, 65210, 21543, 1381, 16384⟩
    (by decide) selected_cut_01953

theorem unmarked_context_12_5385_65211 : frontier 9 ⟨65211, by decide⟩
    (prefixCache 12 5385) (prefixPartial 12 5385) = false := by
  decide +kernel

theorem node_context_12_5385_65211 : EJMOriginalGlobalDAGData.nodes 9 ⟨65211, by decide⟩ =
    .split (coordinate 12) (![⟨65088, by decide⟩,⟨65156, by decide⟩,⟨65192, by decide⟩,⟨65210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5385_65211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5385 ⟨65211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5385
    ⟨65211, by decide⟩ (by decide) (![⟨65088, by decide⟩,⟨65156, by decide⟩,⟨65192, by decide⟩,⟨65210, by decide⟩]) unmarked_context_12_5385_65211 node_context_12_5385_65211
  intro a
  fin_cases a
  · exact context_13_21540_65088
  · exact context_13_21541_65156
  · exact context_13_21542_65192
  · exact context_13_21543_65210

theorem selected_cut_01954 : selected 7 ⟨65228, by decide⟩
    (prefixPartial 14 86176) = some ⟨14, 2, 0, 65228, 86176, 629, 4096⟩ := by
  decide +kernel

theorem context_14_86176_65228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86176 ⟨65228, by decide⟩ :=
  accepted_of_selected 14 86176 ⟨65228, by decide⟩ ⟨14, 2, 0, 65228, 86176, 629, 4096⟩
    (by decide) selected_cut_01954

theorem selected_cut_01955 : selected 7 ⟨65253, by decide⟩
    (prefixPartial 14 86177) = some ⟨14, 2, 0, 65253, 86177, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_86177_65253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86177 ⟨65253, by decide⟩ :=
  accepted_of_selected 14 86177 ⟨65253, by decide⟩ ⟨14, 2, 0, 65253, 86177, 1157, 4096⟩
    (by decide) selected_cut_01955

theorem selected_cut_01956 : selected 7 ⟨65288, by decide⟩
    (prefixPartial 14 86178) = some ⟨14, 2, 0, 65288, 86178, 1409, 4096⟩ := by
  decide +kernel

theorem context_14_86178_65288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86178 ⟨65288, by decide⟩ :=
  accepted_of_selected 14 86178 ⟨65288, by decide⟩ ⟨14, 2, 0, 65288, 86178, 1409, 4096⟩
    (by decide) selected_cut_01956

theorem selected_cut_01957 : selected 7 ⟨65316, by decide⟩
    (prefixPartial 14 86179) = some ⟨14, 2, 0, 65316, 86179, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_86179_65316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86179 ⟨65316, by decide⟩ :=
  accepted_of_selected 14 86179 ⟨65316, by decide⟩ ⟨14, 2, 0, 65316, 86179, 1297, 4096⟩
    (by decide) selected_cut_01957

theorem unmarked_context_13_21544_65317 : frontier 8 ⟨65317, by decide⟩
    (prefixCache 13 21544) (prefixPartial 13 21544) = false := by
  decide +kernel

theorem node_context_13_21544_65317 : EJMOriginalGlobalDAGData.nodes 8 ⟨65317, by decide⟩ =
    .split (coordinate 13) (![⟨65228, by decide⟩,⟨65253, by decide⟩,⟨65288, by decide⟩,⟨65316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_21544_65317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21544 ⟨65317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 21544
    ⟨65317, by decide⟩ (by decide) (![⟨65228, by decide⟩,⟨65253, by decide⟩,⟨65288, by decide⟩,⟨65316, by decide⟩]) unmarked_context_13_21544_65317 node_context_13_21544_65317
  intro a
  fin_cases a
  · exact context_14_86176_65228
  · exact context_14_86177_65253
  · exact context_14_86178_65288
  · exact context_14_86179_65316

theorem selected_cut_01958 : selected 8 ⟨65369, by decide⟩
    (prefixPartial 13 21545) = some ⟨13, 2, 0, 65369, 21545, 3829, 16384⟩ := by
  decide +kernel

theorem context_13_21545_65369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21545 ⟨65369, by decide⟩ :=
  accepted_of_selected 13 21545 ⟨65369, by decide⟩ ⟨13, 2, 0, 65369, 21545, 3829, 16384⟩
    (by decide) selected_cut_01958

theorem selected_cut_01959 : selected 8 ⟨65405, by decide⟩
    (prefixPartial 13 21546) = some ⟨13, 2, 0, 65405, 21546, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_21546_65405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21546 ⟨65405, by decide⟩ :=
  accepted_of_selected 13 21546 ⟨65405, by decide⟩ ⟨13, 2, 0, 65405, 21546, 2773, 16384⟩
    (by decide) selected_cut_01959

theorem selected_cut_01960 : selected 8 ⟨65426, by decide⟩
    (prefixPartial 13 21547) = some ⟨13, 2, 0, 65426, 21547, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_21547_65426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21547 ⟨65426, by decide⟩ :=
  accepted_of_selected 13 21547 ⟨65426, by decide⟩ ⟨13, 2, 0, 65426, 21547, 1445, 16384⟩
    (by decide) selected_cut_01960

theorem unmarked_context_12_5386_65427 : frontier 9 ⟨65427, by decide⟩
    (prefixCache 12 5386) (prefixPartial 12 5386) = false := by
  decide +kernel

theorem node_context_12_5386_65427 : EJMOriginalGlobalDAGData.nodes 9 ⟨65427, by decide⟩ =
    .split (coordinate 12) (![⟨65317, by decide⟩,⟨65369, by decide⟩,⟨65405, by decide⟩,⟨65426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5386_65427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5386 ⟨65427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5386
    ⟨65427, by decide⟩ (by decide) (![⟨65317, by decide⟩,⟨65369, by decide⟩,⟨65405, by decide⟩,⟨65426, by decide⟩]) unmarked_context_12_5386_65427 node_context_12_5386_65427
  intro a
  fin_cases a
  · exact context_13_21544_65317
  · exact context_13_21545_65369
  · exact context_13_21546_65405
  · exact context_13_21547_65426

theorem selected_cut_01961 : selected 7 ⟨65440, by decide⟩
    (prefixPartial 14 86192) = some ⟨14, 2, 0, 65440, 86192, 317, 4096⟩ := by
  decide +kernel

theorem context_14_86192_65440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86192 ⟨65440, by decide⟩ :=
  accepted_of_selected 14 86192 ⟨65440, by decide⟩ ⟨14, 2, 0, 65440, 86192, 317, 4096⟩
    (by decide) selected_cut_01961

theorem selected_cut_01962 : selected 7 ⟨65479, by decide⟩
    (prefixPartial 14 86193) = some ⟨14, 2, 0, 65479, 86193, 1317, 4096⟩ := by
  decide +kernel

theorem context_14_86193_65479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86193 ⟨65479, by decide⟩ :=
  accepted_of_selected 14 86193 ⟨65479, by decide⟩ ⟨14, 2, 0, 65479, 86193, 1317, 4096⟩
    (by decide) selected_cut_01962

theorem selected_cut_01963 : selected 7 ⟨65510, by decide⟩
    (prefixPartial 14 86194) = some ⟨14, 2, 0, 65510, 86194, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_86194_65510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86194 ⟨65510, by decide⟩ :=
  accepted_of_selected 14 86194 ⟨65510, by decide⟩ ⟨14, 2, 0, 65510, 86194, 1209, 4096⟩
    (by decide) selected_cut_01963

theorem selected_cut_01964 : selected 7 ⟨65544, by decide⟩
    (prefixPartial 14 86195) = some ⟨14, 2, 0, 65544, 86195, 1381, 4096⟩ := by
  decide +kernel

theorem context_14_86195_65544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 86195 ⟨65544, by decide⟩ :=
  accepted_of_selected 14 86195 ⟨65544, by decide⟩ ⟨14, 2, 0, 65544, 86195, 1381, 4096⟩
    (by decide) selected_cut_01964

theorem unmarked_context_13_21548_65545 : frontier 8 ⟨65545, by decide⟩
    (prefixCache 13 21548) (prefixPartial 13 21548) = false := by
  decide +kernel

theorem node_context_13_21548_65545 : EJMOriginalGlobalDAGData.nodes 8 ⟨65545, by decide⟩ =
    .split (coordinate 13) (![⟨65440, by decide⟩,⟨65479, by decide⟩,⟨65510, by decide⟩,⟨65544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_21548_65545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21548 ⟨65545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 21548
    ⟨65545, by decide⟩ (by decide) (![⟨65440, by decide⟩,⟨65479, by decide⟩,⟨65510, by decide⟩,⟨65544, by decide⟩]) unmarked_context_13_21548_65545 node_context_13_21548_65545
  intro a
  fin_cases a
  · exact context_14_86192_65440
  · exact context_14_86193_65479
  · exact context_14_86194_65510
  · exact context_14_86195_65544

theorem selected_cut_01965 : selected 8 ⟨65604, by decide⟩
    (prefixPartial 13 21549) = some ⟨13, 2, 0, 65604, 21549, 4037, 16384⟩ := by
  decide +kernel

theorem context_13_21549_65604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21549 ⟨65604, by decide⟩ :=
  accepted_of_selected 13 21549 ⟨65604, by decide⟩ ⟨13, 2, 0, 65604, 21549, 4037, 16384⟩
    (by decide) selected_cut_01965

theorem selected_cut_01966 : selected 8 ⟨65661, by decide⟩
    (prefixPartial 13 21550) = some ⟨13, 2, 0, 65661, 21550, 3057, 16384⟩ := by
  decide +kernel

theorem context_13_21550_65661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21550 ⟨65661, by decide⟩ :=
  accepted_of_selected 13 21550 ⟨65661, by decide⟩ ⟨13, 2, 0, 65661, 21550, 3057, 16384⟩
    (by decide) selected_cut_01966

theorem selected_cut_01967 : selected 8 ⟨65683, by decide⟩
    (prefixPartial 13 21551) = some ⟨13, 2, 0, 65683, 21551, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_21551_65683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21551 ⟨65683, by decide⟩ :=
  accepted_of_selected 13 21551 ⟨65683, by decide⟩ ⟨13, 2, 0, 65683, 21551, 1445, 16384⟩
    (by decide) selected_cut_01967

theorem unmarked_context_12_5387_65684 : frontier 9 ⟨65684, by decide⟩
    (prefixCache 12 5387) (prefixPartial 12 5387) = false := by
  decide +kernel

theorem node_context_12_5387_65684 : EJMOriginalGlobalDAGData.nodes 9 ⟨65684, by decide⟩ =
    .split (coordinate 12) (![⟨65545, by decide⟩,⟨65604, by decide⟩,⟨65661, by decide⟩,⟨65683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5387_65684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5387 ⟨65684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5387
    ⟨65684, by decide⟩ (by decide) (![⟨65545, by decide⟩,⟨65604, by decide⟩,⟨65661, by decide⟩,⟨65683, by decide⟩]) unmarked_context_12_5387_65684 node_context_12_5387_65684
  intro a
  fin_cases a
  · exact context_13_21548_65545
  · exact context_13_21549_65604
  · exact context_13_21550_65661
  · exact context_13_21551_65683

theorem unmarked_context_11_1346_65685 : frontier 10 ⟨65685, by decide⟩
    (prefixCache 11 1346) (prefixPartial 11 1346) = false := by
  decide +kernel

theorem node_context_11_1346_65685 : EJMOriginalGlobalDAGData.nodes 10 ⟨65685, by decide⟩ =
    .split (coordinate 11) (![⟨65003, by decide⟩,⟨65211, by decide⟩,⟨65427, by decide⟩,⟨65684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1346_65685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1346 ⟨65685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1346
    ⟨65685, by decide⟩ (by decide) (![⟨65003, by decide⟩,⟨65211, by decide⟩,⟨65427, by decide⟩,⟨65684, by decide⟩]) unmarked_context_11_1346_65685 node_context_11_1346_65685
  intro a
  fin_cases a
  · exact context_12_5384_65003
  · exact context_12_5385_65211
  · exact context_12_5386_65427
  · exact context_12_5387_65684

theorem selected_cut_01968 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1347) = some ⟨11, 1, 0, 1736, 1347, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1347_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1347 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1347 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1347, 1, 262144⟩
    (by decide) selected_cut_01968

theorem unmarked_context_10_336_65686 : frontier 11 ⟨65686, by decide⟩
    (prefixCache 10 336) (prefixPartial 10 336) = false := by
  decide +kernel

theorem node_context_10_336_65686 : EJMOriginalGlobalDAGData.nodes 11 ⟨65686, by decide⟩ =
    .split (coordinate 10) (![⟨64066, by decide⟩,⟨64705, by decide⟩,⟨65685, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_336_65686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 336 ⟨65686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 336
    ⟨65686, by decide⟩ (by decide) (![⟨64066, by decide⟩,⟨64705, by decide⟩,⟨65685, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_336_65686 node_context_10_336_65686
  intro a
  fin_cases a
  · exact context_11_1344_64066
  · exact context_11_1345_64705
  · exact context_11_1346_65685
  · exact context_11_1347_1736

theorem selected_cut_01969 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5392) = some ⟨12, 1, 0, 1738, 5392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5392_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5392 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5392 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5392, 1, 65536⟩
    (by decide) selected_cut_01969

theorem selected_cut_01970 : selected 9 ⟨65749, by decide⟩
    (prefixPartial 12 5393) = some ⟨12, 2, 0, 65749, 5393, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_5393_65749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5393 ⟨65749, by decide⟩ :=
  accepted_of_selected 12 5393 ⟨65749, by decide⟩ ⟨12, 2, 0, 65749, 5393, 2189, 65536⟩
    (by decide) selected_cut_01970

theorem selected_cut_01971 : selected 8 ⟨65795, by decide⟩
    (prefixPartial 13 21576) = some ⟨13, 2, 0, 65795, 21576, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_21576_65795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21576 ⟨65795, by decide⟩ :=
  accepted_of_selected 13 21576 ⟨65795, by decide⟩ ⟨13, 2, 0, 65795, 21576, 2149, 16384⟩
    (by decide) selected_cut_01971

theorem selected_cut_01972 : selected 8 ⟨65827, by decide⟩
    (prefixPartial 13 21577) = some ⟨13, 2, 0, 65827, 21577, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_21577_65827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21577 ⟨65827, by decide⟩ :=
  accepted_of_selected 13 21577 ⟨65827, by decide⟩ ⟨13, 2, 0, 65827, 21577, 2181, 16384⟩
    (by decide) selected_cut_01972

theorem selected_cut_01973 : selected 8 ⟨65852, by decide⟩
    (prefixPartial 13 21578) = some ⟨13, 2, 0, 65852, 21578, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_21578_65852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21578 ⟨65852, by decide⟩ :=
  accepted_of_selected 13 21578 ⟨65852, by decide⟩ ⟨13, 2, 0, 65852, 21578, 2105, 16384⟩
    (by decide) selected_cut_01973

theorem selected_cut_01974 : selected 8 ⟨65866, by decide⟩
    (prefixPartial 13 21579) = some ⟨13, 2, 0, 65866, 21579, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_21579_65866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21579 ⟨65866, by decide⟩ :=
  accepted_of_selected 13 21579 ⟨65866, by decide⟩ ⟨13, 2, 0, 65866, 21579, 1101, 16384⟩
    (by decide) selected_cut_01974

theorem unmarked_context_12_5394_65867 : frontier 9 ⟨65867, by decide⟩
    (prefixCache 12 5394) (prefixPartial 12 5394) = false := by
  decide +kernel

theorem node_context_12_5394_65867 : EJMOriginalGlobalDAGData.nodes 9 ⟨65867, by decide⟩ =
    .split (coordinate 12) (![⟨65795, by decide⟩,⟨65827, by decide⟩,⟨65852, by decide⟩,⟨65866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5394_65867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5394 ⟨65867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5394
    ⟨65867, by decide⟩ (by decide) (![⟨65795, by decide⟩,⟨65827, by decide⟩,⟨65852, by decide⟩,⟨65866, by decide⟩]) unmarked_context_12_5394_65867 node_context_12_5394_65867
  intro a
  fin_cases a
  · exact context_13_21576_65795
  · exact context_13_21577_65827
  · exact context_13_21578_65852
  · exact context_13_21579_65866

theorem selected_cut_01975 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5395) = some ⟨12, 1, 0, 893, 5395, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5395_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5395 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5395 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5395, 1, 65536⟩
    (by decide) selected_cut_01975

theorem unmarked_context_11_1348_65868 : frontier 10 ⟨65868, by decide⟩
    (prefixCache 11 1348) (prefixPartial 11 1348) = false := by
  decide +kernel

theorem node_context_11_1348_65868 : EJMOriginalGlobalDAGData.nodes 10 ⟨65868, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨65749, by decide⟩,⟨65867, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1348_65868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1348 ⟨65868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1348
    ⟨65868, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨65749, by decide⟩,⟨65867, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1348_65868 node_context_11_1348_65868
  intro a
  fin_cases a
  · exact context_12_5392_1738
  · exact context_12_5393_65749
  · exact context_12_5394_65867
  · exact context_12_5395_893

theorem selected_cut_01976 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5396) = some ⟨12, 1, 0, 1738, 5396, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5396_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5396 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5396 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5396, 1, 65536⟩
    (by decide) selected_cut_01976

theorem selected_cut_01977 : selected 9 ⟨66114, by decide⟩
    (prefixPartial 12 5397) = some ⟨12, 2, 0, 66114, 5397, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_5397_66114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5397 ⟨66114, by decide⟩ :=
  accepted_of_selected 12 5397 ⟨66114, by decide⟩ ⟨12, 2, 0, 66114, 5397, 3037, 65536⟩
    (by decide) selected_cut_01977

theorem selected_cut_01978 : selected 8 ⟨66175, by decide⟩
    (prefixPartial 13 21592) = some ⟨13, 2, 0, 66175, 21592, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_21592_66175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21592 ⟨66175, by decide⟩ :=
  accepted_of_selected 13 21592 ⟨66175, by decide⟩ ⟨13, 2, 0, 66175, 21592, 3073, 16384⟩
    (by decide) selected_cut_01978

theorem selected_cut_01979 : selected 8 ⟨66227, by decide⟩
    (prefixPartial 13 21593) = some ⟨13, 2, 0, 66227, 21593, 4085, 16384⟩ := by
  decide +kernel

theorem context_13_21593_66227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21593 ⟨66227, by decide⟩ :=
  accepted_of_selected 13 21593 ⟨66227, by decide⟩ ⟨13, 2, 0, 66227, 21593, 4085, 16384⟩
    (by decide) selected_cut_01979

theorem selected_cut_01980 : selected 8 ⟨66266, by decide⟩
    (prefixPartial 13 21594) = some ⟨13, 2, 0, 66266, 21594, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_21594_66266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21594 ⟨66266, by decide⟩ :=
  accepted_of_selected 13 21594 ⟨66266, by decide⟩ ⟨13, 2, 0, 66266, 21594, 2921, 16384⟩
    (by decide) selected_cut_01980

theorem selected_cut_01981 : selected 8 ⟨66293, by decide⟩
    (prefixPartial 13 21595) = some ⟨13, 2, 0, 66293, 21595, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_21595_66293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21595 ⟨66293, by decide⟩ :=
  accepted_of_selected 13 21595 ⟨66293, by decide⟩ ⟨13, 2, 0, 66293, 21595, 1541, 16384⟩
    (by decide) selected_cut_01981

theorem unmarked_context_12_5398_66294 : frontier 9 ⟨66294, by decide⟩
    (prefixCache 12 5398) (prefixPartial 12 5398) = false := by
  decide +kernel

theorem node_context_12_5398_66294 : EJMOriginalGlobalDAGData.nodes 9 ⟨66294, by decide⟩ =
    .split (coordinate 12) (![⟨66175, by decide⟩,⟨66227, by decide⟩,⟨66266, by decide⟩,⟨66293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5398_66294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5398 ⟨66294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5398
    ⟨66294, by decide⟩ (by decide) (![⟨66175, by decide⟩,⟨66227, by decide⟩,⟨66266, by decide⟩,⟨66293, by decide⟩]) unmarked_context_12_5398_66294 node_context_12_5398_66294
  intro a
  fin_cases a
  · exact context_13_21592_66175
  · exact context_13_21593_66227
  · exact context_13_21594_66266
  · exact context_13_21595_66293

theorem selected_cut_01982 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5399) = some ⟨12, 1, 0, 893, 5399, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5399_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5399 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5399 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5399, 1, 65536⟩
    (by decide) selected_cut_01982

theorem unmarked_context_11_1349_66295 : frontier 10 ⟨66295, by decide⟩
    (prefixCache 11 1349) (prefixPartial 11 1349) = false := by
  decide +kernel

theorem node_context_11_1349_66295 : EJMOriginalGlobalDAGData.nodes 10 ⟨66295, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨66114, by decide⟩,⟨66294, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1349_66295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1349 ⟨66295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1349
    ⟨66295, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨66114, by decide⟩,⟨66294, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1349_66295 node_context_11_1349_66295
  intro a
  fin_cases a
  · exact context_12_5396_1738
  · exact context_12_5397_66114
  · exact context_12_5398_66294
  · exact context_12_5399_893

theorem selected_cut_01983 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5400) = some ⟨12, 1, 0, 1738, 5400, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5400_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5400 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5400 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5400, 1, 65536⟩
    (by decide) selected_cut_01983

theorem selected_cut_01984 : selected 8 ⟨66328, by decide⟩
    (prefixPartial 13 21604) = some ⟨13, 2, 0, 66328, 21604, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_21604_66328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21604 ⟨66328, by decide⟩ :=
  accepted_of_selected 13 21604 ⟨66328, by decide⟩ ⟨13, 2, 0, 66328, 21604, 1133, 16384⟩
    (by decide) selected_cut_01984

theorem selected_cut_01985 : selected 8 ⟨66354, by decide⟩
    (prefixPartial 13 21605) = some ⟨13, 2, 0, 66354, 21605, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_21605_66354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21605 ⟨66354, by decide⟩ :=
  accepted_of_selected 13 21605 ⟨66354, by decide⟩ ⟨13, 2, 0, 66354, 21605, 1169, 16384⟩
    (by decide) selected_cut_01985

theorem selected_cut_01986 : selected 8 ⟨66377, by decide⟩
    (prefixPartial 13 21606) = some ⟨13, 2, 0, 66377, 21606, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_21606_66377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21606 ⟨66377, by decide⟩ :=
  accepted_of_selected 13 21606 ⟨66377, by decide⟩ ⟨13, 2, 0, 66377, 21606, 1237, 16384⟩
    (by decide) selected_cut_01986

theorem selected_cut_01987 : selected 8 ⟨66387, by decide⟩
    (prefixPartial 13 21607) = some ⟨13, 2, 0, 66387, 21607, 805, 16384⟩ := by
  decide +kernel

theorem context_13_21607_66387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21607 ⟨66387, by decide⟩ :=
  accepted_of_selected 13 21607 ⟨66387, by decide⟩ ⟨13, 2, 0, 66387, 21607, 805, 16384⟩
    (by decide) selected_cut_01987

theorem unmarked_context_12_5401_66388 : frontier 9 ⟨66388, by decide⟩
    (prefixCache 12 5401) (prefixPartial 12 5401) = false := by
  decide +kernel

theorem node_context_12_5401_66388 : EJMOriginalGlobalDAGData.nodes 9 ⟨66388, by decide⟩ =
    .split (coordinate 12) (![⟨66328, by decide⟩,⟨66354, by decide⟩,⟨66377, by decide⟩,⟨66387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5401_66388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5401 ⟨66388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5401
    ⟨66388, by decide⟩ (by decide) (![⟨66328, by decide⟩,⟨66354, by decide⟩,⟨66377, by decide⟩,⟨66387, by decide⟩]) unmarked_context_12_5401_66388 node_context_12_5401_66388
  intro a
  fin_cases a
  · exact context_13_21604_66328
  · exact context_13_21605_66354
  · exact context_13_21606_66377
  · exact context_13_21607_66387

theorem selected_cut_01988 : selected 8 ⟨66429, by decide⟩
    (prefixPartial 13 21608) = some ⟨13, 2, 0, 66429, 21608, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_21608_66429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21608 ⟨66429, by decide⟩ :=
  accepted_of_selected 13 21608 ⟨66429, by decide⟩ ⟨13, 2, 0, 66429, 21608, 1641, 16384⟩
    (by decide) selected_cut_01988

theorem selected_cut_01989 : selected 8 ⟨66461, by decide⟩
    (prefixPartial 13 21609) = some ⟨13, 2, 0, 66461, 21609, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_21609_66461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21609 ⟨66461, by decide⟩ :=
  accepted_of_selected 13 21609 ⟨66461, by decide⟩ ⟨13, 2, 0, 66461, 21609, 2541, 16384⟩
    (by decide) selected_cut_01989

theorem selected_cut_01990 : selected 8 ⟨66484, by decide⟩
    (prefixPartial 13 21610) = some ⟨13, 2, 0, 66484, 21610, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_21610_66484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21610 ⟨66484, by decide⟩ :=
  accepted_of_selected 13 21610 ⟨66484, by decide⟩ ⟨13, 2, 0, 66484, 21610, 1969, 16384⟩
    (by decide) selected_cut_01990

theorem selected_cut_01991 : selected 8 ⟨66498, by decide⟩
    (prefixPartial 13 21611) = some ⟨13, 2, 0, 66498, 21611, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_21611_66498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21611 ⟨66498, by decide⟩ :=
  accepted_of_selected 13 21611 ⟨66498, by decide⟩ ⟨13, 2, 0, 66498, 21611, 1185, 16384⟩
    (by decide) selected_cut_01991

theorem unmarked_context_12_5402_66499 : frontier 9 ⟨66499, by decide⟩
    (prefixCache 12 5402) (prefixPartial 12 5402) = false := by
  decide +kernel

theorem node_context_12_5402_66499 : EJMOriginalGlobalDAGData.nodes 9 ⟨66499, by decide⟩ =
    .split (coordinate 12) (![⟨66429, by decide⟩,⟨66461, by decide⟩,⟨66484, by decide⟩,⟨66498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5402_66499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5402 ⟨66499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5402
    ⟨66499, by decide⟩ (by decide) (![⟨66429, by decide⟩,⟨66461, by decide⟩,⟨66484, by decide⟩,⟨66498, by decide⟩]) unmarked_context_12_5402_66499 node_context_12_5402_66499
  intro a
  fin_cases a
  · exact context_13_21608_66429
  · exact context_13_21609_66461
  · exact context_13_21610_66484
  · exact context_13_21611_66498

theorem selected_cut_01992 : selected 8 ⟨66535, by decide⟩
    (prefixPartial 13 21612) = some ⟨13, 2, 0, 66535, 21612, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_21612_66535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21612 ⟨66535, by decide⟩ :=
  accepted_of_selected 13 21612 ⟨66535, by decide⟩ ⟨13, 2, 0, 66535, 21612, 1513, 16384⟩
    (by decide) selected_cut_01992

theorem selected_cut_01993 : selected 8 ⟨66569, by decide⟩
    (prefixPartial 13 21613) = some ⟨13, 2, 0, 66569, 21613, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_21613_66569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21613 ⟨66569, by decide⟩ :=
  accepted_of_selected 13 21613 ⟨66569, by decide⟩ ⟨13, 2, 0, 66569, 21613, 2541, 16384⟩
    (by decide) selected_cut_01993

theorem selected_cut_01994 : selected 8 ⟨66598, by decide⟩
    (prefixPartial 13 21614) = some ⟨13, 2, 0, 66598, 21614, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_21614_66598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21614 ⟨66598, by decide⟩ :=
  accepted_of_selected 13 21614 ⟨66598, by decide⟩ ⟨13, 2, 0, 66598, 21614, 2113, 16384⟩
    (by decide) selected_cut_01994

theorem selected_cut_01995 : selected 8 ⟨66611, by decide⟩
    (prefixPartial 13 21615) = some ⟨13, 2, 0, 66611, 21615, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_21615_66611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21615 ⟨66611, by decide⟩ :=
  accepted_of_selected 13 21615 ⟨66611, by decide⟩ ⟨13, 2, 0, 66611, 21615, 1213, 16384⟩
    (by decide) selected_cut_01995

theorem unmarked_context_12_5403_66612 : frontier 9 ⟨66612, by decide⟩
    (prefixCache 12 5403) (prefixPartial 12 5403) = false := by
  decide +kernel

theorem node_context_12_5403_66612 : EJMOriginalGlobalDAGData.nodes 9 ⟨66612, by decide⟩ =
    .split (coordinate 12) (![⟨66535, by decide⟩,⟨66569, by decide⟩,⟨66598, by decide⟩,⟨66611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5403_66612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5403 ⟨66612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5403
    ⟨66612, by decide⟩ (by decide) (![⟨66535, by decide⟩,⟨66569, by decide⟩,⟨66598, by decide⟩,⟨66611, by decide⟩]) unmarked_context_12_5403_66612 node_context_12_5403_66612
  intro a
  fin_cases a
  · exact context_13_21612_66535
  · exact context_13_21613_66569
  · exact context_13_21614_66598
  · exact context_13_21615_66611

theorem unmarked_context_11_1350_66613 : frontier 10 ⟨66613, by decide⟩
    (prefixCache 11 1350) (prefixPartial 11 1350) = false := by
  decide +kernel

theorem node_context_11_1350_66613 : EJMOriginalGlobalDAGData.nodes 10 ⟨66613, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨66388, by decide⟩,⟨66499, by decide⟩,⟨66612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1350_66613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1350 ⟨66613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1350
    ⟨66613, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨66388, by decide⟩,⟨66499, by decide⟩,⟨66612, by decide⟩]) unmarked_context_11_1350_66613 node_context_11_1350_66613
  intro a
  fin_cases a
  · exact context_12_5400_1738
  · exact context_12_5401_66388
  · exact context_12_5402_66499
  · exact context_12_5403_66612

theorem selected_cut_01996 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1351) = some ⟨11, 1, 0, 1736, 1351, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1351_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1351 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1351 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1351, 1, 262144⟩
    (by decide) selected_cut_01996

theorem unmarked_context_10_337_66614 : frontier 11 ⟨66614, by decide⟩
    (prefixCache 10 337) (prefixPartial 10 337) = false := by
  decide +kernel

theorem node_context_10_337_66614 : EJMOriginalGlobalDAGData.nodes 11 ⟨66614, by decide⟩ =
    .split (coordinate 10) (![⟨65868, by decide⟩,⟨66295, by decide⟩,⟨66613, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_337_66614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 337 ⟨66614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 337
    ⟨66614, by decide⟩ (by decide) (![⟨65868, by decide⟩,⟨66295, by decide⟩,⟨66613, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_337_66614 node_context_10_337_66614
  intro a
  fin_cases a
  · exact context_11_1348_65868
  · exact context_11_1349_66295
  · exact context_11_1350_66613
  · exact context_11_1351_1736

theorem selected_cut_01997 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5408) = some ⟨12, 1, 0, 1738, 5408, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5408_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5408 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5408 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5408, 1, 65536⟩
    (by decide) selected_cut_01997

theorem selected_cut_01998 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5409) = some ⟨12, 1, 0, 1738, 5409, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5409_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5409 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5409 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5409, 1, 65536⟩
    (by decide) selected_cut_01998

theorem selected_cut_01999 : selected 8 ⟨66648, by decide⟩
    (prefixPartial 13 21640) = some ⟨13, 2, 0, 66648, 21640, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_21640_66648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21640 ⟨66648, by decide⟩ :=
  accepted_of_selected 13 21640 ⟨66648, by decide⟩ ⟨13, 2, 0, 66648, 21640, 1185, 16384⟩
    (by decide) selected_cut_01999

theorem selected_cut_02000 : selected 8 ⟨66692, by decide⟩
    (prefixPartial 13 21641) = some ⟨13, 2, 0, 66692, 21641, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_21641_66692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21641 ⟨66692, by decide⟩ :=
  accepted_of_selected 13 21641 ⟨66692, by decide⟩ ⟨13, 2, 0, 66692, 21641, 1917, 16384⟩
    (by decide) selected_cut_02000

theorem selected_cut_02001 : selected 8 ⟨66736, by decide⟩
    (prefixPartial 13 21642) = some ⟨13, 2, 0, 66736, 21642, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_21642_66736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21642 ⟨66736, by decide⟩ :=
  accepted_of_selected 13 21642 ⟨66736, by decide⟩ ⟨13, 2, 0, 66736, 21642, 1657, 16384⟩
    (by decide) selected_cut_02001

theorem selected_cut_02002 : selected 8 ⟨66759, by decide⟩
    (prefixPartial 13 21643) = some ⟨13, 2, 0, 66759, 21643, 949, 16384⟩ := by
  decide +kernel

theorem context_13_21643_66759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21643 ⟨66759, by decide⟩ :=
  accepted_of_selected 13 21643 ⟨66759, by decide⟩ ⟨13, 2, 0, 66759, 21643, 949, 16384⟩
    (by decide) selected_cut_02002

theorem unmarked_context_12_5410_66760 : frontier 9 ⟨66760, by decide⟩
    (prefixCache 12 5410) (prefixPartial 12 5410) = false := by
  decide +kernel

theorem node_context_12_5410_66760 : EJMOriginalGlobalDAGData.nodes 9 ⟨66760, by decide⟩ =
    .split (coordinate 12) (![⟨66648, by decide⟩,⟨66692, by decide⟩,⟨66736, by decide⟩,⟨66759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5410_66760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5410 ⟨66760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5410
    ⟨66760, by decide⟩ (by decide) (![⟨66648, by decide⟩,⟨66692, by decide⟩,⟨66736, by decide⟩,⟨66759, by decide⟩]) unmarked_context_12_5410_66760 node_context_12_5410_66760
  intro a
  fin_cases a
  · exact context_13_21640_66648
  · exact context_13_21641_66692
  · exact context_13_21642_66736
  · exact context_13_21643_66759

theorem selected_cut_02003 : selected 8 ⟨66789, by decide⟩
    (prefixPartial 13 21644) = some ⟨13, 2, 0, 66789, 21644, 725, 16384⟩ := by
  decide +kernel

theorem context_13_21644_66789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21644 ⟨66789, by decide⟩ :=
  accepted_of_selected 13 21644 ⟨66789, by decide⟩ ⟨13, 2, 0, 66789, 21644, 725, 16384⟩
    (by decide) selected_cut_02003

theorem selected_cut_02004 : selected 8 ⟨66822, by decide⟩
    (prefixPartial 13 21645) = some ⟨13, 2, 0, 66822, 21645, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_21645_66822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21645 ⟨66822, by decide⟩ :=
  accepted_of_selected 13 21645 ⟨66822, by decide⟩ ⟨13, 2, 0, 66822, 21645, 1541, 16384⟩
    (by decide) selected_cut_02004

theorem selected_cut_02005 : selected 8 ⟨66880, by decide⟩
    (prefixPartial 13 21646) = some ⟨13, 2, 0, 66880, 21646, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_21646_66880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21646 ⟨66880, by decide⟩ :=
  accepted_of_selected 13 21646 ⟨66880, by decide⟩ ⟨13, 2, 0, 66880, 21646, 2569, 16384⟩
    (by decide) selected_cut_02005

theorem selected_cut_02006 : selected 8 ⟨4592, by decide⟩
    (prefixPartial 13 21647) = some ⟨13, 1, 0, 4592, 21647, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21647_4592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21647 ⟨4592, by decide⟩ :=
  accepted_of_selected 13 21647 ⟨4592, by decide⟩ ⟨13, 1, 0, 4592, 21647, 1, 16384⟩
    (by decide) selected_cut_02006

theorem unmarked_context_12_5411_66881 : frontier 9 ⟨66881, by decide⟩
    (prefixCache 12 5411) (prefixPartial 12 5411) = false := by
  decide +kernel

theorem node_context_12_5411_66881 : EJMOriginalGlobalDAGData.nodes 9 ⟨66881, by decide⟩ =
    .split (coordinate 12) (![⟨66789, by decide⟩,⟨66822, by decide⟩,⟨66880, by decide⟩,⟨4592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5411_66881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5411 ⟨66881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5411
    ⟨66881, by decide⟩ (by decide) (![⟨66789, by decide⟩,⟨66822, by decide⟩,⟨66880, by decide⟩,⟨4592, by decide⟩]) unmarked_context_12_5411_66881 node_context_12_5411_66881
  intro a
  fin_cases a
  · exact context_13_21644_66789
  · exact context_13_21645_66822
  · exact context_13_21646_66880
  · exact context_13_21647_4592

theorem unmarked_context_11_1352_66882 : frontier 10 ⟨66882, by decide⟩
    (prefixCache 11 1352) (prefixPartial 11 1352) = false := by
  decide +kernel

theorem node_context_11_1352_66882 : EJMOriginalGlobalDAGData.nodes 10 ⟨66882, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨66760, by decide⟩,⟨66881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1352_66882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1352 ⟨66882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1352
    ⟨66882, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨66760, by decide⟩,⟨66881, by decide⟩]) unmarked_context_11_1352_66882 node_context_11_1352_66882
  intro a
  fin_cases a
  · exact context_12_5408_1738
  · exact context_12_5409_1738
  · exact context_12_5410_66760
  · exact context_12_5411_66881

theorem selected_cut_02007 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5412) = some ⟨12, 1, 0, 1738, 5412, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5412_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5412 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5412 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5412, 1, 65536⟩
    (by decide) selected_cut_02007

theorem selected_cut_02008 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5413) = some ⟨12, 1, 0, 1738, 5413, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5413_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5413 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5413 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5413, 1, 65536⟩
    (by decide) selected_cut_02008

theorem selected_cut_02009 : selected 8 ⟨66912, by decide⟩
    (prefixPartial 13 21656) = some ⟨13, 2, 0, 66912, 21656, 857, 16384⟩ := by
  decide +kernel

theorem context_13_21656_66912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21656 ⟨66912, by decide⟩ :=
  accepted_of_selected 13 21656 ⟨66912, by decide⟩ ⟨13, 2, 0, 66912, 21656, 857, 16384⟩
    (by decide) selected_cut_02009

theorem selected_cut_02010 : selected 8 ⟨66944, by decide⟩
    (prefixPartial 13 21657) = some ⟨13, 2, 0, 66944, 21657, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_21657_66944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21657 ⟨66944, by decide⟩ :=
  accepted_of_selected 13 21657 ⟨66944, by decide⟩ ⟨13, 2, 0, 66944, 21657, 1677, 16384⟩
    (by decide) selected_cut_02010

theorem selected_cut_02011 : selected 8 ⟨66970, by decide⟩
    (prefixPartial 13 21658) = some ⟨13, 2, 0, 66970, 21658, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_21658_66970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21658 ⟨66970, by decide⟩ :=
  accepted_of_selected 13 21658 ⟨66970, by decide⟩ ⟨13, 2, 0, 66970, 21658, 1433, 16384⟩
    (by decide) selected_cut_02011

theorem selected_cut_02012 : selected 8 ⟨66987, by decide⟩
    (prefixPartial 13 21659) = some ⟨13, 2, 0, 66987, 21659, 865, 16384⟩ := by
  decide +kernel

theorem context_13_21659_66987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21659 ⟨66987, by decide⟩ :=
  accepted_of_selected 13 21659 ⟨66987, by decide⟩ ⟨13, 2, 0, 66987, 21659, 865, 16384⟩
    (by decide) selected_cut_02012

theorem unmarked_context_12_5414_66988 : frontier 9 ⟨66988, by decide⟩
    (prefixCache 12 5414) (prefixPartial 12 5414) = false := by
  decide +kernel

theorem node_context_12_5414_66988 : EJMOriginalGlobalDAGData.nodes 9 ⟨66988, by decide⟩ =
    .split (coordinate 12) (![⟨66912, by decide⟩,⟨66944, by decide⟩,⟨66970, by decide⟩,⟨66987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5414_66988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5414 ⟨66988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5414
    ⟨66988, by decide⟩ (by decide) (![⟨66912, by decide⟩,⟨66944, by decide⟩,⟨66970, by decide⟩,⟨66987, by decide⟩]) unmarked_context_12_5414_66988 node_context_12_5414_66988
  intro a
  fin_cases a
  · exact context_13_21656_66912
  · exact context_13_21657_66944
  · exact context_13_21658_66970
  · exact context_13_21659_66987

theorem selected_cut_02013 : selected 9 ⟨67091, by decide⟩
    (prefixPartial 12 5415) = some ⟨12, 2, 0, 67091, 5415, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_5415_67091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5415 ⟨67091, by decide⟩ :=
  accepted_of_selected 12 5415 ⟨67091, by decide⟩ ⟨12, 2, 0, 67091, 5415, 4041, 65536⟩
    (by decide) selected_cut_02013

theorem unmarked_context_11_1353_67092 : frontier 10 ⟨67092, by decide⟩
    (prefixCache 11 1353) (prefixPartial 11 1353) = false := by
  decide +kernel

theorem node_context_11_1353_67092 : EJMOriginalGlobalDAGData.nodes 10 ⟨67092, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨66988, by decide⟩,⟨67091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1353_67092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1353 ⟨67092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1353
    ⟨67092, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨66988, by decide⟩,⟨67091, by decide⟩]) unmarked_context_11_1353_67092 node_context_11_1353_67092
  intro a
  fin_cases a
  · exact context_12_5412_1738
  · exact context_12_5413_1738
  · exact context_12_5414_66988
  · exact context_12_5415_67091

theorem selected_cut_02014 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5416) = some ⟨12, 1, 0, 1738, 5416, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5416_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5416 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5416 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5416, 1, 65536⟩
    (by decide) selected_cut_02014

theorem selected_cut_02015 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5417) = some ⟨12, 1, 0, 1738, 5417, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5417_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5417 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5417 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5417, 1, 65536⟩
    (by decide) selected_cut_02015

theorem selected_cut_02016 : selected 8 ⟨67116, by decide⟩
    (prefixPartial 13 21672) = some ⟨13, 2, 0, 67116, 21672, 613, 16384⟩ := by
  decide +kernel

theorem context_13_21672_67116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21672 ⟨67116, by decide⟩ :=
  accepted_of_selected 13 21672 ⟨67116, by decide⟩ ⟨13, 2, 0, 67116, 21672, 613, 16384⟩
    (by decide) selected_cut_02016

theorem selected_cut_02017 : selected 8 ⟨67144, by decide⟩
    (prefixPartial 13 21673) = some ⟨13, 2, 0, 67144, 21673, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_21673_67144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21673 ⟨67144, by decide⟩ :=
  accepted_of_selected 13 21673 ⟨67144, by decide⟩ ⟨13, 2, 0, 67144, 21673, 1793, 16384⟩
    (by decide) selected_cut_02017

theorem selected_cut_02018 : selected 8 ⟨67167, by decide⟩
    (prefixPartial 13 21674) = some ⟨13, 2, 0, 67167, 21674, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_21674_67167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21674 ⟨67167, by decide⟩ :=
  accepted_of_selected 13 21674 ⟨67167, by decide⟩ ⟨13, 2, 0, 67167, 21674, 1413, 16384⟩
    (by decide) selected_cut_02018

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
