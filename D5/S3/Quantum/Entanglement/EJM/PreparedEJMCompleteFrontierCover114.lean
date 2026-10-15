/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover113
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10947 : selected 8 ⟨294935, by decide⟩
    (prefixPartial 13 101526) = some ⟨13, 2, 0, 294935, 101526, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_101526_294935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101526 ⟨294935, by decide⟩ :=
  accepted_of_selected 13 101526 ⟨294935, by decide⟩ ⟨13, 2, 0, 294935, 101526, 1345, 16384⟩
    (by decide) selected_cut_10947

theorem selected_cut_10948 : selected 8 ⟨294941, by decide⟩
    (prefixPartial 13 101527) = some ⟨13, 2, 0, 294941, 101527, 681, 16384⟩ := by
  decide +kernel

theorem context_13_101527_294941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101527 ⟨294941, by decide⟩ :=
  accepted_of_selected 13 101527 ⟨294941, by decide⟩ ⟨13, 2, 0, 294941, 101527, 681, 16384⟩
    (by decide) selected_cut_10948

theorem unmarked_context_12_25381_294942 : frontier 9 ⟨294942, by decide⟩
    (prefixCache 12 25381) (prefixPartial 12 25381) = false := by
  decide +kernel

theorem node_context_12_25381_294942 : EJMOriginalGlobalDAGData.nodes 9 ⟨294942, by decide⟩ =
    .split (coordinate 12) (![⟨294892, by decide⟩,⟨294917, by decide⟩,⟨294935, by decide⟩,⟨294941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25381_294942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25381 ⟨294942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25381
    ⟨294942, by decide⟩ (by decide) (![⟨294892, by decide⟩,⟨294917, by decide⟩,⟨294935, by decide⟩,⟨294941, by decide⟩]) unmarked_context_12_25381_294942 node_context_12_25381_294942
  intro a
  fin_cases a
  · exact context_13_101524_294892
  · exact context_13_101525_294917
  · exact context_13_101526_294935
  · exact context_13_101527_294941

theorem selected_cut_10949 : selected 8 ⟨294953, by decide⟩
    (prefixPartial 13 101528) = some ⟨13, 2, 0, 294953, 101528, 829, 16384⟩ := by
  decide +kernel

theorem context_13_101528_294953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101528 ⟨294953, by decide⟩ :=
  accepted_of_selected 13 101528 ⟨294953, by decide⟩ ⟨13, 2, 0, 294953, 101528, 829, 16384⟩
    (by decide) selected_cut_10949

theorem selected_cut_10950 : selected 8 ⟨294977, by decide⟩
    (prefixPartial 13 101529) = some ⟨13, 2, 0, 294977, 101529, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_101529_294977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101529 ⟨294977, by decide⟩ :=
  accepted_of_selected 13 101529 ⟨294977, by decide⟩ ⟨13, 2, 0, 294977, 101529, 2289, 16384⟩
    (by decide) selected_cut_10950

theorem selected_cut_10951 : selected 8 ⟨294991, by decide⟩
    (prefixPartial 13 101530) = some ⟨13, 2, 0, 294991, 101530, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_101530_294991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101530 ⟨294991, by decide⟩ :=
  accepted_of_selected 13 101530 ⟨294991, by decide⟩ ⟨13, 2, 0, 294991, 101530, 1385, 16384⟩
    (by decide) selected_cut_10951

theorem selected_cut_10952 : selected 8 ⟨294998, by decide⟩
    (prefixPartial 13 101531) = some ⟨13, 2, 0, 294998, 101531, 777, 16384⟩ := by
  decide +kernel

theorem context_13_101531_294998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101531 ⟨294998, by decide⟩ :=
  accepted_of_selected 13 101531 ⟨294998, by decide⟩ ⟨13, 2, 0, 294998, 101531, 777, 16384⟩
    (by decide) selected_cut_10952

theorem unmarked_context_12_25382_294999 : frontier 9 ⟨294999, by decide⟩
    (prefixCache 12 25382) (prefixPartial 12 25382) = false := by
  decide +kernel

theorem node_context_12_25382_294999 : EJMOriginalGlobalDAGData.nodes 9 ⟨294999, by decide⟩ =
    .split (coordinate 12) (![⟨294953, by decide⟩,⟨294977, by decide⟩,⟨294991, by decide⟩,⟨294998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25382_294999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25382 ⟨294999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25382
    ⟨294999, by decide⟩ (by decide) (![⟨294953, by decide⟩,⟨294977, by decide⟩,⟨294991, by decide⟩,⟨294998, by decide⟩]) unmarked_context_12_25382_294999 node_context_12_25382_294999
  intro a
  fin_cases a
  · exact context_13_101528_294953
  · exact context_13_101529_294977
  · exact context_13_101530_294991
  · exact context_13_101531_294998

theorem selected_cut_10953 : selected 8 ⟨295012, by decide⟩
    (prefixPartial 13 101532) = some ⟨13, 2, 0, 295012, 101532, 837, 16384⟩ := by
  decide +kernel

theorem context_13_101532_295012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101532 ⟨295012, by decide⟩ :=
  accepted_of_selected 13 101532 ⟨295012, by decide⟩ ⟨13, 2, 0, 295012, 101532, 837, 16384⟩
    (by decide) selected_cut_10953

theorem selected_cut_10954 : selected 8 ⟨295039, by decide⟩
    (prefixPartial 13 101533) = some ⟨13, 2, 0, 295039, 101533, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_101533_295039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101533 ⟨295039, by decide⟩ :=
  accepted_of_selected 13 101533 ⟨295039, by decide⟩ ⟨13, 2, 0, 295039, 101533, 2253, 16384⟩
    (by decide) selected_cut_10954

theorem selected_cut_10955 : selected 8 ⟨295054, by decide⟩
    (prefixPartial 13 101534) = some ⟨13, 2, 0, 295054, 101534, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_101534_295054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101534 ⟨295054, by decide⟩ :=
  accepted_of_selected 13 101534 ⟨295054, by decide⟩ ⟨13, 2, 0, 295054, 101534, 1393, 16384⟩
    (by decide) selected_cut_10955

theorem selected_cut_10956 : selected 8 ⟨295063, by decide⟩
    (prefixPartial 13 101535) = some ⟨13, 2, 0, 295063, 101535, 721, 16384⟩ := by
  decide +kernel

theorem context_13_101535_295063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101535 ⟨295063, by decide⟩ :=
  accepted_of_selected 13 101535 ⟨295063, by decide⟩ ⟨13, 2, 0, 295063, 101535, 721, 16384⟩
    (by decide) selected_cut_10956

theorem unmarked_context_12_25383_295064 : frontier 9 ⟨295064, by decide⟩
    (prefixCache 12 25383) (prefixPartial 12 25383) = false := by
  decide +kernel

theorem node_context_12_25383_295064 : EJMOriginalGlobalDAGData.nodes 9 ⟨295064, by decide⟩ =
    .split (coordinate 12) (![⟨295012, by decide⟩,⟨295039, by decide⟩,⟨295054, by decide⟩,⟨295063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25383_295064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25383 ⟨295064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25383
    ⟨295064, by decide⟩ (by decide) (![⟨295012, by decide⟩,⟨295039, by decide⟩,⟨295054, by decide⟩,⟨295063, by decide⟩]) unmarked_context_12_25383_295064 node_context_12_25383_295064
  intro a
  fin_cases a
  · exact context_13_101532_295012
  · exact context_13_101533_295039
  · exact context_13_101534_295054
  · exact context_13_101535_295063

theorem unmarked_context_11_6345_295065 : frontier 10 ⟨295065, by decide⟩
    (prefixCache 11 6345) (prefixPartial 11 6345) = false := by
  decide +kernel

theorem node_context_11_6345_295065 : EJMOriginalGlobalDAGData.nodes 10 ⟨295065, by decide⟩ =
    .split (coordinate 11) (![⟨294882, by decide⟩,⟨294942, by decide⟩,⟨294999, by decide⟩,⟨295064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6345_295065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6345 ⟨295065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6345
    ⟨295065, by decide⟩ (by decide) (![⟨294882, by decide⟩,⟨294942, by decide⟩,⟨294999, by decide⟩,⟨295064, by decide⟩]) unmarked_context_11_6345_295065 node_context_11_6345_295065
  intro a
  fin_cases a
  · exact context_12_25380_294882
  · exact context_12_25381_294942
  · exact context_12_25382_294999
  · exact context_12_25383_295064

theorem selected_cut_10957 : selected 8 ⟨295078, by decide⟩
    (prefixPartial 13 101536) = some ⟨13, 2, 0, 295078, 101536, 829, 16384⟩ := by
  decide +kernel

theorem context_13_101536_295078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101536 ⟨295078, by decide⟩ :=
  accepted_of_selected 13 101536 ⟨295078, by decide⟩ ⟨13, 2, 0, 295078, 101536, 829, 16384⟩
    (by decide) selected_cut_10957

theorem selected_cut_10958 : selected 8 ⟨295106, by decide⟩
    (prefixPartial 13 101537) = some ⟨13, 2, 0, 295106, 101537, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_101537_295106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101537 ⟨295106, by decide⟩ :=
  accepted_of_selected 13 101537 ⟨295106, by decide⟩ ⟨13, 2, 0, 295106, 101537, 1953, 16384⟩
    (by decide) selected_cut_10958

theorem selected_cut_10959 : selected 8 ⟨295121, by decide⟩
    (prefixPartial 13 101538) = some ⟨13, 2, 0, 295121, 101538, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_101538_295121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101538 ⟨295121, by decide⟩ :=
  accepted_of_selected 13 101538 ⟨295121, by decide⟩ ⟨13, 2, 0, 295121, 101538, 1241, 16384⟩
    (by decide) selected_cut_10959

theorem selected_cut_10960 : selected 8 ⟨295127, by decide⟩
    (prefixPartial 13 101539) = some ⟨13, 2, 0, 295127, 101539, 669, 16384⟩ := by
  decide +kernel

theorem context_13_101539_295127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101539 ⟨295127, by decide⟩ :=
  accepted_of_selected 13 101539 ⟨295127, by decide⟩ ⟨13, 2, 0, 295127, 101539, 669, 16384⟩
    (by decide) selected_cut_10960

theorem unmarked_context_12_25384_295128 : frontier 9 ⟨295128, by decide⟩
    (prefixCache 12 25384) (prefixPartial 12 25384) = false := by
  decide +kernel

theorem node_context_12_25384_295128 : EJMOriginalGlobalDAGData.nodes 9 ⟨295128, by decide⟩ =
    .split (coordinate 12) (![⟨295078, by decide⟩,⟨295106, by decide⟩,⟨295121, by decide⟩,⟨295127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25384_295128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25384 ⟨295128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25384
    ⟨295128, by decide⟩ (by decide) (![⟨295078, by decide⟩,⟨295106, by decide⟩,⟨295121, by decide⟩,⟨295127, by decide⟩]) unmarked_context_12_25384_295128 node_context_12_25384_295128
  intro a
  fin_cases a
  · exact context_13_101536_295078
  · exact context_13_101537_295106
  · exact context_13_101538_295121
  · exact context_13_101539_295127

theorem selected_cut_10961 : selected 8 ⟨295137, by decide⟩
    (prefixPartial 13 101540) = some ⟨13, 2, 0, 295137, 101540, 841, 16384⟩ := by
  decide +kernel

theorem context_13_101540_295137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101540 ⟨295137, by decide⟩ :=
  accepted_of_selected 13 101540 ⟨295137, by decide⟩ ⟨13, 2, 0, 295137, 101540, 841, 16384⟩
    (by decide) selected_cut_10961

theorem selected_cut_10962 : selected 8 ⟨295169, by decide⟩
    (prefixPartial 13 101541) = some ⟨13, 2, 0, 295169, 101541, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_101541_295169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101541 ⟨295169, by decide⟩ :=
  accepted_of_selected 13 101541 ⟨295169, by decide⟩ ⟨13, 2, 0, 295169, 101541, 2257, 16384⟩
    (by decide) selected_cut_10962

theorem selected_cut_10963 : selected 8 ⟨295187, by decide⟩
    (prefixPartial 13 101542) = some ⟨13, 2, 0, 295187, 101542, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_101542_295187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101542 ⟨295187, by decide⟩ :=
  accepted_of_selected 13 101542 ⟨295187, by decide⟩ ⟨13, 2, 0, 295187, 101542, 1365, 16384⟩
    (by decide) selected_cut_10963

theorem selected_cut_10964 : selected 8 ⟨295195, by decide⟩
    (prefixPartial 13 101543) = some ⟨13, 2, 0, 295195, 101543, 709, 16384⟩ := by
  decide +kernel

theorem context_13_101543_295195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101543 ⟨295195, by decide⟩ :=
  accepted_of_selected 13 101543 ⟨295195, by decide⟩ ⟨13, 2, 0, 295195, 101543, 709, 16384⟩
    (by decide) selected_cut_10964

theorem unmarked_context_12_25385_295196 : frontier 9 ⟨295196, by decide⟩
    (prefixCache 12 25385) (prefixPartial 12 25385) = false := by
  decide +kernel

theorem node_context_12_25385_295196 : EJMOriginalGlobalDAGData.nodes 9 ⟨295196, by decide⟩ =
    .split (coordinate 12) (![⟨295137, by decide⟩,⟨295169, by decide⟩,⟨295187, by decide⟩,⟨295195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25385_295196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25385 ⟨295196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25385
    ⟨295196, by decide⟩ (by decide) (![⟨295137, by decide⟩,⟨295169, by decide⟩,⟨295187, by decide⟩,⟨295195, by decide⟩]) unmarked_context_12_25385_295196 node_context_12_25385_295196
  intro a
  fin_cases a
  · exact context_13_101540_295137
  · exact context_13_101541_295169
  · exact context_13_101542_295187
  · exact context_13_101543_295195

theorem selected_cut_10965 : selected 8 ⟨295208, by decide⟩
    (prefixPartial 13 101544) = some ⟨13, 2, 0, 295208, 101544, 689, 16384⟩ := by
  decide +kernel

theorem context_13_101544_295208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101544 ⟨295208, by decide⟩ :=
  accepted_of_selected 13 101544 ⟨295208, by decide⟩ ⟨13, 2, 0, 295208, 101544, 689, 16384⟩
    (by decide) selected_cut_10965

theorem selected_cut_10966 : selected 8 ⟨295233, by decide⟩
    (prefixPartial 13 101545) = some ⟨13, 2, 0, 295233, 101545, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_101545_295233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101545 ⟨295233, by decide⟩ :=
  accepted_of_selected 13 101545 ⟨295233, by decide⟩ ⟨13, 2, 0, 295233, 101545, 2149, 16384⟩
    (by decide) selected_cut_10966

theorem selected_cut_10967 : selected 8 ⟨295249, by decide⟩
    (prefixPartial 13 101546) = some ⟨13, 2, 0, 295249, 101546, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_101546_295249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101546 ⟨295249, by decide⟩ :=
  accepted_of_selected 13 101546 ⟨295249, by decide⟩ ⟨13, 2, 0, 295249, 101546, 1369, 16384⟩
    (by decide) selected_cut_10967

theorem selected_cut_10968 : selected 8 ⟨295253, by decide⟩
    (prefixPartial 13 101547) = some ⟨13, 2, 0, 295253, 101547, 629, 16384⟩ := by
  decide +kernel

theorem context_13_101547_295253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101547 ⟨295253, by decide⟩ :=
  accepted_of_selected 13 101547 ⟨295253, by decide⟩ ⟨13, 2, 0, 295253, 101547, 629, 16384⟩
    (by decide) selected_cut_10968

theorem unmarked_context_12_25386_295254 : frontier 9 ⟨295254, by decide⟩
    (prefixCache 12 25386) (prefixPartial 12 25386) = false := by
  decide +kernel

theorem node_context_12_25386_295254 : EJMOriginalGlobalDAGData.nodes 9 ⟨295254, by decide⟩ =
    .split (coordinate 12) (![⟨295208, by decide⟩,⟨295233, by decide⟩,⟨295249, by decide⟩,⟨295253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25386_295254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25386 ⟨295254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25386
    ⟨295254, by decide⟩ (by decide) (![⟨295208, by decide⟩,⟨295233, by decide⟩,⟨295249, by decide⟩,⟨295253, by decide⟩]) unmarked_context_12_25386_295254 node_context_12_25386_295254
  intro a
  fin_cases a
  · exact context_13_101544_295208
  · exact context_13_101545_295233
  · exact context_13_101546_295249
  · exact context_13_101547_295253

theorem selected_cut_10969 : selected 8 ⟨295266, by decide⟩
    (prefixPartial 13 101548) = some ⟨13, 2, 0, 295266, 101548, 709, 16384⟩ := by
  decide +kernel

theorem context_13_101548_295266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101548 ⟨295266, by decide⟩ :=
  accepted_of_selected 13 101548 ⟨295266, by decide⟩ ⟨13, 2, 0, 295266, 101548, 709, 16384⟩
    (by decide) selected_cut_10969

theorem selected_cut_10970 : selected 8 ⟨295300, by decide⟩
    (prefixPartial 13 101549) = some ⟨13, 2, 0, 295300, 101549, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_101549_295300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101549 ⟨295300, by decide⟩ :=
  accepted_of_selected 13 101549 ⟨295300, by decide⟩ ⟨13, 2, 0, 295300, 101549, 2317, 16384⟩
    (by decide) selected_cut_10970

theorem selected_cut_10971 : selected 8 ⟨295312, by decide⟩
    (prefixPartial 13 101550) = some ⟨13, 2, 0, 295312, 101550, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_101550_295312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101550 ⟨295312, by decide⟩ :=
  accepted_of_selected 13 101550 ⟨295312, by decide⟩ ⟨13, 2, 0, 295312, 101550, 1157, 16384⟩
    (by decide) selected_cut_10971

theorem selected_cut_10972 : selected 8 ⟨295317, by decide⟩
    (prefixPartial 13 101551) = some ⟨13, 2, 0, 295317, 101551, 593, 16384⟩ := by
  decide +kernel

theorem context_13_101551_295317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101551 ⟨295317, by decide⟩ :=
  accepted_of_selected 13 101551 ⟨295317, by decide⟩ ⟨13, 2, 0, 295317, 101551, 593, 16384⟩
    (by decide) selected_cut_10972

theorem unmarked_context_12_25387_295318 : frontier 9 ⟨295318, by decide⟩
    (prefixCache 12 25387) (prefixPartial 12 25387) = false := by
  decide +kernel

theorem node_context_12_25387_295318 : EJMOriginalGlobalDAGData.nodes 9 ⟨295318, by decide⟩ =
    .split (coordinate 12) (![⟨295266, by decide⟩,⟨295300, by decide⟩,⟨295312, by decide⟩,⟨295317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25387_295318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25387 ⟨295318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25387
    ⟨295318, by decide⟩ (by decide) (![⟨295266, by decide⟩,⟨295300, by decide⟩,⟨295312, by decide⟩,⟨295317, by decide⟩]) unmarked_context_12_25387_295318 node_context_12_25387_295318
  intro a
  fin_cases a
  · exact context_13_101548_295266
  · exact context_13_101549_295300
  · exact context_13_101550_295312
  · exact context_13_101551_295317

theorem unmarked_context_11_6346_295319 : frontier 10 ⟨295319, by decide⟩
    (prefixCache 11 6346) (prefixPartial 11 6346) = false := by
  decide +kernel

theorem node_context_11_6346_295319 : EJMOriginalGlobalDAGData.nodes 10 ⟨295319, by decide⟩ =
    .split (coordinate 11) (![⟨295128, by decide⟩,⟨295196, by decide⟩,⟨295254, by decide⟩,⟨295318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6346_295319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6346 ⟨295319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6346
    ⟨295319, by decide⟩ (by decide) (![⟨295128, by decide⟩,⟨295196, by decide⟩,⟨295254, by decide⟩,⟨295318, by decide⟩]) unmarked_context_11_6346_295319 node_context_11_6346_295319
  intro a
  fin_cases a
  · exact context_12_25384_295128
  · exact context_12_25385_295196
  · exact context_12_25386_295254
  · exact context_12_25387_295318

theorem selected_cut_10973 : selected 8 ⟨295330, by decide⟩
    (prefixPartial 13 101552) = some ⟨13, 2, 0, 295330, 101552, 689, 16384⟩ := by
  decide +kernel

theorem context_13_101552_295330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101552 ⟨295330, by decide⟩ :=
  accepted_of_selected 13 101552 ⟨295330, by decide⟩ ⟨13, 2, 0, 295330, 101552, 689, 16384⟩
    (by decide) selected_cut_10973

theorem selected_cut_10974 : selected 8 ⟨295355, by decide⟩
    (prefixPartial 13 101553) = some ⟨13, 2, 0, 295355, 101553, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_101553_295355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101553 ⟨295355, by decide⟩ :=
  accepted_of_selected 13 101553 ⟨295355, by decide⟩ ⟨13, 2, 0, 295355, 101553, 1777, 16384⟩
    (by decide) selected_cut_10974

theorem selected_cut_10975 : selected 8 ⟨295366, by decide⟩
    (prefixPartial 13 101554) = some ⟨13, 2, 0, 295366, 101554, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_101554_295366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101554 ⟨295366, by decide⟩ :=
  accepted_of_selected 13 101554 ⟨295366, by decide⟩ ⟨13, 2, 0, 295366, 101554, 1053, 16384⟩
    (by decide) selected_cut_10975

theorem selected_cut_10976 : selected 8 ⟨295374, by decide⟩
    (prefixPartial 13 101555) = some ⟨13, 2, 0, 295374, 101555, 697, 16384⟩ := by
  decide +kernel

theorem context_13_101555_295374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101555 ⟨295374, by decide⟩ :=
  accepted_of_selected 13 101555 ⟨295374, by decide⟩ ⟨13, 2, 0, 295374, 101555, 697, 16384⟩
    (by decide) selected_cut_10976

theorem unmarked_context_12_25388_295375 : frontier 9 ⟨295375, by decide⟩
    (prefixCache 12 25388) (prefixPartial 12 25388) = false := by
  decide +kernel

theorem node_context_12_25388_295375 : EJMOriginalGlobalDAGData.nodes 9 ⟨295375, by decide⟩ =
    .split (coordinate 12) (![⟨295330, by decide⟩,⟨295355, by decide⟩,⟨295366, by decide⟩,⟨295374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25388_295375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25388 ⟨295375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25388
    ⟨295375, by decide⟩ (by decide) (![⟨295330, by decide⟩,⟨295355, by decide⟩,⟨295366, by decide⟩,⟨295374, by decide⟩]) unmarked_context_12_25388_295375 node_context_12_25388_295375
  intro a
  fin_cases a
  · exact context_13_101552_295330
  · exact context_13_101553_295355
  · exact context_13_101554_295366
  · exact context_13_101555_295374

theorem selected_cut_10977 : selected 8 ⟨295388, by decide⟩
    (prefixPartial 13 101556) = some ⟨13, 2, 0, 295388, 101556, 793, 16384⟩ := by
  decide +kernel

theorem context_13_101556_295388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101556 ⟨295388, by decide⟩ :=
  accepted_of_selected 13 101556 ⟨295388, by decide⟩ ⟨13, 2, 0, 295388, 101556, 793, 16384⟩
    (by decide) selected_cut_10977

theorem selected_cut_10978 : selected 8 ⟨295417, by decide⟩
    (prefixPartial 13 101557) = some ⟨13, 2, 0, 295417, 101557, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_101557_295417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101557 ⟨295417, by decide⟩ :=
  accepted_of_selected 13 101557 ⟨295417, by decide⟩ ⟨13, 2, 0, 295417, 101557, 2253, 16384⟩
    (by decide) selected_cut_10978

theorem selected_cut_10979 : selected 8 ⟨295432, by decide⟩
    (prefixPartial 13 101558) = some ⟨13, 2, 0, 295432, 101558, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_101558_295432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101558 ⟨295432, by decide⟩ :=
  accepted_of_selected 13 101558 ⟨295432, by decide⟩ ⟨13, 2, 0, 295432, 101558, 1345, 16384⟩
    (by decide) selected_cut_10979

theorem selected_cut_10980 : selected 8 ⟨295441, by decide⟩
    (prefixPartial 13 101559) = some ⟨13, 2, 0, 295441, 101559, 729, 16384⟩ := by
  decide +kernel

theorem context_13_101559_295441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101559 ⟨295441, by decide⟩ :=
  accepted_of_selected 13 101559 ⟨295441, by decide⟩ ⟨13, 2, 0, 295441, 101559, 729, 16384⟩
    (by decide) selected_cut_10980

theorem unmarked_context_12_25389_295442 : frontier 9 ⟨295442, by decide⟩
    (prefixCache 12 25389) (prefixPartial 12 25389) = false := by
  decide +kernel

theorem node_context_12_25389_295442 : EJMOriginalGlobalDAGData.nodes 9 ⟨295442, by decide⟩ =
    .split (coordinate 12) (![⟨295388, by decide⟩,⟨295417, by decide⟩,⟨295432, by decide⟩,⟨295441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25389_295442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25389 ⟨295442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25389
    ⟨295442, by decide⟩ (by decide) (![⟨295388, by decide⟩,⟨295417, by decide⟩,⟨295432, by decide⟩,⟨295441, by decide⟩]) unmarked_context_12_25389_295442 node_context_12_25389_295442
  intro a
  fin_cases a
  · exact context_13_101556_295388
  · exact context_13_101557_295417
  · exact context_13_101558_295432
  · exact context_13_101559_295441

theorem selected_cut_10981 : selected 8 ⟨295455, by decide⟩
    (prefixPartial 13 101560) = some ⟨13, 2, 0, 295455, 101560, 665, 16384⟩ := by
  decide +kernel

theorem context_13_101560_295455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101560 ⟨295455, by decide⟩ :=
  accepted_of_selected 13 101560 ⟨295455, by decide⟩ ⟨13, 2, 0, 295455, 101560, 665, 16384⟩
    (by decide) selected_cut_10981

theorem selected_cut_10982 : selected 8 ⟨295491, by decide⟩
    (prefixPartial 13 101561) = some ⟨13, 2, 0, 295491, 101561, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_101561_295491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101561 ⟨295491, by decide⟩ :=
  accepted_of_selected 13 101561 ⟨295491, by decide⟩ ⟨13, 2, 0, 295491, 101561, 2361, 16384⟩
    (by decide) selected_cut_10982

theorem selected_cut_10983 : selected 8 ⟨295504, by decide⟩
    (prefixPartial 13 101562) = some ⟨13, 2, 0, 295504, 101562, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_101562_295504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101562 ⟨295504, by decide⟩ :=
  accepted_of_selected 13 101562 ⟨295504, by decide⟩ ⟨13, 2, 0, 295504, 101562, 1181, 16384⟩
    (by decide) selected_cut_10983

theorem selected_cut_10984 : selected 8 ⟨295509, by decide⟩
    (prefixPartial 13 101563) = some ⟨13, 2, 0, 295509, 101563, 673, 16384⟩ := by
  decide +kernel

theorem context_13_101563_295509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101563 ⟨295509, by decide⟩ :=
  accepted_of_selected 13 101563 ⟨295509, by decide⟩ ⟨13, 2, 0, 295509, 101563, 673, 16384⟩
    (by decide) selected_cut_10984

theorem unmarked_context_12_25390_295510 : frontier 9 ⟨295510, by decide⟩
    (prefixCache 12 25390) (prefixPartial 12 25390) = false := by
  decide +kernel

theorem node_context_12_25390_295510 : EJMOriginalGlobalDAGData.nodes 9 ⟨295510, by decide⟩ =
    .split (coordinate 12) (![⟨295455, by decide⟩,⟨295491, by decide⟩,⟨295504, by decide⟩,⟨295509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25390_295510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25390 ⟨295510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25390
    ⟨295510, by decide⟩ (by decide) (![⟨295455, by decide⟩,⟨295491, by decide⟩,⟨295504, by decide⟩,⟨295509, by decide⟩]) unmarked_context_12_25390_295510 node_context_12_25390_295510
  intro a
  fin_cases a
  · exact context_13_101560_295455
  · exact context_13_101561_295491
  · exact context_13_101562_295504
  · exact context_13_101563_295509

theorem selected_cut_10985 : selected 8 ⟨295529, by decide⟩
    (prefixPartial 13 101564) = some ⟨13, 2, 0, 295529, 101564, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_101564_295529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101564 ⟨295529, by decide⟩ :=
  accepted_of_selected 13 101564 ⟨295529, by decide⟩ ⟨13, 2, 0, 295529, 101564, 1173, 16384⟩
    (by decide) selected_cut_10985

theorem selected_cut_10986 : selected 8 ⟨295590, by decide⟩
    (prefixPartial 13 101565) = some ⟨13, 2, 0, 295590, 101565, 3825, 16384⟩ := by
  decide +kernel

theorem context_13_101565_295590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101565 ⟨295590, by decide⟩ :=
  accepted_of_selected 13 101565 ⟨295590, by decide⟩ ⟨13, 2, 0, 295590, 101565, 3825, 16384⟩
    (by decide) selected_cut_10986

theorem selected_cut_10987 : selected 8 ⟨295622, by decide⟩
    (prefixPartial 13 101566) = some ⟨13, 2, 0, 295622, 101566, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_101566_295622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101566 ⟨295622, by decide⟩ :=
  accepted_of_selected 13 101566 ⟨295622, by decide⟩ ⟨13, 2, 0, 295622, 101566, 2229, 16384⟩
    (by decide) selected_cut_10987

theorem selected_cut_10988 : selected 8 ⟨295647, by decide⟩
    (prefixPartial 13 101567) = some ⟨13, 2, 0, 295647, 101567, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_101567_295647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101567 ⟨295647, by decide⟩ :=
  accepted_of_selected 13 101567 ⟨295647, by decide⟩ ⟨13, 2, 0, 295647, 101567, 1225, 16384⟩
    (by decide) selected_cut_10988

theorem unmarked_context_12_25391_295648 : frontier 9 ⟨295648, by decide⟩
    (prefixCache 12 25391) (prefixPartial 12 25391) = false := by
  decide +kernel

theorem node_context_12_25391_295648 : EJMOriginalGlobalDAGData.nodes 9 ⟨295648, by decide⟩ =
    .split (coordinate 12) (![⟨295529, by decide⟩,⟨295590, by decide⟩,⟨295622, by decide⟩,⟨295647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25391_295648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25391 ⟨295648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25391
    ⟨295648, by decide⟩ (by decide) (![⟨295529, by decide⟩,⟨295590, by decide⟩,⟨295622, by decide⟩,⟨295647, by decide⟩]) unmarked_context_12_25391_295648 node_context_12_25391_295648
  intro a
  fin_cases a
  · exact context_13_101564_295529
  · exact context_13_101565_295590
  · exact context_13_101566_295622
  · exact context_13_101567_295647

theorem unmarked_context_11_6347_295649 : frontier 10 ⟨295649, by decide⟩
    (prefixCache 11 6347) (prefixPartial 11 6347) = false := by
  decide +kernel

theorem node_context_11_6347_295649 : EJMOriginalGlobalDAGData.nodes 10 ⟨295649, by decide⟩ =
    .split (coordinate 11) (![⟨295375, by decide⟩,⟨295442, by decide⟩,⟨295510, by decide⟩,⟨295648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6347_295649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6347 ⟨295649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6347
    ⟨295649, by decide⟩ (by decide) (![⟨295375, by decide⟩,⟨295442, by decide⟩,⟨295510, by decide⟩,⟨295648, by decide⟩]) unmarked_context_11_6347_295649 node_context_11_6347_295649
  intro a
  fin_cases a
  · exact context_12_25388_295375
  · exact context_12_25389_295442
  · exact context_12_25390_295510
  · exact context_12_25391_295648

theorem unmarked_context_10_1586_295650 : frontier 11 ⟨295650, by decide⟩
    (prefixCache 10 1586) (prefixPartial 10 1586) = false := by
  decide +kernel

theorem node_context_10_1586_295650 : EJMOriginalGlobalDAGData.nodes 11 ⟨295650, by decide⟩ =
    .split (coordinate 10) (![⟨294819, by decide⟩,⟨295065, by decide⟩,⟨295319, by decide⟩,⟨295649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1586_295650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1586 ⟨295650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1586
    ⟨295650, by decide⟩ (by decide) (![⟨294819, by decide⟩,⟨295065, by decide⟩,⟨295319, by decide⟩,⟨295649, by decide⟩]) unmarked_context_10_1586_295650 node_context_10_1586_295650
  intro a
  fin_cases a
  · exact context_11_6344_294819
  · exact context_11_6345_295065
  · exact context_11_6346_295319
  · exact context_11_6347_295649

theorem selected_cut_10989 : selected 9 ⟨295700, by decide⟩
    (prefixPartial 12 25392) = some ⟨12, 2, 0, 295700, 25392, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_25392_295700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25392 ⟨295700, by decide⟩ :=
  accepted_of_selected 12 25392 ⟨295700, by decide⟩ ⟨12, 2, 0, 295700, 25392, 3529, 65536⟩
    (by decide) selected_cut_10989

theorem selected_cut_10990 : selected 8 ⟨295706, by decide⟩
    (prefixPartial 13 101572) = some ⟨13, 2, 0, 295706, 101572, 409, 16384⟩ := by
  decide +kernel

theorem context_13_101572_295706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101572 ⟨295706, by decide⟩ :=
  accepted_of_selected 13 101572 ⟨295706, by decide⟩ ⟨13, 2, 0, 295706, 101572, 409, 16384⟩
    (by decide) selected_cut_10990

theorem selected_cut_10991 : selected 8 ⟨295730, by decide⟩
    (prefixPartial 13 101573) = some ⟨13, 2, 0, 295730, 101573, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_101573_295730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101573 ⟨295730, by decide⟩ :=
  accepted_of_selected 13 101573 ⟨295730, by decide⟩ ⟨13, 2, 0, 295730, 101573, 1833, 16384⟩
    (by decide) selected_cut_10991

theorem selected_cut_10992 : selected 8 ⟨295749, by decide⟩
    (prefixPartial 13 101574) = some ⟨13, 2, 0, 295749, 101574, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_101574_295749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101574 ⟨295749, by decide⟩ :=
  accepted_of_selected 13 101574 ⟨295749, by decide⟩ ⟨13, 2, 0, 295749, 101574, 1381, 16384⟩
    (by decide) selected_cut_10992

theorem selected_cut_10993 : selected 8 ⟨295755, by decide⟩
    (prefixPartial 13 101575) = some ⟨13, 2, 0, 295755, 101575, 641, 16384⟩ := by
  decide +kernel

theorem context_13_101575_295755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101575 ⟨295755, by decide⟩ :=
  accepted_of_selected 13 101575 ⟨295755, by decide⟩ ⟨13, 2, 0, 295755, 101575, 641, 16384⟩
    (by decide) selected_cut_10993

theorem unmarked_context_12_25393_295756 : frontier 9 ⟨295756, by decide⟩
    (prefixCache 12 25393) (prefixPartial 12 25393) = false := by
  decide +kernel

theorem node_context_12_25393_295756 : EJMOriginalGlobalDAGData.nodes 9 ⟨295756, by decide⟩ =
    .split (coordinate 12) (![⟨295706, by decide⟩,⟨295730, by decide⟩,⟨295749, by decide⟩,⟨295755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25393_295756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25393 ⟨295756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25393
    ⟨295756, by decide⟩ (by decide) (![⟨295706, by decide⟩,⟨295730, by decide⟩,⟨295749, by decide⟩,⟨295755, by decide⟩]) unmarked_context_12_25393_295756 node_context_12_25393_295756
  intro a
  fin_cases a
  · exact context_13_101572_295706
  · exact context_13_101573_295730
  · exact context_13_101574_295749
  · exact context_13_101575_295755

theorem selected_cut_10994 : selected 8 ⟨295764, by decide⟩
    (prefixPartial 13 101576) = some ⟨13, 2, 0, 295764, 101576, 389, 16384⟩ := by
  decide +kernel

theorem context_13_101576_295764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101576 ⟨295764, by decide⟩ :=
  accepted_of_selected 13 101576 ⟨295764, by decide⟩ ⟨13, 2, 0, 295764, 101576, 389, 16384⟩
    (by decide) selected_cut_10994

theorem selected_cut_10995 : selected 8 ⟨295788, by decide⟩
    (prefixPartial 13 101577) = some ⟨13, 2, 0, 295788, 101577, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_101577_295788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101577 ⟨295788, by decide⟩ :=
  accepted_of_selected 13 101577 ⟨295788, by decide⟩ ⟨13, 2, 0, 295788, 101577, 1933, 16384⟩
    (by decide) selected_cut_10995

theorem selected_cut_10996 : selected 8 ⟨295804, by decide⟩
    (prefixPartial 13 101578) = some ⟨13, 2, 0, 295804, 101578, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_101578_295804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101578 ⟨295804, by decide⟩ :=
  accepted_of_selected 13 101578 ⟨295804, by decide⟩ ⟨13, 2, 0, 295804, 101578, 1181, 16384⟩
    (by decide) selected_cut_10996

theorem selected_cut_10997 : selected 8 ⟨295811, by decide⟩
    (prefixPartial 13 101579) = some ⟨13, 2, 0, 295811, 101579, 629, 16384⟩ := by
  decide +kernel

theorem context_13_101579_295811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101579 ⟨295811, by decide⟩ :=
  accepted_of_selected 13 101579 ⟨295811, by decide⟩ ⟨13, 2, 0, 295811, 101579, 629, 16384⟩
    (by decide) selected_cut_10997

theorem unmarked_context_12_25394_295812 : frontier 9 ⟨295812, by decide⟩
    (prefixCache 12 25394) (prefixPartial 12 25394) = false := by
  decide +kernel

theorem node_context_12_25394_295812 : EJMOriginalGlobalDAGData.nodes 9 ⟨295812, by decide⟩ =
    .split (coordinate 12) (![⟨295764, by decide⟩,⟨295788, by decide⟩,⟨295804, by decide⟩,⟨295811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25394_295812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25394 ⟨295812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25394
    ⟨295812, by decide⟩ (by decide) (![⟨295764, by decide⟩,⟨295788, by decide⟩,⟨295804, by decide⟩,⟨295811, by decide⟩]) unmarked_context_12_25394_295812 node_context_12_25394_295812
  intro a
  fin_cases a
  · exact context_13_101576_295764
  · exact context_13_101577_295788
  · exact context_13_101578_295804
  · exact context_13_101579_295811

theorem selected_cut_10998 : selected 8 ⟨295818, by decide⟩
    (prefixPartial 13 101580) = some ⟨13, 2, 0, 295818, 101580, 365, 16384⟩ := by
  decide +kernel

theorem context_13_101580_295818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101580 ⟨295818, by decide⟩ :=
  accepted_of_selected 13 101580 ⟨295818, by decide⟩ ⟨13, 2, 0, 295818, 101580, 365, 16384⟩
    (by decide) selected_cut_10998

theorem selected_cut_10999 : selected 8 ⟨295842, by decide⟩
    (prefixPartial 13 101581) = some ⟨13, 2, 0, 295842, 101581, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_101581_295842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101581 ⟨295842, by decide⟩ :=
  accepted_of_selected 13 101581 ⟨295842, by decide⟩ ⟨13, 2, 0, 295842, 101581, 2005, 16384⟩
    (by decide) selected_cut_10999

theorem selected_cut_11000 : selected 8 ⟨295856, by decide⟩
    (prefixPartial 13 101582) = some ⟨13, 2, 0, 295856, 101582, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_101582_295856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101582 ⟨295856, by decide⟩ :=
  accepted_of_selected 13 101582 ⟨295856, by decide⟩ ⟨13, 2, 0, 295856, 101582, 1209, 16384⟩
    (by decide) selected_cut_11000

theorem selected_cut_11001 : selected 8 ⟨295860, by decide⟩
    (prefixPartial 13 101583) = some ⟨13, 2, 0, 295860, 101583, 593, 16384⟩ := by
  decide +kernel

theorem context_13_101583_295860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101583 ⟨295860, by decide⟩ :=
  accepted_of_selected 13 101583 ⟨295860, by decide⟩ ⟨13, 2, 0, 295860, 101583, 593, 16384⟩
    (by decide) selected_cut_11001

theorem unmarked_context_12_25395_295861 : frontier 9 ⟨295861, by decide⟩
    (prefixCache 12 25395) (prefixPartial 12 25395) = false := by
  decide +kernel

theorem node_context_12_25395_295861 : EJMOriginalGlobalDAGData.nodes 9 ⟨295861, by decide⟩ =
    .split (coordinate 12) (![⟨295818, by decide⟩,⟨295842, by decide⟩,⟨295856, by decide⟩,⟨295860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25395_295861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25395 ⟨295861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25395
    ⟨295861, by decide⟩ (by decide) (![⟨295818, by decide⟩,⟨295842, by decide⟩,⟨295856, by decide⟩,⟨295860, by decide⟩]) unmarked_context_12_25395_295861 node_context_12_25395_295861
  intro a
  fin_cases a
  · exact context_13_101580_295818
  · exact context_13_101581_295842
  · exact context_13_101582_295856
  · exact context_13_101583_295860

theorem unmarked_context_11_6348_295862 : frontier 10 ⟨295862, by decide⟩
    (prefixCache 11 6348) (prefixPartial 11 6348) = false := by
  decide +kernel

theorem node_context_11_6348_295862 : EJMOriginalGlobalDAGData.nodes 10 ⟨295862, by decide⟩ =
    .split (coordinate 11) (![⟨295700, by decide⟩,⟨295756, by decide⟩,⟨295812, by decide⟩,⟨295861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6348_295862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6348 ⟨295862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6348
    ⟨295862, by decide⟩ (by decide) (![⟨295700, by decide⟩,⟨295756, by decide⟩,⟨295812, by decide⟩,⟨295861, by decide⟩]) unmarked_context_11_6348_295862 node_context_11_6348_295862
  intro a
  fin_cases a
  · exact context_12_25392_295700
  · exact context_12_25393_295756
  · exact context_12_25394_295812
  · exact context_12_25395_295861

theorem selected_cut_11002 : selected 8 ⟨295867, by decide⟩
    (prefixPartial 13 101584) = some ⟨13, 2, 0, 295867, 101584, 377, 16384⟩ := by
  decide +kernel

theorem context_13_101584_295867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101584 ⟨295867, by decide⟩ :=
  accepted_of_selected 13 101584 ⟨295867, by decide⟩ ⟨13, 2, 0, 295867, 101584, 377, 16384⟩
    (by decide) selected_cut_11002

theorem selected_cut_11003 : selected 8 ⟨295899, by decide⟩
    (prefixPartial 13 101585) = some ⟨13, 2, 0, 295899, 101585, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_101585_295899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101585 ⟨295899, by decide⟩ :=
  accepted_of_selected 13 101585 ⟨295899, by decide⟩ ⟨13, 2, 0, 295899, 101585, 2265, 16384⟩
    (by decide) selected_cut_11003

theorem selected_cut_11004 : selected 8 ⟨295919, by decide⟩
    (prefixPartial 13 101586) = some ⟨13, 2, 0, 295919, 101586, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_101586_295919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101586 ⟨295919, by decide⟩ :=
  accepted_of_selected 13 101586 ⟨295919, by decide⟩ ⟨13, 2, 0, 295919, 101586, 1437, 16384⟩
    (by decide) selected_cut_11004

theorem selected_cut_11005 : selected 8 ⟨295927, by decide⟩
    (prefixPartial 13 101587) = some ⟨13, 2, 0, 295927, 101587, 921, 16384⟩ := by
  decide +kernel

theorem context_13_101587_295927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101587 ⟨295927, by decide⟩ :=
  accepted_of_selected 13 101587 ⟨295927, by decide⟩ ⟨13, 2, 0, 295927, 101587, 921, 16384⟩
    (by decide) selected_cut_11005

theorem unmarked_context_12_25396_295928 : frontier 9 ⟨295928, by decide⟩
    (prefixCache 12 25396) (prefixPartial 12 25396) = false := by
  decide +kernel

theorem node_context_12_25396_295928 : EJMOriginalGlobalDAGData.nodes 9 ⟨295928, by decide⟩ =
    .split (coordinate 12) (![⟨295867, by decide⟩,⟨295899, by decide⟩,⟨295919, by decide⟩,⟨295927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25396_295928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25396 ⟨295928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25396
    ⟨295928, by decide⟩ (by decide) (![⟨295867, by decide⟩,⟨295899, by decide⟩,⟨295919, by decide⟩,⟨295927, by decide⟩]) unmarked_context_12_25396_295928 node_context_12_25396_295928
  intro a
  fin_cases a
  · exact context_13_101584_295867
  · exact context_13_101585_295899
  · exact context_13_101586_295919
  · exact context_13_101587_295927

theorem selected_cut_11006 : selected 8 ⟨295934, by decide⟩
    (prefixPartial 13 101588) = some ⟨13, 2, 0, 295934, 101588, 349, 16384⟩ := by
  decide +kernel

theorem context_13_101588_295934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101588 ⟨295934, by decide⟩ :=
  accepted_of_selected 13 101588 ⟨295934, by decide⟩ ⟨13, 2, 0, 295934, 101588, 349, 16384⟩
    (by decide) selected_cut_11006

theorem selected_cut_11007 : selected 8 ⟨295962, by decide⟩
    (prefixPartial 13 101589) = some ⟨13, 2, 0, 295962, 101589, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_101589_295962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101589 ⟨295962, by decide⟩ :=
  accepted_of_selected 13 101589 ⟨295962, by decide⟩ ⟨13, 2, 0, 295962, 101589, 2265, 16384⟩
    (by decide) selected_cut_11007

theorem selected_cut_11008 : selected 8 ⟨295981, by decide⟩
    (prefixPartial 13 101590) = some ⟨13, 2, 0, 295981, 101590, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_101590_295981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101590 ⟨295981, by decide⟩ :=
  accepted_of_selected 13 101590 ⟨295981, by decide⟩ ⟨13, 2, 0, 295981, 101590, 1569, 16384⟩
    (by decide) selected_cut_11008

theorem selected_cut_11009 : selected 8 ⟨295988, by decide⟩
    (prefixPartial 13 101591) = some ⟨13, 2, 0, 295988, 101591, 849, 16384⟩ := by
  decide +kernel

theorem context_13_101591_295988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101591 ⟨295988, by decide⟩ :=
  accepted_of_selected 13 101591 ⟨295988, by decide⟩ ⟨13, 2, 0, 295988, 101591, 849, 16384⟩
    (by decide) selected_cut_11009

theorem unmarked_context_12_25397_295989 : frontier 9 ⟨295989, by decide⟩
    (prefixCache 12 25397) (prefixPartial 12 25397) = false := by
  decide +kernel

theorem node_context_12_25397_295989 : EJMOriginalGlobalDAGData.nodes 9 ⟨295989, by decide⟩ =
    .split (coordinate 12) (![⟨295934, by decide⟩,⟨295962, by decide⟩,⟨295981, by decide⟩,⟨295988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25397_295989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25397 ⟨295989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25397
    ⟨295989, by decide⟩ (by decide) (![⟨295934, by decide⟩,⟨295962, by decide⟩,⟨295981, by decide⟩,⟨295988, by decide⟩]) unmarked_context_12_25397_295989 node_context_12_25397_295989
  intro a
  fin_cases a
  · exact context_13_101588_295934
  · exact context_13_101589_295962
  · exact context_13_101590_295981
  · exact context_13_101591_295988

theorem selected_cut_11010 : selected 8 ⟨295995, by decide⟩
    (prefixPartial 13 101592) = some ⟨13, 2, 0, 295995, 101592, 337, 16384⟩ := by
  decide +kernel

theorem context_13_101592_295995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101592 ⟨295995, by decide⟩ :=
  accepted_of_selected 13 101592 ⟨295995, by decide⟩ ⟨13, 2, 0, 295995, 101592, 337, 16384⟩
    (by decide) selected_cut_11010

theorem selected_cut_11011 : selected 8 ⟨296021, by decide⟩
    (prefixPartial 13 101593) = some ⟨13, 2, 0, 296021, 101593, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_101593_296021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101593 ⟨296021, by decide⟩ :=
  accepted_of_selected 13 101593 ⟨296021, by decide⟩ ⟨13, 2, 0, 296021, 101593, 2449, 16384⟩
    (by decide) selected_cut_11011

theorem selected_cut_11012 : selected 8 ⟨296039, by decide⟩
    (prefixPartial 13 101594) = some ⟨13, 2, 0, 296039, 101594, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_101594_296039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101594 ⟨296039, by decide⟩ :=
  accepted_of_selected 13 101594 ⟨296039, by decide⟩ ⟨13, 2, 0, 296039, 101594, 1453, 16384⟩
    (by decide) selected_cut_11012

theorem selected_cut_11013 : selected 8 ⟨296045, by decide⟩
    (prefixPartial 13 101595) = some ⟨13, 2, 0, 296045, 101595, 925, 16384⟩ := by
  decide +kernel

theorem context_13_101595_296045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101595 ⟨296045, by decide⟩ :=
  accepted_of_selected 13 101595 ⟨296045, by decide⟩ ⟨13, 2, 0, 296045, 101595, 925, 16384⟩
    (by decide) selected_cut_11013

theorem unmarked_context_12_25398_296046 : frontier 9 ⟨296046, by decide⟩
    (prefixCache 12 25398) (prefixPartial 12 25398) = false := by
  decide +kernel

theorem node_context_12_25398_296046 : EJMOriginalGlobalDAGData.nodes 9 ⟨296046, by decide⟩ =
    .split (coordinate 12) (![⟨295995, by decide⟩,⟨296021, by decide⟩,⟨296039, by decide⟩,⟨296045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25398_296046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25398 ⟨296046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25398
    ⟨296046, by decide⟩ (by decide) (![⟨295995, by decide⟩,⟨296021, by decide⟩,⟨296039, by decide⟩,⟨296045, by decide⟩]) unmarked_context_12_25398_296046 node_context_12_25398_296046
  intro a
  fin_cases a
  · exact context_13_101592_295995
  · exact context_13_101593_296021
  · exact context_13_101594_296039
  · exact context_13_101595_296045

theorem selected_cut_11014 : selected 8 ⟨296052, by decide⟩
    (prefixPartial 13 101596) = some ⟨13, 2, 0, 296052, 101596, 301, 16384⟩ := by
  decide +kernel

theorem context_13_101596_296052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101596 ⟨296052, by decide⟩ :=
  accepted_of_selected 13 101596 ⟨296052, by decide⟩ ⟨13, 2, 0, 296052, 101596, 301, 16384⟩
    (by decide) selected_cut_11014

theorem selected_cut_11015 : selected 8 ⟨296082, by decide⟩
    (prefixPartial 13 101597) = some ⟨13, 2, 0, 296082, 101597, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_101597_296082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101597 ⟨296082, by decide⟩ :=
  accepted_of_selected 13 101597 ⟨296082, by decide⟩ ⟨13, 2, 0, 296082, 101597, 2313, 16384⟩
    (by decide) selected_cut_11015

theorem selected_cut_11016 : selected 8 ⟨296099, by decide⟩
    (prefixPartial 13 101598) = some ⟨13, 2, 0, 296099, 101598, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_101598_296099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101598 ⟨296099, by decide⟩ :=
  accepted_of_selected 13 101598 ⟨296099, by decide⟩ ⟨13, 2, 0, 296099, 101598, 1617, 16384⟩
    (by decide) selected_cut_11016

theorem selected_cut_11017 : selected 8 ⟨296106, by decide⟩
    (prefixPartial 13 101599) = some ⟨13, 2, 0, 296106, 101599, 921, 16384⟩ := by
  decide +kernel

theorem context_13_101599_296106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101599 ⟨296106, by decide⟩ :=
  accepted_of_selected 13 101599 ⟨296106, by decide⟩ ⟨13, 2, 0, 296106, 101599, 921, 16384⟩
    (by decide) selected_cut_11017

theorem unmarked_context_12_25399_296107 : frontier 9 ⟨296107, by decide⟩
    (prefixCache 12 25399) (prefixPartial 12 25399) = false := by
  decide +kernel

theorem node_context_12_25399_296107 : EJMOriginalGlobalDAGData.nodes 9 ⟨296107, by decide⟩ =
    .split (coordinate 12) (![⟨296052, by decide⟩,⟨296082, by decide⟩,⟨296099, by decide⟩,⟨296106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25399_296107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25399 ⟨296107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25399
    ⟨296107, by decide⟩ (by decide) (![⟨296052, by decide⟩,⟨296082, by decide⟩,⟨296099, by decide⟩,⟨296106, by decide⟩]) unmarked_context_12_25399_296107 node_context_12_25399_296107
  intro a
  fin_cases a
  · exact context_13_101596_296052
  · exact context_13_101597_296082
  · exact context_13_101598_296099
  · exact context_13_101599_296106

theorem unmarked_context_11_6349_296108 : frontier 10 ⟨296108, by decide⟩
    (prefixCache 11 6349) (prefixPartial 11 6349) = false := by
  decide +kernel

theorem node_context_11_6349_296108 : EJMOriginalGlobalDAGData.nodes 10 ⟨296108, by decide⟩ =
    .split (coordinate 11) (![⟨295928, by decide⟩,⟨295989, by decide⟩,⟨296046, by decide⟩,⟨296107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6349_296108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6349 ⟨296108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6349
    ⟨296108, by decide⟩ (by decide) (![⟨295928, by decide⟩,⟨295989, by decide⟩,⟨296046, by decide⟩,⟨296107, by decide⟩]) unmarked_context_11_6349_296108 node_context_11_6349_296108
  intro a
  fin_cases a
  · exact context_12_25396_295928
  · exact context_12_25397_295989
  · exact context_12_25398_296046
  · exact context_12_25399_296107

theorem selected_cut_11018 : selected 8 ⟨296112, by decide⟩
    (prefixPartial 13 101600) = some ⟨13, 2, 0, 296112, 101600, 305, 16384⟩ := by
  decide +kernel

theorem context_13_101600_296112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101600 ⟨296112, by decide⟩ :=
  accepted_of_selected 13 101600 ⟨296112, by decide⟩ ⟨13, 2, 0, 296112, 101600, 305, 16384⟩
    (by decide) selected_cut_11018

theorem selected_cut_11019 : selected 8 ⟨296139, by decide⟩
    (prefixPartial 13 101601) = some ⟨13, 2, 0, 296139, 101601, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_101601_296139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101601 ⟨296139, by decide⟩ :=
  accepted_of_selected 13 101601 ⟨296139, by decide⟩ ⟨13, 2, 0, 296139, 101601, 2093, 16384⟩
    (by decide) selected_cut_11019

theorem selected_cut_11020 : selected 8 ⟨296158, by decide⟩
    (prefixPartial 13 101602) = some ⟨13, 2, 0, 296158, 101602, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_101602_296158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101602 ⟨296158, by decide⟩ :=
  accepted_of_selected 13 101602 ⟨296158, by decide⟩ ⟨13, 2, 0, 296158, 101602, 1629, 16384⟩
    (by decide) selected_cut_11020

theorem selected_cut_11021 : selected 8 ⟨296162, by decide⟩
    (prefixPartial 13 101603) = some ⟨13, 2, 0, 296162, 101603, 801, 16384⟩ := by
  decide +kernel

theorem context_13_101603_296162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101603 ⟨296162, by decide⟩ :=
  accepted_of_selected 13 101603 ⟨296162, by decide⟩ ⟨13, 2, 0, 296162, 101603, 801, 16384⟩
    (by decide) selected_cut_11021

theorem unmarked_context_12_25400_296163 : frontier 9 ⟨296163, by decide⟩
    (prefixCache 12 25400) (prefixPartial 12 25400) = false := by
  decide +kernel

theorem node_context_12_25400_296163 : EJMOriginalGlobalDAGData.nodes 9 ⟨296163, by decide⟩ =
    .split (coordinate 12) (![⟨296112, by decide⟩,⟨296139, by decide⟩,⟨296158, by decide⟩,⟨296162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25400_296163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25400 ⟨296163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25400
    ⟨296163, by decide⟩ (by decide) (![⟨296112, by decide⟩,⟨296139, by decide⟩,⟨296158, by decide⟩,⟨296162, by decide⟩]) unmarked_context_12_25400_296163 node_context_12_25400_296163
  intro a
  fin_cases a
  · exact context_13_101600_296112
  · exact context_13_101601_296139
  · exact context_13_101602_296158
  · exact context_13_101603_296162

theorem selected_cut_11022 : selected 8 ⟨296167, by decide⟩
    (prefixPartial 13 101604) = some ⟨13, 2, 0, 296167, 101604, 269, 16384⟩ := by
  decide +kernel

theorem context_13_101604_296167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101604 ⟨296167, by decide⟩ :=
  accepted_of_selected 13 101604 ⟨296167, by decide⟩ ⟨13, 2, 0, 296167, 101604, 269, 16384⟩
    (by decide) selected_cut_11022

theorem selected_cut_11023 : selected 8 ⟨296195, by decide⟩
    (prefixPartial 13 101605) = some ⟨13, 2, 0, 296195, 101605, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_101605_296195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101605 ⟨296195, by decide⟩ :=
  accepted_of_selected 13 101605 ⟨296195, by decide⟩ ⟨13, 2, 0, 296195, 101605, 2317, 16384⟩
    (by decide) selected_cut_11023

theorem selected_cut_11024 : selected 8 ⟨296218, by decide⟩
    (prefixPartial 13 101606) = some ⟨13, 2, 0, 296218, 101606, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_101606_296218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101606 ⟨296218, by decide⟩ :=
  accepted_of_selected 13 101606 ⟨296218, by decide⟩ ⟨13, 2, 0, 296218, 101606, 1669, 16384⟩
    (by decide) selected_cut_11024

theorem selected_cut_11025 : selected 8 ⟨296226, by decide⟩
    (prefixPartial 13 101607) = some ⟨13, 2, 0, 296226, 101607, 849, 16384⟩ := by
  decide +kernel

theorem context_13_101607_296226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101607 ⟨296226, by decide⟩ :=
  accepted_of_selected 13 101607 ⟨296226, by decide⟩ ⟨13, 2, 0, 296226, 101607, 849, 16384⟩
    (by decide) selected_cut_11025

theorem unmarked_context_12_25401_296227 : frontier 9 ⟨296227, by decide⟩
    (prefixCache 12 25401) (prefixPartial 12 25401) = false := by
  decide +kernel

theorem node_context_12_25401_296227 : EJMOriginalGlobalDAGData.nodes 9 ⟨296227, by decide⟩ =
    .split (coordinate 12) (![⟨296167, by decide⟩,⟨296195, by decide⟩,⟨296218, by decide⟩,⟨296226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25401_296227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25401 ⟨296227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25401
    ⟨296227, by decide⟩ (by decide) (![⟨296167, by decide⟩,⟨296195, by decide⟩,⟨296218, by decide⟩,⟨296226, by decide⟩]) unmarked_context_12_25401_296227 node_context_12_25401_296227
  intro a
  fin_cases a
  · exact context_13_101604_296167
  · exact context_13_101605_296195
  · exact context_13_101606_296218
  · exact context_13_101607_296226

theorem selected_cut_11026 : selected 8 ⟨296232, by decide⟩
    (prefixPartial 13 101608) = some ⟨13, 2, 0, 296232, 101608, 213, 16384⟩ := by
  decide +kernel

theorem context_13_101608_296232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101608 ⟨296232, by decide⟩ :=
  accepted_of_selected 13 101608 ⟨296232, by decide⟩ ⟨13, 2, 0, 296232, 101608, 213, 16384⟩
    (by decide) selected_cut_11026

theorem selected_cut_11027 : selected 8 ⟨296262, by decide⟩
    (prefixPartial 13 101609) = some ⟨13, 2, 0, 296262, 101609, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_101609_296262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101609 ⟨296262, by decide⟩ :=
  accepted_of_selected 13 101609 ⟨296262, by decide⟩ ⟨13, 2, 0, 296262, 101609, 2361, 16384⟩
    (by decide) selected_cut_11027

theorem selected_cut_11028 : selected 8 ⟨296283, by decide⟩
    (prefixPartial 13 101610) = some ⟨13, 2, 0, 296283, 101610, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_101610_296283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101610 ⟨296283, by decide⟩ :=
  accepted_of_selected 13 101610 ⟨296283, by decide⟩ ⟨13, 2, 0, 296283, 101610, 1473, 16384⟩
    (by decide) selected_cut_11028

theorem selected_cut_11029 : selected 8 ⟨296292, by decide⟩
    (prefixPartial 13 101611) = some ⟨13, 2, 0, 296292, 101611, 749, 16384⟩ := by
  decide +kernel

theorem context_13_101611_296292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101611 ⟨296292, by decide⟩ :=
  accepted_of_selected 13 101611 ⟨296292, by decide⟩ ⟨13, 2, 0, 296292, 101611, 749, 16384⟩
    (by decide) selected_cut_11029

theorem unmarked_context_12_25402_296293 : frontier 9 ⟨296293, by decide⟩
    (prefixCache 12 25402) (prefixPartial 12 25402) = false := by
  decide +kernel

theorem node_context_12_25402_296293 : EJMOriginalGlobalDAGData.nodes 9 ⟨296293, by decide⟩ =
    .split (coordinate 12) (![⟨296232, by decide⟩,⟨296262, by decide⟩,⟨296283, by decide⟩,⟨296292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25402_296293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25402 ⟨296293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25402
    ⟨296293, by decide⟩ (by decide) (![⟨296232, by decide⟩,⟨296262, by decide⟩,⟨296283, by decide⟩,⟨296292, by decide⟩]) unmarked_context_12_25402_296293 node_context_12_25402_296293
  intro a
  fin_cases a
  · exact context_13_101608_296232
  · exact context_13_101609_296262
  · exact context_13_101610_296283
  · exact context_13_101611_296292

theorem selected_cut_11030 : selected 8 ⟨296298, by decide⟩
    (prefixPartial 13 101612) = some ⟨13, 2, 0, 296298, 101612, 177, 16384⟩ := by
  decide +kernel

theorem context_13_101612_296298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101612 ⟨296298, by decide⟩ :=
  accepted_of_selected 13 101612 ⟨296298, by decide⟩ ⟨13, 2, 0, 296298, 101612, 177, 16384⟩
    (by decide) selected_cut_11030

theorem selected_cut_11031 : selected 8 ⟨296326, by decide⟩
    (prefixPartial 13 101613) = some ⟨13, 2, 0, 296326, 101613, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_101613_296326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101613 ⟨296326, by decide⟩ :=
  accepted_of_selected 13 101613 ⟨296326, by decide⟩ ⟨13, 2, 0, 296326, 101613, 2397, 16384⟩
    (by decide) selected_cut_11031

theorem selected_cut_11032 : selected 8 ⟨296345, by decide⟩
    (prefixPartial 13 101614) = some ⟨13, 2, 0, 296345, 101614, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_101614_296345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101614 ⟨296345, by decide⟩ :=
  accepted_of_selected 13 101614 ⟨296345, by decide⟩ ⟨13, 2, 0, 296345, 101614, 1477, 16384⟩
    (by decide) selected_cut_11032

theorem selected_cut_11033 : selected 8 ⟨296352, by decide⟩
    (prefixPartial 13 101615) = some ⟨13, 2, 0, 296352, 101615, 725, 16384⟩ := by
  decide +kernel

theorem context_13_101615_296352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101615 ⟨296352, by decide⟩ :=
  accepted_of_selected 13 101615 ⟨296352, by decide⟩ ⟨13, 2, 0, 296352, 101615, 725, 16384⟩
    (by decide) selected_cut_11033

theorem unmarked_context_12_25403_296353 : frontier 9 ⟨296353, by decide⟩
    (prefixCache 12 25403) (prefixPartial 12 25403) = false := by
  decide +kernel

theorem node_context_12_25403_296353 : EJMOriginalGlobalDAGData.nodes 9 ⟨296353, by decide⟩ =
    .split (coordinate 12) (![⟨296298, by decide⟩,⟨296326, by decide⟩,⟨296345, by decide⟩,⟨296352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25403_296353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25403 ⟨296353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25403
    ⟨296353, by decide⟩ (by decide) (![⟨296298, by decide⟩,⟨296326, by decide⟩,⟨296345, by decide⟩,⟨296352, by decide⟩]) unmarked_context_12_25403_296353 node_context_12_25403_296353
  intro a
  fin_cases a
  · exact context_13_101612_296298
  · exact context_13_101613_296326
  · exact context_13_101614_296345
  · exact context_13_101615_296352

theorem unmarked_context_11_6350_296354 : frontier 10 ⟨296354, by decide⟩
    (prefixCache 11 6350) (prefixPartial 11 6350) = false := by
  decide +kernel

theorem node_context_11_6350_296354 : EJMOriginalGlobalDAGData.nodes 10 ⟨296354, by decide⟩ =
    .split (coordinate 11) (![⟨296163, by decide⟩,⟨296227, by decide⟩,⟨296293, by decide⟩,⟨296353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6350_296354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6350 ⟨296354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6350
    ⟨296354, by decide⟩ (by decide) (![⟨296163, by decide⟩,⟨296227, by decide⟩,⟨296293, by decide⟩,⟨296353, by decide⟩]) unmarked_context_11_6350_296354 node_context_11_6350_296354
  intro a
  fin_cases a
  · exact context_12_25400_296163
  · exact context_12_25401_296227
  · exact context_12_25402_296293
  · exact context_12_25403_296353

theorem selected_cut_11034 : selected 9 ⟨296410, by decide⟩
    (prefixPartial 12 25404) = some ⟨12, 2, 0, 296410, 25404, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_25404_296410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25404 ⟨296410, by decide⟩ :=
  accepted_of_selected 12 25404 ⟨296410, by decide⟩ ⟨12, 2, 0, 296410, 25404, 3897, 65536⟩
    (by decide) selected_cut_11034

theorem selected_cut_11035 : selected 8 ⟨296414, by decide⟩
    (prefixPartial 13 101620) = some ⟨13, 2, 0, 296414, 101620, 69, 16384⟩ := by
  decide +kernel

theorem context_13_101620_296414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101620 ⟨296414, by decide⟩ :=
  accepted_of_selected 13 101620 ⟨296414, by decide⟩ ⟨13, 2, 0, 296414, 101620, 69, 16384⟩
    (by decide) selected_cut_11035

theorem selected_cut_11036 : selected 8 ⟨296443, by decide⟩
    (prefixPartial 13 101621) = some ⟨13, 2, 0, 296443, 101621, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_101621_296443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101621 ⟨296443, by decide⟩ :=
  accepted_of_selected 13 101621 ⟨296443, by decide⟩ ⟨13, 2, 0, 296443, 101621, 2137, 16384⟩
    (by decide) selected_cut_11036

theorem selected_cut_11037 : selected 8 ⟨296464, by decide⟩
    (prefixPartial 13 101622) = some ⟨13, 2, 0, 296464, 101622, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_101622_296464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101622 ⟨296464, by decide⟩ :=
  accepted_of_selected 13 101622 ⟨296464, by decide⟩ ⟨13, 2, 0, 296464, 101622, 1569, 16384⟩
    (by decide) selected_cut_11037

theorem selected_cut_11038 : selected 8 ⟨296472, by decide⟩
    (prefixPartial 13 101623) = some ⟨13, 2, 0, 296472, 101623, 741, 16384⟩ := by
  decide +kernel

theorem context_13_101623_296472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101623 ⟨296472, by decide⟩ :=
  accepted_of_selected 13 101623 ⟨296472, by decide⟩ ⟨13, 2, 0, 296472, 101623, 741, 16384⟩
    (by decide) selected_cut_11038

theorem unmarked_context_12_25405_296473 : frontier 9 ⟨296473, by decide⟩
    (prefixCache 12 25405) (prefixPartial 12 25405) = false := by
  decide +kernel

theorem node_context_12_25405_296473 : EJMOriginalGlobalDAGData.nodes 9 ⟨296473, by decide⟩ =
    .split (coordinate 12) (![⟨296414, by decide⟩,⟨296443, by decide⟩,⟨296464, by decide⟩,⟨296472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25405_296473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25405 ⟨296473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25405
    ⟨296473, by decide⟩ (by decide) (![⟨296414, by decide⟩,⟨296443, by decide⟩,⟨296464, by decide⟩,⟨296472, by decide⟩]) unmarked_context_12_25405_296473 node_context_12_25405_296473
  intro a
  fin_cases a
  · exact context_13_101620_296414
  · exact context_13_101621_296443
  · exact context_13_101622_296464
  · exact context_13_101623_296472

theorem selected_cut_11039 : selected 8 ⟨296477, by decide⟩
    (prefixPartial 13 101624) = some ⟨13, 2, 0, 296477, 101624, 57, 16384⟩ := by
  decide +kernel

theorem context_13_101624_296477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101624 ⟨296477, by decide⟩ :=
  accepted_of_selected 13 101624 ⟨296477, by decide⟩ ⟨13, 2, 0, 296477, 101624, 57, 16384⟩
    (by decide) selected_cut_11039

theorem selected_cut_11040 : selected 8 ⟨296500, by decide⟩
    (prefixPartial 13 101625) = some ⟨13, 2, 0, 296500, 101625, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_101625_296500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101625 ⟨296500, by decide⟩ :=
  accepted_of_selected 13 101625 ⟨296500, by decide⟩ ⟨13, 2, 0, 296500, 101625, 2293, 16384⟩
    (by decide) selected_cut_11040

theorem selected_cut_11041 : selected 8 ⟨296520, by decide⟩
    (prefixPartial 13 101626) = some ⟨13, 2, 0, 296520, 101626, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_101626_296520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101626 ⟨296520, by decide⟩ :=
  accepted_of_selected 13 101626 ⟨296520, by decide⟩ ⟨13, 2, 0, 296520, 101626, 1345, 16384⟩
    (by decide) selected_cut_11041

theorem selected_cut_11042 : selected 8 ⟨296528, by decide⟩
    (prefixPartial 13 101627) = some ⟨13, 2, 0, 296528, 101627, 733, 16384⟩ := by
  decide +kernel

theorem context_13_101627_296528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101627 ⟨296528, by decide⟩ :=
  accepted_of_selected 13 101627 ⟨296528, by decide⟩ ⟨13, 2, 0, 296528, 101627, 733, 16384⟩
    (by decide) selected_cut_11042

theorem unmarked_context_12_25406_296529 : frontier 9 ⟨296529, by decide⟩
    (prefixCache 12 25406) (prefixPartial 12 25406) = false := by
  decide +kernel

theorem node_context_12_25406_296529 : EJMOriginalGlobalDAGData.nodes 9 ⟨296529, by decide⟩ =
    .split (coordinate 12) (![⟨296477, by decide⟩,⟨296500, by decide⟩,⟨296520, by decide⟩,⟨296528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25406_296529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25406 ⟨296529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25406
    ⟨296529, by decide⟩ (by decide) (![⟨296477, by decide⟩,⟨296500, by decide⟩,⟨296520, by decide⟩,⟨296528, by decide⟩]) unmarked_context_12_25406_296529 node_context_12_25406_296529
  intro a
  fin_cases a
  · exact context_13_101624_296477
  · exact context_13_101625_296500
  · exact context_13_101626_296520
  · exact context_13_101627_296528

theorem selected_cut_11043 : selected 9 ⟨296530, by decide⟩
    (prefixPartial 12 25407) = some ⟨12, 1, 0, 296530, 25407, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25407_296530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25407 ⟨296530, by decide⟩ :=
  accepted_of_selected 12 25407 ⟨296530, by decide⟩ ⟨12, 1, 0, 296530, 25407, 1, 65536⟩
    (by decide) selected_cut_11043

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
