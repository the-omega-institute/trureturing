/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover072
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_22062_206229 : frontier 9 ⟨206229, by decide⟩
    (prefixCache 12 22062) (prefixPartial 12 22062) = false := by
  decide +kernel

theorem node_context_12_22062_206229 : EJMOriginalGlobalDAGData.nodes 9 ⟨206229, by decide⟩ =
    .split (coordinate 12) (![⟨206182, by decide⟩,⟨206211, by decide⟩,⟨206223, by decide⟩,⟨206228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22062_206229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22062 ⟨206229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22062
    ⟨206229, by decide⟩ (by decide) (![⟨206182, by decide⟩,⟨206211, by decide⟩,⟨206223, by decide⟩,⟨206228, by decide⟩]) unmarked_context_12_22062_206229 node_context_12_22062_206229
  intro a
  fin_cases a
  · exact context_13_88248_206182
  · exact context_13_88249_206211
  · exact context_13_88250_206223
  · exact context_13_88251_206228

theorem selected_cut_07012 : selected 8 ⟨206238, by decide⟩
    (prefixPartial 13 88252) = some ⟨13, 2, 0, 206238, 88252, 565, 16384⟩ := by
  decide +kernel

theorem context_13_88252_206238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88252 ⟨206238, by decide⟩ :=
  accepted_of_selected 13 88252 ⟨206238, by decide⟩ ⟨13, 2, 0, 206238, 88252, 565, 16384⟩
    (by decide) selected_cut_07012

theorem selected_cut_07013 : selected 8 ⟨206272, by decide⟩
    (prefixPartial 13 88253) = some ⟨13, 2, 0, 206272, 88253, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_88253_206272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88253 ⟨206272, by decide⟩ :=
  accepted_of_selected 13 88253 ⟨206272, by decide⟩ ⟨13, 2, 0, 206272, 88253, 2537, 16384⟩
    (by decide) selected_cut_07013

theorem selected_cut_07014 : selected 8 ⟨206290, by decide⟩
    (prefixPartial 13 88254) = some ⟨13, 2, 0, 206290, 88254, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_88254_206290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88254 ⟨206290, by decide⟩ :=
  accepted_of_selected 13 88254 ⟨206290, by decide⟩ ⟨13, 2, 0, 206290, 88254, 1441, 16384⟩
    (by decide) selected_cut_07014

theorem selected_cut_07015 : selected 8 ⟨206296, by decide⟩
    (prefixPartial 13 88255) = some ⟨13, 2, 0, 206296, 88255, 721, 16384⟩ := by
  decide +kernel

theorem context_13_88255_206296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88255 ⟨206296, by decide⟩ :=
  accepted_of_selected 13 88255 ⟨206296, by decide⟩ ⟨13, 2, 0, 206296, 88255, 721, 16384⟩
    (by decide) selected_cut_07015

theorem unmarked_context_12_22063_206297 : frontier 9 ⟨206297, by decide⟩
    (prefixCache 12 22063) (prefixPartial 12 22063) = false := by
  decide +kernel

theorem node_context_12_22063_206297 : EJMOriginalGlobalDAGData.nodes 9 ⟨206297, by decide⟩ =
    .split (coordinate 12) (![⟨206238, by decide⟩,⟨206272, by decide⟩,⟨206290, by decide⟩,⟨206296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22063_206297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22063 ⟨206297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22063
    ⟨206297, by decide⟩ (by decide) (![⟨206238, by decide⟩,⟨206272, by decide⟩,⟨206290, by decide⟩,⟨206296, by decide⟩]) unmarked_context_12_22063_206297 node_context_12_22063_206297
  intro a
  fin_cases a
  · exact context_13_88252_206238
  · exact context_13_88253_206272
  · exact context_13_88254_206290
  · exact context_13_88255_206296

theorem unmarked_context_11_5515_206298 : frontier 10 ⟨206298, by decide⟩
    (prefixCache 11 5515) (prefixPartial 11 5515) = false := by
  decide +kernel

theorem node_context_11_5515_206298 : EJMOriginalGlobalDAGData.nodes 10 ⟨206298, by decide⟩ =
    .split (coordinate 11) (![⟨206113, by decide⟩,⟨206173, by decide⟩,⟨206229, by decide⟩,⟨206297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5515_206298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5515 ⟨206298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5515
    ⟨206298, by decide⟩ (by decide) (![⟨206113, by decide⟩,⟨206173, by decide⟩,⟨206229, by decide⟩,⟨206297, by decide⟩]) unmarked_context_11_5515_206298 node_context_11_5515_206298
  intro a
  fin_cases a
  · exact context_12_22060_206113
  · exact context_12_22061_206173
  · exact context_12_22062_206229
  · exact context_12_22063_206297

theorem unmarked_context_10_1378_206299 : frontier 11 ⟨206299, by decide⟩
    (prefixCache 10 1378) (prefixPartial 10 1378) = false := by
  decide +kernel

theorem node_context_10_1378_206299 : EJMOriginalGlobalDAGData.nodes 11 ⟨206299, by decide⟩ =
    .split (coordinate 10) (![⟨205476, by decide⟩,⟨205753, by decide⟩,⟨206058, by decide⟩,⟨206298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1378_206299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1378 ⟨206299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1378
    ⟨206299, by decide⟩ (by decide) (![⟨205476, by decide⟩,⟨205753, by decide⟩,⟨206058, by decide⟩,⟨206298, by decide⟩]) unmarked_context_10_1378_206299 node_context_10_1378_206299
  intro a
  fin_cases a
  · exact context_11_5512_205476
  · exact context_11_5513_205753
  · exact context_11_5514_206058
  · exact context_11_5515_206298

theorem selected_cut_07016 : selected 8 ⟨206306, by decide⟩
    (prefixPartial 13 88256) = some ⟨13, 2, 0, 206306, 88256, 561, 16384⟩ := by
  decide +kernel

theorem context_13_88256_206306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88256 ⟨206306, by decide⟩ :=
  accepted_of_selected 13 88256 ⟨206306, by decide⟩ ⟨13, 2, 0, 206306, 88256, 561, 16384⟩
    (by decide) selected_cut_07016

theorem selected_cut_07017 : selected 8 ⟨206329, by decide⟩
    (prefixPartial 13 88257) = some ⟨13, 2, 0, 206329, 88257, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_88257_206329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88257 ⟨206329, by decide⟩ :=
  accepted_of_selected 13 88257 ⟨206329, by decide⟩ ⟨13, 2, 0, 206329, 88257, 1909, 16384⟩
    (by decide) selected_cut_07017

theorem selected_cut_07018 : selected 8 ⟨206347, by decide⟩
    (prefixPartial 13 88258) = some ⟨13, 2, 0, 206347, 88258, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_88258_206347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88258 ⟨206347, by decide⟩ :=
  accepted_of_selected 13 88258 ⟨206347, by decide⟩ ⟨13, 2, 0, 206347, 88258, 1349, 16384⟩
    (by decide) selected_cut_07018

theorem selected_cut_07019 : selected 8 ⟨206352, by decide⟩
    (prefixPartial 13 88259) = some ⟨13, 2, 0, 206352, 88259, 681, 16384⟩ := by
  decide +kernel

theorem context_13_88259_206352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88259 ⟨206352, by decide⟩ :=
  accepted_of_selected 13 88259 ⟨206352, by decide⟩ ⟨13, 2, 0, 206352, 88259, 681, 16384⟩
    (by decide) selected_cut_07019

theorem unmarked_context_12_22064_206353 : frontier 9 ⟨206353, by decide⟩
    (prefixCache 12 22064) (prefixPartial 12 22064) = false := by
  decide +kernel

theorem node_context_12_22064_206353 : EJMOriginalGlobalDAGData.nodes 9 ⟨206353, by decide⟩ =
    .split (coordinate 12) (![⟨206306, by decide⟩,⟨206329, by decide⟩,⟨206347, by decide⟩,⟨206352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22064_206353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22064 ⟨206353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22064
    ⟨206353, by decide⟩ (by decide) (![⟨206306, by decide⟩,⟨206329, by decide⟩,⟨206347, by decide⟩,⟨206352, by decide⟩]) unmarked_context_12_22064_206353 node_context_12_22064_206353
  intro a
  fin_cases a
  · exact context_13_88256_206306
  · exact context_13_88257_206329
  · exact context_13_88258_206347
  · exact context_13_88259_206352

theorem selected_cut_07020 : selected 8 ⟨206360, by decide⟩
    (prefixPartial 13 88260) = some ⟨13, 2, 0, 206360, 88260, 649, 16384⟩ := by
  decide +kernel

theorem context_13_88260_206360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88260 ⟨206360, by decide⟩ :=
  accepted_of_selected 13 88260 ⟨206360, by decide⟩ ⟨13, 2, 0, 206360, 88260, 649, 16384⟩
    (by decide) selected_cut_07020

theorem selected_cut_07021 : selected 8 ⟨206390, by decide⟩
    (prefixPartial 13 88261) = some ⟨13, 2, 0, 206390, 88261, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_88261_206390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88261 ⟨206390, by decide⟩ :=
  accepted_of_selected 13 88261 ⟨206390, by decide⟩ ⟨13, 2, 0, 206390, 88261, 1993, 16384⟩
    (by decide) selected_cut_07021

theorem selected_cut_07022 : selected 8 ⟨206407, by decide⟩
    (prefixPartial 13 88262) = some ⟨13, 2, 0, 206407, 88262, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_88262_206407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88262 ⟨206407, by decide⟩ :=
  accepted_of_selected 13 88262 ⟨206407, by decide⟩ ⟨13, 2, 0, 206407, 88262, 1221, 16384⟩
    (by decide) selected_cut_07022

theorem selected_cut_07023 : selected 8 ⟨206414, by decide⟩
    (prefixPartial 13 88263) = some ⟨13, 2, 0, 206414, 88263, 789, 16384⟩ := by
  decide +kernel

theorem context_13_88263_206414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88263 ⟨206414, by decide⟩ :=
  accepted_of_selected 13 88263 ⟨206414, by decide⟩ ⟨13, 2, 0, 206414, 88263, 789, 16384⟩
    (by decide) selected_cut_07023

theorem unmarked_context_12_22065_206415 : frontier 9 ⟨206415, by decide⟩
    (prefixCache 12 22065) (prefixPartial 12 22065) = false := by
  decide +kernel

theorem node_context_12_22065_206415 : EJMOriginalGlobalDAGData.nodes 9 ⟨206415, by decide⟩ =
    .split (coordinate 12) (![⟨206360, by decide⟩,⟨206390, by decide⟩,⟨206407, by decide⟩,⟨206414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22065_206415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22065 ⟨206415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22065
    ⟨206415, by decide⟩ (by decide) (![⟨206360, by decide⟩,⟨206390, by decide⟩,⟨206407, by decide⟩,⟨206414, by decide⟩]) unmarked_context_12_22065_206415 node_context_12_22065_206415
  intro a
  fin_cases a
  · exact context_13_88260_206360
  · exact context_13_88261_206390
  · exact context_13_88262_206407
  · exact context_13_88263_206414

theorem selected_cut_07024 : selected 8 ⟨206423, by decide⟩
    (prefixPartial 13 88264) = some ⟨13, 2, 0, 206423, 88264, 597, 16384⟩ := by
  decide +kernel

theorem context_13_88264_206423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88264 ⟨206423, by decide⟩ :=
  accepted_of_selected 13 88264 ⟨206423, by decide⟩ ⟨13, 2, 0, 206423, 88264, 597, 16384⟩
    (by decide) selected_cut_07024

theorem selected_cut_07025 : selected 8 ⟨206462, by decide⟩
    (prefixPartial 13 88265) = some ⟨13, 2, 0, 206462, 88265, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_88265_206462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88265 ⟨206462, by decide⟩ :=
  accepted_of_selected 13 88265 ⟨206462, by decide⟩ ⟨13, 2, 0, 206462, 88265, 2369, 16384⟩
    (by decide) selected_cut_07025

theorem selected_cut_07026 : selected 8 ⟨206474, by decide⟩
    (prefixPartial 13 88266) = some ⟨13, 2, 0, 206474, 88266, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_88266_206474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88266 ⟨206474, by decide⟩ :=
  accepted_of_selected 13 88266 ⟨206474, by decide⟩ ⟨13, 2, 0, 206474, 88266, 1073, 16384⟩
    (by decide) selected_cut_07026

theorem selected_cut_07027 : selected 8 ⟨206481, by decide⟩
    (prefixPartial 13 88267) = some ⟨13, 2, 0, 206481, 88267, 805, 16384⟩ := by
  decide +kernel

theorem context_13_88267_206481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88267 ⟨206481, by decide⟩ :=
  accepted_of_selected 13 88267 ⟨206481, by decide⟩ ⟨13, 2, 0, 206481, 88267, 805, 16384⟩
    (by decide) selected_cut_07027

theorem unmarked_context_12_22066_206482 : frontier 9 ⟨206482, by decide⟩
    (prefixCache 12 22066) (prefixPartial 12 22066) = false := by
  decide +kernel

theorem node_context_12_22066_206482 : EJMOriginalGlobalDAGData.nodes 9 ⟨206482, by decide⟩ =
    .split (coordinate 12) (![⟨206423, by decide⟩,⟨206462, by decide⟩,⟨206474, by decide⟩,⟨206481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22066_206482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22066 ⟨206482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22066
    ⟨206482, by decide⟩ (by decide) (![⟨206423, by decide⟩,⟨206462, by decide⟩,⟨206474, by decide⟩,⟨206481, by decide⟩]) unmarked_context_12_22066_206482 node_context_12_22066_206482
  intro a
  fin_cases a
  · exact context_13_88264_206423
  · exact context_13_88265_206462
  · exact context_13_88266_206474
  · exact context_13_88267_206481

theorem selected_cut_07028 : selected 8 ⟨206494, by decide⟩
    (prefixPartial 13 88268) = some ⟨13, 2, 0, 206494, 88268, 805, 16384⟩ := by
  decide +kernel

theorem context_13_88268_206494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88268 ⟨206494, by decide⟩ :=
  accepted_of_selected 13 88268 ⟨206494, by decide⟩ ⟨13, 2, 0, 206494, 88268, 805, 16384⟩
    (by decide) selected_cut_07028

theorem selected_cut_07029 : selected 8 ⟨206537, by decide⟩
    (prefixPartial 13 88269) = some ⟨13, 2, 0, 206537, 88269, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_88269_206537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88269 ⟨206537, by decide⟩ :=
  accepted_of_selected 13 88269 ⟨206537, by decide⟩ ⟨13, 2, 0, 206537, 88269, 2765, 16384⟩
    (by decide) selected_cut_07029

theorem selected_cut_07030 : selected 8 ⟨206553, by decide⟩
    (prefixPartial 13 88270) = some ⟨13, 2, 0, 206553, 88270, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_88270_206553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88270 ⟨206553, by decide⟩ :=
  accepted_of_selected 13 88270 ⟨206553, by decide⟩ ⟨13, 2, 0, 206553, 88270, 1329, 16384⟩
    (by decide) selected_cut_07030

theorem selected_cut_07031 : selected 8 ⟨206557, by decide⟩
    (prefixPartial 13 88271) = some ⟨13, 2, 0, 206557, 88271, 737, 16384⟩ := by
  decide +kernel

theorem context_13_88271_206557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88271 ⟨206557, by decide⟩ :=
  accepted_of_selected 13 88271 ⟨206557, by decide⟩ ⟨13, 2, 0, 206557, 88271, 737, 16384⟩
    (by decide) selected_cut_07031

theorem unmarked_context_12_22067_206558 : frontier 9 ⟨206558, by decide⟩
    (prefixCache 12 22067) (prefixPartial 12 22067) = false := by
  decide +kernel

theorem node_context_12_22067_206558 : EJMOriginalGlobalDAGData.nodes 9 ⟨206558, by decide⟩ =
    .split (coordinate 12) (![⟨206494, by decide⟩,⟨206537, by decide⟩,⟨206553, by decide⟩,⟨206557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22067_206558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22067 ⟨206558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22067
    ⟨206558, by decide⟩ (by decide) (![⟨206494, by decide⟩,⟨206537, by decide⟩,⟨206553, by decide⟩,⟨206557, by decide⟩]) unmarked_context_12_22067_206558 node_context_12_22067_206558
  intro a
  fin_cases a
  · exact context_13_88268_206494
  · exact context_13_88269_206537
  · exact context_13_88270_206553
  · exact context_13_88271_206557

theorem unmarked_context_11_5516_206559 : frontier 10 ⟨206559, by decide⟩
    (prefixCache 11 5516) (prefixPartial 11 5516) = false := by
  decide +kernel

theorem node_context_11_5516_206559 : EJMOriginalGlobalDAGData.nodes 10 ⟨206559, by decide⟩ =
    .split (coordinate 11) (![⟨206353, by decide⟩,⟨206415, by decide⟩,⟨206482, by decide⟩,⟨206558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5516_206559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5516 ⟨206559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5516
    ⟨206559, by decide⟩ (by decide) (![⟨206353, by decide⟩,⟨206415, by decide⟩,⟨206482, by decide⟩,⟨206558, by decide⟩]) unmarked_context_11_5516_206559 node_context_11_5516_206559
  intro a
  fin_cases a
  · exact context_12_22064_206353
  · exact context_12_22065_206415
  · exact context_12_22066_206482
  · exact context_12_22067_206558

theorem selected_cut_07032 : selected 8 ⟨206567, by decide⟩
    (prefixPartial 13 88272) = some ⟨13, 2, 0, 206567, 88272, 425, 16384⟩ := by
  decide +kernel

theorem context_13_88272_206567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88272 ⟨206567, by decide⟩ :=
  accepted_of_selected 13 88272 ⟨206567, by decide⟩ ⟨13, 2, 0, 206567, 88272, 425, 16384⟩
    (by decide) selected_cut_07032

theorem selected_cut_07033 : selected 8 ⟨206603, by decide⟩
    (prefixPartial 13 88273) = some ⟨13, 2, 0, 206603, 88273, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_88273_206603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88273 ⟨206603, by decide⟩ :=
  accepted_of_selected 13 88273 ⟨206603, by decide⟩ ⟨13, 2, 0, 206603, 88273, 2473, 16384⟩
    (by decide) selected_cut_07033

theorem selected_cut_07034 : selected 8 ⟨206621, by decide⟩
    (prefixPartial 13 88274) = some ⟨13, 2, 0, 206621, 88274, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_88274_206621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88274 ⟨206621, by decide⟩ :=
  accepted_of_selected 13 88274 ⟨206621, by decide⟩ ⟨13, 2, 0, 206621, 88274, 1373, 16384⟩
    (by decide) selected_cut_07034

theorem selected_cut_07035 : selected 8 ⟨206629, by decide⟩
    (prefixPartial 13 88275) = some ⟨13, 2, 0, 206629, 88275, 821, 16384⟩ := by
  decide +kernel

theorem context_13_88275_206629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88275 ⟨206629, by decide⟩ :=
  accepted_of_selected 13 88275 ⟨206629, by decide⟩ ⟨13, 2, 0, 206629, 88275, 821, 16384⟩
    (by decide) selected_cut_07035

theorem unmarked_context_12_22068_206630 : frontier 9 ⟨206630, by decide⟩
    (prefixCache 12 22068) (prefixPartial 12 22068) = false := by
  decide +kernel

theorem node_context_12_22068_206630 : EJMOriginalGlobalDAGData.nodes 9 ⟨206630, by decide⟩ =
    .split (coordinate 12) (![⟨206567, by decide⟩,⟨206603, by decide⟩,⟨206621, by decide⟩,⟨206629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22068_206630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22068 ⟨206630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22068
    ⟨206630, by decide⟩ (by decide) (![⟨206567, by decide⟩,⟨206603, by decide⟩,⟨206621, by decide⟩,⟨206629, by decide⟩]) unmarked_context_12_22068_206630 node_context_12_22068_206630
  intro a
  fin_cases a
  · exact context_13_88272_206567
  · exact context_13_88273_206603
  · exact context_13_88274_206621
  · exact context_13_88275_206629

theorem selected_cut_07036 : selected 8 ⟨206637, by decide⟩
    (prefixPartial 13 88276) = some ⟨13, 2, 0, 206637, 88276, 445, 16384⟩ := by
  decide +kernel

theorem context_13_88276_206637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88276 ⟨206637, by decide⟩ :=
  accepted_of_selected 13 88276 ⟨206637, by decide⟩ ⟨13, 2, 0, 206637, 88276, 445, 16384⟩
    (by decide) selected_cut_07036

theorem selected_cut_07037 : selected 8 ⟨206666, by decide⟩
    (prefixPartial 13 88277) = some ⟨13, 2, 0, 206666, 88277, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_88277_206666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88277 ⟨206666, by decide⟩ :=
  accepted_of_selected 13 88277 ⟨206666, by decide⟩ ⟨13, 2, 0, 206666, 88277, 2057, 16384⟩
    (by decide) selected_cut_07037

theorem selected_cut_07038 : selected 8 ⟨206686, by decide⟩
    (prefixPartial 13 88278) = some ⟨13, 2, 0, 206686, 88278, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_88278_206686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88278 ⟨206686, by decide⟩ :=
  accepted_of_selected 13 88278 ⟨206686, by decide⟩ ⟨13, 2, 0, 206686, 88278, 1245, 16384⟩
    (by decide) selected_cut_07038

theorem selected_cut_07039 : selected 8 ⟨206692, by decide⟩
    (prefixPartial 13 88279) = some ⟨13, 2, 0, 206692, 88279, 749, 16384⟩ := by
  decide +kernel

theorem context_13_88279_206692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88279 ⟨206692, by decide⟩ :=
  accepted_of_selected 13 88279 ⟨206692, by decide⟩ ⟨13, 2, 0, 206692, 88279, 749, 16384⟩
    (by decide) selected_cut_07039

theorem unmarked_context_12_22069_206693 : frontier 9 ⟨206693, by decide⟩
    (prefixCache 12 22069) (prefixPartial 12 22069) = false := by
  decide +kernel

theorem node_context_12_22069_206693 : EJMOriginalGlobalDAGData.nodes 9 ⟨206693, by decide⟩ =
    .split (coordinate 12) (![⟨206637, by decide⟩,⟨206666, by decide⟩,⟨206686, by decide⟩,⟨206692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22069_206693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22069 ⟨206693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22069
    ⟨206693, by decide⟩ (by decide) (![⟨206637, by decide⟩,⟨206666, by decide⟩,⟨206686, by decide⟩,⟨206692, by decide⟩]) unmarked_context_12_22069_206693 node_context_12_22069_206693
  intro a
  fin_cases a
  · exact context_13_88276_206637
  · exact context_13_88277_206666
  · exact context_13_88278_206686
  · exact context_13_88279_206692

theorem selected_cut_07040 : selected 8 ⟨206699, by decide⟩
    (prefixPartial 13 88280) = some ⟨13, 2, 0, 206699, 88280, 413, 16384⟩ := by
  decide +kernel

theorem context_13_88280_206699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88280 ⟨206699, by decide⟩ :=
  accepted_of_selected 13 88280 ⟨206699, by decide⟩ ⟨13, 2, 0, 206699, 88280, 413, 16384⟩
    (by decide) selected_cut_07040

theorem selected_cut_07041 : selected 8 ⟨206729, by decide⟩
    (prefixPartial 13 88281) = some ⟨13, 2, 0, 206729, 88281, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_88281_206729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88281 ⟨206729, by decide⟩ :=
  accepted_of_selected 13 88281 ⟨206729, by decide⟩ ⟨13, 2, 0, 206729, 88281, 2321, 16384⟩
    (by decide) selected_cut_07041

theorem selected_cut_07042 : selected 8 ⟨206742, by decide⟩
    (prefixPartial 13 88282) = some ⟨13, 2, 0, 206742, 88282, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_88282_206742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88282 ⟨206742, by decide⟩ :=
  accepted_of_selected 13 88282 ⟨206742, by decide⟩ ⟨13, 2, 0, 206742, 88282, 1013, 16384⟩
    (by decide) selected_cut_07042

theorem selected_cut_07043 : selected 8 ⟨206749, by decide⟩
    (prefixPartial 13 88283) = some ⟨13, 2, 0, 206749, 88283, 849, 16384⟩ := by
  decide +kernel

theorem context_13_88283_206749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88283 ⟨206749, by decide⟩ :=
  accepted_of_selected 13 88283 ⟨206749, by decide⟩ ⟨13, 2, 0, 206749, 88283, 849, 16384⟩
    (by decide) selected_cut_07043

theorem unmarked_context_12_22070_206750 : frontier 9 ⟨206750, by decide⟩
    (prefixCache 12 22070) (prefixPartial 12 22070) = false := by
  decide +kernel

theorem node_context_12_22070_206750 : EJMOriginalGlobalDAGData.nodes 9 ⟨206750, by decide⟩ =
    .split (coordinate 12) (![⟨206699, by decide⟩,⟨206729, by decide⟩,⟨206742, by decide⟩,⟨206749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22070_206750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22070 ⟨206750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22070
    ⟨206750, by decide⟩ (by decide) (![⟨206699, by decide⟩,⟨206729, by decide⟩,⟨206742, by decide⟩,⟨206749, by decide⟩]) unmarked_context_12_22070_206750 node_context_12_22070_206750
  intro a
  fin_cases a
  · exact context_13_88280_206699
  · exact context_13_88281_206729
  · exact context_13_88282_206742
  · exact context_13_88283_206749

theorem selected_cut_07044 : selected 8 ⟨206760, by decide⟩
    (prefixPartial 13 88284) = some ⟨13, 2, 0, 206760, 88284, 525, 16384⟩ := by
  decide +kernel

theorem context_13_88284_206760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88284 ⟨206760, by decide⟩ :=
  accepted_of_selected 13 88284 ⟨206760, by decide⟩ ⟨13, 2, 0, 206760, 88284, 525, 16384⟩
    (by decide) selected_cut_07044

theorem selected_cut_07045 : selected 8 ⟨206797, by decide⟩
    (prefixPartial 13 88285) = some ⟨13, 2, 0, 206797, 88285, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_88285_206797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88285 ⟨206797, by decide⟩ :=
  accepted_of_selected 13 88285 ⟨206797, by decide⟩ ⟨13, 2, 0, 206797, 88285, 2713, 16384⟩
    (by decide) selected_cut_07045

theorem selected_cut_07046 : selected 8 ⟨206818, by decide⟩
    (prefixPartial 13 88286) = some ⟨13, 2, 0, 206818, 88286, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_88286_206818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88286 ⟨206818, by decide⟩ :=
  accepted_of_selected 13 88286 ⟨206818, by decide⟩ ⟨13, 2, 0, 206818, 88286, 1477, 16384⟩
    (by decide) selected_cut_07046

theorem selected_cut_07047 : selected 8 ⟨206824, by decide⟩
    (prefixPartial 13 88287) = some ⟨13, 2, 0, 206824, 88287, 717, 16384⟩ := by
  decide +kernel

theorem context_13_88287_206824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88287 ⟨206824, by decide⟩ :=
  accepted_of_selected 13 88287 ⟨206824, by decide⟩ ⟨13, 2, 0, 206824, 88287, 717, 16384⟩
    (by decide) selected_cut_07047

theorem unmarked_context_12_22071_206825 : frontier 9 ⟨206825, by decide⟩
    (prefixCache 12 22071) (prefixPartial 12 22071) = false := by
  decide +kernel

theorem node_context_12_22071_206825 : EJMOriginalGlobalDAGData.nodes 9 ⟨206825, by decide⟩ =
    .split (coordinate 12) (![⟨206760, by decide⟩,⟨206797, by decide⟩,⟨206818, by decide⟩,⟨206824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22071_206825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22071 ⟨206825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22071
    ⟨206825, by decide⟩ (by decide) (![⟨206760, by decide⟩,⟨206797, by decide⟩,⟨206818, by decide⟩,⟨206824, by decide⟩]) unmarked_context_12_22071_206825 node_context_12_22071_206825
  intro a
  fin_cases a
  · exact context_13_88284_206760
  · exact context_13_88285_206797
  · exact context_13_88286_206818
  · exact context_13_88287_206824

theorem unmarked_context_11_5517_206826 : frontier 10 ⟨206826, by decide⟩
    (prefixCache 11 5517) (prefixPartial 11 5517) = false := by
  decide +kernel

theorem node_context_11_5517_206826 : EJMOriginalGlobalDAGData.nodes 10 ⟨206826, by decide⟩ =
    .split (coordinate 11) (![⟨206630, by decide⟩,⟨206693, by decide⟩,⟨206750, by decide⟩,⟨206825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5517_206826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5517 ⟨206826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5517
    ⟨206826, by decide⟩ (by decide) (![⟨206630, by decide⟩,⟨206693, by decide⟩,⟨206750, by decide⟩,⟨206825, by decide⟩]) unmarked_context_11_5517_206826 node_context_11_5517_206826
  intro a
  fin_cases a
  · exact context_12_22068_206630
  · exact context_12_22069_206693
  · exact context_12_22070_206750
  · exact context_12_22071_206825

theorem selected_cut_07048 : selected 8 ⟨206830, by decide⟩
    (prefixPartial 13 88288) = some ⟨13, 2, 0, 206830, 88288, 293, 16384⟩ := by
  decide +kernel

theorem context_13_88288_206830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88288 ⟨206830, by decide⟩ :=
  accepted_of_selected 13 88288 ⟨206830, by decide⟩ ⟨13, 2, 0, 206830, 88288, 293, 16384⟩
    (by decide) selected_cut_07048

theorem selected_cut_07049 : selected 8 ⟨206858, by decide⟩
    (prefixPartial 13 88289) = some ⟨13, 2, 0, 206858, 88289, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_88289_206858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88289 ⟨206858, by decide⟩ :=
  accepted_of_selected 13 88289 ⟨206858, by decide⟩ ⟨13, 2, 0, 206858, 88289, 2101, 16384⟩
    (by decide) selected_cut_07049

theorem selected_cut_07050 : selected 8 ⟨206870, by decide⟩
    (prefixPartial 13 88290) = some ⟨13, 2, 0, 206870, 88290, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_88290_206870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88290 ⟨206870, by decide⟩ :=
  accepted_of_selected 13 88290 ⟨206870, by decide⟩ ⟨13, 2, 0, 206870, 88290, 1305, 16384⟩
    (by decide) selected_cut_07050

theorem selected_cut_07051 : selected 8 ⟨206877, by decide⟩
    (prefixPartial 13 88291) = some ⟨13, 2, 0, 206877, 88291, 797, 16384⟩ := by
  decide +kernel

theorem context_13_88291_206877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88291 ⟨206877, by decide⟩ :=
  accepted_of_selected 13 88291 ⟨206877, by decide⟩ ⟨13, 2, 0, 206877, 88291, 797, 16384⟩
    (by decide) selected_cut_07051

theorem unmarked_context_12_22072_206878 : frontier 9 ⟨206878, by decide⟩
    (prefixCache 12 22072) (prefixPartial 12 22072) = false := by
  decide +kernel

theorem node_context_12_22072_206878 : EJMOriginalGlobalDAGData.nodes 9 ⟨206878, by decide⟩ =
    .split (coordinate 12) (![⟨206830, by decide⟩,⟨206858, by decide⟩,⟨206870, by decide⟩,⟨206877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22072_206878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22072 ⟨206878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22072
    ⟨206878, by decide⟩ (by decide) (![⟨206830, by decide⟩,⟨206858, by decide⟩,⟨206870, by decide⟩,⟨206877, by decide⟩]) unmarked_context_12_22072_206878 node_context_12_22072_206878
  intro a
  fin_cases a
  · exact context_13_88288_206830
  · exact context_13_88289_206858
  · exact context_13_88290_206870
  · exact context_13_88291_206877

theorem selected_cut_07052 : selected 8 ⟨206884, by decide⟩
    (prefixPartial 13 88292) = some ⟨13, 2, 0, 206884, 88292, 309, 16384⟩ := by
  decide +kernel

theorem context_13_88292_206884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88292 ⟨206884, by decide⟩ :=
  accepted_of_selected 13 88292 ⟨206884, by decide⟩ ⟨13, 2, 0, 206884, 88292, 309, 16384⟩
    (by decide) selected_cut_07052

theorem selected_cut_07053 : selected 8 ⟨206913, by decide⟩
    (prefixPartial 13 88293) = some ⟨13, 2, 0, 206913, 88293, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_88293_206913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88293 ⟨206913, by decide⟩ :=
  accepted_of_selected 13 88293 ⟨206913, by decide⟩ ⟨13, 2, 0, 206913, 88293, 1861, 16384⟩
    (by decide) selected_cut_07053

theorem selected_cut_07054 : selected 8 ⟨206931, by decide⟩
    (prefixPartial 13 88294) = some ⟨13, 2, 0, 206931, 88294, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_88294_206931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88294 ⟨206931, by decide⟩ :=
  accepted_of_selected 13 88294 ⟨206931, by decide⟩ ⟨13, 2, 0, 206931, 88294, 1217, 16384⟩
    (by decide) selected_cut_07054

theorem selected_cut_07055 : selected 8 ⟨206937, by decide⟩
    (prefixPartial 13 88295) = some ⟨13, 2, 0, 206937, 88295, 781, 16384⟩ := by
  decide +kernel

theorem context_13_88295_206937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88295 ⟨206937, by decide⟩ :=
  accepted_of_selected 13 88295 ⟨206937, by decide⟩ ⟨13, 2, 0, 206937, 88295, 781, 16384⟩
    (by decide) selected_cut_07055

theorem unmarked_context_12_22073_206938 : frontier 9 ⟨206938, by decide⟩
    (prefixCache 12 22073) (prefixPartial 12 22073) = false := by
  decide +kernel

theorem node_context_12_22073_206938 : EJMOriginalGlobalDAGData.nodes 9 ⟨206938, by decide⟩ =
    .split (coordinate 12) (![⟨206884, by decide⟩,⟨206913, by decide⟩,⟨206931, by decide⟩,⟨206937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22073_206938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22073 ⟨206938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22073
    ⟨206938, by decide⟩ (by decide) (![⟨206884, by decide⟩,⟨206913, by decide⟩,⟨206931, by decide⟩,⟨206937, by decide⟩]) unmarked_context_12_22073_206938 node_context_12_22073_206938
  intro a
  fin_cases a
  · exact context_13_88292_206884
  · exact context_13_88293_206913
  · exact context_13_88294_206931
  · exact context_13_88295_206937

theorem selected_cut_07056 : selected 8 ⟨206948, by decide⟩
    (prefixPartial 13 88296) = some ⟨13, 2, 0, 206948, 88296, 445, 16384⟩ := by
  decide +kernel

theorem context_13_88296_206948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88296 ⟨206948, by decide⟩ :=
  accepted_of_selected 13 88296 ⟨206948, by decide⟩ ⟨13, 2, 0, 206948, 88296, 445, 16384⟩
    (by decide) selected_cut_07056

theorem selected_cut_07057 : selected 8 ⟨207025, by decide⟩
    (prefixPartial 13 88297) = some ⟨13, 2, 0, 207025, 88297, 4025, 16384⟩ := by
  decide +kernel

theorem context_13_88297_207025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88297 ⟨207025, by decide⟩ :=
  accepted_of_selected 13 88297 ⟨207025, by decide⟩ ⟨13, 2, 0, 207025, 88297, 4025, 16384⟩
    (by decide) selected_cut_07057

theorem selected_cut_07058 : selected 8 ⟨207045, by decide⟩
    (prefixPartial 13 88298) = some ⟨13, 2, 0, 207045, 88298, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_88298_207045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88298 ⟨207045, by decide⟩ :=
  accepted_of_selected 13 88298 ⟨207045, by decide⟩ ⟨13, 2, 0, 207045, 88298, 1901, 16384⟩
    (by decide) selected_cut_07058

theorem selected_cut_07059 : selected 8 ⟨207058, by decide⟩
    (prefixPartial 13 88299) = some ⟨13, 2, 0, 207058, 88299, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_88299_207058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88299 ⟨207058, by decide⟩ :=
  accepted_of_selected 13 88299 ⟨207058, by decide⟩ ⟨13, 2, 0, 207058, 88299, 1185, 16384⟩
    (by decide) selected_cut_07059

theorem unmarked_context_12_22074_207059 : frontier 9 ⟨207059, by decide⟩
    (prefixCache 12 22074) (prefixPartial 12 22074) = false := by
  decide +kernel

theorem node_context_12_22074_207059 : EJMOriginalGlobalDAGData.nodes 9 ⟨207059, by decide⟩ =
    .split (coordinate 12) (![⟨206948, by decide⟩,⟨207025, by decide⟩,⟨207045, by decide⟩,⟨207058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22074_207059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22074 ⟨207059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22074
    ⟨207059, by decide⟩ (by decide) (![⟨206948, by decide⟩,⟨207025, by decide⟩,⟨207045, by decide⟩,⟨207058, by decide⟩]) unmarked_context_12_22074_207059 node_context_12_22074_207059
  intro a
  fin_cases a
  · exact context_13_88296_206948
  · exact context_13_88297_207025
  · exact context_13_88298_207045
  · exact context_13_88299_207058

theorem selected_cut_07060 : selected 8 ⟨207065, by decide⟩
    (prefixPartial 13 88300) = some ⟨13, 2, 0, 207065, 88300, 233, 16384⟩ := by
  decide +kernel

theorem context_13_88300_207065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88300 ⟨207065, by decide⟩ :=
  accepted_of_selected 13 88300 ⟨207065, by decide⟩ ⟨13, 2, 0, 207065, 88300, 233, 16384⟩
    (by decide) selected_cut_07060

theorem selected_cut_07061 : selected 8 ⟨207111, by decide⟩
    (prefixPartial 13 88301) = some ⟨13, 2, 0, 207111, 88301, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_88301_207111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88301 ⟨207111, by decide⟩ :=
  accepted_of_selected 13 88301 ⟨207111, by decide⟩ ⟨13, 2, 0, 207111, 88301, 2717, 16384⟩
    (by decide) selected_cut_07061

theorem selected_cut_07062 : selected 8 ⟨207125, by decide⟩
    (prefixPartial 13 88302) = some ⟨13, 2, 0, 207125, 88302, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_88302_207125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88302 ⟨207125, by decide⟩ :=
  accepted_of_selected 13 88302 ⟨207125, by decide⟩ ⟨13, 2, 0, 207125, 88302, 1329, 16384⟩
    (by decide) selected_cut_07062

theorem selected_cut_07063 : selected 8 ⟨207130, by decide⟩
    (prefixPartial 13 88303) = some ⟨13, 2, 0, 207130, 88303, 717, 16384⟩ := by
  decide +kernel

theorem context_13_88303_207130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88303 ⟨207130, by decide⟩ :=
  accepted_of_selected 13 88303 ⟨207130, by decide⟩ ⟨13, 2, 0, 207130, 88303, 717, 16384⟩
    (by decide) selected_cut_07063

theorem unmarked_context_12_22075_207131 : frontier 9 ⟨207131, by decide⟩
    (prefixCache 12 22075) (prefixPartial 12 22075) = false := by
  decide +kernel

theorem node_context_12_22075_207131 : EJMOriginalGlobalDAGData.nodes 9 ⟨207131, by decide⟩ =
    .split (coordinate 12) (![⟨207065, by decide⟩,⟨207111, by decide⟩,⟨207125, by decide⟩,⟨207130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22075_207131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22075 ⟨207131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22075
    ⟨207131, by decide⟩ (by decide) (![⟨207065, by decide⟩,⟨207111, by decide⟩,⟨207125, by decide⟩,⟨207130, by decide⟩]) unmarked_context_12_22075_207131 node_context_12_22075_207131
  intro a
  fin_cases a
  · exact context_13_88300_207065
  · exact context_13_88301_207111
  · exact context_13_88302_207125
  · exact context_13_88303_207130

theorem unmarked_context_11_5518_207132 : frontier 10 ⟨207132, by decide⟩
    (prefixCache 11 5518) (prefixPartial 11 5518) = false := by
  decide +kernel

theorem node_context_11_5518_207132 : EJMOriginalGlobalDAGData.nodes 10 ⟨207132, by decide⟩ =
    .split (coordinate 11) (![⟨206878, by decide⟩,⟨206938, by decide⟩,⟨207059, by decide⟩,⟨207131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5518_207132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5518 ⟨207132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5518
    ⟨207132, by decide⟩ (by decide) (![⟨206878, by decide⟩,⟨206938, by decide⟩,⟨207059, by decide⟩,⟨207131, by decide⟩]) unmarked_context_11_5518_207132 node_context_11_5518_207132
  intro a
  fin_cases a
  · exact context_12_22072_206878
  · exact context_12_22073_206938
  · exact context_12_22074_207059
  · exact context_12_22075_207131

theorem selected_cut_07064 : selected 8 ⟨207135, by decide⟩
    (prefixPartial 13 88304) = some ⟨13, 2, 0, 207135, 88304, 113, 16384⟩ := by
  decide +kernel

theorem context_13_88304_207135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88304 ⟨207135, by decide⟩ :=
  accepted_of_selected 13 88304 ⟨207135, by decide⟩ ⟨13, 2, 0, 207135, 88304, 113, 16384⟩
    (by decide) selected_cut_07064

theorem selected_cut_07065 : selected 8 ⟨207162, by decide⟩
    (prefixPartial 13 88305) = some ⟨13, 2, 0, 207162, 88305, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_88305_207162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88305 ⟨207162, by decide⟩ :=
  accepted_of_selected 13 88305 ⟨207162, by decide⟩ ⟨13, 2, 0, 207162, 88305, 2413, 16384⟩
    (by decide) selected_cut_07065

theorem selected_cut_07066 : selected 8 ⟨207185, by decide⟩
    (prefixPartial 13 88306) = some ⟨13, 2, 0, 207185, 88306, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_88306_207185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88306 ⟨207185, by decide⟩ :=
  accepted_of_selected 13 88306 ⟨207185, by decide⟩ ⟨13, 2, 0, 207185, 88306, 1641, 16384⟩
    (by decide) selected_cut_07066

theorem selected_cut_07067 : selected 8 ⟨207194, by decide⟩
    (prefixPartial 13 88307) = some ⟨13, 2, 0, 207194, 88307, 829, 16384⟩ := by
  decide +kernel

theorem context_13_88307_207194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88307 ⟨207194, by decide⟩ :=
  accepted_of_selected 13 88307 ⟨207194, by decide⟩ ⟨13, 2, 0, 207194, 88307, 829, 16384⟩
    (by decide) selected_cut_07067

theorem unmarked_context_12_22076_207195 : frontier 9 ⟨207195, by decide⟩
    (prefixCache 12 22076) (prefixPartial 12 22076) = false := by
  decide +kernel

theorem node_context_12_22076_207195 : EJMOriginalGlobalDAGData.nodes 9 ⟨207195, by decide⟩ =
    .split (coordinate 12) (![⟨207135, by decide⟩,⟨207162, by decide⟩,⟨207185, by decide⟩,⟨207194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22076_207195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22076 ⟨207195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22076
    ⟨207195, by decide⟩ (by decide) (![⟨207135, by decide⟩,⟨207162, by decide⟩,⟨207185, by decide⟩,⟨207194, by decide⟩]) unmarked_context_12_22076_207195 node_context_12_22076_207195
  intro a
  fin_cases a
  · exact context_13_88304_207135
  · exact context_13_88305_207162
  · exact context_13_88306_207185
  · exact context_13_88307_207194

theorem selected_cut_07068 : selected 8 ⟨207198, by decide⟩
    (prefixPartial 13 88308) = some ⟨13, 2, 0, 207198, 88308, 89, 16384⟩ := by
  decide +kernel

theorem context_13_88308_207198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88308 ⟨207198, by decide⟩ :=
  accepted_of_selected 13 88308 ⟨207198, by decide⟩ ⟨13, 2, 0, 207198, 88308, 89, 16384⟩
    (by decide) selected_cut_07068

theorem selected_cut_07069 : selected 8 ⟨207225, by decide⟩
    (prefixPartial 13 88309) = some ⟨13, 2, 0, 207225, 88309, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_88309_207225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88309 ⟨207225, by decide⟩ :=
  accepted_of_selected 13 88309 ⟨207225, by decide⟩ ⟨13, 2, 0, 207225, 88309, 2137, 16384⟩
    (by decide) selected_cut_07069

theorem selected_cut_07070 : selected 8 ⟨207250, by decide⟩
    (prefixPartial 13 88310) = some ⟨13, 2, 0, 207250, 88310, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_88310_207250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88310 ⟨207250, by decide⟩ :=
  accepted_of_selected 13 88310 ⟨207250, by decide⟩ ⟨13, 2, 0, 207250, 88310, 1557, 16384⟩
    (by decide) selected_cut_07070

theorem selected_cut_07071 : selected 8 ⟨207258, by decide⟩
    (prefixPartial 13 88311) = some ⟨13, 2, 0, 207258, 88311, 753, 16384⟩ := by
  decide +kernel

theorem context_13_88311_207258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88311 ⟨207258, by decide⟩ :=
  accepted_of_selected 13 88311 ⟨207258, by decide⟩ ⟨13, 2, 0, 207258, 88311, 753, 16384⟩
    (by decide) selected_cut_07071

theorem unmarked_context_12_22077_207259 : frontier 9 ⟨207259, by decide⟩
    (prefixCache 12 22077) (prefixPartial 12 22077) = false := by
  decide +kernel

theorem node_context_12_22077_207259 : EJMOriginalGlobalDAGData.nodes 9 ⟨207259, by decide⟩ =
    .split (coordinate 12) (![⟨207198, by decide⟩,⟨207225, by decide⟩,⟨207250, by decide⟩,⟨207258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22077_207259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22077 ⟨207259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22077
    ⟨207259, by decide⟩ (by decide) (![⟨207198, by decide⟩,⟨207225, by decide⟩,⟨207250, by decide⟩,⟨207258, by decide⟩]) unmarked_context_12_22077_207259 node_context_12_22077_207259
  intro a
  fin_cases a
  · exact context_13_88308_207198
  · exact context_13_88309_207225
  · exact context_13_88310_207250
  · exact context_13_88311_207258

theorem selected_cut_07072 : selected 8 ⟨207262, by decide⟩
    (prefixPartial 13 88312) = some ⟨13, 2, 0, 207262, 88312, 73, 16384⟩ := by
  decide +kernel

theorem context_13_88312_207262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88312 ⟨207262, by decide⟩ :=
  accepted_of_selected 13 88312 ⟨207262, by decide⟩ ⟨13, 2, 0, 207262, 88312, 73, 16384⟩
    (by decide) selected_cut_07072

theorem selected_cut_07073 : selected 8 ⟨207303, by decide⟩
    (prefixPartial 13 88313) = some ⟨13, 2, 0, 207303, 88313, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_88313_207303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88313 ⟨207303, by decide⟩ :=
  accepted_of_selected 13 88313 ⟨207303, by decide⟩ ⟨13, 2, 0, 207303, 88313, 2657, 16384⟩
    (by decide) selected_cut_07073

theorem selected_cut_07074 : selected 8 ⟨207316, by decide⟩
    (prefixPartial 13 88314) = some ⟨13, 2, 0, 207316, 88314, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_88314_207316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88314 ⟨207316, by decide⟩ :=
  accepted_of_selected 13 88314 ⟨207316, by decide⟩ ⟨13, 2, 0, 207316, 88314, 1309, 16384⟩
    (by decide) selected_cut_07074

theorem selected_cut_07075 : selected 8 ⟨207321, by decide⟩
    (prefixPartial 13 88315) = some ⟨13, 2, 0, 207321, 88315, 781, 16384⟩ := by
  decide +kernel

theorem context_13_88315_207321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88315 ⟨207321, by decide⟩ :=
  accepted_of_selected 13 88315 ⟨207321, by decide⟩ ⟨13, 2, 0, 207321, 88315, 781, 16384⟩
    (by decide) selected_cut_07075

theorem unmarked_context_12_22078_207322 : frontier 9 ⟨207322, by decide⟩
    (prefixCache 12 22078) (prefixPartial 12 22078) = false := by
  decide +kernel

theorem node_context_12_22078_207322 : EJMOriginalGlobalDAGData.nodes 9 ⟨207322, by decide⟩ =
    .split (coordinate 12) (![⟨207262, by decide⟩,⟨207303, by decide⟩,⟨207316, by decide⟩,⟨207321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22078_207322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22078 ⟨207322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22078
    ⟨207322, by decide⟩ (by decide) (![⟨207262, by decide⟩,⟨207303, by decide⟩,⟨207316, by decide⟩,⟨207321, by decide⟩]) unmarked_context_12_22078_207322 node_context_12_22078_207322
  intro a
  fin_cases a
  · exact context_13_88312_207262
  · exact context_13_88313_207303
  · exact context_13_88314_207316
  · exact context_13_88315_207321

theorem selected_cut_07076 : selected 8 ⟨207325, by decide⟩
    (prefixPartial 13 88316) = some ⟨13, 2, 0, 207325, 88316, 57, 16384⟩ := by
  decide +kernel

theorem context_13_88316_207325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88316 ⟨207325, by decide⟩ :=
  accepted_of_selected 13 88316 ⟨207325, by decide⟩ ⟨13, 2, 0, 207325, 88316, 57, 16384⟩
    (by decide) selected_cut_07076

theorem selected_cut_07077 : selected 8 ⟨207365, by decide⟩
    (prefixPartial 13 88317) = some ⟨13, 2, 0, 207365, 88317, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_88317_207365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88317 ⟨207365, by decide⟩ :=
  accepted_of_selected 13 88317 ⟨207365, by decide⟩ ⟨13, 2, 0, 207365, 88317, 2749, 16384⟩
    (by decide) selected_cut_07077

theorem selected_cut_07078 : selected 8 ⟨207385, by decide⟩
    (prefixPartial 13 88318) = some ⟨13, 2, 0, 207385, 88318, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_88318_207385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88318 ⟨207385, by decide⟩ :=
  accepted_of_selected 13 88318 ⟨207385, by decide⟩ ⟨13, 2, 0, 207385, 88318, 1529, 16384⟩
    (by decide) selected_cut_07078

theorem selected_cut_07079 : selected 8 ⟨207394, by decide⟩
    (prefixPartial 13 88319) = some ⟨13, 2, 0, 207394, 88319, 737, 16384⟩ := by
  decide +kernel

theorem context_13_88319_207394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88319 ⟨207394, by decide⟩ :=
  accepted_of_selected 13 88319 ⟨207394, by decide⟩ ⟨13, 2, 0, 207394, 88319, 737, 16384⟩
    (by decide) selected_cut_07079

theorem unmarked_context_12_22079_207395 : frontier 9 ⟨207395, by decide⟩
    (prefixCache 12 22079) (prefixPartial 12 22079) = false := by
  decide +kernel

theorem node_context_12_22079_207395 : EJMOriginalGlobalDAGData.nodes 9 ⟨207395, by decide⟩ =
    .split (coordinate 12) (![⟨207325, by decide⟩,⟨207365, by decide⟩,⟨207385, by decide⟩,⟨207394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22079_207395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22079 ⟨207395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22079
    ⟨207395, by decide⟩ (by decide) (![⟨207325, by decide⟩,⟨207365, by decide⟩,⟨207385, by decide⟩,⟨207394, by decide⟩]) unmarked_context_12_22079_207395 node_context_12_22079_207395
  intro a
  fin_cases a
  · exact context_13_88316_207325
  · exact context_13_88317_207365
  · exact context_13_88318_207385
  · exact context_13_88319_207394

theorem unmarked_context_11_5519_207396 : frontier 10 ⟨207396, by decide⟩
    (prefixCache 11 5519) (prefixPartial 11 5519) = false := by
  decide +kernel

theorem node_context_11_5519_207396 : EJMOriginalGlobalDAGData.nodes 10 ⟨207396, by decide⟩ =
    .split (coordinate 11) (![⟨207195, by decide⟩,⟨207259, by decide⟩,⟨207322, by decide⟩,⟨207395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5519_207396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5519 ⟨207396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5519
    ⟨207396, by decide⟩ (by decide) (![⟨207195, by decide⟩,⟨207259, by decide⟩,⟨207322, by decide⟩,⟨207395, by decide⟩]) unmarked_context_11_5519_207396 node_context_11_5519_207396
  intro a
  fin_cases a
  · exact context_12_22076_207195
  · exact context_12_22077_207259
  · exact context_12_22078_207322
  · exact context_12_22079_207395

theorem unmarked_context_10_1379_207397 : frontier 11 ⟨207397, by decide⟩
    (prefixCache 10 1379) (prefixPartial 10 1379) = false := by
  decide +kernel

theorem node_context_10_1379_207397 : EJMOriginalGlobalDAGData.nodes 11 ⟨207397, by decide⟩ =
    .split (coordinate 10) (![⟨206559, by decide⟩,⟨206826, by decide⟩,⟨207132, by decide⟩,⟨207396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1379_207397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1379 ⟨207397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1379
    ⟨207397, by decide⟩ (by decide) (![⟨206559, by decide⟩,⟨206826, by decide⟩,⟨207132, by decide⟩,⟨207396, by decide⟩]) unmarked_context_10_1379_207397 node_context_10_1379_207397
  intro a
  fin_cases a
  · exact context_11_5516_206559
  · exact context_11_5517_206826
  · exact context_11_5518_207132
  · exact context_11_5519_207396

theorem unmarked_context_9_344_207398 : frontier 12 ⟨207398, by decide⟩
    (prefixCache 9 344) (prefixPartial 9 344) = false := by
  decide +kernel

theorem node_context_9_344_207398 : EJMOriginalGlobalDAGData.nodes 12 ⟨207398, by decide⟩ =
    .split (coordinate 9) (![⟨203843, by decide⟩,⟨205211, by decide⟩,⟨206299, by decide⟩,⟨207397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_344_207398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 344 ⟨207398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 344
    ⟨207398, by decide⟩ (by decide) (![⟨203843, by decide⟩,⟨205211, by decide⟩,⟨206299, by decide⟩,⟨207397, by decide⟩]) unmarked_context_9_344_207398 node_context_9_344_207398
  intro a
  fin_cases a
  · exact context_10_1376_203843
  · exact context_10_1377_205211
  · exact context_10_1378_206299
  · exact context_10_1379_207397

theorem selected_cut_07080 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88320) = some ⟨13, 1, 0, 3444, 88320, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88320_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88320 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88320 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88320, 1, 16384⟩
    (by decide) selected_cut_07080

theorem selected_cut_07081 : selected 8 ⟨207425, by decide⟩
    (prefixPartial 13 88321) = some ⟨13, 2, 0, 207425, 88321, 2885, 16384⟩ := by
  decide +kernel

theorem context_13_88321_207425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88321 ⟨207425, by decide⟩ :=
  accepted_of_selected 13 88321 ⟨207425, by decide⟩ ⟨13, 2, 0, 207425, 88321, 2885, 16384⟩
    (by decide) selected_cut_07081

theorem selected_cut_07082 : selected 8 ⟨207444, by decide⟩
    (prefixPartial 13 88322) = some ⟨13, 2, 0, 207444, 88322, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_88322_207444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88322 ⟨207444, by decide⟩ :=
  accepted_of_selected 13 88322 ⟨207444, by decide⟩ ⟨13, 2, 0, 207444, 88322, 1657, 16384⟩
    (by decide) selected_cut_07082

theorem selected_cut_07083 : selected 8 ⟨207452, by decide⟩
    (prefixPartial 13 88323) = some ⟨13, 2, 0, 207452, 88323, 841, 16384⟩ := by
  decide +kernel

theorem context_13_88323_207452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88323 ⟨207452, by decide⟩ :=
  accepted_of_selected 13 88323 ⟨207452, by decide⟩ ⟨13, 2, 0, 207452, 88323, 841, 16384⟩
    (by decide) selected_cut_07083

theorem unmarked_context_12_22080_207453 : frontier 9 ⟨207453, by decide⟩
    (prefixCache 12 22080) (prefixPartial 12 22080) = false := by
  decide +kernel

theorem node_context_12_22080_207453 : EJMOriginalGlobalDAGData.nodes 9 ⟨207453, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207425, by decide⟩,⟨207444, by decide⟩,⟨207452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22080_207453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22080 ⟨207453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22080
    ⟨207453, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207425, by decide⟩,⟨207444, by decide⟩,⟨207452, by decide⟩]) unmarked_context_12_22080_207453 node_context_12_22080_207453
  intro a
  fin_cases a
  · exact context_13_88320_3444
  · exact context_13_88321_207425
  · exact context_13_88322_207444
  · exact context_13_88323_207452

theorem selected_cut_07084 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88324) = some ⟨13, 1, 0, 3444, 88324, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88324_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88324 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88324 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88324, 1, 16384⟩
    (by decide) selected_cut_07084

theorem selected_cut_07085 : selected 8 ⟨207506, by decide⟩
    (prefixPartial 13 88325) = some ⟨13, 2, 0, 207506, 88325, 3729, 16384⟩ := by
  decide +kernel

theorem context_13_88325_207506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88325 ⟨207506, by decide⟩ :=
  accepted_of_selected 13 88325 ⟨207506, by decide⟩ ⟨13, 2, 0, 207506, 88325, 3729, 16384⟩
    (by decide) selected_cut_07085

theorem selected_cut_07086 : selected 8 ⟨207536, by decide⟩
    (prefixPartial 13 88326) = some ⟨13, 2, 0, 207536, 88326, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_88326_207536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88326 ⟨207536, by decide⟩ :=
  accepted_of_selected 13 88326 ⟨207536, by decide⟩ ⟨13, 2, 0, 207536, 88326, 2073, 16384⟩
    (by decide) selected_cut_07086

theorem selected_cut_07087 : selected 8 ⟨207545, by decide⟩
    (prefixPartial 13 88327) = some ⟨13, 2, 0, 207545, 88327, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_88327_207545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88327 ⟨207545, by decide⟩ :=
  accepted_of_selected 13 88327 ⟨207545, by decide⟩ ⟨13, 2, 0, 207545, 88327, 1261, 16384⟩
    (by decide) selected_cut_07087

theorem unmarked_context_12_22081_207546 : frontier 9 ⟨207546, by decide⟩
    (prefixCache 12 22081) (prefixPartial 12 22081) = false := by
  decide +kernel

theorem node_context_12_22081_207546 : EJMOriginalGlobalDAGData.nodes 9 ⟨207546, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207506, by decide⟩,⟨207536, by decide⟩,⟨207545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22081_207546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22081 ⟨207546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22081
    ⟨207546, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207506, by decide⟩,⟨207536, by decide⟩,⟨207545, by decide⟩]) unmarked_context_12_22081_207546 node_context_12_22081_207546
  intro a
  fin_cases a
  · exact context_13_88324_3444
  · exact context_13_88325_207506
  · exact context_13_88326_207536
  · exact context_13_88327_207545

theorem selected_cut_07088 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88328) = some ⟨13, 1, 0, 3444, 88328, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88328_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88328 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88328 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88328, 1, 16384⟩
    (by decide) selected_cut_07088

theorem selected_cut_07089 : selected 8 ⟨207575, by decide⟩
    (prefixPartial 13 88329) = some ⟨13, 2, 0, 207575, 88329, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_88329_207575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88329 ⟨207575, by decide⟩ :=
  accepted_of_selected 13 88329 ⟨207575, by decide⟩ ⟨13, 2, 0, 207575, 88329, 2969, 16384⟩
    (by decide) selected_cut_07089

theorem selected_cut_07090 : selected 8 ⟨207596, by decide⟩
    (prefixPartial 13 88330) = some ⟨13, 2, 0, 207596, 88330, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_88330_207596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88330 ⟨207596, by decide⟩ :=
  accepted_of_selected 13 88330 ⟨207596, by decide⟩ ⟨13, 2, 0, 207596, 88330, 1405, 16384⟩
    (by decide) selected_cut_07090

theorem selected_cut_07091 : selected 8 ⟨207607, by decide⟩
    (prefixPartial 13 88331) = some ⟨13, 2, 0, 207607, 88331, 997, 16384⟩ := by
  decide +kernel

theorem context_13_88331_207607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88331 ⟨207607, by decide⟩ :=
  accepted_of_selected 13 88331 ⟨207607, by decide⟩ ⟨13, 2, 0, 207607, 88331, 997, 16384⟩
    (by decide) selected_cut_07091

theorem unmarked_context_12_22082_207608 : frontier 9 ⟨207608, by decide⟩
    (prefixCache 12 22082) (prefixPartial 12 22082) = false := by
  decide +kernel

theorem node_context_12_22082_207608 : EJMOriginalGlobalDAGData.nodes 9 ⟨207608, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207575, by decide⟩,⟨207596, by decide⟩,⟨207607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22082_207608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22082 ⟨207608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22082
    ⟨207608, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207575, by decide⟩,⟨207596, by decide⟩,⟨207607, by decide⟩]) unmarked_context_12_22082_207608 node_context_12_22082_207608
  intro a
  fin_cases a
  · exact context_13_88328_3444
  · exact context_13_88329_207575
  · exact context_13_88330_207596
  · exact context_13_88331_207607

theorem selected_cut_07092 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88332) = some ⟨13, 1, 0, 3444, 88332, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88332_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88332 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88332 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88332, 1, 16384⟩
    (by decide) selected_cut_07092

theorem selected_cut_07093 : selected 8 ⟨207646, by decide⟩
    (prefixPartial 13 88333) = some ⟨13, 2, 0, 207646, 88333, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_88333_207646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88333 ⟨207646, by decide⟩ :=
  accepted_of_selected 13 88333 ⟨207646, by decide⟩ ⟨13, 2, 0, 207646, 88333, 3157, 16384⟩
    (by decide) selected_cut_07093

theorem selected_cut_07094 : selected 8 ⟨207667, by decide⟩
    (prefixPartial 13 88334) = some ⟨13, 2, 0, 207667, 88334, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_88334_207667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88334 ⟨207667, by decide⟩ :=
  accepted_of_selected 13 88334 ⟨207667, by decide⟩ ⟨13, 2, 0, 207667, 88334, 1605, 16384⟩
    (by decide) selected_cut_07094

theorem selected_cut_07095 : selected 8 ⟨207677, by decide⟩
    (prefixPartial 13 88335) = some ⟨13, 2, 0, 207677, 88335, 997, 16384⟩ := by
  decide +kernel

theorem context_13_88335_207677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88335 ⟨207677, by decide⟩ :=
  accepted_of_selected 13 88335 ⟨207677, by decide⟩ ⟨13, 2, 0, 207677, 88335, 997, 16384⟩
    (by decide) selected_cut_07095

theorem unmarked_context_12_22083_207678 : frontier 9 ⟨207678, by decide⟩
    (prefixCache 12 22083) (prefixPartial 12 22083) = false := by
  decide +kernel

theorem node_context_12_22083_207678 : EJMOriginalGlobalDAGData.nodes 9 ⟨207678, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207646, by decide⟩,⟨207667, by decide⟩,⟨207677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22083_207678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22083 ⟨207678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22083
    ⟨207678, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207646, by decide⟩,⟨207667, by decide⟩,⟨207677, by decide⟩]) unmarked_context_12_22083_207678 node_context_12_22083_207678
  intro a
  fin_cases a
  · exact context_13_88332_3444
  · exact context_13_88333_207646
  · exact context_13_88334_207667
  · exact context_13_88335_207677

theorem unmarked_context_11_5520_207679 : frontier 10 ⟨207679, by decide⟩
    (prefixCache 11 5520) (prefixPartial 11 5520) = false := by
  decide +kernel

theorem node_context_11_5520_207679 : EJMOriginalGlobalDAGData.nodes 10 ⟨207679, by decide⟩ =
    .split (coordinate 11) (![⟨207453, by decide⟩,⟨207546, by decide⟩,⟨207608, by decide⟩,⟨207678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5520_207679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5520 ⟨207679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5520
    ⟨207679, by decide⟩ (by decide) (![⟨207453, by decide⟩,⟨207546, by decide⟩,⟨207608, by decide⟩,⟨207678, by decide⟩]) unmarked_context_11_5520_207679 node_context_11_5520_207679
  intro a
  fin_cases a
  · exact context_12_22080_207453
  · exact context_12_22081_207546
  · exact context_12_22082_207608
  · exact context_12_22083_207678

theorem selected_cut_07096 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88336) = some ⟨13, 1, 0, 3444, 88336, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88336_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88336 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88336 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88336, 1, 16384⟩
    (by decide) selected_cut_07096

theorem selected_cut_07097 : selected 8 ⟨207719, by decide⟩
    (prefixPartial 13 88337) = some ⟨13, 2, 0, 207719, 88337, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_88337_207719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88337 ⟨207719, by decide⟩ :=
  accepted_of_selected 13 88337 ⟨207719, by decide⟩ ⟨13, 2, 0, 207719, 88337, 2969, 16384⟩
    (by decide) selected_cut_07097

theorem selected_cut_07098 : selected 8 ⟨207738, by decide⟩
    (prefixPartial 13 88338) = some ⟨13, 2, 0, 207738, 88338, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_88338_207738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88338 ⟨207738, by decide⟩ :=
  accepted_of_selected 13 88338 ⟨207738, by decide⟩ ⟨13, 2, 0, 207738, 88338, 1653, 16384⟩
    (by decide) selected_cut_07098

theorem selected_cut_07099 : selected 8 ⟨207750, by decide⟩
    (prefixPartial 13 88339) = some ⟨13, 2, 0, 207750, 88339, 893, 16384⟩ := by
  decide +kernel

theorem context_13_88339_207750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88339 ⟨207750, by decide⟩ :=
  accepted_of_selected 13 88339 ⟨207750, by decide⟩ ⟨13, 2, 0, 207750, 88339, 893, 16384⟩
    (by decide) selected_cut_07099

theorem unmarked_context_12_22084_207751 : frontier 9 ⟨207751, by decide⟩
    (prefixCache 12 22084) (prefixPartial 12 22084) = false := by
  decide +kernel

theorem node_context_12_22084_207751 : EJMOriginalGlobalDAGData.nodes 9 ⟨207751, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207719, by decide⟩,⟨207738, by decide⟩,⟨207750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22084_207751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22084 ⟨207751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22084
    ⟨207751, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207719, by decide⟩,⟨207738, by decide⟩,⟨207750, by decide⟩]) unmarked_context_12_22084_207751 node_context_12_22084_207751
  intro a
  fin_cases a
  · exact context_13_88336_3444
  · exact context_13_88337_207719
  · exact context_13_88338_207738
  · exact context_13_88339_207750

theorem selected_cut_07100 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88340) = some ⟨13, 1, 0, 3444, 88340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88340, 1, 16384⟩
    (by decide) selected_cut_07100

theorem selected_cut_07101 : selected 8 ⟨207825, by decide⟩
    (prefixPartial 13 88341) = some ⟨13, 2, 0, 207825, 88341, 3689, 16384⟩ := by
  decide +kernel

theorem context_13_88341_207825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88341 ⟨207825, by decide⟩ :=
  accepted_of_selected 13 88341 ⟨207825, by decide⟩ ⟨13, 2, 0, 207825, 88341, 3689, 16384⟩
    (by decide) selected_cut_07101

theorem selected_cut_07102 : selected 8 ⟨207848, by decide⟩
    (prefixPartial 13 88342) = some ⟨13, 2, 0, 207848, 88342, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_88342_207848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88342 ⟨207848, by decide⟩ :=
  accepted_of_selected 13 88342 ⟨207848, by decide⟩ ⟨13, 2, 0, 207848, 88342, 2093, 16384⟩
    (by decide) selected_cut_07102

theorem selected_cut_07103 : selected 8 ⟨207864, by decide⟩
    (prefixPartial 13 88343) = some ⟨13, 2, 0, 207864, 88343, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_88343_207864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88343 ⟨207864, by decide⟩ :=
  accepted_of_selected 13 88343 ⟨207864, by decide⟩ ⟨13, 2, 0, 207864, 88343, 1205, 16384⟩
    (by decide) selected_cut_07103

theorem unmarked_context_12_22085_207865 : frontier 9 ⟨207865, by decide⟩
    (prefixCache 12 22085) (prefixPartial 12 22085) = false := by
  decide +kernel

theorem node_context_12_22085_207865 : EJMOriginalGlobalDAGData.nodes 9 ⟨207865, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207825, by decide⟩,⟨207848, by decide⟩,⟨207864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22085_207865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22085 ⟨207865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22085
    ⟨207865, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207825, by decide⟩,⟨207848, by decide⟩,⟨207864, by decide⟩]) unmarked_context_12_22085_207865 node_context_12_22085_207865
  intro a
  fin_cases a
  · exact context_13_88340_3444
  · exact context_13_88341_207825
  · exact context_13_88342_207848
  · exact context_13_88343_207864

theorem selected_cut_07104 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88344) = some ⟨13, 1, 0, 3444, 88344, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88344_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88344 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88344 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88344, 1, 16384⟩
    (by decide) selected_cut_07104

theorem selected_cut_07105 : selected 8 ⟨207900, by decide⟩
    (prefixPartial 13 88345) = some ⟨13, 2, 0, 207900, 88345, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_88345_207900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88345 ⟨207900, by decide⟩ :=
  accepted_of_selected 13 88345 ⟨207900, by decide⟩ ⟨13, 2, 0, 207900, 88345, 2753, 16384⟩
    (by decide) selected_cut_07105

theorem selected_cut_07106 : selected 8 ⟨207920, by decide⟩
    (prefixPartial 13 88346) = some ⟨13, 2, 0, 207920, 88346, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_88346_207920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88346 ⟨207920, by decide⟩ :=
  accepted_of_selected 13 88346 ⟨207920, by decide⟩ ⟨13, 2, 0, 207920, 88346, 1385, 16384⟩
    (by decide) selected_cut_07106

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
