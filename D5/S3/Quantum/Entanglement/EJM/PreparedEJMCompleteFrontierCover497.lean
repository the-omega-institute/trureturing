/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover496
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_23379_1335969 : frontier 11 ⟨1335969, by decide⟩
    (prefixCache 10 23379) (prefixPartial 10 23379) = false := by
  decide +kernel

theorem node_context_10_23379_1335969 : EJMOriginalGlobalDAGData.nodes 11 ⟨1335969, by decide⟩ =
    .split (coordinate 10) (![⟨1335698, by decide⟩,⟨1335797, by decide⟩,⟨1335909, by decide⟩,⟨1335968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23379_1335969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23379 ⟨1335969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23379
    ⟨1335969, by decide⟩ (by decide) (![⟨1335698, by decide⟩,⟨1335797, by decide⟩,⟨1335909, by decide⟩,⟨1335968, by decide⟩]) unmarked_context_10_23379_1335969 node_context_10_23379_1335969
  intro a
  fin_cases a
  · exact context_11_93516_1335698
  · exact context_11_93517_1335797
  · exact context_11_93518_1335909
  · exact context_11_93519_1335968

theorem unmarked_context_9_5844_1335970 : frontier 12 ⟨1335970, by decide⟩
    (prefixCache 9 5844) (prefixPartial 9 5844) = false := by
  decide +kernel

theorem node_context_9_5844_1335970 : EJMOriginalGlobalDAGData.nodes 12 ⟨1335970, by decide⟩ =
    .split (coordinate 9) (![⟨1334872, by decide⟩,⟨1335194, by decide⟩,⟨1335612, by decide⟩,⟨1335969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5844_1335970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5844 ⟨1335970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5844
    ⟨1335970, by decide⟩ (by decide) (![⟨1334872, by decide⟩,⟨1335194, by decide⟩,⟨1335612, by decide⟩,⟨1335969, by decide⟩]) unmarked_context_9_5844_1335970 node_context_9_5844_1335970
  intro a
  fin_cases a
  · exact context_10_23376_1334872
  · exact context_10_23377_1335194
  · exact context_10_23378_1335612
  · exact context_10_23379_1335969

theorem selected_cut_47716 : selected 10 ⟨1283168, by decide⟩
    (prefixPartial 11 93520) = some ⟨11, 1, 0, 1283168, 93520, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93520_1283168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93520 ⟨1283168, by decide⟩ :=
  accepted_of_selected 11 93520 ⟨1283168, by decide⟩ ⟨11, 1, 0, 1283168, 93520, 1, 262144⟩
    (by decide) selected_cut_47716

theorem selected_cut_47717 : selected 10 ⟨1336039, by decide⟩
    (prefixPartial 11 93521) = some ⟨11, 2, 0, 1336039, 93521, 4029, 262144⟩ := by
  decide +kernel

theorem context_11_93521_1336039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93521 ⟨1336039, by decide⟩ :=
  accepted_of_selected 11 93521 ⟨1336039, by decide⟩ ⟨11, 2, 0, 1336039, 93521, 4029, 262144⟩
    (by decide) selected_cut_47717

theorem selected_cut_47718 : selected 10 ⟨1336092, by decide⟩
    (prefixPartial 11 93522) = some ⟨11, 2, 0, 1336092, 93522, 3049, 262144⟩ := by
  decide +kernel

theorem context_11_93522_1336092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93522 ⟨1336092, by decide⟩ :=
  accepted_of_selected 11 93522 ⟨1336092, by decide⟩ ⟨11, 2, 0, 1336092, 93522, 3049, 262144⟩
    (by decide) selected_cut_47718

theorem selected_cut_47719 : selected 9 ⟨1336112, by decide⟩
    (prefixPartial 12 374092) = some ⟨12, 2, 0, 1336112, 374092, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_374092_1336112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374092 ⟨1336112, by decide⟩ :=
  accepted_of_selected 12 374092 ⟨1336112, by decide⟩ ⟨12, 2, 0, 1336112, 374092, 1429, 65536⟩
    (by decide) selected_cut_47719

theorem selected_cut_47720 : selected 9 ⟨1336132, by decide⟩
    (prefixPartial 12 374093) = some ⟨12, 2, 0, 1336132, 374093, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_374093_1336132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374093 ⟨1336132, by decide⟩ :=
  accepted_of_selected 12 374093 ⟨1336132, by decide⟩ ⟨12, 2, 0, 1336132, 374093, 1305, 65536⟩
    (by decide) selected_cut_47720

theorem selected_cut_47721 : selected 9 ⟨1336156, by decide⟩
    (prefixPartial 12 374094) = some ⟨12, 2, 0, 1336156, 374094, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_374094_1336156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374094 ⟨1336156, by decide⟩ :=
  accepted_of_selected 12 374094 ⟨1336156, by decide⟩ ⟨12, 2, 0, 1336156, 374094, 1453, 65536⟩
    (by decide) selected_cut_47721

theorem selected_cut_47722 : selected 9 ⟨1336193, by decide⟩
    (prefixPartial 12 374095) = some ⟨12, 2, 0, 1336193, 374095, 749, 65536⟩ := by
  decide +kernel

theorem context_12_374095_1336193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374095 ⟨1336193, by decide⟩ :=
  accepted_of_selected 12 374095 ⟨1336193, by decide⟩ ⟨12, 2, 0, 1336193, 374095, 749, 65536⟩
    (by decide) selected_cut_47722

theorem unmarked_context_11_93523_1336194 : frontier 10 ⟨1336194, by decide⟩
    (prefixCache 11 93523) (prefixPartial 11 93523) = false := by
  decide +kernel

theorem node_context_11_93523_1336194 : EJMOriginalGlobalDAGData.nodes 10 ⟨1336194, by decide⟩ =
    .split (coordinate 11) (![⟨1336112, by decide⟩,⟨1336132, by decide⟩,⟨1336156, by decide⟩,⟨1336193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93523_1336194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93523 ⟨1336194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93523
    ⟨1336194, by decide⟩ (by decide) (![⟨1336112, by decide⟩,⟨1336132, by decide⟩,⟨1336156, by decide⟩,⟨1336193, by decide⟩]) unmarked_context_11_93523_1336194 node_context_11_93523_1336194
  intro a
  fin_cases a
  · exact context_12_374092_1336112
  · exact context_12_374093_1336132
  · exact context_12_374094_1336156
  · exact context_12_374095_1336193

theorem unmarked_context_10_23380_1336195 : frontier 11 ⟨1336195, by decide⟩
    (prefixCache 10 23380) (prefixPartial 10 23380) = false := by
  decide +kernel

theorem node_context_10_23380_1336195 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336195, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1336039, by decide⟩,⟨1336092, by decide⟩,⟨1336194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23380_1336195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23380 ⟨1336195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23380
    ⟨1336195, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1336039, by decide⟩,⟨1336092, by decide⟩,⟨1336194, by decide⟩]) unmarked_context_10_23380_1336195 node_context_10_23380_1336195
  intro a
  fin_cases a
  · exact context_11_93520_1283168
  · exact context_11_93521_1336039
  · exact context_11_93522_1336092
  · exact context_11_93523_1336194

theorem selected_cut_47723 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23381) = some ⟨10, 1, 0, 893098, 23381, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23381_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23381 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23381 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23381, 1, 1048576⟩
    (by decide) selected_cut_47723

theorem selected_cut_47724 : selected 10 ⟨1336227, by decide⟩
    (prefixPartial 11 93528) = some ⟨11, 2, 0, 1336227, 93528, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_93528_1336227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93528 ⟨1336227, by decide⟩ :=
  accepted_of_selected 11 93528 ⟨1336227, by decide⟩ ⟨11, 2, 0, 1336227, 93528, 2445, 262144⟩
    (by decide) selected_cut_47724

theorem selected_cut_47725 : selected 10 ⟨1336281, by decide⟩
    (prefixPartial 11 93529) = some ⟨11, 2, 0, 1336281, 93529, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_93529_1336281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93529 ⟨1336281, by decide⟩ :=
  accepted_of_selected 11 93529 ⟨1336281, by decide⟩ ⟨11, 2, 0, 1336281, 93529, 3169, 262144⟩
    (by decide) selected_cut_47725

theorem selected_cut_47726 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 93530) = some ⟨11, 1, 0, 1283737, 93530, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93530_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93530 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 93530 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 93530, 1, 262144⟩
    (by decide) selected_cut_47726

theorem selected_cut_47727 : selected 10 ⟨1336324, by decide⟩
    (prefixPartial 11 93531) = some ⟨11, 2, 0, 1336324, 93531, 2437, 262144⟩ := by
  decide +kernel

theorem context_11_93531_1336324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93531 ⟨1336324, by decide⟩ :=
  accepted_of_selected 11 93531 ⟨1336324, by decide⟩ ⟨11, 2, 0, 1336324, 93531, 2437, 262144⟩
    (by decide) selected_cut_47727

theorem unmarked_context_10_23382_1336325 : frontier 11 ⟨1336325, by decide⟩
    (prefixCache 10 23382) (prefixPartial 10 23382) = false := by
  decide +kernel

theorem node_context_10_23382_1336325 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336325, by decide⟩ =
    .split (coordinate 10) (![⟨1336227, by decide⟩,⟨1336281, by decide⟩,⟨1283737, by decide⟩,⟨1336324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23382_1336325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23382 ⟨1336325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23382
    ⟨1336325, by decide⟩ (by decide) (![⟨1336227, by decide⟩,⟨1336281, by decide⟩,⟨1283737, by decide⟩,⟨1336324, by decide⟩]) unmarked_context_10_23382_1336325 node_context_10_23382_1336325
  intro a
  fin_cases a
  · exact context_11_93528_1336227
  · exact context_11_93529_1336281
  · exact context_11_93530_1283737
  · exact context_11_93531_1336324

theorem selected_cut_47728 : selected 10 ⟨1336390, by decide⟩
    (prefixPartial 11 93532) = some ⟨11, 2, 0, 1336390, 93532, 3473, 262144⟩ := by
  decide +kernel

theorem context_11_93532_1336390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93532 ⟨1336390, by decide⟩ :=
  accepted_of_selected 11 93532 ⟨1336390, by decide⟩ ⟨11, 2, 0, 1336390, 93532, 3473, 262144⟩
    (by decide) selected_cut_47728

theorem selected_cut_47729 : selected 10 ⟨1336436, by decide⟩
    (prefixPartial 11 93533) = some ⟨11, 2, 0, 1336436, 93533, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_93533_1336436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93533 ⟨1336436, by decide⟩ :=
  accepted_of_selected 11 93533 ⟨1336436, by decide⟩ ⟨11, 2, 0, 1336436, 93533, 2613, 262144⟩
    (by decide) selected_cut_47729

theorem selected_cut_47730 : selected 10 ⟨1336472, by decide⟩
    (prefixPartial 11 93534) = some ⟨11, 2, 0, 1336472, 93534, 2037, 262144⟩ := by
  decide +kernel

theorem context_11_93534_1336472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93534 ⟨1336472, by decide⟩ :=
  accepted_of_selected 11 93534 ⟨1336472, by decide⟩ ⟨11, 2, 0, 1336472, 93534, 2037, 262144⟩
    (by decide) selected_cut_47730

theorem selected_cut_47731 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 93535) = some ⟨11, 1, 0, 1284138, 93535, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93535_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93535 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 93535 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 93535, 1, 262144⟩
    (by decide) selected_cut_47731

theorem unmarked_context_10_23383_1336473 : frontier 11 ⟨1336473, by decide⟩
    (prefixCache 10 23383) (prefixPartial 10 23383) = false := by
  decide +kernel

theorem node_context_10_23383_1336473 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336473, by decide⟩ =
    .split (coordinate 10) (![⟨1336390, by decide⟩,⟨1336436, by decide⟩,⟨1336472, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23383_1336473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23383 ⟨1336473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23383
    ⟨1336473, by decide⟩ (by decide) (![⟨1336390, by decide⟩,⟨1336436, by decide⟩,⟨1336472, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23383_1336473 node_context_10_23383_1336473
  intro a
  fin_cases a
  · exact context_11_93532_1336390
  · exact context_11_93533_1336436
  · exact context_11_93534_1336472
  · exact context_11_93535_1284138

theorem unmarked_context_9_5845_1336474 : frontier 12 ⟨1336474, by decide⟩
    (prefixCache 9 5845) (prefixPartial 9 5845) = false := by
  decide +kernel

theorem node_context_9_5845_1336474 : EJMOriginalGlobalDAGData.nodes 12 ⟨1336474, by decide⟩ =
    .split (coordinate 9) (![⟨1336195, by decide⟩,⟨893098, by decide⟩,⟨1336325, by decide⟩,⟨1336473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5845_1336474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5845 ⟨1336474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5845
    ⟨1336474, by decide⟩ (by decide) (![⟨1336195, by decide⟩,⟨893098, by decide⟩,⟨1336325, by decide⟩,⟨1336473, by decide⟩]) unmarked_context_9_5845_1336474 node_context_9_5845_1336474
  intro a
  fin_cases a
  · exact context_10_23380_1336195
  · exact context_10_23381_893098
  · exact context_10_23382_1336325
  · exact context_10_23383_1336473

theorem selected_cut_47732 : selected 10 ⟨1336489, by decide⟩
    (prefixPartial 11 93536) = some ⟨11, 2, 0, 1336489, 93536, 1045, 262144⟩ := by
  decide +kernel

theorem context_11_93536_1336489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93536 ⟨1336489, by decide⟩ :=
  accepted_of_selected 11 93536 ⟨1336489, by decide⟩ ⟨11, 2, 0, 1336489, 93536, 1045, 262144⟩
    (by decide) selected_cut_47732

theorem selected_cut_47733 : selected 10 ⟨1336523, by decide⟩
    (prefixPartial 11 93537) = some ⟨11, 2, 0, 1336523, 93537, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_93537_1336523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93537 ⟨1336523, by decide⟩ :=
  accepted_of_selected 11 93537 ⟨1336523, by decide⟩ ⟨11, 2, 0, 1336523, 93537, 1941, 262144⟩
    (by decide) selected_cut_47733

theorem selected_cut_47734 : selected 10 ⟨1336561, by decide⟩
    (prefixPartial 11 93538) = some ⟨11, 2, 0, 1336561, 93538, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_93538_1336561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93538 ⟨1336561, by decide⟩ :=
  accepted_of_selected 11 93538 ⟨1336561, by decide⟩ ⟨11, 2, 0, 1336561, 93538, 2809, 262144⟩
    (by decide) selected_cut_47734

theorem selected_cut_47735 : selected 10 ⟨1336602, by decide⟩
    (prefixPartial 11 93539) = some ⟨11, 2, 0, 1336602, 93539, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_93539_1336602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93539 ⟨1336602, by decide⟩ :=
  accepted_of_selected 11 93539 ⟨1336602, by decide⟩ ⟨11, 2, 0, 1336602, 93539, 2541, 262144⟩
    (by decide) selected_cut_47735

theorem unmarked_context_10_23384_1336603 : frontier 11 ⟨1336603, by decide⟩
    (prefixCache 10 23384) (prefixPartial 10 23384) = false := by
  decide +kernel

theorem node_context_10_23384_1336603 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336603, by decide⟩ =
    .split (coordinate 10) (![⟨1336489, by decide⟩,⟨1336523, by decide⟩,⟨1336561, by decide⟩,⟨1336602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23384_1336603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23384 ⟨1336603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23384
    ⟨1336603, by decide⟩ (by decide) (![⟨1336489, by decide⟩,⟨1336523, by decide⟩,⟨1336561, by decide⟩,⟨1336602, by decide⟩]) unmarked_context_10_23384_1336603 node_context_10_23384_1336603
  intro a
  fin_cases a
  · exact context_11_93536_1336489
  · exact context_11_93537_1336523
  · exact context_11_93538_1336561
  · exact context_11_93539_1336602

theorem selected_cut_47736 : selected 10 ⟨1336622, by decide⟩
    (prefixPartial 11 93540) = some ⟨11, 2, 0, 1336622, 93540, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_93540_1336622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93540 ⟨1336622, by decide⟩ :=
  accepted_of_selected 11 93540 ⟨1336622, by decide⟩ ⟨11, 2, 0, 1336622, 93540, 1493, 262144⟩
    (by decide) selected_cut_47736

theorem selected_cut_47737 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93541) = some ⟨11, 1, 0, 892405, 93541, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93541_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93541 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93541 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93541, 1, 262144⟩
    (by decide) selected_cut_47737

theorem selected_cut_47738 : selected 10 ⟨1336659, by decide⟩
    (prefixPartial 11 93542) = some ⟨11, 2, 0, 1336659, 93542, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_93542_1336659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93542 ⟨1336659, by decide⟩ :=
  accepted_of_selected 11 93542 ⟨1336659, by decide⟩ ⟨11, 2, 0, 1336659, 93542, 2165, 262144⟩
    (by decide) selected_cut_47738

theorem selected_cut_47739 : selected 10 ⟨1336677, by decide⟩
    (prefixPartial 11 93543) = some ⟨11, 2, 0, 1336677, 93543, 1241, 262144⟩ := by
  decide +kernel

theorem context_11_93543_1336677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93543 ⟨1336677, by decide⟩ :=
  accepted_of_selected 11 93543 ⟨1336677, by decide⟩ ⟨11, 2, 0, 1336677, 93543, 1241, 262144⟩
    (by decide) selected_cut_47739

theorem unmarked_context_10_23385_1336678 : frontier 11 ⟨1336678, by decide⟩
    (prefixCache 10 23385) (prefixPartial 10 23385) = false := by
  decide +kernel

theorem node_context_10_23385_1336678 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336678, by decide⟩ =
    .split (coordinate 10) (![⟨1336622, by decide⟩,⟨892405, by decide⟩,⟨1336659, by decide⟩,⟨1336677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23385_1336678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23385 ⟨1336678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23385
    ⟨1336678, by decide⟩ (by decide) (![⟨1336622, by decide⟩,⟨892405, by decide⟩,⟨1336659, by decide⟩,⟨1336677, by decide⟩]) unmarked_context_10_23385_1336678 node_context_10_23385_1336678
  intro a
  fin_cases a
  · exact context_11_93540_1336622
  · exact context_11_93541_892405
  · exact context_11_93542_1336659
  · exact context_11_93543_1336677

theorem selected_cut_47740 : selected 11 ⟨1336715, by decide⟩
    (prefixPartial 10 23386) = some ⟨10, 2, 0, 1336715, 23386, 2521, 1048576⟩ := by
  decide +kernel

theorem context_10_23386_1336715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23386 ⟨1336715, by decide⟩ :=
  accepted_of_selected 10 23386 ⟨1336715, by decide⟩ ⟨10, 2, 0, 1336715, 23386, 2521, 1048576⟩
    (by decide) selected_cut_47740

theorem selected_cut_47741 : selected 10 ⟨1336734, by decide⟩
    (prefixPartial 11 93548) = some ⟨11, 2, 0, 1336734, 93548, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_93548_1336734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93548 ⟨1336734, by decide⟩ :=
  accepted_of_selected 11 93548 ⟨1336734, by decide⟩ ⟨11, 2, 0, 1336734, 93548, 1521, 262144⟩
    (by decide) selected_cut_47741

theorem selected_cut_47742 : selected 10 ⟨1336747, by decide⟩
    (prefixPartial 11 93549) = some ⟨11, 2, 0, 1336747, 93549, 893, 262144⟩ := by
  decide +kernel

theorem context_11_93549_1336747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93549 ⟨1336747, by decide⟩ :=
  accepted_of_selected 11 93549 ⟨1336747, by decide⟩ ⟨11, 2, 0, 1336747, 93549, 893, 262144⟩
    (by decide) selected_cut_47742

theorem selected_cut_47743 : selected 10 ⟨1336767, by decide⟩
    (prefixPartial 11 93550) = some ⟨11, 2, 0, 1336767, 93550, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_93550_1336767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93550 ⟨1336767, by decide⟩ :=
  accepted_of_selected 11 93550 ⟨1336767, by decide⟩ ⟨11, 2, 0, 1336767, 93550, 1313, 262144⟩
    (by decide) selected_cut_47743

theorem selected_cut_47744 : selected 10 ⟨1336774, by decide⟩
    (prefixPartial 11 93551) = some ⟨11, 2, 0, 1336774, 93551, 385, 262144⟩ := by
  decide +kernel

theorem context_11_93551_1336774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93551 ⟨1336774, by decide⟩ :=
  accepted_of_selected 11 93551 ⟨1336774, by decide⟩ ⟨11, 2, 0, 1336774, 93551, 385, 262144⟩
    (by decide) selected_cut_47744

theorem unmarked_context_10_23387_1336775 : frontier 11 ⟨1336775, by decide⟩
    (prefixCache 10 23387) (prefixPartial 10 23387) = false := by
  decide +kernel

theorem node_context_10_23387_1336775 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336775, by decide⟩ =
    .split (coordinate 10) (![⟨1336734, by decide⟩,⟨1336747, by decide⟩,⟨1336767, by decide⟩,⟨1336774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23387_1336775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23387 ⟨1336775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23387
    ⟨1336775, by decide⟩ (by decide) (![⟨1336734, by decide⟩,⟨1336747, by decide⟩,⟨1336767, by decide⟩,⟨1336774, by decide⟩]) unmarked_context_10_23387_1336775 node_context_10_23387_1336775
  intro a
  fin_cases a
  · exact context_11_93548_1336734
  · exact context_11_93549_1336747
  · exact context_11_93550_1336767
  · exact context_11_93551_1336774

theorem unmarked_context_9_5846_1336776 : frontier 12 ⟨1336776, by decide⟩
    (prefixCache 9 5846) (prefixPartial 9 5846) = false := by
  decide +kernel

theorem node_context_9_5846_1336776 : EJMOriginalGlobalDAGData.nodes 12 ⟨1336776, by decide⟩ =
    .split (coordinate 9) (![⟨1336603, by decide⟩,⟨1336678, by decide⟩,⟨1336715, by decide⟩,⟨1336775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5846_1336776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5846 ⟨1336776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5846
    ⟨1336776, by decide⟩ (by decide) (![⟨1336603, by decide⟩,⟨1336678, by decide⟩,⟨1336715, by decide⟩,⟨1336775, by decide⟩]) unmarked_context_9_5846_1336776 node_context_9_5846_1336776
  intro a
  fin_cases a
  · exact context_10_23384_1336603
  · exact context_10_23385_1336678
  · exact context_10_23386_1336715
  · exact context_10_23387_1336775

theorem selected_cut_47745 : selected 10 ⟨1336787, by decide⟩
    (prefixPartial 11 93552) = some ⟨11, 2, 0, 1336787, 93552, 805, 262144⟩ := by
  decide +kernel

theorem context_11_93552_1336787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93552 ⟨1336787, by decide⟩ :=
  accepted_of_selected 11 93552 ⟨1336787, by decide⟩ ⟨11, 2, 0, 1336787, 93552, 805, 262144⟩
    (by decide) selected_cut_47745

theorem selected_cut_47746 : selected 10 ⟨1336807, by decide⟩
    (prefixPartial 11 93553) = some ⟨11, 2, 0, 1336807, 93553, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_93553_1336807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93553 ⟨1336807, by decide⟩ :=
  accepted_of_selected 11 93553 ⟨1336807, by decide⟩ ⟨11, 2, 0, 1336807, 93553, 1129, 262144⟩
    (by decide) selected_cut_47746

theorem selected_cut_47747 : selected 10 ⟨1336825, by decide⟩
    (prefixPartial 11 93554) = some ⟨11, 2, 0, 1336825, 93554, 1301, 262144⟩ := by
  decide +kernel

theorem context_11_93554_1336825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93554 ⟨1336825, by decide⟩ :=
  accepted_of_selected 11 93554 ⟨1336825, by decide⟩ ⟨11, 2, 0, 1336825, 93554, 1301, 262144⟩
    (by decide) selected_cut_47747

theorem selected_cut_47748 : selected 10 ⟨1336851, by decide⟩
    (prefixPartial 11 93555) = some ⟨11, 2, 0, 1336851, 93555, 1045, 262144⟩ := by
  decide +kernel

theorem context_11_93555_1336851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93555 ⟨1336851, by decide⟩ :=
  accepted_of_selected 11 93555 ⟨1336851, by decide⟩ ⟨11, 2, 0, 1336851, 93555, 1045, 262144⟩
    (by decide) selected_cut_47748

theorem unmarked_context_10_23388_1336852 : frontier 11 ⟨1336852, by decide⟩
    (prefixCache 10 23388) (prefixPartial 10 23388) = false := by
  decide +kernel

theorem node_context_10_23388_1336852 : EJMOriginalGlobalDAGData.nodes 11 ⟨1336852, by decide⟩ =
    .split (coordinate 10) (![⟨1336787, by decide⟩,⟨1336807, by decide⟩,⟨1336825, by decide⟩,⟨1336851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23388_1336852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23388 ⟨1336852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23388
    ⟨1336852, by decide⟩ (by decide) (![⟨1336787, by decide⟩,⟨1336807, by decide⟩,⟨1336825, by decide⟩,⟨1336851, by decide⟩]) unmarked_context_10_23388_1336852 node_context_10_23388_1336852
  intro a
  fin_cases a
  · exact context_11_93552_1336787
  · exact context_11_93553_1336807
  · exact context_11_93554_1336825
  · exact context_11_93555_1336851

theorem selected_cut_47749 : selected 11 ⟨1336886, by decide⟩
    (prefixPartial 10 23389) = some ⟨10, 2, 0, 1336886, 23389, 1877, 1048576⟩ := by
  decide +kernel

theorem context_10_23389_1336886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23389 ⟨1336886, by decide⟩ :=
  accepted_of_selected 10 23389 ⟨1336886, by decide⟩ ⟨10, 2, 0, 1336886, 23389, 1877, 1048576⟩
    (by decide) selected_cut_47749

theorem selected_cut_47750 : selected 11 ⟨1336919, by decide⟩
    (prefixPartial 10 23390) = some ⟨10, 2, 0, 1336919, 23390, 1209, 1048576⟩ := by
  decide +kernel

theorem context_10_23390_1336919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23390 ⟨1336919, by decide⟩ :=
  accepted_of_selected 10 23390 ⟨1336919, by decide⟩ ⟨10, 2, 0, 1336919, 23390, 1209, 1048576⟩
    (by decide) selected_cut_47750

theorem selected_cut_47751 : selected 11 ⟨1336923, by decide⟩
    (prefixPartial 10 23391) = some ⟨10, 2, 0, 1336923, 23391, 173, 1048576⟩ := by
  decide +kernel

theorem context_10_23391_1336923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23391 ⟨1336923, by decide⟩ :=
  accepted_of_selected 10 23391 ⟨1336923, by decide⟩ ⟨10, 2, 0, 1336923, 23391, 173, 1048576⟩
    (by decide) selected_cut_47751

theorem unmarked_context_9_5847_1336924 : frontier 12 ⟨1336924, by decide⟩
    (prefixCache 9 5847) (prefixPartial 9 5847) = false := by
  decide +kernel

theorem node_context_9_5847_1336924 : EJMOriginalGlobalDAGData.nodes 12 ⟨1336924, by decide⟩ =
    .split (coordinate 9) (![⟨1336852, by decide⟩,⟨1336886, by decide⟩,⟨1336919, by decide⟩,⟨1336923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5847_1336924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5847 ⟨1336924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5847
    ⟨1336924, by decide⟩ (by decide) (![⟨1336852, by decide⟩,⟨1336886, by decide⟩,⟨1336919, by decide⟩,⟨1336923, by decide⟩]) unmarked_context_9_5847_1336924 node_context_9_5847_1336924
  intro a
  fin_cases a
  · exact context_10_23388_1336852
  · exact context_10_23389_1336886
  · exact context_10_23390_1336919
  · exact context_10_23391_1336923

theorem unmarked_context_8_1461_1336925 : frontier 13 ⟨1336925, by decide⟩
    (prefixCache 8 1461) (prefixPartial 8 1461) = false := by
  decide +kernel

theorem node_context_8_1461_1336925 : EJMOriginalGlobalDAGData.nodes 13 ⟨1336925, by decide⟩ =
    .split (coordinate 8) (![⟨1335970, by decide⟩,⟨1336474, by decide⟩,⟨1336776, by decide⟩,⟨1336924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1461_1336925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1461 ⟨1336925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1461
    ⟨1336925, by decide⟩ (by decide) (![⟨1335970, by decide⟩,⟨1336474, by decide⟩,⟨1336776, by decide⟩,⟨1336924, by decide⟩]) unmarked_context_8_1461_1336925 node_context_8_1461_1336925
  intro a
  fin_cases a
  · exact context_9_5844_1335970
  · exact context_9_5845_1336474
  · exact context_9_5846_1336776
  · exact context_9_5847_1336924

theorem selected_cut_47752 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93568) = some ⟨11, 1, 0, 434745, 93568, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93568_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93568 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93568 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93568, 1, 262144⟩
    (by decide) selected_cut_47752

theorem selected_cut_47753 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93569) = some ⟨11, 1, 0, 167448, 93569, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93569_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93569 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93569 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93569, 1, 262144⟩
    (by decide) selected_cut_47753

theorem selected_cut_47754 : selected 10 ⟨1336988, by decide⟩
    (prefixPartial 11 93570) = some ⟨11, 2, 0, 1336988, 93570, 3193, 262144⟩ := by
  decide +kernel

theorem context_11_93570_1336988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93570 ⟨1336988, by decide⟩ :=
  accepted_of_selected 11 93570 ⟨1336988, by decide⟩ ⟨11, 2, 0, 1336988, 93570, 3193, 262144⟩
    (by decide) selected_cut_47754

theorem selected_cut_47755 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 374284) = some ⟨12, 1, 0, 448748, 374284, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374284_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374284 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 374284 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 374284, 1, 65536⟩
    (by decide) selected_cut_47755

theorem selected_cut_47756 : selected 9 ⟨1337065, by decide⟩
    (prefixPartial 12 374285) = some ⟨12, 2, 0, 1337065, 374285, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_374285_1337065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374285 ⟨1337065, by decide⟩ :=
  accepted_of_selected 12 374285 ⟨1337065, by decide⟩ ⟨12, 2, 0, 1337065, 374285, 3277, 65536⟩
    (by decide) selected_cut_47756

theorem selected_cut_47757 : selected 9 ⟨1337119, by decide⟩
    (prefixPartial 12 374286) = some ⟨12, 2, 0, 1337119, 374286, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_374286_1337119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374286 ⟨1337119, by decide⟩ :=
  accepted_of_selected 12 374286 ⟨1337119, by decide⟩ ⟨12, 2, 0, 1337119, 374286, 3173, 65536⟩
    (by decide) selected_cut_47757

theorem selected_cut_47758 : selected 9 ⟨1337181, by decide⟩
    (prefixPartial 12 374287) = some ⟨12, 2, 0, 1337181, 374287, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_374287_1337181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374287 ⟨1337181, by decide⟩ :=
  accepted_of_selected 12 374287 ⟨1337181, by decide⟩ ⟨12, 2, 0, 1337181, 374287, 3225, 65536⟩
    (by decide) selected_cut_47758

theorem unmarked_context_11_93571_1337182 : frontier 10 ⟨1337182, by decide⟩
    (prefixCache 11 93571) (prefixPartial 11 93571) = false := by
  decide +kernel

theorem node_context_11_93571_1337182 : EJMOriginalGlobalDAGData.nodes 10 ⟨1337182, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1337065, by decide⟩,⟨1337119, by decide⟩,⟨1337181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93571_1337182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93571 ⟨1337182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93571
    ⟨1337182, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1337065, by decide⟩,⟨1337119, by decide⟩,⟨1337181, by decide⟩]) unmarked_context_11_93571_1337182 node_context_11_93571_1337182
  intro a
  fin_cases a
  · exact context_12_374284_448748
  · exact context_12_374285_1337065
  · exact context_12_374286_1337119
  · exact context_12_374287_1337181

theorem unmarked_context_10_23392_1337183 : frontier 11 ⟨1337183, by decide⟩
    (prefixCache 10 23392) (prefixPartial 10 23392) = false := by
  decide +kernel

theorem node_context_10_23392_1337183 : EJMOriginalGlobalDAGData.nodes 11 ⟨1337183, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1336988, by decide⟩,⟨1337182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23392_1337183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23392 ⟨1337183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23392
    ⟨1337183, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1336988, by decide⟩,⟨1337182, by decide⟩]) unmarked_context_10_23392_1337183 node_context_10_23392_1337183
  intro a
  fin_cases a
  · exact context_11_93568_434745
  · exact context_11_93569_167448
  · exact context_11_93570_1336988
  · exact context_11_93571_1337182

theorem selected_cut_47759 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 374288) = some ⟨12, 1, 0, 1255011, 374288, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374288_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374288 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 374288 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 374288, 1, 65536⟩
    (by decide) selected_cut_47759

theorem selected_cut_47760 : selected 9 ⟨1337229, by decide⟩
    (prefixPartial 12 374289) = some ⟨12, 2, 0, 1337229, 374289, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_374289_1337229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374289 ⟨1337229, by decide⟩ :=
  accepted_of_selected 12 374289 ⟨1337229, by decide⟩ ⟨12, 2, 0, 1337229, 374289, 2669, 65536⟩
    (by decide) selected_cut_47760

theorem selected_cut_47761 : selected 9 ⟨1337280, by decide⟩
    (prefixPartial 12 374290) = some ⟨12, 2, 0, 1337280, 374290, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_374290_1337280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374290 ⟨1337280, by decide⟩ :=
  accepted_of_selected 12 374290 ⟨1337280, by decide⟩ ⟨12, 2, 0, 1337280, 374290, 2733, 65536⟩
    (by decide) selected_cut_47761

theorem selected_cut_47762 : selected 9 ⟨1337347, by decide⟩
    (prefixPartial 12 374291) = some ⟨12, 2, 0, 1337347, 374291, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_374291_1337347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374291 ⟨1337347, by decide⟩ :=
  accepted_of_selected 12 374291 ⟨1337347, by decide⟩ ⟨12, 2, 0, 1337347, 374291, 3265, 65536⟩
    (by decide) selected_cut_47762

theorem unmarked_context_11_93572_1337348 : frontier 10 ⟨1337348, by decide⟩
    (prefixCache 11 93572) (prefixPartial 11 93572) = false := by
  decide +kernel

theorem node_context_11_93572_1337348 : EJMOriginalGlobalDAGData.nodes 10 ⟨1337348, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1337229, by decide⟩,⟨1337280, by decide⟩,⟨1337347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93572_1337348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93572 ⟨1337348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93572
    ⟨1337348, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1337229, by decide⟩,⟨1337280, by decide⟩,⟨1337347, by decide⟩]) unmarked_context_11_93572_1337348 node_context_11_93572_1337348
  intro a
  fin_cases a
  · exact context_12_374288_1255011
  · exact context_12_374289_1337229
  · exact context_12_374290_1337280
  · exact context_12_374291_1337347

theorem selected_cut_47763 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93573) = some ⟨11, 1, 0, 892405, 93573, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93573_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93573 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93573 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93573, 1, 262144⟩
    (by decide) selected_cut_47763

theorem selected_cut_47764 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 374296) = some ⟨12, 1, 0, 994572, 374296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374296_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374296 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 374296 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 374296, 1, 65536⟩
    (by decide) selected_cut_47764

theorem selected_cut_47765 : selected 9 ⟨1337383, by decide⟩
    (prefixPartial 12 374297) = some ⟨12, 2, 0, 1337383, 374297, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_374297_1337383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374297 ⟨1337383, by decide⟩ :=
  accepted_of_selected 12 374297 ⟨1337383, by decide⟩ ⟨12, 2, 0, 1337383, 374297, 2257, 65536⟩
    (by decide) selected_cut_47765

theorem selected_cut_47766 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 374298) = some ⟨12, 1, 0, 893903, 374298, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374298_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374298 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 374298 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 374298, 1, 65536⟩
    (by decide) selected_cut_47766

theorem selected_cut_47767 : selected 9 ⟨1337435, by decide⟩
    (prefixPartial 12 374299) = some ⟨12, 2, 0, 1337435, 374299, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_374299_1337435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374299 ⟨1337435, by decide⟩ :=
  accepted_of_selected 12 374299 ⟨1337435, by decide⟩ ⟨12, 2, 0, 1337435, 374299, 2837, 65536⟩
    (by decide) selected_cut_47767

theorem unmarked_context_11_93574_1337436 : frontier 10 ⟨1337436, by decide⟩
    (prefixCache 11 93574) (prefixPartial 11 93574) = false := by
  decide +kernel

theorem node_context_11_93574_1337436 : EJMOriginalGlobalDAGData.nodes 10 ⟨1337436, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1337383, by decide⟩,⟨893903, by decide⟩,⟨1337435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93574_1337436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93574 ⟨1337436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93574
    ⟨1337436, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1337383, by decide⟩,⟨893903, by decide⟩,⟨1337435, by decide⟩]) unmarked_context_11_93574_1337436 node_context_11_93574_1337436
  intro a
  fin_cases a
  · exact context_12_374296_994572
  · exact context_12_374297_1337383
  · exact context_12_374298_893903
  · exact context_12_374299_1337435

theorem selected_cut_47768 : selected 9 ⟨1337491, by decide⟩
    (prefixPartial 12 374300) = some ⟨12, 2, 0, 1337491, 374300, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_374300_1337491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374300 ⟨1337491, by decide⟩ :=
  accepted_of_selected 12 374300 ⟨1337491, by decide⟩ ⟨12, 2, 0, 1337491, 374300, 3045, 65536⟩
    (by decide) selected_cut_47768

theorem selected_cut_47769 : selected 9 ⟨1337537, by decide⟩
    (prefixPartial 12 374301) = some ⟨12, 2, 0, 1337537, 374301, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_374301_1337537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374301 ⟨1337537, by decide⟩ :=
  accepted_of_selected 12 374301 ⟨1337537, by decide⟩ ⟨12, 2, 0, 1337537, 374301, 2589, 65536⟩
    (by decide) selected_cut_47769

theorem selected_cut_47770 : selected 9 ⟨1337582, by decide⟩
    (prefixPartial 12 374302) = some ⟨12, 2, 0, 1337582, 374302, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_374302_1337582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374302 ⟨1337582, by decide⟩ :=
  accepted_of_selected 12 374302 ⟨1337582, by decide⟩ ⟨12, 2, 0, 1337582, 374302, 2529, 65536⟩
    (by decide) selected_cut_47770

theorem selected_cut_47771 : selected 9 ⟨1337640, by decide⟩
    (prefixPartial 12 374303) = some ⟨12, 2, 0, 1337640, 374303, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_374303_1337640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374303 ⟨1337640, by decide⟩ :=
  accepted_of_selected 12 374303 ⟨1337640, by decide⟩ ⟨12, 2, 0, 1337640, 374303, 2797, 65536⟩
    (by decide) selected_cut_47771

theorem unmarked_context_11_93575_1337641 : frontier 10 ⟨1337641, by decide⟩
    (prefixCache 11 93575) (prefixPartial 11 93575) = false := by
  decide +kernel

theorem node_context_11_93575_1337641 : EJMOriginalGlobalDAGData.nodes 10 ⟨1337641, by decide⟩ =
    .split (coordinate 11) (![⟨1337491, by decide⟩,⟨1337537, by decide⟩,⟨1337582, by decide⟩,⟨1337640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93575_1337641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93575 ⟨1337641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93575
    ⟨1337641, by decide⟩ (by decide) (![⟨1337491, by decide⟩,⟨1337537, by decide⟩,⟨1337582, by decide⟩,⟨1337640, by decide⟩]) unmarked_context_11_93575_1337641 node_context_11_93575_1337641
  intro a
  fin_cases a
  · exact context_12_374300_1337491
  · exact context_12_374301_1337537
  · exact context_12_374302_1337582
  · exact context_12_374303_1337640

theorem unmarked_context_10_23393_1337642 : frontier 11 ⟨1337642, by decide⟩
    (prefixCache 10 23393) (prefixPartial 10 23393) = false := by
  decide +kernel

theorem node_context_10_23393_1337642 : EJMOriginalGlobalDAGData.nodes 11 ⟨1337642, by decide⟩ =
    .split (coordinate 10) (![⟨1337348, by decide⟩,⟨892405, by decide⟩,⟨1337436, by decide⟩,⟨1337641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23393_1337642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23393 ⟨1337642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23393
    ⟨1337642, by decide⟩ (by decide) (![⟨1337348, by decide⟩,⟨892405, by decide⟩,⟨1337436, by decide⟩,⟨1337641, by decide⟩]) unmarked_context_10_23393_1337642 node_context_10_23393_1337642
  intro a
  fin_cases a
  · exact context_11_93572_1337348
  · exact context_11_93573_892405
  · exact context_11_93574_1337436
  · exact context_11_93575_1337641

theorem selected_cut_47772 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374304) = some ⟨12, 1, 0, 435790, 374304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374304_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374304 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374304 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374304, 1, 65536⟩
    (by decide) selected_cut_47772

theorem selected_cut_47773 : selected 9 ⟨1337692, by decide⟩
    (prefixPartial 12 374305) = some ⟨12, 2, 0, 1337692, 374305, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_374305_1337692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374305 ⟨1337692, by decide⟩ :=
  accepted_of_selected 12 374305 ⟨1337692, by decide⟩ ⟨12, 2, 0, 1337692, 374305, 2577, 65536⟩
    (by decide) selected_cut_47773

theorem selected_cut_47774 : selected 9 ⟨1337735, by decide⟩
    (prefixPartial 12 374306) = some ⟨12, 2, 0, 1337735, 374306, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_374306_1337735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374306 ⟨1337735, by decide⟩ :=
  accepted_of_selected 12 374306 ⟨1337735, by decide⟩ ⟨12, 2, 0, 1337735, 374306, 2545, 65536⟩
    (by decide) selected_cut_47774

theorem selected_cut_47775 : selected 9 ⟨1337795, by decide⟩
    (prefixPartial 12 374307) = some ⟨12, 2, 0, 1337795, 374307, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_374307_1337795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374307 ⟨1337795, by decide⟩ :=
  accepted_of_selected 12 374307 ⟨1337795, by decide⟩ ⟨12, 2, 0, 1337795, 374307, 2885, 65536⟩
    (by decide) selected_cut_47775

theorem unmarked_context_11_93576_1337796 : frontier 10 ⟨1337796, by decide⟩
    (prefixCache 11 93576) (prefixPartial 11 93576) = false := by
  decide +kernel

theorem node_context_11_93576_1337796 : EJMOriginalGlobalDAGData.nodes 10 ⟨1337796, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1337692, by decide⟩,⟨1337735, by decide⟩,⟨1337795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93576_1337796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93576 ⟨1337796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93576
    ⟨1337796, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1337692, by decide⟩,⟨1337735, by decide⟩,⟨1337795, by decide⟩]) unmarked_context_11_93576_1337796 node_context_11_93576_1337796
  intro a
  fin_cases a
  · exact context_12_374304_435790
  · exact context_12_374305_1337692
  · exact context_12_374306_1337735
  · exact context_12_374307_1337795

theorem selected_cut_47776 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374308) = some ⟨12, 1, 0, 435790, 374308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374308_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374308 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374308 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374308, 1, 65536⟩
    (by decide) selected_cut_47776

theorem selected_cut_47777 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 374309) = some ⟨12, 1, 0, 688903, 374309, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374309_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374309 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 374309 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 374309, 1, 65536⟩
    (by decide) selected_cut_47777

theorem selected_cut_47778 : selected 9 ⟨1337844, by decide⟩
    (prefixPartial 12 374310) = some ⟨12, 2, 0, 1337844, 374310, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_374310_1337844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374310 ⟨1337844, by decide⟩ :=
  accepted_of_selected 12 374310 ⟨1337844, by decide⟩ ⟨12, 2, 0, 1337844, 374310, 2669, 65536⟩
    (by decide) selected_cut_47778

theorem selected_cut_47779 : selected 9 ⟨1337898, by decide⟩
    (prefixPartial 12 374311) = some ⟨12, 2, 0, 1337898, 374311, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_374311_1337898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374311 ⟨1337898, by decide⟩ :=
  accepted_of_selected 12 374311 ⟨1337898, by decide⟩ ⟨12, 2, 0, 1337898, 374311, 2745, 65536⟩
    (by decide) selected_cut_47779

theorem unmarked_context_11_93577_1337899 : frontier 10 ⟨1337899, by decide⟩
    (prefixCache 11 93577) (prefixPartial 11 93577) = false := by
  decide +kernel

theorem node_context_11_93577_1337899 : EJMOriginalGlobalDAGData.nodes 10 ⟨1337899, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨688903, by decide⟩,⟨1337844, by decide⟩,⟨1337898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93577_1337899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93577 ⟨1337899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93577
    ⟨1337899, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨688903, by decide⟩,⟨1337844, by decide⟩,⟨1337898, by decide⟩]) unmarked_context_11_93577_1337899 node_context_11_93577_1337899
  intro a
  fin_cases a
  · exact context_12_374308_435790
  · exact context_12_374309_688903
  · exact context_12_374310_1337844
  · exact context_12_374311_1337898

theorem selected_cut_47780 : selected 10 ⟨1337946, by decide⟩
    (prefixPartial 11 93578) = some ⟨11, 2, 0, 1337946, 93578, 2585, 262144⟩ := by
  decide +kernel

theorem context_11_93578_1337946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93578 ⟨1337946, by decide⟩ :=
  accepted_of_selected 11 93578 ⟨1337946, by decide⟩ ⟨11, 2, 0, 1337946, 93578, 2585, 262144⟩
    (by decide) selected_cut_47780

theorem selected_cut_47781 : selected 9 ⟨1337994, by decide⟩
    (prefixPartial 12 374316) = some ⟨12, 2, 0, 1337994, 374316, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_374316_1337994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374316 ⟨1337994, by decide⟩ :=
  accepted_of_selected 12 374316 ⟨1337994, by decide⟩ ⟨12, 2, 0, 1337994, 374316, 1497, 65536⟩
    (by decide) selected_cut_47781

theorem selected_cut_47782 : selected 9 ⟨1338046, by decide⟩
    (prefixPartial 12 374317) = some ⟨12, 2, 0, 1338046, 374317, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_374317_1338046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374317 ⟨1338046, by decide⟩ :=
  accepted_of_selected 12 374317 ⟨1338046, by decide⟩ ⟨12, 2, 0, 1338046, 374317, 2553, 65536⟩
    (by decide) selected_cut_47782

theorem selected_cut_47783 : selected 9 ⟨1338088, by decide⟩
    (prefixPartial 12 374318) = some ⟨12, 2, 0, 1338088, 374318, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_374318_1338088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374318 ⟨1338088, by decide⟩ :=
  accepted_of_selected 12 374318 ⟨1338088, by decide⟩ ⟨12, 2, 0, 1338088, 374318, 2425, 65536⟩
    (by decide) selected_cut_47783

theorem selected_cut_47784 : selected 9 ⟨1338167, by decide⟩
    (prefixPartial 12 374319) = some ⟨12, 2, 0, 1338167, 374319, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_374319_1338167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374319 ⟨1338167, by decide⟩ :=
  accepted_of_selected 12 374319 ⟨1338167, by decide⟩ ⟨12, 2, 0, 1338167, 374319, 1541, 65536⟩
    (by decide) selected_cut_47784

theorem unmarked_context_11_93579_1338168 : frontier 10 ⟨1338168, by decide⟩
    (prefixCache 11 93579) (prefixPartial 11 93579) = false := by
  decide +kernel

theorem node_context_11_93579_1338168 : EJMOriginalGlobalDAGData.nodes 10 ⟨1338168, by decide⟩ =
    .split (coordinate 11) (![⟨1337994, by decide⟩,⟨1338046, by decide⟩,⟨1338088, by decide⟩,⟨1338167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93579_1338168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93579 ⟨1338168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93579
    ⟨1338168, by decide⟩ (by decide) (![⟨1337994, by decide⟩,⟨1338046, by decide⟩,⟨1338088, by decide⟩,⟨1338167, by decide⟩]) unmarked_context_11_93579_1338168 node_context_11_93579_1338168
  intro a
  fin_cases a
  · exact context_12_374316_1337994
  · exact context_12_374317_1338046
  · exact context_12_374318_1338088
  · exact context_12_374319_1338167

theorem unmarked_context_10_23394_1338169 : frontier 11 ⟨1338169, by decide⟩
    (prefixCache 10 23394) (prefixPartial 10 23394) = false := by
  decide +kernel

theorem node_context_10_23394_1338169 : EJMOriginalGlobalDAGData.nodes 11 ⟨1338169, by decide⟩ =
    .split (coordinate 10) (![⟨1337796, by decide⟩,⟨1337899, by decide⟩,⟨1337946, by decide⟩,⟨1338168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23394_1338169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23394 ⟨1338169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23394
    ⟨1338169, by decide⟩ (by decide) (![⟨1337796, by decide⟩,⟨1337899, by decide⟩,⟨1337946, by decide⟩,⟨1338168, by decide⟩]) unmarked_context_10_23394_1338169 node_context_10_23394_1338169
  intro a
  fin_cases a
  · exact context_11_93576_1337796
  · exact context_11_93577_1337899
  · exact context_11_93578_1337946
  · exact context_11_93579_1338168

theorem selected_cut_47785 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 374320) = some ⟨12, 1, 0, 1255011, 374320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374320_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374320 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 374320 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 374320, 1, 65536⟩
    (by decide) selected_cut_47785

theorem selected_cut_47786 : selected 9 ⟨1338206, by decide⟩
    (prefixPartial 12 374321) = some ⟨12, 2, 0, 1338206, 374321, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_374321_1338206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374321 ⟨1338206, by decide⟩ :=
  accepted_of_selected 12 374321 ⟨1338206, by decide⟩ ⟨12, 2, 0, 1338206, 374321, 2269, 65536⟩
    (by decide) selected_cut_47786

theorem selected_cut_47787 : selected 9 ⟨1338253, by decide⟩
    (prefixPartial 12 374322) = some ⟨12, 2, 0, 1338253, 374322, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_374322_1338253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374322 ⟨1338253, by decide⟩ :=
  accepted_of_selected 12 374322 ⟨1338253, by decide⟩ ⟨12, 2, 0, 1338253, 374322, 2433, 65536⟩
    (by decide) selected_cut_47787

theorem selected_cut_47788 : selected 9 ⟨1338306, by decide⟩
    (prefixPartial 12 374323) = some ⟨12, 2, 0, 1338306, 374323, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_374323_1338306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374323 ⟨1338306, by decide⟩ :=
  accepted_of_selected 12 374323 ⟨1338306, by decide⟩ ⟨12, 2, 0, 1338306, 374323, 2653, 65536⟩
    (by decide) selected_cut_47788

theorem unmarked_context_11_93580_1338307 : frontier 10 ⟨1338307, by decide⟩
    (prefixCache 11 93580) (prefixPartial 11 93580) = false := by
  decide +kernel

theorem node_context_11_93580_1338307 : EJMOriginalGlobalDAGData.nodes 10 ⟨1338307, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1338206, by decide⟩,⟨1338253, by decide⟩,⟨1338306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93580_1338307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93580 ⟨1338307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93580
    ⟨1338307, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1338206, by decide⟩,⟨1338253, by decide⟩,⟨1338306, by decide⟩]) unmarked_context_11_93580_1338307 node_context_11_93580_1338307
  intro a
  fin_cases a
  · exact context_12_374320_1255011
  · exact context_12_374321_1338206
  · exact context_12_374322_1338253
  · exact context_12_374323_1338306

theorem selected_cut_47789 : selected 9 ⟨1338369, by decide⟩
    (prefixPartial 12 374324) = some ⟨12, 2, 0, 1338369, 374324, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_374324_1338369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374324 ⟨1338369, by decide⟩ :=
  accepted_of_selected 12 374324 ⟨1338369, by decide⟩ ⟨12, 2, 0, 1338369, 374324, 2445, 65536⟩
    (by decide) selected_cut_47789

theorem selected_cut_47790 : selected 9 ⟨1338406, by decide⟩
    (prefixPartial 12 374325) = some ⟨12, 2, 0, 1338406, 374325, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_374325_1338406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374325 ⟨1338406, by decide⟩ :=
  accepted_of_selected 12 374325 ⟨1338406, by decide⟩ ⟨12, 2, 0, 1338406, 374325, 2069, 65536⟩
    (by decide) selected_cut_47790

theorem selected_cut_47791 : selected 9 ⟨1338443, by decide⟩
    (prefixPartial 12 374326) = some ⟨12, 2, 0, 1338443, 374326, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_374326_1338443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374326 ⟨1338443, by decide⟩ :=
  accepted_of_selected 12 374326 ⟨1338443, by decide⟩ ⟨12, 2, 0, 1338443, 374326, 2181, 65536⟩
    (by decide) selected_cut_47791

theorem selected_cut_47792 : selected 9 ⟨1338487, by decide⟩
    (prefixPartial 12 374327) = some ⟨12, 2, 0, 1338487, 374327, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_374327_1338487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374327 ⟨1338487, by decide⟩ :=
  accepted_of_selected 12 374327 ⟨1338487, by decide⟩ ⟨12, 2, 0, 1338487, 374327, 2209, 65536⟩
    (by decide) selected_cut_47792

theorem unmarked_context_11_93581_1338488 : frontier 10 ⟨1338488, by decide⟩
    (prefixCache 11 93581) (prefixPartial 11 93581) = false := by
  decide +kernel

theorem node_context_11_93581_1338488 : EJMOriginalGlobalDAGData.nodes 10 ⟨1338488, by decide⟩ =
    .split (coordinate 11) (![⟨1338369, by decide⟩,⟨1338406, by decide⟩,⟨1338443, by decide⟩,⟨1338487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93581_1338488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93581 ⟨1338488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93581
    ⟨1338488, by decide⟩ (by decide) (![⟨1338369, by decide⟩,⟨1338406, by decide⟩,⟨1338443, by decide⟩,⟨1338487, by decide⟩]) unmarked_context_11_93581_1338488 node_context_11_93581_1338488
  intro a
  fin_cases a
  · exact context_12_374324_1338369
  · exact context_12_374325_1338406
  · exact context_12_374326_1338443
  · exact context_12_374327_1338487

theorem selected_cut_47793 : selected 10 ⟨1338553, by decide⟩
    (prefixPartial 11 93582) = some ⟨11, 2, 0, 1338553, 93582, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_93582_1338553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93582 ⟨1338553, by decide⟩ :=
  accepted_of_selected 11 93582 ⟨1338553, by decide⟩ ⟨11, 2, 0, 1338553, 93582, 4037, 262144⟩
    (by decide) selected_cut_47793

theorem selected_cut_47794 : selected 9 ⟨1338600, by decide⟩
    (prefixPartial 12 374332) = some ⟨12, 2, 0, 1338600, 374332, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_374332_1338600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374332 ⟨1338600, by decide⟩ :=
  accepted_of_selected 12 374332 ⟨1338600, by decide⟩ ⟨12, 2, 0, 1338600, 374332, 2169, 65536⟩
    (by decide) selected_cut_47794

theorem selected_cut_47795 : selected 9 ⟨1338651, by decide⟩
    (prefixPartial 12 374333) = some ⟨12, 2, 0, 1338651, 374333, 825, 65536⟩ := by
  decide +kernel

theorem context_12_374333_1338651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374333 ⟨1338651, by decide⟩ :=
  accepted_of_selected 12 374333 ⟨1338651, by decide⟩ ⟨12, 2, 0, 1338651, 374333, 825, 65536⟩
    (by decide) selected_cut_47795

theorem selected_cut_47796 : selected 9 ⟨1338680, by decide⟩
    (prefixPartial 12 374334) = some ⟨12, 2, 0, 1338680, 374334, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_374334_1338680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374334 ⟨1338680, by decide⟩ :=
  accepted_of_selected 12 374334 ⟨1338680, by decide⟩ ⟨12, 2, 0, 1338680, 374334, 1797, 65536⟩
    (by decide) selected_cut_47796

theorem selected_cut_47797 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 374335) = some ⟨12, 1, 0, 1116246, 374335, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374335_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374335 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 374335 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 374335, 1, 65536⟩
    (by decide) selected_cut_47797

theorem unmarked_context_11_93583_1338681 : frontier 10 ⟨1338681, by decide⟩
    (prefixCache 11 93583) (prefixPartial 11 93583) = false := by
  decide +kernel

theorem node_context_11_93583_1338681 : EJMOriginalGlobalDAGData.nodes 10 ⟨1338681, by decide⟩ =
    .split (coordinate 11) (![⟨1338600, by decide⟩,⟨1338651, by decide⟩,⟨1338680, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93583_1338681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93583 ⟨1338681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93583
    ⟨1338681, by decide⟩ (by decide) (![⟨1338600, by decide⟩,⟨1338651, by decide⟩,⟨1338680, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_93583_1338681 node_context_11_93583_1338681
  intro a
  fin_cases a
  · exact context_12_374332_1338600
  · exact context_12_374333_1338651
  · exact context_12_374334_1338680
  · exact context_12_374335_1116246

theorem unmarked_context_10_23395_1338682 : frontier 11 ⟨1338682, by decide⟩
    (prefixCache 10 23395) (prefixPartial 10 23395) = false := by
  decide +kernel

theorem node_context_10_23395_1338682 : EJMOriginalGlobalDAGData.nodes 11 ⟨1338682, by decide⟩ =
    .split (coordinate 10) (![⟨1338307, by decide⟩,⟨1338488, by decide⟩,⟨1338553, by decide⟩,⟨1338681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23395_1338682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23395 ⟨1338682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23395
    ⟨1338682, by decide⟩ (by decide) (![⟨1338307, by decide⟩,⟨1338488, by decide⟩,⟨1338553, by decide⟩,⟨1338681, by decide⟩]) unmarked_context_10_23395_1338682 node_context_10_23395_1338682
  intro a
  fin_cases a
  · exact context_11_93580_1338307
  · exact context_11_93581_1338488
  · exact context_11_93582_1338553
  · exact context_11_93583_1338681

theorem unmarked_context_9_5848_1338683 : frontier 12 ⟨1338683, by decide⟩
    (prefixCache 9 5848) (prefixPartial 9 5848) = false := by
  decide +kernel

theorem node_context_9_5848_1338683 : EJMOriginalGlobalDAGData.nodes 12 ⟨1338683, by decide⟩ =
    .split (coordinate 9) (![⟨1337183, by decide⟩,⟨1337642, by decide⟩,⟨1338169, by decide⟩,⟨1338682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5848_1338683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5848 ⟨1338683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5848
    ⟨1338683, by decide⟩ (by decide) (![⟨1337183, by decide⟩,⟨1337642, by decide⟩,⟨1338169, by decide⟩,⟨1338682, by decide⟩]) unmarked_context_9_5848_1338683 node_context_9_5848_1338683
  intro a
  fin_cases a
  · exact context_10_23392_1337183
  · exact context_10_23393_1337642
  · exact context_10_23394_1338169
  · exact context_10_23395_1338682

theorem selected_cut_47798 : selected 10 ⟨1283168, by decide⟩
    (prefixPartial 11 93584) = some ⟨11, 1, 0, 1283168, 93584, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93584_1283168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93584 ⟨1283168, by decide⟩ :=
  accepted_of_selected 11 93584 ⟨1283168, by decide⟩ ⟨11, 1, 0, 1283168, 93584, 1, 262144⟩
    (by decide) selected_cut_47798

theorem selected_cut_47799 : selected 9 ⟨1338738, by decide⟩
    (prefixPartial 12 374340) = some ⟨12, 2, 0, 1338738, 374340, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_374340_1338738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374340 ⟨1338738, by decide⟩ :=
  accepted_of_selected 12 374340 ⟨1338738, by decide⟩ ⟨12, 2, 0, 1338738, 374340, 2001, 65536⟩
    (by decide) selected_cut_47799

theorem selected_cut_47800 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 374341) = some ⟨12, 1, 0, 1257136, 374341, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374341_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374341 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 374341 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 374341, 1, 65536⟩
    (by decide) selected_cut_47800

theorem selected_cut_47801 : selected 9 ⟨1338774, by decide⟩
    (prefixPartial 12 374342) = some ⟨12, 2, 0, 1338774, 374342, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_374342_1338774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374342 ⟨1338774, by decide⟩ :=
  accepted_of_selected 12 374342 ⟨1338774, by decide⟩ ⟨12, 2, 0, 1338774, 374342, 1881, 65536⟩
    (by decide) selected_cut_47801

theorem selected_cut_47802 : selected 9 ⟨1338809, by decide⟩
    (prefixPartial 12 374343) = some ⟨12, 2, 0, 1338809, 374343, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_374343_1338809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374343 ⟨1338809, by decide⟩ :=
  accepted_of_selected 12 374343 ⟨1338809, by decide⟩ ⟨12, 2, 0, 1338809, 374343, 1869, 65536⟩
    (by decide) selected_cut_47802

theorem unmarked_context_11_93585_1338810 : frontier 10 ⟨1338810, by decide⟩
    (prefixCache 11 93585) (prefixPartial 11 93585) = false := by
  decide +kernel

theorem node_context_11_93585_1338810 : EJMOriginalGlobalDAGData.nodes 10 ⟨1338810, by decide⟩ =
    .split (coordinate 11) (![⟨1338738, by decide⟩,⟨1257136, by decide⟩,⟨1338774, by decide⟩,⟨1338809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93585_1338810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93585 ⟨1338810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93585
    ⟨1338810, by decide⟩ (by decide) (![⟨1338738, by decide⟩,⟨1257136, by decide⟩,⟨1338774, by decide⟩,⟨1338809, by decide⟩]) unmarked_context_11_93585_1338810 node_context_11_93585_1338810
  intro a
  fin_cases a
  · exact context_12_374340_1338738
  · exact context_12_374341_1257136
  · exact context_12_374342_1338774
  · exact context_12_374343_1338809

theorem selected_cut_47803 : selected 9 ⟨1338861, by decide⟩
    (prefixPartial 12 374344) = some ⟨12, 2, 0, 1338861, 374344, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_374344_1338861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374344 ⟨1338861, by decide⟩ :=
  accepted_of_selected 12 374344 ⟨1338861, by decide⟩ ⟨12, 2, 0, 1338861, 374344, 2085, 65536⟩
    (by decide) selected_cut_47803

theorem selected_cut_47804 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 374345) = some ⟨12, 1, 0, 691709, 374345, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374345_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374345 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 374345 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 374345, 1, 65536⟩
    (by decide) selected_cut_47804

theorem selected_cut_47805 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 374346) = some ⟨12, 1, 0, 893903, 374346, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374346_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374346 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 374346 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 374346, 1, 65536⟩
    (by decide) selected_cut_47805

theorem selected_cut_47806 : selected 9 ⟨1338901, by decide⟩
    (prefixPartial 12 374347) = some ⟨12, 2, 0, 1338901, 374347, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_374347_1338901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374347 ⟨1338901, by decide⟩ :=
  accepted_of_selected 12 374347 ⟨1338901, by decide⟩ ⟨12, 2, 0, 1338901, 374347, 2041, 65536⟩
    (by decide) selected_cut_47806

theorem unmarked_context_11_93586_1338902 : frontier 10 ⟨1338902, by decide⟩
    (prefixCache 11 93586) (prefixPartial 11 93586) = false := by
  decide +kernel

theorem node_context_11_93586_1338902 : EJMOriginalGlobalDAGData.nodes 10 ⟨1338902, by decide⟩ =
    .split (coordinate 11) (![⟨1338861, by decide⟩,⟨691709, by decide⟩,⟨893903, by decide⟩,⟨1338901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93586_1338902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93586 ⟨1338902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93586
    ⟨1338902, by decide⟩ (by decide) (![⟨1338861, by decide⟩,⟨691709, by decide⟩,⟨893903, by decide⟩,⟨1338901, by decide⟩]) unmarked_context_11_93586_1338902 node_context_11_93586_1338902
  intro a
  fin_cases a
  · exact context_12_374344_1338861
  · exact context_12_374345_691709
  · exact context_12_374346_893903
  · exact context_12_374347_1338901

theorem selected_cut_47807 : selected 9 ⟨1338953, by decide⟩
    (prefixPartial 12 374348) = some ⟨12, 2, 0, 1338953, 374348, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_374348_1338953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374348 ⟨1338953, by decide⟩ :=
  accepted_of_selected 12 374348 ⟨1338953, by decide⟩ ⟨12, 2, 0, 1338953, 374348, 2101, 65536⟩
    (by decide) selected_cut_47807

theorem selected_cut_47808 : selected 9 ⟨1338986, by decide⟩
    (prefixPartial 12 374349) = some ⟨12, 2, 0, 1338986, 374349, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_374349_1338986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374349 ⟨1338986, by decide⟩ :=
  accepted_of_selected 12 374349 ⟨1338986, by decide⟩ ⟨12, 2, 0, 1338986, 374349, 1753, 65536⟩
    (by decide) selected_cut_47808

theorem selected_cut_47809 : selected 9 ⟨1339015, by decide⟩
    (prefixPartial 12 374350) = some ⟨12, 2, 0, 1339015, 374350, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_374350_1339015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374350 ⟨1339015, by decide⟩ :=
  accepted_of_selected 12 374350 ⟨1339015, by decide⟩ ⟨12, 2, 0, 1339015, 374350, 1869, 65536⟩
    (by decide) selected_cut_47809

theorem selected_cut_47810 : selected 9 ⟨1339049, by decide⟩
    (prefixPartial 12 374351) = some ⟨12, 2, 0, 1339049, 374351, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_374351_1339049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374351 ⟨1339049, by decide⟩ :=
  accepted_of_selected 12 374351 ⟨1339049, by decide⟩ ⟨12, 2, 0, 1339049, 374351, 1849, 65536⟩
    (by decide) selected_cut_47810

theorem unmarked_context_11_93587_1339050 : frontier 10 ⟨1339050, by decide⟩
    (prefixCache 11 93587) (prefixPartial 11 93587) = false := by
  decide +kernel

theorem node_context_11_93587_1339050 : EJMOriginalGlobalDAGData.nodes 10 ⟨1339050, by decide⟩ =
    .split (coordinate 11) (![⟨1338953, by decide⟩,⟨1338986, by decide⟩,⟨1339015, by decide⟩,⟨1339049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93587_1339050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93587 ⟨1339050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93587
    ⟨1339050, by decide⟩ (by decide) (![⟨1338953, by decide⟩,⟨1338986, by decide⟩,⟨1339015, by decide⟩,⟨1339049, by decide⟩]) unmarked_context_11_93587_1339050 node_context_11_93587_1339050
  intro a
  fin_cases a
  · exact context_12_374348_1338953
  · exact context_12_374349_1338986
  · exact context_12_374350_1339015
  · exact context_12_374351_1339049

theorem unmarked_context_10_23396_1339051 : frontier 11 ⟨1339051, by decide⟩
    (prefixCache 10 23396) (prefixPartial 10 23396) = false := by
  decide +kernel

theorem node_context_10_23396_1339051 : EJMOriginalGlobalDAGData.nodes 11 ⟨1339051, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1338810, by decide⟩,⟨1338902, by decide⟩,⟨1339050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23396_1339051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23396 ⟨1339051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23396
    ⟨1339051, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1338810, by decide⟩,⟨1338902, by decide⟩,⟨1339050, by decide⟩]) unmarked_context_10_23396_1339051 node_context_10_23396_1339051
  intro a
  fin_cases a
  · exact context_11_93584_1283168
  · exact context_11_93585_1338810
  · exact context_11_93586_1338902
  · exact context_11_93587_1339050

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
