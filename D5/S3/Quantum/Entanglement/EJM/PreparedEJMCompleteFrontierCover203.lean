/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover202
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19491 : selected 8 ⟨498796, by decide⟩
    (prefixPartial 13 288918) = some ⟨13, 2, 0, 498796, 288918, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_288918_498796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288918 ⟨498796, by decide⟩ :=
  accepted_of_selected 13 288918 ⟨498796, by decide⟩ ⟨13, 2, 0, 498796, 288918, 1181, 16384⟩
    (by decide) selected_cut_19491

theorem selected_cut_19492 : selected 8 ⟨498805, by decide⟩
    (prefixPartial 13 288919) = some ⟨13, 2, 0, 498805, 288919, 981, 16384⟩ := by
  decide +kernel

theorem context_13_288919_498805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288919 ⟨498805, by decide⟩ :=
  accepted_of_selected 13 288919 ⟨498805, by decide⟩ ⟨13, 2, 0, 498805, 288919, 981, 16384⟩
    (by decide) selected_cut_19492

theorem unmarked_context_12_72229_498806 : frontier 9 ⟨498806, by decide⟩
    (prefixCache 12 72229) (prefixPartial 12 72229) = false := by
  decide +kernel

theorem node_context_12_72229_498806 : EJMOriginalGlobalDAGData.nodes 9 ⟨498806, by decide⟩ =
    .split (coordinate 12) (![⟨498749, by decide⟩,⟨498780, by decide⟩,⟨498796, by decide⟩,⟨498805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72229_498806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72229 ⟨498806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72229
    ⟨498806, by decide⟩ (by decide) (![⟨498749, by decide⟩,⟨498780, by decide⟩,⟨498796, by decide⟩,⟨498805, by decide⟩]) unmarked_context_12_72229_498806 node_context_12_72229_498806
  intro a
  fin_cases a
  · exact context_13_288916_498749
  · exact context_13_288917_498780
  · exact context_13_288918_498796
  · exact context_13_288919_498805

theorem selected_cut_19493 : selected 8 ⟨498827, by decide⟩
    (prefixPartial 13 288920) = some ⟨13, 2, 0, 498827, 288920, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_288920_498827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288920 ⟨498827, by decide⟩ :=
  accepted_of_selected 13 288920 ⟨498827, by decide⟩ ⟨13, 2, 0, 498827, 288920, 1165, 16384⟩
    (by decide) selected_cut_19493

theorem selected_cut_19494 : selected 8 ⟨498852, by decide⟩
    (prefixPartial 13 288921) = some ⟨13, 2, 0, 498852, 288921, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_288921_498852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288921 ⟨498852, by decide⟩ :=
  accepted_of_selected 13 288921 ⟨498852, by decide⟩ ⟨13, 2, 0, 498852, 288921, 2097, 16384⟩
    (by decide) selected_cut_19494

theorem selected_cut_19495 : selected 8 ⟨498869, by decide⟩
    (prefixPartial 13 288922) = some ⟨13, 2, 0, 498869, 288922, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_288922_498869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288922 ⟨498869, by decide⟩ :=
  accepted_of_selected 13 288922 ⟨498869, by decide⟩ ⟨13, 2, 0, 498869, 288922, 1161, 16384⟩
    (by decide) selected_cut_19495

theorem selected_cut_19496 : selected 8 ⟨498877, by decide⟩
    (prefixPartial 13 288923) = some ⟨13, 2, 0, 498877, 288923, 961, 16384⟩ := by
  decide +kernel

theorem context_13_288923_498877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288923 ⟨498877, by decide⟩ :=
  accepted_of_selected 13 288923 ⟨498877, by decide⟩ ⟨13, 2, 0, 498877, 288923, 961, 16384⟩
    (by decide) selected_cut_19496

theorem unmarked_context_12_72230_498878 : frontier 9 ⟨498878, by decide⟩
    (prefixCache 12 72230) (prefixPartial 12 72230) = false := by
  decide +kernel

theorem node_context_12_72230_498878 : EJMOriginalGlobalDAGData.nodes 9 ⟨498878, by decide⟩ =
    .split (coordinate 12) (![⟨498827, by decide⟩,⟨498852, by decide⟩,⟨498869, by decide⟩,⟨498877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72230_498878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72230 ⟨498878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72230
    ⟨498878, by decide⟩ (by decide) (![⟨498827, by decide⟩,⟨498852, by decide⟩,⟨498869, by decide⟩,⟨498877, by decide⟩]) unmarked_context_12_72230_498878 node_context_12_72230_498878
  intro a
  fin_cases a
  · exact context_13_288920_498827
  · exact context_13_288921_498852
  · exact context_13_288922_498869
  · exact context_13_288923_498877

theorem selected_cut_19497 : selected 8 ⟨498902, by decide⟩
    (prefixPartial 13 288924) = some ⟨13, 2, 0, 498902, 288924, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_288924_498902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288924 ⟨498902, by decide⟩ :=
  accepted_of_selected 13 288924 ⟨498902, by decide⟩ ⟨13, 2, 0, 498902, 288924, 1189, 16384⟩
    (by decide) selected_cut_19497

theorem selected_cut_19498 : selected 8 ⟨498941, by decide⟩
    (prefixPartial 13 288925) = some ⟨13, 2, 0, 498941, 288925, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_288925_498941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288925 ⟨498941, by decide⟩ :=
  accepted_of_selected 13 288925 ⟨498941, by decide⟩ ⟨13, 2, 0, 498941, 288925, 2433, 16384⟩
    (by decide) selected_cut_19498

theorem selected_cut_19499 : selected 8 ⟨498959, by decide⟩
    (prefixPartial 13 288926) = some ⟨13, 2, 0, 498959, 288926, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_288926_498959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288926 ⟨498959, by decide⟩ :=
  accepted_of_selected 13 288926 ⟨498959, by decide⟩ ⟨13, 2, 0, 498959, 288926, 1569, 16384⟩
    (by decide) selected_cut_19499

theorem selected_cut_19500 : selected 8 ⟨498969, by decide⟩
    (prefixPartial 13 288927) = some ⟨13, 2, 0, 498969, 288927, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_288927_498969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288927 ⟨498969, by decide⟩ :=
  accepted_of_selected 13 288927 ⟨498969, by decide⟩ ⟨13, 2, 0, 498969, 288927, 1065, 16384⟩
    (by decide) selected_cut_19500

theorem unmarked_context_12_72231_498970 : frontier 9 ⟨498970, by decide⟩
    (prefixCache 12 72231) (prefixPartial 12 72231) = false := by
  decide +kernel

theorem node_context_12_72231_498970 : EJMOriginalGlobalDAGData.nodes 9 ⟨498970, by decide⟩ =
    .split (coordinate 12) (![⟨498902, by decide⟩,⟨498941, by decide⟩,⟨498959, by decide⟩,⟨498969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72231_498970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72231 ⟨498970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72231
    ⟨498970, by decide⟩ (by decide) (![⟨498902, by decide⟩,⟨498941, by decide⟩,⟨498959, by decide⟩,⟨498969, by decide⟩]) unmarked_context_12_72231_498970 node_context_12_72231_498970
  intro a
  fin_cases a
  · exact context_13_288924_498902
  · exact context_13_288925_498941
  · exact context_13_288926_498959
  · exact context_13_288927_498969

theorem unmarked_context_11_18057_498971 : frontier 10 ⟨498971, by decide⟩
    (prefixCache 11 18057) (prefixPartial 11 18057) = false := by
  decide +kernel

theorem node_context_11_18057_498971 : EJMOriginalGlobalDAGData.nodes 10 ⟨498971, by decide⟩ =
    .split (coordinate 11) (![⟨498726, by decide⟩,⟨498806, by decide⟩,⟨498878, by decide⟩,⟨498970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18057_498971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18057 ⟨498971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18057
    ⟨498971, by decide⟩ (by decide) (![⟨498726, by decide⟩,⟨498806, by decide⟩,⟨498878, by decide⟩,⟨498970, by decide⟩]) unmarked_context_11_18057_498971 node_context_11_18057_498971
  intro a
  fin_cases a
  · exact context_12_72228_498726
  · exact context_12_72229_498806
  · exact context_12_72230_498878
  · exact context_12_72231_498970

theorem selected_cut_19501 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 72232) = some ⟨12, 1, 0, 450498, 72232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72232_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72232 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 72232 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 72232, 1, 65536⟩
    (by decide) selected_cut_19501

theorem selected_cut_19502 : selected 8 ⟨499019, by decide⟩
    (prefixPartial 13 288932) = some ⟨13, 2, 0, 499019, 288932, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_288932_499019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288932 ⟨499019, by decide⟩ :=
  accepted_of_selected 13 288932 ⟨499019, by decide⟩ ⟨13, 2, 0, 499019, 288932, 1441, 16384⟩
    (by decide) selected_cut_19502

theorem selected_cut_19503 : selected 8 ⟨499074, by decide⟩
    (prefixPartial 13 288933) = some ⟨13, 2, 0, 499074, 288933, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_288933_499074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288933 ⟨499074, by decide⟩ :=
  accepted_of_selected 13 288933 ⟨499074, by decide⟩ ⟨13, 2, 0, 499074, 288933, 2585, 16384⟩
    (by decide) selected_cut_19503

theorem selected_cut_19504 : selected 8 ⟨499110, by decide⟩
    (prefixPartial 13 288934) = some ⟨13, 2, 0, 499110, 288934, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_288934_499110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288934 ⟨499110, by decide⟩ :=
  accepted_of_selected 13 288934 ⟨499110, by decide⟩ ⟨13, 2, 0, 499110, 288934, 1809, 16384⟩
    (by decide) selected_cut_19504

theorem selected_cut_19505 : selected 8 ⟨499161, by decide⟩
    (prefixPartial 13 288935) = some ⟨13, 2, 0, 499161, 288935, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_288935_499161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288935 ⟨499161, by decide⟩ :=
  accepted_of_selected 13 288935 ⟨499161, by decide⟩ ⟨13, 2, 0, 499161, 288935, 1285, 16384⟩
    (by decide) selected_cut_19505

theorem unmarked_context_12_72233_499162 : frontier 9 ⟨499162, by decide⟩
    (prefixCache 12 72233) (prefixPartial 12 72233) = false := by
  decide +kernel

theorem node_context_12_72233_499162 : EJMOriginalGlobalDAGData.nodes 9 ⟨499162, by decide⟩ =
    .split (coordinate 12) (![⟨499019, by decide⟩,⟨499074, by decide⟩,⟨499110, by decide⟩,⟨499161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72233_499162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72233 ⟨499162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72233
    ⟨499162, by decide⟩ (by decide) (![⟨499019, by decide⟩,⟨499074, by decide⟩,⟨499110, by decide⟩,⟨499161, by decide⟩]) unmarked_context_12_72233_499162 node_context_12_72233_499162
  intro a
  fin_cases a
  · exact context_13_288932_499019
  · exact context_13_288933_499074
  · exact context_13_288934_499110
  · exact context_13_288935_499161

theorem selected_cut_19506 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 72234) = some ⟨12, 1, 0, 474208, 72234, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72234_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72234 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 72234 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 72234, 1, 65536⟩
    (by decide) selected_cut_19506

theorem selected_cut_19507 : selected 8 ⟨499199, by decide⟩
    (prefixPartial 13 288940) = some ⟨13, 2, 0, 499199, 288940, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_288940_499199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288940 ⟨499199, by decide⟩ :=
  accepted_of_selected 13 288940 ⟨499199, by decide⟩ ⟨13, 2, 0, 499199, 288940, 1417, 16384⟩
    (by decide) selected_cut_19507

theorem selected_cut_19508 : selected 8 ⟨499274, by decide⟩
    (prefixPartial 13 288941) = some ⟨13, 2, 0, 499274, 288941, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_288941_499274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288941 ⟨499274, by decide⟩ :=
  accepted_of_selected 13 288941 ⟨499274, by decide⟩ ⟨13, 2, 0, 499274, 288941, 3421, 16384⟩
    (by decide) selected_cut_19508

theorem selected_cut_19509 : selected 8 ⟨499305, by decide⟩
    (prefixPartial 13 288942) = some ⟨13, 2, 0, 499305, 288942, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_288942_499305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288942 ⟨499305, by decide⟩ :=
  accepted_of_selected 13 288942 ⟨499305, by decide⟩ ⟨13, 2, 0, 499305, 288942, 2109, 16384⟩
    (by decide) selected_cut_19509

theorem selected_cut_19510 : selected 8 ⟨499335, by decide⟩
    (prefixPartial 13 288943) = some ⟨13, 2, 0, 499335, 288943, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_288943_499335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288943 ⟨499335, by decide⟩ :=
  accepted_of_selected 13 288943 ⟨499335, by decide⟩ ⟨13, 2, 0, 499335, 288943, 1193, 16384⟩
    (by decide) selected_cut_19510

theorem unmarked_context_12_72235_499336 : frontier 9 ⟨499336, by decide⟩
    (prefixCache 12 72235) (prefixPartial 12 72235) = false := by
  decide +kernel

theorem node_context_12_72235_499336 : EJMOriginalGlobalDAGData.nodes 9 ⟨499336, by decide⟩ =
    .split (coordinate 12) (![⟨499199, by decide⟩,⟨499274, by decide⟩,⟨499305, by decide⟩,⟨499335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72235_499336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72235 ⟨499336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72235
    ⟨499336, by decide⟩ (by decide) (![⟨499199, by decide⟩,⟨499274, by decide⟩,⟨499305, by decide⟩,⟨499335, by decide⟩]) unmarked_context_12_72235_499336 node_context_12_72235_499336
  intro a
  fin_cases a
  · exact context_13_288940_499199
  · exact context_13_288941_499274
  · exact context_13_288942_499305
  · exact context_13_288943_499335

theorem unmarked_context_11_18058_499337 : frontier 10 ⟨499337, by decide⟩
    (prefixCache 11 18058) (prefixPartial 11 18058) = false := by
  decide +kernel

theorem node_context_11_18058_499337 : EJMOriginalGlobalDAGData.nodes 10 ⟨499337, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨499162, by decide⟩,⟨474208, by decide⟩,⟨499336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18058_499337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18058 ⟨499337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18058
    ⟨499337, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨499162, by decide⟩,⟨474208, by decide⟩,⟨499336, by decide⟩]) unmarked_context_11_18058_499337 node_context_11_18058_499337
  intro a
  fin_cases a
  · exact context_12_72232_450498
  · exact context_12_72233_499162
  · exact context_12_72234_474208
  · exact context_12_72235_499336

theorem selected_cut_19511 : selected 8 ⟨499361, by decide⟩
    (prefixPartial 13 288944) = some ⟨13, 2, 0, 499361, 288944, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_288944_499361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288944 ⟨499361, by decide⟩ :=
  accepted_of_selected 13 288944 ⟨499361, by decide⟩ ⟨13, 2, 0, 499361, 288944, 1365, 16384⟩
    (by decide) selected_cut_19511

theorem selected_cut_19512 : selected 8 ⟨499428, by decide⟩
    (prefixPartial 13 288945) = some ⟨13, 2, 0, 499428, 288945, 3841, 16384⟩ := by
  decide +kernel

theorem context_13_288945_499428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288945 ⟨499428, by decide⟩ :=
  accepted_of_selected 13 288945 ⟨499428, by decide⟩ ⟨13, 2, 0, 499428, 288945, 3841, 16384⟩
    (by decide) selected_cut_19512

theorem selected_cut_19513 : selected 8 ⟨499469, by decide⟩
    (prefixPartial 13 288946) = some ⟨13, 2, 0, 499469, 288946, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_288946_499469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288946 ⟨499469, by decide⟩ :=
  accepted_of_selected 13 288946 ⟨499469, by decide⟩ ⟨13, 2, 0, 499469, 288946, 2361, 16384⟩
    (by decide) selected_cut_19513

theorem selected_cut_19514 : selected 8 ⟨499489, by decide⟩
    (prefixPartial 13 288947) = some ⟨13, 2, 0, 499489, 288947, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_288947_499489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288947 ⟨499489, by decide⟩ :=
  accepted_of_selected 13 288947 ⟨499489, by decide⟩ ⟨13, 2, 0, 499489, 288947, 1349, 16384⟩
    (by decide) selected_cut_19514

theorem unmarked_context_12_72236_499490 : frontier 9 ⟨499490, by decide⟩
    (prefixCache 12 72236) (prefixPartial 12 72236) = false := by
  decide +kernel

theorem node_context_12_72236_499490 : EJMOriginalGlobalDAGData.nodes 9 ⟨499490, by decide⟩ =
    .split (coordinate 12) (![⟨499361, by decide⟩,⟨499428, by decide⟩,⟨499469, by decide⟩,⟨499489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72236_499490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72236 ⟨499490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72236
    ⟨499490, by decide⟩ (by decide) (![⟨499361, by decide⟩,⟨499428, by decide⟩,⟨499469, by decide⟩,⟨499489, by decide⟩]) unmarked_context_12_72236_499490 node_context_12_72236_499490
  intro a
  fin_cases a
  · exact context_13_288944_499361
  · exact context_13_288945_499428
  · exact context_13_288946_499469
  · exact context_13_288947_499489

theorem selected_cut_19515 : selected 8 ⟨499503, by decide⟩
    (prefixPartial 13 288948) = some ⟨13, 2, 0, 499503, 288948, 981, 16384⟩ := by
  decide +kernel

theorem context_13_288948_499503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288948 ⟨499503, by decide⟩ :=
  accepted_of_selected 13 288948 ⟨499503, by decide⟩ ⟨13, 2, 0, 499503, 288948, 981, 16384⟩
    (by decide) selected_cut_19515

theorem selected_cut_19516 : selected 8 ⟨499541, by decide⟩
    (prefixPartial 13 288949) = some ⟨13, 2, 0, 499541, 288949, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_288949_499541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288949 ⟨499541, by decide⟩ :=
  accepted_of_selected 13 288949 ⟨499541, by decide⟩ ⟨13, 2, 0, 499541, 288949, 2321, 16384⟩
    (by decide) selected_cut_19516

theorem selected_cut_19517 : selected 8 ⟨499560, by decide⟩
    (prefixPartial 13 288950) = some ⟨13, 2, 0, 499560, 288950, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_288950_499560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288950 ⟨499560, by decide⟩ :=
  accepted_of_selected 13 288950 ⟨499560, by decide⟩ ⟨13, 2, 0, 499560, 288950, 1593, 16384⟩
    (by decide) selected_cut_19517

theorem selected_cut_19518 : selected 8 ⟨499567, by decide⟩
    (prefixPartial 13 288951) = some ⟨13, 2, 0, 499567, 288951, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_288951_499567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288951 ⟨499567, by decide⟩ :=
  accepted_of_selected 13 288951 ⟨499567, by decide⟩ ⟨13, 2, 0, 499567, 288951, 1021, 16384⟩
    (by decide) selected_cut_19518

theorem unmarked_context_12_72237_499568 : frontier 9 ⟨499568, by decide⟩
    (prefixCache 12 72237) (prefixPartial 12 72237) = false := by
  decide +kernel

theorem node_context_12_72237_499568 : EJMOriginalGlobalDAGData.nodes 9 ⟨499568, by decide⟩ =
    .split (coordinate 12) (![⟨499503, by decide⟩,⟨499541, by decide⟩,⟨499560, by decide⟩,⟨499567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72237_499568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72237 ⟨499568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72237
    ⟨499568, by decide⟩ (by decide) (![⟨499503, by decide⟩,⟨499541, by decide⟩,⟨499560, by decide⟩,⟨499567, by decide⟩]) unmarked_context_12_72237_499568 node_context_12_72237_499568
  intro a
  fin_cases a
  · exact context_13_288948_499503
  · exact context_13_288949_499541
  · exact context_13_288950_499560
  · exact context_13_288951_499567

theorem selected_cut_19519 : selected 8 ⟨499586, by decide⟩
    (prefixPartial 13 288952) = some ⟨13, 2, 0, 499586, 288952, 693, 16384⟩ := by
  decide +kernel

theorem context_13_288952_499586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288952 ⟨499586, by decide⟩ :=
  accepted_of_selected 13 288952 ⟨499586, by decide⟩ ⟨13, 2, 0, 499586, 288952, 693, 16384⟩
    (by decide) selected_cut_19519

theorem selected_cut_19520 : selected 8 ⟨499624, by decide⟩
    (prefixPartial 13 288953) = some ⟨13, 2, 0, 499624, 288953, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_288953_499624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288953 ⟨499624, by decide⟩ :=
  accepted_of_selected 13 288953 ⟨499624, by decide⟩ ⟨13, 2, 0, 499624, 288953, 2549, 16384⟩
    (by decide) selected_cut_19520

theorem selected_cut_19521 : selected 8 ⟨499645, by decide⟩
    (prefixPartial 13 288954) = some ⟨13, 2, 0, 499645, 288954, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_288954_499645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288954 ⟨499645, by decide⟩ :=
  accepted_of_selected 13 288954 ⟨499645, by decide⟩ ⟨13, 2, 0, 499645, 288954, 1629, 16384⟩
    (by decide) selected_cut_19521

theorem selected_cut_19522 : selected 8 ⟨499653, by decide⟩
    (prefixPartial 13 288955) = some ⟨13, 2, 0, 499653, 288955, 865, 16384⟩ := by
  decide +kernel

theorem context_13_288955_499653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288955 ⟨499653, by decide⟩ :=
  accepted_of_selected 13 288955 ⟨499653, by decide⟩ ⟨13, 2, 0, 499653, 288955, 865, 16384⟩
    (by decide) selected_cut_19522

theorem unmarked_context_12_72238_499654 : frontier 9 ⟨499654, by decide⟩
    (prefixCache 12 72238) (prefixPartial 12 72238) = false := by
  decide +kernel

theorem node_context_12_72238_499654 : EJMOriginalGlobalDAGData.nodes 9 ⟨499654, by decide⟩ =
    .split (coordinate 12) (![⟨499586, by decide⟩,⟨499624, by decide⟩,⟨499645, by decide⟩,⟨499653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72238_499654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72238 ⟨499654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72238
    ⟨499654, by decide⟩ (by decide) (![⟨499586, by decide⟩,⟨499624, by decide⟩,⟨499645, by decide⟩,⟨499653, by decide⟩]) unmarked_context_12_72238_499654 node_context_12_72238_499654
  intro a
  fin_cases a
  · exact context_13_288952_499586
  · exact context_13_288953_499624
  · exact context_13_288954_499645
  · exact context_13_288955_499653

theorem selected_cut_19523 : selected 8 ⟨499674, by decide⟩
    (prefixPartial 13 288956) = some ⟨13, 2, 0, 499674, 288956, 873, 16384⟩ := by
  decide +kernel

theorem context_13_288956_499674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288956 ⟨499674, by decide⟩ :=
  accepted_of_selected 13 288956 ⟨499674, by decide⟩ ⟨13, 2, 0, 499674, 288956, 873, 16384⟩
    (by decide) selected_cut_19523

theorem selected_cut_19524 : selected 8 ⟨499714, by decide⟩
    (prefixPartial 13 288957) = some ⟨13, 2, 0, 499714, 288957, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_288957_499714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288957 ⟨499714, by decide⟩ :=
  accepted_of_selected 13 288957 ⟨499714, by decide⟩ ⟨13, 2, 0, 499714, 288957, 2909, 16384⟩
    (by decide) selected_cut_19524

theorem selected_cut_19525 : selected 8 ⟨499729, by decide⟩
    (prefixPartial 13 288958) = some ⟨13, 2, 0, 499729, 288958, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_288958_499729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288958 ⟨499729, by decide⟩ :=
  accepted_of_selected 13 288958 ⟨499729, by decide⟩ ⟨13, 2, 0, 499729, 288958, 1985, 16384⟩
    (by decide) selected_cut_19525

theorem selected_cut_19526 : selected 8 ⟨499737, by decide⟩
    (prefixPartial 13 288959) = some ⟨13, 2, 0, 499737, 288959, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_288959_499737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288959 ⟨499737, by decide⟩ :=
  accepted_of_selected 13 288959 ⟨499737, by decide⟩ ⟨13, 2, 0, 499737, 288959, 1065, 16384⟩
    (by decide) selected_cut_19526

theorem unmarked_context_12_72239_499738 : frontier 9 ⟨499738, by decide⟩
    (prefixCache 12 72239) (prefixPartial 12 72239) = false := by
  decide +kernel

theorem node_context_12_72239_499738 : EJMOriginalGlobalDAGData.nodes 9 ⟨499738, by decide⟩ =
    .split (coordinate 12) (![⟨499674, by decide⟩,⟨499714, by decide⟩,⟨499729, by decide⟩,⟨499737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72239_499738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72239 ⟨499738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72239
    ⟨499738, by decide⟩ (by decide) (![⟨499674, by decide⟩,⟨499714, by decide⟩,⟨499729, by decide⟩,⟨499737, by decide⟩]) unmarked_context_12_72239_499738 node_context_12_72239_499738
  intro a
  fin_cases a
  · exact context_13_288956_499674
  · exact context_13_288957_499714
  · exact context_13_288958_499729
  · exact context_13_288959_499737

theorem unmarked_context_11_18059_499739 : frontier 10 ⟨499739, by decide⟩
    (prefixCache 11 18059) (prefixPartial 11 18059) = false := by
  decide +kernel

theorem node_context_11_18059_499739 : EJMOriginalGlobalDAGData.nodes 10 ⟨499739, by decide⟩ =
    .split (coordinate 11) (![⟨499490, by decide⟩,⟨499568, by decide⟩,⟨499654, by decide⟩,⟨499738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18059_499739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18059 ⟨499739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18059
    ⟨499739, by decide⟩ (by decide) (![⟨499490, by decide⟩,⟨499568, by decide⟩,⟨499654, by decide⟩,⟨499738, by decide⟩]) unmarked_context_11_18059_499739 node_context_11_18059_499739
  intro a
  fin_cases a
  · exact context_12_72236_499490
  · exact context_12_72237_499568
  · exact context_12_72238_499654
  · exact context_12_72239_499738

theorem unmarked_context_10_4514_499740 : frontier 11 ⟨499740, by decide⟩
    (prefixCache 10 4514) (prefixPartial 10 4514) = false := by
  decide +kernel

theorem node_context_10_4514_499740 : EJMOriginalGlobalDAGData.nodes 11 ⟨499740, by decide⟩ =
    .split (coordinate 10) (![⟨498575, by decide⟩,⟨498971, by decide⟩,⟨499337, by decide⟩,⟨499739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4514_499740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4514 ⟨499740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4514
    ⟨499740, by decide⟩ (by decide) (![⟨498575, by decide⟩,⟨498971, by decide⟩,⟨499337, by decide⟩,⟨499739, by decide⟩]) unmarked_context_10_4514_499740 node_context_10_4514_499740
  intro a
  fin_cases a
  · exact context_11_18056_498575
  · exact context_11_18057_498971
  · exact context_11_18058_499337
  · exact context_11_18059_499739

theorem selected_cut_19527 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 72240) = some ⟨12, 1, 0, 445562, 72240, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72240_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72240 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 72240 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 72240, 1, 65536⟩
    (by decide) selected_cut_19527

theorem selected_cut_19528 : selected 8 ⟨499759, by decide⟩
    (prefixPartial 13 288964) = some ⟨13, 2, 0, 499759, 288964, 921, 16384⟩ := by
  decide +kernel

theorem context_13_288964_499759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288964 ⟨499759, by decide⟩ :=
  accepted_of_selected 13 288964 ⟨499759, by decide⟩ ⟨13, 2, 0, 499759, 288964, 921, 16384⟩
    (by decide) selected_cut_19528

theorem selected_cut_19529 : selected 8 ⟨499802, by decide⟩
    (prefixPartial 13 288965) = some ⟨13, 2, 0, 499802, 288965, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_288965_499802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288965 ⟨499802, by decide⟩ :=
  accepted_of_selected 13 288965 ⟨499802, by decide⟩ ⟨13, 2, 0, 499802, 288965, 2749, 16384⟩
    (by decide) selected_cut_19529

theorem selected_cut_19530 : selected 8 ⟨499822, by decide⟩
    (prefixPartial 13 288966) = some ⟨13, 2, 0, 499822, 288966, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_288966_499822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288966 ⟨499822, by decide⟩ :=
  accepted_of_selected 13 288966 ⟨499822, by decide⟩ ⟨13, 2, 0, 499822, 288966, 1301, 16384⟩
    (by decide) selected_cut_19530

theorem selected_cut_19531 : selected 8 ⟨499839, by decide⟩
    (prefixPartial 13 288967) = some ⟨13, 2, 0, 499839, 288967, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_288967_499839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288967 ⟨499839, by decide⟩ :=
  accepted_of_selected 13 288967 ⟨499839, by decide⟩ ⟨13, 2, 0, 499839, 288967, 1157, 16384⟩
    (by decide) selected_cut_19531

theorem unmarked_context_12_72241_499840 : frontier 9 ⟨499840, by decide⟩
    (prefixCache 12 72241) (prefixPartial 12 72241) = false := by
  decide +kernel

theorem node_context_12_72241_499840 : EJMOriginalGlobalDAGData.nodes 9 ⟨499840, by decide⟩ =
    .split (coordinate 12) (![⟨499759, by decide⟩,⟨499802, by decide⟩,⟨499822, by decide⟩,⟨499839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72241_499840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72241 ⟨499840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72241
    ⟨499840, by decide⟩ (by decide) (![⟨499759, by decide⟩,⟨499802, by decide⟩,⟨499822, by decide⟩,⟨499839, by decide⟩]) unmarked_context_12_72241_499840 node_context_12_72241_499840
  intro a
  fin_cases a
  · exact context_13_288964_499759
  · exact context_13_288965_499802
  · exact context_13_288966_499822
  · exact context_13_288967_499839

theorem selected_cut_19532 : selected 8 ⟨499852, by decide⟩
    (prefixPartial 13 288968) = some ⟨13, 2, 0, 499852, 288968, 757, 16384⟩ := by
  decide +kernel

theorem context_13_288968_499852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288968 ⟨499852, by decide⟩ :=
  accepted_of_selected 13 288968 ⟨499852, by decide⟩ ⟨13, 2, 0, 499852, 288968, 757, 16384⟩
    (by decide) selected_cut_19532

theorem selected_cut_19533 : selected 8 ⟨499879, by decide⟩
    (prefixPartial 13 288969) = some ⟨13, 2, 0, 499879, 288969, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_288969_499879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288969 ⟨499879, by decide⟩ :=
  accepted_of_selected 13 288969 ⟨499879, by decide⟩ ⟨13, 2, 0, 499879, 288969, 2669, 16384⟩
    (by decide) selected_cut_19533

theorem selected_cut_19534 : selected 8 ⟨499899, by decide⟩
    (prefixPartial 13 288970) = some ⟨13, 2, 0, 499899, 288970, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_288970_499899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288970 ⟨499899, by decide⟩ :=
  accepted_of_selected 13 288970 ⟨499899, by decide⟩ ⟨13, 2, 0, 499899, 288970, 1473, 16384⟩
    (by decide) selected_cut_19534

theorem selected_cut_19535 : selected 8 ⟨499905, by decide⟩
    (prefixPartial 13 288971) = some ⟨13, 2, 0, 499905, 288971, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_288971_499905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288971 ⟨499905, by decide⟩ :=
  accepted_of_selected 13 288971 ⟨499905, by decide⟩ ⟨13, 2, 0, 499905, 288971, 1049, 16384⟩
    (by decide) selected_cut_19535

theorem unmarked_context_12_72242_499906 : frontier 9 ⟨499906, by decide⟩
    (prefixCache 12 72242) (prefixPartial 12 72242) = false := by
  decide +kernel

theorem node_context_12_72242_499906 : EJMOriginalGlobalDAGData.nodes 9 ⟨499906, by decide⟩ =
    .split (coordinate 12) (![⟨499852, by decide⟩,⟨499879, by decide⟩,⟨499899, by decide⟩,⟨499905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72242_499906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72242 ⟨499906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72242
    ⟨499906, by decide⟩ (by decide) (![⟨499852, by decide⟩,⟨499879, by decide⟩,⟨499899, by decide⟩,⟨499905, by decide⟩]) unmarked_context_12_72242_499906 node_context_12_72242_499906
  intro a
  fin_cases a
  · exact context_13_288968_499852
  · exact context_13_288969_499879
  · exact context_13_288970_499899
  · exact context_13_288971_499905

theorem selected_cut_19536 : selected 8 ⟨499922, by decide⟩
    (prefixPartial 13 288972) = some ⟨13, 2, 0, 499922, 288972, 901, 16384⟩ := by
  decide +kernel

theorem context_13_288972_499922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288972 ⟨499922, by decide⟩ :=
  accepted_of_selected 13 288972 ⟨499922, by decide⟩ ⟨13, 2, 0, 499922, 288972, 901, 16384⟩
    (by decide) selected_cut_19536

theorem selected_cut_19537 : selected 8 ⟨499966, by decide⟩
    (prefixPartial 13 288973) = some ⟨13, 2, 0, 499966, 288973, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_288973_499966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288973 ⟨499966, by decide⟩ :=
  accepted_of_selected 13 288973 ⟨499966, by decide⟩ ⟨13, 2, 0, 499966, 288973, 2729, 16384⟩
    (by decide) selected_cut_19537

theorem selected_cut_19538 : selected 8 ⟨499985, by decide⟩
    (prefixPartial 13 288974) = some ⟨13, 2, 0, 499985, 288974, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_288974_499985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288974 ⟨499985, by decide⟩ :=
  accepted_of_selected 13 288974 ⟨499985, by decide⟩ ⟨13, 2, 0, 499985, 288974, 1625, 16384⟩
    (by decide) selected_cut_19538

theorem selected_cut_19539 : selected 8 ⟨499993, by decide⟩
    (prefixPartial 13 288975) = some ⟨13, 2, 0, 499993, 288975, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_288975_499993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288975 ⟨499993, by decide⟩ :=
  accepted_of_selected 13 288975 ⟨499993, by decide⟩ ⟨13, 2, 0, 499993, 288975, 1009, 16384⟩
    (by decide) selected_cut_19539

theorem unmarked_context_12_72243_499994 : frontier 9 ⟨499994, by decide⟩
    (prefixCache 12 72243) (prefixPartial 12 72243) = false := by
  decide +kernel

theorem node_context_12_72243_499994 : EJMOriginalGlobalDAGData.nodes 9 ⟨499994, by decide⟩ =
    .split (coordinate 12) (![⟨499922, by decide⟩,⟨499966, by decide⟩,⟨499985, by decide⟩,⟨499993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72243_499994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72243 ⟨499994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72243
    ⟨499994, by decide⟩ (by decide) (![⟨499922, by decide⟩,⟨499966, by decide⟩,⟨499985, by decide⟩,⟨499993, by decide⟩]) unmarked_context_12_72243_499994 node_context_12_72243_499994
  intro a
  fin_cases a
  · exact context_13_288972_499922
  · exact context_13_288973_499966
  · exact context_13_288974_499985
  · exact context_13_288975_499993

theorem unmarked_context_11_18060_499995 : frontier 10 ⟨499995, by decide⟩
    (prefixCache 11 18060) (prefixPartial 11 18060) = false := by
  decide +kernel

theorem node_context_11_18060_499995 : EJMOriginalGlobalDAGData.nodes 10 ⟨499995, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨499840, by decide⟩,⟨499906, by decide⟩,⟨499994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18060_499995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18060 ⟨499995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18060
    ⟨499995, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨499840, by decide⟩,⟨499906, by decide⟩,⟨499994, by decide⟩]) unmarked_context_11_18060_499995 node_context_11_18060_499995
  intro a
  fin_cases a
  · exact context_12_72240_445562
  · exact context_12_72241_499840
  · exact context_12_72242_499906
  · exact context_12_72243_499994

theorem selected_cut_19540 : selected 8 ⟨500015, by decide⟩
    (prefixPartial 13 288976) = some ⟨13, 2, 0, 500015, 288976, 949, 16384⟩ := by
  decide +kernel

theorem context_13_288976_500015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288976 ⟨500015, by decide⟩ :=
  accepted_of_selected 13 288976 ⟨500015, by decide⟩ ⟨13, 2, 0, 500015, 288976, 949, 16384⟩
    (by decide) selected_cut_19540

theorem selected_cut_19541 : selected 8 ⟨500098, by decide⟩
    (prefixPartial 13 288977) = some ⟨13, 2, 0, 500098, 288977, 4061, 16384⟩ := by
  decide +kernel

theorem context_13_288977_500098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288977 ⟨500098, by decide⟩ :=
  accepted_of_selected 13 288977 ⟨500098, by decide⟩ ⟨13, 2, 0, 500098, 288977, 4061, 16384⟩
    (by decide) selected_cut_19541

theorem selected_cut_19542 : selected 8 ⟨500136, by decide⟩
    (prefixPartial 13 288978) = some ⟨13, 2, 0, 500136, 288978, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_288978_500136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288978 ⟨500136, by decide⟩ :=
  accepted_of_selected 13 288978 ⟨500136, by decide⟩ ⟨13, 2, 0, 500136, 288978, 2121, 16384⟩
    (by decide) selected_cut_19542

theorem selected_cut_19543 : selected 8 ⟨500157, by decide⟩
    (prefixPartial 13 288979) = some ⟨13, 2, 0, 500157, 288979, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_288979_500157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288979 ⟨500157, by decide⟩ :=
  accepted_of_selected 13 288979 ⟨500157, by decide⟩ ⟨13, 2, 0, 500157, 288979, 1369, 16384⟩
    (by decide) selected_cut_19543

theorem unmarked_context_12_72244_500158 : frontier 9 ⟨500158, by decide⟩
    (prefixCache 12 72244) (prefixPartial 12 72244) = false := by
  decide +kernel

theorem node_context_12_72244_500158 : EJMOriginalGlobalDAGData.nodes 9 ⟨500158, by decide⟩ =
    .split (coordinate 12) (![⟨500015, by decide⟩,⟨500098, by decide⟩,⟨500136, by decide⟩,⟨500157, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72244_500158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72244 ⟨500158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72244
    ⟨500158, by decide⟩ (by decide) (![⟨500015, by decide⟩,⟨500098, by decide⟩,⟨500136, by decide⟩,⟨500157, by decide⟩]) unmarked_context_12_72244_500158 node_context_12_72244_500158
  intro a
  fin_cases a
  · exact context_13_288976_500015
  · exact context_13_288977_500098
  · exact context_13_288978_500136
  · exact context_13_288979_500157

theorem selected_cut_19544 : selected 8 ⟨500173, by decide⟩
    (prefixPartial 13 288980) = some ⟨13, 2, 0, 500173, 288980, 697, 16384⟩ := by
  decide +kernel

theorem context_13_288980_500173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288980 ⟨500173, by decide⟩ :=
  accepted_of_selected 13 288980 ⟨500173, by decide⟩ ⟨13, 2, 0, 500173, 288980, 697, 16384⟩
    (by decide) selected_cut_19544

theorem selected_cut_19545 : selected 8 ⟨500208, by decide⟩
    (prefixPartial 13 288981) = some ⟨13, 2, 0, 500208, 288981, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_288981_500208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288981 ⟨500208, by decide⟩ :=
  accepted_of_selected 13 288981 ⟨500208, by decide⟩ ⟨13, 2, 0, 500208, 288981, 2729, 16384⟩
    (by decide) selected_cut_19545

theorem selected_cut_19546 : selected 8 ⟨500225, by decide⟩
    (prefixPartial 13 288982) = some ⟨13, 2, 0, 500225, 288982, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_288982_500225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288982 ⟨500225, by decide⟩ :=
  accepted_of_selected 13 288982 ⟨500225, by decide⟩ ⟨13, 2, 0, 500225, 288982, 1233, 16384⟩
    (by decide) selected_cut_19546

theorem selected_cut_19547 : selected 8 ⟨500236, by decide⟩
    (prefixPartial 13 288983) = some ⟨13, 2, 0, 500236, 288983, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_288983_500236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288983 ⟨500236, by decide⟩ :=
  accepted_of_selected 13 288983 ⟨500236, by decide⟩ ⟨13, 2, 0, 500236, 288983, 1093, 16384⟩
    (by decide) selected_cut_19547

theorem unmarked_context_12_72245_500237 : frontier 9 ⟨500237, by decide⟩
    (prefixCache 12 72245) (prefixPartial 12 72245) = false := by
  decide +kernel

theorem node_context_12_72245_500237 : EJMOriginalGlobalDAGData.nodes 9 ⟨500237, by decide⟩ =
    .split (coordinate 12) (![⟨500173, by decide⟩,⟨500208, by decide⟩,⟨500225, by decide⟩,⟨500236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72245_500237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72245 ⟨500237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72245
    ⟨500237, by decide⟩ (by decide) (![⟨500173, by decide⟩,⟨500208, by decide⟩,⟨500225, by decide⟩,⟨500236, by decide⟩]) unmarked_context_12_72245_500237 node_context_12_72245_500237
  intro a
  fin_cases a
  · exact context_13_288980_500173
  · exact context_13_288981_500208
  · exact context_13_288982_500225
  · exact context_13_288983_500236

theorem selected_cut_19548 : selected 8 ⟨500249, by decide⟩
    (prefixPartial 13 288984) = some ⟨13, 2, 0, 500249, 288984, 605, 16384⟩ := by
  decide +kernel

theorem context_13_288984_500249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288984 ⟨500249, by decide⟩ :=
  accepted_of_selected 13 288984 ⟨500249, by decide⟩ ⟨13, 2, 0, 500249, 288984, 605, 16384⟩
    (by decide) selected_cut_19548

theorem selected_cut_19549 : selected 8 ⟨500275, by decide⟩
    (prefixPartial 13 288985) = some ⟨13, 2, 0, 500275, 288985, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_288985_500275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288985 ⟨500275, by decide⟩ :=
  accepted_of_selected 13 288985 ⟨500275, by decide⟩ ⟨13, 2, 0, 500275, 288985, 2877, 16384⟩
    (by decide) selected_cut_19549

theorem selected_cut_19550 : selected 8 ⟨500295, by decide⟩
    (prefixPartial 13 288986) = some ⟨13, 2, 0, 500295, 288986, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_288986_500295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288986 ⟨500295, by decide⟩ :=
  accepted_of_selected 13 288986 ⟨500295, by decide⟩ ⟨13, 2, 0, 500295, 288986, 1557, 16384⟩
    (by decide) selected_cut_19550

theorem selected_cut_19551 : selected 8 ⟨500302, by decide⟩
    (prefixPartial 13 288987) = some ⟨13, 2, 0, 500302, 288987, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_288987_500302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288987 ⟨500302, by decide⟩ :=
  accepted_of_selected 13 288987 ⟨500302, by decide⟩ ⟨13, 2, 0, 500302, 288987, 1089, 16384⟩
    (by decide) selected_cut_19551

theorem unmarked_context_12_72246_500303 : frontier 9 ⟨500303, by decide⟩
    (prefixCache 12 72246) (prefixPartial 12 72246) = false := by
  decide +kernel

theorem node_context_12_72246_500303 : EJMOriginalGlobalDAGData.nodes 9 ⟨500303, by decide⟩ =
    .split (coordinate 12) (![⟨500249, by decide⟩,⟨500275, by decide⟩,⟨500295, by decide⟩,⟨500302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72246_500303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72246 ⟨500303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72246
    ⟨500303, by decide⟩ (by decide) (![⟨500249, by decide⟩,⟨500275, by decide⟩,⟨500295, by decide⟩,⟨500302, by decide⟩]) unmarked_context_12_72246_500303 node_context_12_72246_500303
  intro a
  fin_cases a
  · exact context_13_288984_500249
  · exact context_13_288985_500275
  · exact context_13_288986_500295
  · exact context_13_288987_500302

theorem selected_cut_19552 : selected 8 ⟨500313, by decide⟩
    (prefixPartial 13 288988) = some ⟨13, 2, 0, 500313, 288988, 565, 16384⟩ := by
  decide +kernel

theorem context_13_288988_500313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288988 ⟨500313, by decide⟩ :=
  accepted_of_selected 13 288988 ⟨500313, by decide⟩ ⟨13, 2, 0, 500313, 288988, 565, 16384⟩
    (by decide) selected_cut_19552

theorem selected_cut_19553 : selected 8 ⟨500354, by decide⟩
    (prefixPartial 13 288989) = some ⟨13, 2, 0, 500354, 288989, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_288989_500354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288989 ⟨500354, by decide⟩ :=
  accepted_of_selected 13 288989 ⟨500354, by decide⟩ ⟨13, 2, 0, 500354, 288989, 2917, 16384⟩
    (by decide) selected_cut_19553

theorem selected_cut_19554 : selected 8 ⟨500379, by decide⟩
    (prefixPartial 13 288990) = some ⟨13, 2, 0, 500379, 288990, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_288990_500379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288990 ⟨500379, by decide⟩ :=
  accepted_of_selected 13 288990 ⟨500379, by decide⟩ ⟨13, 2, 0, 500379, 288990, 1721, 16384⟩
    (by decide) selected_cut_19554

theorem selected_cut_19555 : selected 8 ⟨500391, by decide⟩
    (prefixPartial 13 288991) = some ⟨13, 2, 0, 500391, 288991, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_288991_500391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288991 ⟨500391, by decide⟩ :=
  accepted_of_selected 13 288991 ⟨500391, by decide⟩ ⟨13, 2, 0, 500391, 288991, 1033, 16384⟩
    (by decide) selected_cut_19555

theorem unmarked_context_12_72247_500392 : frontier 9 ⟨500392, by decide⟩
    (prefixCache 12 72247) (prefixPartial 12 72247) = false := by
  decide +kernel

theorem node_context_12_72247_500392 : EJMOriginalGlobalDAGData.nodes 9 ⟨500392, by decide⟩ =
    .split (coordinate 12) (![⟨500313, by decide⟩,⟨500354, by decide⟩,⟨500379, by decide⟩,⟨500391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72247_500392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72247 ⟨500392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72247
    ⟨500392, by decide⟩ (by decide) (![⟨500313, by decide⟩,⟨500354, by decide⟩,⟨500379, by decide⟩,⟨500391, by decide⟩]) unmarked_context_12_72247_500392 node_context_12_72247_500392
  intro a
  fin_cases a
  · exact context_13_288988_500313
  · exact context_13_288989_500354
  · exact context_13_288990_500379
  · exact context_13_288991_500391

theorem unmarked_context_11_18061_500393 : frontier 10 ⟨500393, by decide⟩
    (prefixCache 11 18061) (prefixPartial 11 18061) = false := by
  decide +kernel

theorem node_context_11_18061_500393 : EJMOriginalGlobalDAGData.nodes 10 ⟨500393, by decide⟩ =
    .split (coordinate 11) (![⟨500158, by decide⟩,⟨500237, by decide⟩,⟨500303, by decide⟩,⟨500392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18061_500393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18061 ⟨500393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18061
    ⟨500393, by decide⟩ (by decide) (![⟨500158, by decide⟩,⟨500237, by decide⟩,⟨500303, by decide⟩,⟨500392, by decide⟩]) unmarked_context_11_18061_500393 node_context_11_18061_500393
  intro a
  fin_cases a
  · exact context_12_72244_500158
  · exact context_12_72245_500237
  · exact context_12_72246_500303
  · exact context_12_72247_500392

theorem selected_cut_19556 : selected 8 ⟨500406, by decide⟩
    (prefixPartial 13 288992) = some ⟨13, 2, 0, 500406, 288992, 573, 16384⟩ := by
  decide +kernel

theorem context_13_288992_500406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288992 ⟨500406, by decide⟩ :=
  accepted_of_selected 13 288992 ⟨500406, by decide⟩ ⟨13, 2, 0, 500406, 288992, 573, 16384⟩
    (by decide) selected_cut_19556

theorem selected_cut_19557 : selected 8 ⟨500472, by decide⟩
    (prefixPartial 13 288993) = some ⟨13, 2, 0, 500472, 288993, 3401, 16384⟩ := by
  decide +kernel

theorem context_13_288993_500472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288993 ⟨500472, by decide⟩ :=
  accepted_of_selected 13 288993 ⟨500472, by decide⟩ ⟨13, 2, 0, 500472, 288993, 3401, 16384⟩
    (by decide) selected_cut_19557

theorem selected_cut_19558 : selected 8 ⟨500510, by decide⟩
    (prefixPartial 13 288994) = some ⟨13, 2, 0, 500510, 288994, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_288994_500510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288994 ⟨500510, by decide⟩ :=
  accepted_of_selected 13 288994 ⟨500510, by decide⟩ ⟨13, 2, 0, 500510, 288994, 2097, 16384⟩
    (by decide) selected_cut_19558

theorem selected_cut_19559 : selected 8 ⟨500556, by decide⟩
    (prefixPartial 13 288995) = some ⟨13, 2, 0, 500556, 288995, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_288995_500556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288995 ⟨500556, by decide⟩ :=
  accepted_of_selected 13 288995 ⟨500556, by decide⟩ ⟨13, 2, 0, 500556, 288995, 1285, 16384⟩
    (by decide) selected_cut_19559

theorem unmarked_context_12_72248_500557 : frontier 9 ⟨500557, by decide⟩
    (prefixCache 12 72248) (prefixPartial 12 72248) = false := by
  decide +kernel

theorem node_context_12_72248_500557 : EJMOriginalGlobalDAGData.nodes 9 ⟨500557, by decide⟩ =
    .split (coordinate 12) (![⟨500406, by decide⟩,⟨500472, by decide⟩,⟨500510, by decide⟩,⟨500556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72248_500557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72248 ⟨500557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72248
    ⟨500557, by decide⟩ (by decide) (![⟨500406, by decide⟩,⟨500472, by decide⟩,⟨500510, by decide⟩,⟨500556, by decide⟩]) unmarked_context_12_72248_500557 node_context_12_72248_500557
  intro a
  fin_cases a
  · exact context_13_288992_500406
  · exact context_13_288993_500472
  · exact context_13_288994_500510
  · exact context_13_288995_500556

theorem selected_cut_19560 : selected 8 ⟨500565, by decide⟩
    (prefixPartial 13 288996) = some ⟨13, 2, 0, 500565, 288996, 361, 16384⟩ := by
  decide +kernel

theorem context_13_288996_500565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288996 ⟨500565, by decide⟩ :=
  accepted_of_selected 13 288996 ⟨500565, by decide⟩ ⟨13, 2, 0, 500565, 288996, 361, 16384⟩
    (by decide) selected_cut_19560

theorem selected_cut_19561 : selected 8 ⟨500598, by decide⟩
    (prefixPartial 13 288997) = some ⟨13, 2, 0, 500598, 288997, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_288997_500598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288997 ⟨500598, by decide⟩ :=
  accepted_of_selected 13 288997 ⟨500598, by decide⟩ ⟨13, 2, 0, 500598, 288997, 2329, 16384⟩
    (by decide) selected_cut_19561

theorem selected_cut_19562 : selected 8 ⟨500619, by decide⟩
    (prefixPartial 13 288998) = some ⟨13, 2, 0, 500619, 288998, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_288998_500619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288998 ⟨500619, by decide⟩ :=
  accepted_of_selected 13 288998 ⟨500619, by decide⟩ ⟨13, 2, 0, 500619, 288998, 1281, 16384⟩
    (by decide) selected_cut_19562

theorem selected_cut_19563 : selected 8 ⟨500641, by decide⟩
    (prefixPartial 13 288999) = some ⟨13, 2, 0, 500641, 288999, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_288999_500641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288999 ⟨500641, by decide⟩ :=
  accepted_of_selected 13 288999 ⟨500641, by decide⟩ ⟨13, 2, 0, 500641, 288999, 1161, 16384⟩
    (by decide) selected_cut_19563

theorem unmarked_context_12_72249_500642 : frontier 9 ⟨500642, by decide⟩
    (prefixCache 12 72249) (prefixPartial 12 72249) = false := by
  decide +kernel

theorem node_context_12_72249_500642 : EJMOriginalGlobalDAGData.nodes 9 ⟨500642, by decide⟩ =
    .split (coordinate 12) (![⟨500565, by decide⟩,⟨500598, by decide⟩,⟨500619, by decide⟩,⟨500641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72249_500642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72249 ⟨500642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72249
    ⟨500642, by decide⟩ (by decide) (![⟨500565, by decide⟩,⟨500598, by decide⟩,⟨500619, by decide⟩,⟨500641, by decide⟩]) unmarked_context_12_72249_500642 node_context_12_72249_500642
  intro a
  fin_cases a
  · exact context_13_288996_500565
  · exact context_13_288997_500598
  · exact context_13_288998_500619
  · exact context_13_288999_500641

theorem selected_cut_19564 : selected 8 ⟨500653, by decide⟩
    (prefixPartial 13 289000) = some ⟨13, 2, 0, 500653, 289000, 437, 16384⟩ := by
  decide +kernel

theorem context_13_289000_500653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289000 ⟨500653, by decide⟩ :=
  accepted_of_selected 13 289000 ⟨500653, by decide⟩ ⟨13, 2, 0, 500653, 289000, 437, 16384⟩
    (by decide) selected_cut_19564

theorem selected_cut_19565 : selected 8 ⟨500724, by decide⟩
    (prefixPartial 13 289001) = some ⟨13, 2, 0, 500724, 289001, 3901, 16384⟩ := by
  decide +kernel

theorem context_13_289001_500724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289001 ⟨500724, by decide⟩ :=
  accepted_of_selected 13 289001 ⟨500724, by decide⟩ ⟨13, 2, 0, 500724, 289001, 3901, 16384⟩
    (by decide) selected_cut_19565

theorem selected_cut_19566 : selected 8 ⟨500764, by decide⟩
    (prefixPartial 13 289002) = some ⟨13, 2, 0, 500764, 289002, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_289002_500764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289002 ⟨500764, by decide⟩ :=
  accepted_of_selected 13 289002 ⟨500764, by decide⟩ ⟨13, 2, 0, 500764, 289002, 2361, 16384⟩
    (by decide) selected_cut_19566

theorem selected_cut_19567 : selected 8 ⟨500819, by decide⟩
    (prefixPartial 13 289003) = some ⟨13, 2, 0, 500819, 289003, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_289003_500819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289003 ⟨500819, by decide⟩ :=
  accepted_of_selected 13 289003 ⟨500819, by decide⟩ ⟨13, 2, 0, 500819, 289003, 1465, 16384⟩
    (by decide) selected_cut_19567

theorem unmarked_context_12_72250_500820 : frontier 9 ⟨500820, by decide⟩
    (prefixCache 12 72250) (prefixPartial 12 72250) = false := by
  decide +kernel

theorem node_context_12_72250_500820 : EJMOriginalGlobalDAGData.nodes 9 ⟨500820, by decide⟩ =
    .split (coordinate 12) (![⟨500653, by decide⟩,⟨500724, by decide⟩,⟨500764, by decide⟩,⟨500819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72250_500820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72250 ⟨500820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72250
    ⟨500820, by decide⟩ (by decide) (![⟨500653, by decide⟩,⟨500724, by decide⟩,⟨500764, by decide⟩,⟨500819, by decide⟩]) unmarked_context_12_72250_500820 node_context_12_72250_500820
  intro a
  fin_cases a
  · exact context_13_289000_500653
  · exact context_13_289001_500724
  · exact context_13_289002_500764
  · exact context_13_289003_500819

theorem selected_cut_19568 : selected 8 ⟨500826, by decide⟩
    (prefixPartial 13 289004) = some ⟨13, 2, 0, 500826, 289004, 221, 16384⟩ := by
  decide +kernel

theorem context_13_289004_500826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289004 ⟨500826, by decide⟩ :=
  accepted_of_selected 13 289004 ⟨500826, by decide⟩ ⟨13, 2, 0, 500826, 289004, 221, 16384⟩
    (by decide) selected_cut_19568

theorem selected_cut_19569 : selected 8 ⟨500875, by decide⟩
    (prefixPartial 13 289005) = some ⟨13, 2, 0, 500875, 289005, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_289005_500875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289005 ⟨500875, by decide⟩ :=
  accepted_of_selected 13 289005 ⟨500875, by decide⟩ ⟨13, 2, 0, 500875, 289005, 2977, 16384⟩
    (by decide) selected_cut_19569

theorem selected_cut_19570 : selected 8 ⟨500896, by decide⟩
    (prefixPartial 13 289006) = some ⟨13, 2, 0, 500896, 289006, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_289006_500896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289006 ⟨500896, by decide⟩ :=
  accepted_of_selected 13 289006 ⟨500896, by decide⟩ ⟨13, 2, 0, 500896, 289006, 1665, 16384⟩
    (by decide) selected_cut_19570

theorem selected_cut_19571 : selected 8 ⟨500908, by decide⟩
    (prefixPartial 13 289007) = some ⟨13, 2, 0, 500908, 289007, 977, 16384⟩ := by
  decide +kernel

theorem context_13_289007_500908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289007 ⟨500908, by decide⟩ :=
  accepted_of_selected 13 289007 ⟨500908, by decide⟩ ⟨13, 2, 0, 500908, 289007, 977, 16384⟩
    (by decide) selected_cut_19571

theorem unmarked_context_12_72251_500909 : frontier 9 ⟨500909, by decide⟩
    (prefixCache 12 72251) (prefixPartial 12 72251) = false := by
  decide +kernel

theorem node_context_12_72251_500909 : EJMOriginalGlobalDAGData.nodes 9 ⟨500909, by decide⟩ =
    .split (coordinate 12) (![⟨500826, by decide⟩,⟨500875, by decide⟩,⟨500896, by decide⟩,⟨500908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72251_500909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72251 ⟨500909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72251
    ⟨500909, by decide⟩ (by decide) (![⟨500826, by decide⟩,⟨500875, by decide⟩,⟨500896, by decide⟩,⟨500908, by decide⟩]) unmarked_context_12_72251_500909 node_context_12_72251_500909
  intro a
  fin_cases a
  · exact context_13_289004_500826
  · exact context_13_289005_500875
  · exact context_13_289006_500896
  · exact context_13_289007_500908

theorem unmarked_context_11_18062_500910 : frontier 10 ⟨500910, by decide⟩
    (prefixCache 11 18062) (prefixPartial 11 18062) = false := by
  decide +kernel

theorem node_context_11_18062_500910 : EJMOriginalGlobalDAGData.nodes 10 ⟨500910, by decide⟩ =
    .split (coordinate 11) (![⟨500557, by decide⟩,⟨500642, by decide⟩,⟨500820, by decide⟩,⟨500909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18062_500910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18062 ⟨500910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18062
    ⟨500910, by decide⟩ (by decide) (![⟨500557, by decide⟩,⟨500642, by decide⟩,⟨500820, by decide⟩,⟨500909, by decide⟩]) unmarked_context_11_18062_500910 node_context_11_18062_500910
  intro a
  fin_cases a
  · exact context_12_72248_500557
  · exact context_12_72249_500642
  · exact context_12_72250_500820
  · exact context_12_72251_500909

theorem selected_cut_19572 : selected 8 ⟨500913, by decide⟩
    (prefixPartial 13 289008) = some ⟨13, 2, 0, 500913, 289008, 13, 16384⟩ := by
  decide +kernel

theorem context_13_289008_500913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289008 ⟨500913, by decide⟩ :=
  accepted_of_selected 13 289008 ⟨500913, by decide⟩ ⟨13, 2, 0, 500913, 289008, 13, 16384⟩
    (by decide) selected_cut_19572

theorem selected_cut_19573 : selected 7 ⟨500944, by decide⟩
    (prefixPartial 14 1156036) = some ⟨14, 2, 0, 500944, 1156036, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_1156036_500944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1156036 ⟨500944, by decide⟩ :=
  accepted_of_selected 14 1156036 ⟨500944, by decide⟩ ⟨14, 2, 0, 500944, 1156036, 1125, 4096⟩
    (by decide) selected_cut_19573

theorem selected_cut_19574 : selected 7 ⟨500991, by decide⟩
    (prefixPartial 14 1156037) = some ⟨14, 2, 0, 500991, 1156037, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_1156037_500991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1156037 ⟨500991, by decide⟩ :=
  accepted_of_selected 14 1156037 ⟨500991, by decide⟩ ⟨14, 2, 0, 500991, 1156037, 1129, 4096⟩
    (by decide) selected_cut_19574

theorem selected_cut_19575 : selected 7 ⟨501023, by decide⟩
    (prefixPartial 14 1156038) = some ⟨14, 2, 0, 501023, 1156038, 1013, 4096⟩ := by
  decide +kernel

theorem context_14_1156038_501023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1156038 ⟨501023, by decide⟩ :=
  accepted_of_selected 14 1156038 ⟨501023, by decide⟩ ⟨14, 2, 0, 501023, 1156038, 1013, 4096⟩
    (by decide) selected_cut_19575

theorem selected_cut_19576 : selected 7 ⟨501053, by decide⟩
    (prefixPartial 14 1156039) = some ⟨14, 2, 0, 501053, 1156039, 909, 4096⟩ := by
  decide +kernel

theorem context_14_1156039_501053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1156039 ⟨501053, by decide⟩ :=
  accepted_of_selected 14 1156039 ⟨501053, by decide⟩ ⟨14, 2, 0, 501053, 1156039, 909, 4096⟩
    (by decide) selected_cut_19576

theorem unmarked_context_13_289009_501054 : frontier 8 ⟨501054, by decide⟩
    (prefixCache 13 289009) (prefixPartial 13 289009) = false := by
  decide +kernel

theorem node_context_13_289009_501054 : EJMOriginalGlobalDAGData.nodes 8 ⟨501054, by decide⟩ =
    .split (coordinate 13) (![⟨500944, by decide⟩,⟨500991, by decide⟩,⟨501023, by decide⟩,⟨501053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_289009_501054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289009 ⟨501054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 289009
    ⟨501054, by decide⟩ (by decide) (![⟨500944, by decide⟩,⟨500991, by decide⟩,⟨501023, by decide⟩,⟨501053, by decide⟩]) unmarked_context_13_289009_501054 node_context_13_289009_501054
  intro a
  fin_cases a
  · exact context_14_1156036_500944
  · exact context_14_1156037_500991
  · exact context_14_1156038_501023
  · exact context_14_1156039_501053

theorem selected_cut_19577 : selected 8 ⟨501105, by decide⟩
    (prefixPartial 13 289010) = some ⟨13, 2, 0, 501105, 289010, 597, 16384⟩ := by
  decide +kernel

theorem context_13_289010_501105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289010 ⟨501105, by decide⟩ :=
  accepted_of_selected 13 289010 ⟨501105, by decide⟩ ⟨13, 2, 0, 501105, 289010, 597, 16384⟩
    (by decide) selected_cut_19577

theorem selected_cut_19578 : selected 8 ⟨501106, by decide⟩
    (prefixPartial 13 289011) = some ⟨13, 1, 0, 501106, 289011, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289011_501106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289011 ⟨501106, by decide⟩ :=
  accepted_of_selected 13 289011 ⟨501106, by decide⟩ ⟨13, 1, 0, 501106, 289011, 1, 16384⟩
    (by decide) selected_cut_19578

theorem unmarked_context_12_72252_501107 : frontier 9 ⟨501107, by decide⟩
    (prefixCache 12 72252) (prefixPartial 12 72252) = false := by
  decide +kernel

theorem node_context_12_72252_501107 : EJMOriginalGlobalDAGData.nodes 9 ⟨501107, by decide⟩ =
    .split (coordinate 12) (![⟨500913, by decide⟩,⟨501054, by decide⟩,⟨501105, by decide⟩,⟨501106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72252_501107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72252 ⟨501107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72252
    ⟨501107, by decide⟩ (by decide) (![⟨500913, by decide⟩,⟨501054, by decide⟩,⟨501105, by decide⟩,⟨501106, by decide⟩]) unmarked_context_12_72252_501107 node_context_12_72252_501107
  intro a
  fin_cases a
  · exact context_13_289008_500913
  · exact context_13_289009_501054
  · exact context_13_289010_501105
  · exact context_13_289011_501106

theorem selected_cut_19579 : selected 8 ⟨501110, by decide⟩
    (prefixPartial 13 289012) = some ⟨13, 2, 0, 501110, 289012, 169, 16384⟩ := by
  decide +kernel

theorem context_13_289012_501110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289012 ⟨501110, by decide⟩ :=
  accepted_of_selected 13 289012 ⟨501110, by decide⟩ ⟨13, 2, 0, 501110, 289012, 169, 16384⟩
    (by decide) selected_cut_19579

theorem selected_cut_19580 : selected 8 ⟨501150, by decide⟩
    (prefixPartial 13 289013) = some ⟨13, 2, 0, 501150, 289013, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_289013_501150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289013 ⟨501150, by decide⟩ :=
  accepted_of_selected 13 289013 ⟨501150, by decide⟩ ⟨13, 2, 0, 501150, 289013, 2749, 16384⟩
    (by decide) selected_cut_19580

theorem selected_cut_19581 : selected 8 ⟨501165, by decide⟩
    (prefixPartial 13 289014) = some ⟨13, 2, 0, 501165, 289014, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_289014_501165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289014 ⟨501165, by decide⟩ :=
  accepted_of_selected 13 289014 ⟨501165, by decide⟩ ⟨13, 2, 0, 501165, 289014, 1333, 16384⟩
    (by decide) selected_cut_19581

theorem selected_cut_19582 : selected 8 ⟨501186, by decide⟩
    (prefixPartial 13 289015) = some ⟨13, 2, 0, 501186, 289015, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_289015_501186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289015 ⟨501186, by decide⟩ :=
  accepted_of_selected 13 289015 ⟨501186, by decide⟩ ⟨13, 2, 0, 501186, 289015, 1209, 16384⟩
    (by decide) selected_cut_19582

theorem unmarked_context_12_72253_501187 : frontier 9 ⟨501187, by decide⟩
    (prefixCache 12 72253) (prefixPartial 12 72253) = false := by
  decide +kernel

theorem node_context_12_72253_501187 : EJMOriginalGlobalDAGData.nodes 9 ⟨501187, by decide⟩ =
    .split (coordinate 12) (![⟨501110, by decide⟩,⟨501150, by decide⟩,⟨501165, by decide⟩,⟨501186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72253_501187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72253 ⟨501187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72253
    ⟨501187, by decide⟩ (by decide) (![⟨501110, by decide⟩,⟨501150, by decide⟩,⟨501165, by decide⟩,⟨501186, by decide⟩]) unmarked_context_12_72253_501187 node_context_12_72253_501187
  intro a
  fin_cases a
  · exact context_13_289012_501110
  · exact context_13_289013_501150
  · exact context_13_289014_501165
  · exact context_13_289015_501186

theorem selected_cut_19583 : selected 8 ⟨501190, by decide⟩
    (prefixPartial 13 289016) = some ⟨13, 2, 0, 501190, 289016, 97, 16384⟩ := by
  decide +kernel

theorem context_13_289016_501190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289016 ⟨501190, by decide⟩ :=
  accepted_of_selected 13 289016 ⟨501190, by decide⟩ ⟨13, 2, 0, 501190, 289016, 97, 16384⟩
    (by decide) selected_cut_19583

theorem selected_cut_19584 : selected 8 ⟨501229, by decide⟩
    (prefixPartial 13 289017) = some ⟨13, 2, 0, 501229, 289017, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_289017_501229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289017 ⟨501229, by decide⟩ :=
  accepted_of_selected 13 289017 ⟨501229, by decide⟩ ⟨13, 2, 0, 501229, 289017, 3137, 16384⟩
    (by decide) selected_cut_19584

theorem selected_cut_19585 : selected 8 ⟨501249, by decide⟩
    (prefixPartial 13 289018) = some ⟨13, 2, 0, 501249, 289018, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_289018_501249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289018 ⟨501249, by decide⟩ :=
  accepted_of_selected 13 289018 ⟨501249, by decide⟩ ⟨13, 2, 0, 501249, 289018, 1637, 16384⟩
    (by decide) selected_cut_19585

theorem selected_cut_19586 : selected 8 ⟨501259, by decide⟩
    (prefixPartial 13 289019) = some ⟨13, 2, 0, 501259, 289019, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_289019_501259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289019 ⟨501259, by decide⟩ :=
  accepted_of_selected 13 289019 ⟨501259, by decide⟩ ⟨13, 2, 0, 501259, 289019, 1109, 16384⟩
    (by decide) selected_cut_19586

theorem unmarked_context_12_72254_501260 : frontier 9 ⟨501260, by decide⟩
    (prefixCache 12 72254) (prefixPartial 12 72254) = false := by
  decide +kernel

theorem node_context_12_72254_501260 : EJMOriginalGlobalDAGData.nodes 9 ⟨501260, by decide⟩ =
    .split (coordinate 12) (![⟨501190, by decide⟩,⟨501229, by decide⟩,⟨501249, by decide⟩,⟨501259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72254_501260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72254 ⟨501260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72254
    ⟨501260, by decide⟩ (by decide) (![⟨501190, by decide⟩,⟨501229, by decide⟩,⟨501249, by decide⟩,⟨501259, by decide⟩]) unmarked_context_12_72254_501260 node_context_12_72254_501260
  intro a
  fin_cases a
  · exact context_13_289016_501190
  · exact context_13_289017_501229
  · exact context_13_289018_501249
  · exact context_13_289019_501259

theorem selected_cut_19587 : selected 8 ⟨501263, by decide⟩
    (prefixPartial 13 289020) = some ⟨13, 2, 0, 501263, 289020, 73, 16384⟩ := by
  decide +kernel

theorem context_13_289020_501263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289020 ⟨501263, by decide⟩ :=
  accepted_of_selected 13 289020 ⟨501263, by decide⟩ ⟨13, 2, 0, 501263, 289020, 73, 16384⟩
    (by decide) selected_cut_19587

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
