/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover026
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_5727_82052 : frontier 9 ⟨82052, by decide⟩
    (prefixCache 12 5727) (prefixPartial 12 5727) = false := by
  decide +kernel

theorem node_context_12_5727_82052 : EJMOriginalGlobalDAGData.nodes 9 ⟨82052, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82013, by decide⟩,⟨82039, by decide⟩,⟨82051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5727_82052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5727 ⟨82052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5727
    ⟨82052, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82013, by decide⟩,⟨82039, by decide⟩,⟨82051, by decide⟩]) unmarked_context_12_5727_82052 node_context_12_5727_82052
  intro a
  fin_cases a
  · exact context_13_22908_3444
  · exact context_13_22909_82013
  · exact context_13_22910_82039
  · exact context_13_22911_82051

theorem unmarked_context_11_1431_82053 : frontier 10 ⟨82053, by decide⟩
    (prefixCache 11 1431) (prefixPartial 11 1431) = false := by
  decide +kernel

theorem node_context_11_1431_82053 : EJMOriginalGlobalDAGData.nodes 10 ⟨82053, by decide⟩ =
    .split (coordinate 11) (![⟨81871, by decide⟩,⟨81937, by decide⟩,⟨81996, by decide⟩,⟨82052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1431_82053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1431 ⟨82053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1431
    ⟨82053, by decide⟩ (by decide) (![⟨81871, by decide⟩,⟨81937, by decide⟩,⟨81996, by decide⟩,⟨82052, by decide⟩]) unmarked_context_11_1431_82053 node_context_11_1431_82053
  intro a
  fin_cases a
  · exact context_12_5724_81871
  · exact context_12_5725_81937
  · exact context_12_5726_81996
  · exact context_12_5727_82052

theorem unmarked_context_10_357_82054 : frontier 11 ⟨82054, by decide⟩
    (prefixCache 10 357) (prefixPartial 10 357) = false := by
  decide +kernel

theorem node_context_10_357_82054 : EJMOriginalGlobalDAGData.nodes 11 ⟨82054, by decide⟩ =
    .split (coordinate 10) (![⟨80907, by decide⟩,⟨81509, by decide⟩,⟨81817, by decide⟩,⟨82053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_357_82054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 357 ⟨82054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 357
    ⟨82054, by decide⟩ (by decide) (![⟨80907, by decide⟩,⟨81509, by decide⟩,⟨81817, by decide⟩,⟨82053, by decide⟩]) unmarked_context_10_357_82054 node_context_10_357_82054
  intro a
  fin_cases a
  · exact context_11_1428_80907
  · exact context_11_1429_81509
  · exact context_11_1430_81817
  · exact context_11_1431_82053

theorem selected_cut_02596 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22912) = some ⟨13, 1, 0, 3444, 22912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22912, 1, 16384⟩
    (by decide) selected_cut_02596

theorem selected_cut_02597 : selected 8 ⟨82070, by decide⟩
    (prefixPartial 13 22913) = some ⟨13, 2, 0, 82070, 22913, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_22913_82070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22913 ⟨82070, by decide⟩ :=
  accepted_of_selected 13 22913 ⟨82070, by decide⟩ ⟨13, 2, 0, 82070, 22913, 1509, 16384⟩
    (by decide) selected_cut_02597

theorem selected_cut_02598 : selected 8 ⟨82093, by decide⟩
    (prefixPartial 13 22914) = some ⟨13, 2, 0, 82093, 22914, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_22914_82093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22914 ⟨82093, by decide⟩ :=
  accepted_of_selected 13 22914 ⟨82093, by decide⟩ ⟨13, 2, 0, 82093, 22914, 2417, 16384⟩
    (by decide) selected_cut_02598

theorem selected_cut_02599 : selected 8 ⟨82104, by decide⟩
    (prefixPartial 13 22915) = some ⟨13, 2, 0, 82104, 22915, 933, 16384⟩ := by
  decide +kernel

theorem context_13_22915_82104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22915 ⟨82104, by decide⟩ :=
  accepted_of_selected 13 22915 ⟨82104, by decide⟩ ⟨13, 2, 0, 82104, 22915, 933, 16384⟩
    (by decide) selected_cut_02599

theorem unmarked_context_12_5728_82105 : frontier 9 ⟨82105, by decide⟩
    (prefixCache 12 5728) (prefixPartial 12 5728) = false := by
  decide +kernel

theorem node_context_12_5728_82105 : EJMOriginalGlobalDAGData.nodes 9 ⟨82105, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82070, by decide⟩,⟨82093, by decide⟩,⟨82104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5728_82105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5728 ⟨82105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5728
    ⟨82105, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82070, by decide⟩,⟨82093, by decide⟩,⟨82104, by decide⟩]) unmarked_context_12_5728_82105 node_context_12_5728_82105
  intro a
  fin_cases a
  · exact context_13_22912_3444
  · exact context_13_22913_82070
  · exact context_13_22914_82093
  · exact context_13_22915_82104

theorem selected_cut_02600 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22916) = some ⟨13, 1, 0, 3444, 22916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22916, 1, 16384⟩
    (by decide) selected_cut_02600

theorem selected_cut_02601 : selected 8 ⟨82128, by decide⟩
    (prefixPartial 13 22917) = some ⟨13, 2, 0, 82128, 22917, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_22917_82128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22917 ⟨82128, by decide⟩ :=
  accepted_of_selected 13 22917 ⟨82128, by decide⟩ ⟨13, 2, 0, 82128, 22917, 1813, 16384⟩
    (by decide) selected_cut_02601

theorem selected_cut_02602 : selected 8 ⟨82168, by decide⟩
    (prefixPartial 13 22918) = some ⟨13, 2, 0, 82168, 22918, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_22918_82168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22918 ⟨82168, by decide⟩ :=
  accepted_of_selected 13 22918 ⟨82168, by decide⟩ ⟨13, 2, 0, 82168, 22918, 2481, 16384⟩
    (by decide) selected_cut_02602

theorem selected_cut_02603 : selected 8 ⟨82181, by decide⟩
    (prefixPartial 13 22919) = some ⟨13, 2, 0, 82181, 22919, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_22919_82181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22919 ⟨82181, by decide⟩ :=
  accepted_of_selected 13 22919 ⟨82181, by decide⟩ ⟨13, 2, 0, 82181, 22919, 1185, 16384⟩
    (by decide) selected_cut_02603

theorem unmarked_context_12_5729_82182 : frontier 9 ⟨82182, by decide⟩
    (prefixCache 12 5729) (prefixPartial 12 5729) = false := by
  decide +kernel

theorem node_context_12_5729_82182 : EJMOriginalGlobalDAGData.nodes 9 ⟨82182, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82128, by decide⟩,⟨82168, by decide⟩,⟨82181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5729_82182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5729 ⟨82182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5729
    ⟨82182, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82128, by decide⟩,⟨82168, by decide⟩,⟨82181, by decide⟩]) unmarked_context_12_5729_82182 node_context_12_5729_82182
  intro a
  fin_cases a
  · exact context_13_22916_3444
  · exact context_13_22917_82128
  · exact context_13_22918_82168
  · exact context_13_22919_82181

theorem selected_cut_02604 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22920) = some ⟨13, 1, 0, 3444, 22920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22920, 1, 16384⟩
    (by decide) selected_cut_02604

theorem selected_cut_02605 : selected 8 ⟨82202, by decide⟩
    (prefixPartial 13 22921) = some ⟨13, 2, 0, 82202, 22921, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_22921_82202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22921 ⟨82202, by decide⟩ :=
  accepted_of_selected 13 22921 ⟨82202, by decide⟩ ⟨13, 2, 0, 82202, 22921, 1717, 16384⟩
    (by decide) selected_cut_02605

theorem selected_cut_02606 : selected 8 ⟨82230, by decide⟩
    (prefixPartial 13 22922) = some ⟨13, 2, 0, 82230, 22922, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_22922_82230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22922 ⟨82230, by decide⟩ :=
  accepted_of_selected 13 22922 ⟨82230, by decide⟩ ⟨13, 2, 0, 82230, 22922, 2317, 16384⟩
    (by decide) selected_cut_02606

theorem selected_cut_02607 : selected 8 ⟨82246, by decide⟩
    (prefixPartial 13 22923) = some ⟨13, 2, 0, 82246, 22923, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_22923_82246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22923 ⟨82246, by decide⟩ :=
  accepted_of_selected 13 22923 ⟨82246, by decide⟩ ⟨13, 2, 0, 82246, 22923, 1197, 16384⟩
    (by decide) selected_cut_02607

theorem unmarked_context_12_5730_82247 : frontier 9 ⟨82247, by decide⟩
    (prefixCache 12 5730) (prefixPartial 12 5730) = false := by
  decide +kernel

theorem node_context_12_5730_82247 : EJMOriginalGlobalDAGData.nodes 9 ⟨82247, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82202, by decide⟩,⟨82230, by decide⟩,⟨82246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5730_82247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5730 ⟨82247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5730
    ⟨82247, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82202, by decide⟩,⟨82230, by decide⟩,⟨82246, by decide⟩]) unmarked_context_12_5730_82247 node_context_12_5730_82247
  intro a
  fin_cases a
  · exact context_13_22920_3444
  · exact context_13_22921_82202
  · exact context_13_22922_82230
  · exact context_13_22923_82246

theorem selected_cut_02608 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22924) = some ⟨13, 1, 0, 3444, 22924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22924, 1, 16384⟩
    (by decide) selected_cut_02608

theorem selected_cut_02609 : selected 8 ⟨82277, by decide⟩
    (prefixPartial 13 22925) = some ⟨13, 2, 0, 82277, 22925, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_22925_82277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22925 ⟨82277, by decide⟩ :=
  accepted_of_selected 13 22925 ⟨82277, by decide⟩ ⟨13, 2, 0, 82277, 22925, 1913, 16384⟩
    (by decide) selected_cut_02609

theorem selected_cut_02610 : selected 8 ⟨82313, by decide⟩
    (prefixPartial 13 22926) = some ⟨13, 2, 0, 82313, 22926, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_22926_82313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22926 ⟨82313, by decide⟩ :=
  accepted_of_selected 13 22926 ⟨82313, by decide⟩ ⟨13, 2, 0, 82313, 22926, 2725, 16384⟩
    (by decide) selected_cut_02610

theorem selected_cut_02611 : selected 8 ⟨82323, by decide⟩
    (prefixPartial 13 22927) = some ⟨13, 2, 0, 82323, 22927, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_22927_82323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22927 ⟨82323, by decide⟩ :=
  accepted_of_selected 13 22927 ⟨82323, by decide⟩ ⟨13, 2, 0, 82323, 22927, 1089, 16384⟩
    (by decide) selected_cut_02611

theorem unmarked_context_12_5731_82324 : frontier 9 ⟨82324, by decide⟩
    (prefixCache 12 5731) (prefixPartial 12 5731) = false := by
  decide +kernel

theorem node_context_12_5731_82324 : EJMOriginalGlobalDAGData.nodes 9 ⟨82324, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82277, by decide⟩,⟨82313, by decide⟩,⟨82323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5731_82324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5731 ⟨82324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5731
    ⟨82324, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82277, by decide⟩,⟨82313, by decide⟩,⟨82323, by decide⟩]) unmarked_context_12_5731_82324 node_context_12_5731_82324
  intro a
  fin_cases a
  · exact context_13_22924_3444
  · exact context_13_22925_82277
  · exact context_13_22926_82313
  · exact context_13_22927_82323

theorem unmarked_context_11_1432_82325 : frontier 10 ⟨82325, by decide⟩
    (prefixCache 11 1432) (prefixPartial 11 1432) = false := by
  decide +kernel

theorem node_context_11_1432_82325 : EJMOriginalGlobalDAGData.nodes 10 ⟨82325, by decide⟩ =
    .split (coordinate 11) (![⟨82105, by decide⟩,⟨82182, by decide⟩,⟨82247, by decide⟩,⟨82324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1432_82325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1432 ⟨82325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1432
    ⟨82325, by decide⟩ (by decide) (![⟨82105, by decide⟩,⟨82182, by decide⟩,⟨82247, by decide⟩,⟨82324, by decide⟩]) unmarked_context_11_1432_82325 node_context_11_1432_82325
  intro a
  fin_cases a
  · exact context_12_5728_82105
  · exact context_12_5729_82182
  · exact context_12_5730_82247
  · exact context_12_5731_82324

theorem selected_cut_02612 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22928) = some ⟨13, 1, 0, 3444, 22928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22928, 1, 16384⟩
    (by decide) selected_cut_02612

theorem selected_cut_02613 : selected 8 ⟨82341, by decide⟩
    (prefixPartial 13 22929) = some ⟨13, 2, 0, 82341, 22929, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_22929_82341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22929 ⟨82341, by decide⟩ :=
  accepted_of_selected 13 22929 ⟨82341, by decide⟩ ⟨13, 2, 0, 82341, 22929, 1405, 16384⟩
    (by decide) selected_cut_02613

theorem selected_cut_02614 : selected 8 ⟨82373, by decide⟩
    (prefixPartial 13 22930) = some ⟨13, 2, 0, 82373, 22930, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_22930_82373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22930 ⟨82373, by decide⟩ :=
  accepted_of_selected 13 22930 ⟨82373, by decide⟩ ⟨13, 2, 0, 82373, 22930, 2389, 16384⟩
    (by decide) selected_cut_02614

theorem selected_cut_02615 : selected 8 ⟨82384, by decide⟩
    (prefixPartial 13 22931) = some ⟨13, 2, 0, 82384, 22931, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_22931_82384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22931 ⟨82384, by decide⟩ :=
  accepted_of_selected 13 22931 ⟨82384, by decide⟩ ⟨13, 2, 0, 82384, 22931, 1017, 16384⟩
    (by decide) selected_cut_02615

theorem unmarked_context_12_5732_82385 : frontier 9 ⟨82385, by decide⟩
    (prefixCache 12 5732) (prefixPartial 12 5732) = false := by
  decide +kernel

theorem node_context_12_5732_82385 : EJMOriginalGlobalDAGData.nodes 9 ⟨82385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82341, by decide⟩,⟨82373, by decide⟩,⟨82384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5732_82385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5732 ⟨82385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5732
    ⟨82385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82341, by decide⟩,⟨82373, by decide⟩,⟨82384, by decide⟩]) unmarked_context_12_5732_82385 node_context_12_5732_82385
  intro a
  fin_cases a
  · exact context_13_22928_3444
  · exact context_13_22929_82341
  · exact context_13_22930_82373
  · exact context_13_22931_82384

theorem selected_cut_02616 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22932) = some ⟨13, 1, 0, 3444, 22932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22932, 1, 16384⟩
    (by decide) selected_cut_02616

theorem selected_cut_02617 : selected 8 ⟨82401, by decide⟩
    (prefixPartial 13 22933) = some ⟨13, 2, 0, 82401, 22933, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_22933_82401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22933 ⟨82401, by decide⟩ :=
  accepted_of_selected 13 22933 ⟨82401, by decide⟩ ⟨13, 2, 0, 82401, 22933, 1553, 16384⟩
    (by decide) selected_cut_02617

theorem selected_cut_02618 : selected 8 ⟨82430, by decide⟩
    (prefixPartial 13 22934) = some ⟨13, 2, 0, 82430, 22934, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_22934_82430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22934 ⟨82430, by decide⟩ :=
  accepted_of_selected 13 22934 ⟨82430, by decide⟩ ⟨13, 2, 0, 82430, 22934, 2449, 16384⟩
    (by decide) selected_cut_02618

theorem selected_cut_02619 : selected 8 ⟨82441, by decide⟩
    (prefixPartial 13 22935) = some ⟨13, 2, 0, 82441, 22935, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_22935_82441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22935 ⟨82441, by decide⟩ :=
  accepted_of_selected 13 22935 ⟨82441, by decide⟩ ⟨13, 2, 0, 82441, 22935, 1193, 16384⟩
    (by decide) selected_cut_02619

theorem unmarked_context_12_5733_82442 : frontier 9 ⟨82442, by decide⟩
    (prefixCache 12 5733) (prefixPartial 12 5733) = false := by
  decide +kernel

theorem node_context_12_5733_82442 : EJMOriginalGlobalDAGData.nodes 9 ⟨82442, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82401, by decide⟩,⟨82430, by decide⟩,⟨82441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5733_82442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5733 ⟨82442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5733
    ⟨82442, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82401, by decide⟩,⟨82430, by decide⟩,⟨82441, by decide⟩]) unmarked_context_12_5733_82442 node_context_12_5733_82442
  intro a
  fin_cases a
  · exact context_13_22932_3444
  · exact context_13_22933_82401
  · exact context_13_22934_82430
  · exact context_13_22935_82441

theorem selected_cut_02620 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22936) = some ⟨13, 1, 0, 3444, 22936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22936, 1, 16384⟩
    (by decide) selected_cut_02620

theorem selected_cut_02621 : selected 8 ⟨82457, by decide⟩
    (prefixPartial 13 22937) = some ⟨13, 2, 0, 82457, 22937, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_22937_82457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22937 ⟨82457, by decide⟩ :=
  accepted_of_selected 13 22937 ⟨82457, by decide⟩ ⟨13, 2, 0, 82457, 22937, 1481, 16384⟩
    (by decide) selected_cut_02621

theorem selected_cut_02622 : selected 8 ⟨82482, by decide⟩
    (prefixPartial 13 22938) = some ⟨13, 2, 0, 82482, 22938, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_22938_82482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22938 ⟨82482, by decide⟩ :=
  accepted_of_selected 13 22938 ⟨82482, by decide⟩ ⟨13, 2, 0, 82482, 22938, 2325, 16384⟩
    (by decide) selected_cut_02622

theorem selected_cut_02623 : selected 8 ⟨82495, by decide⟩
    (prefixPartial 13 22939) = some ⟨13, 2, 0, 82495, 22939, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_22939_82495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22939 ⟨82495, by decide⟩ :=
  accepted_of_selected 13 22939 ⟨82495, by decide⟩ ⟨13, 2, 0, 82495, 22939, 1257, 16384⟩
    (by decide) selected_cut_02623

theorem unmarked_context_12_5734_82496 : frontier 9 ⟨82496, by decide⟩
    (prefixCache 12 5734) (prefixPartial 12 5734) = false := by
  decide +kernel

theorem node_context_12_5734_82496 : EJMOriginalGlobalDAGData.nodes 9 ⟨82496, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82457, by decide⟩,⟨82482, by decide⟩,⟨82495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5734_82496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5734 ⟨82496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5734
    ⟨82496, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82457, by decide⟩,⟨82482, by decide⟩,⟨82495, by decide⟩]) unmarked_context_12_5734_82496 node_context_12_5734_82496
  intro a
  fin_cases a
  · exact context_13_22936_3444
  · exact context_13_22937_82457
  · exact context_13_22938_82482
  · exact context_13_22939_82495

theorem selected_cut_02624 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22940) = some ⟨13, 1, 0, 3444, 22940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22940, 1, 16384⟩
    (by decide) selected_cut_02624

theorem selected_cut_02625 : selected 8 ⟨82516, by decide⟩
    (prefixPartial 13 22941) = some ⟨13, 2, 0, 82516, 22941, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_22941_82516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22941 ⟨82516, by decide⟩ :=
  accepted_of_selected 13 22941 ⟨82516, by decide⟩ ⟨13, 2, 0, 82516, 22941, 1533, 16384⟩
    (by decide) selected_cut_02625

theorem selected_cut_02626 : selected 8 ⟨82560, by decide⟩
    (prefixPartial 13 22942) = some ⟨13, 2, 0, 82560, 22942, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_22942_82560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22942 ⟨82560, by decide⟩ :=
  accepted_of_selected 13 22942 ⟨82560, by decide⟩ ⟨13, 2, 0, 82560, 22942, 2965, 16384⟩
    (by decide) selected_cut_02626

theorem selected_cut_02627 : selected 8 ⟨82570, by decide⟩
    (prefixPartial 13 22943) = some ⟨13, 2, 0, 82570, 22943, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_22943_82570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22943 ⟨82570, by decide⟩ :=
  accepted_of_selected 13 22943 ⟨82570, by decide⟩ ⟨13, 2, 0, 82570, 22943, 1125, 16384⟩
    (by decide) selected_cut_02627

theorem unmarked_context_12_5735_82571 : frontier 9 ⟨82571, by decide⟩
    (prefixCache 12 5735) (prefixPartial 12 5735) = false := by
  decide +kernel

theorem node_context_12_5735_82571 : EJMOriginalGlobalDAGData.nodes 9 ⟨82571, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82516, by decide⟩,⟨82560, by decide⟩,⟨82570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5735_82571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5735 ⟨82571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5735
    ⟨82571, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82516, by decide⟩,⟨82560, by decide⟩,⟨82570, by decide⟩]) unmarked_context_12_5735_82571 node_context_12_5735_82571
  intro a
  fin_cases a
  · exact context_13_22940_3444
  · exact context_13_22941_82516
  · exact context_13_22942_82560
  · exact context_13_22943_82570

theorem unmarked_context_11_1433_82572 : frontier 10 ⟨82572, by decide⟩
    (prefixCache 11 1433) (prefixPartial 11 1433) = false := by
  decide +kernel

theorem node_context_11_1433_82572 : EJMOriginalGlobalDAGData.nodes 10 ⟨82572, by decide⟩ =
    .split (coordinate 11) (![⟨82385, by decide⟩,⟨82442, by decide⟩,⟨82496, by decide⟩,⟨82571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1433_82572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1433 ⟨82572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1433
    ⟨82572, by decide⟩ (by decide) (![⟨82385, by decide⟩,⟨82442, by decide⟩,⟨82496, by decide⟩,⟨82571, by decide⟩]) unmarked_context_11_1433_82572 node_context_11_1433_82572
  intro a
  fin_cases a
  · exact context_12_5732_82385
  · exact context_12_5733_82442
  · exact context_12_5734_82496
  · exact context_12_5735_82571

theorem selected_cut_02628 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22944) = some ⟨13, 1, 0, 3444, 22944, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22944_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22944 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22944 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22944, 1, 16384⟩
    (by decide) selected_cut_02628

theorem selected_cut_02629 : selected 8 ⟨82582, by decide⟩
    (prefixPartial 13 22945) = some ⟨13, 2, 0, 82582, 22945, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_22945_82582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22945 ⟨82582, by decide⟩ :=
  accepted_of_selected 13 22945 ⟨82582, by decide⟩ ⟨13, 2, 0, 82582, 22945, 1041, 16384⟩
    (by decide) selected_cut_02629

theorem selected_cut_02630 : selected 8 ⟨82606, by decide⟩
    (prefixPartial 13 22946) = some ⟨13, 2, 0, 82606, 22946, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_22946_82606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22946 ⟨82606, by decide⟩ :=
  accepted_of_selected 13 22946 ⟨82606, by decide⟩ ⟨13, 2, 0, 82606, 22946, 2253, 16384⟩
    (by decide) selected_cut_02630

theorem selected_cut_02631 : selected 8 ⟨82616, by decide⟩
    (prefixPartial 13 22947) = some ⟨13, 2, 0, 82616, 22947, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_22947_82616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22947 ⟨82616, by decide⟩ :=
  accepted_of_selected 13 22947 ⟨82616, by decide⟩ ⟨13, 2, 0, 82616, 22947, 1021, 16384⟩
    (by decide) selected_cut_02631

theorem unmarked_context_12_5736_82617 : frontier 9 ⟨82617, by decide⟩
    (prefixCache 12 5736) (prefixPartial 12 5736) = false := by
  decide +kernel

theorem node_context_12_5736_82617 : EJMOriginalGlobalDAGData.nodes 9 ⟨82617, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82582, by decide⟩,⟨82606, by decide⟩,⟨82616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5736_82617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5736 ⟨82617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5736
    ⟨82617, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82582, by decide⟩,⟨82606, by decide⟩,⟨82616, by decide⟩]) unmarked_context_12_5736_82617 node_context_12_5736_82617
  intro a
  fin_cases a
  · exact context_13_22944_3444
  · exact context_13_22945_82582
  · exact context_13_22946_82606
  · exact context_13_22947_82616

theorem selected_cut_02632 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22948) = some ⟨13, 1, 0, 3444, 22948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22948, 1, 16384⟩
    (by decide) selected_cut_02632

theorem selected_cut_02633 : selected 8 ⟨82630, by decide⟩
    (prefixPartial 13 22949) = some ⟨13, 2, 0, 82630, 22949, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_22949_82630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22949 ⟨82630, by decide⟩ :=
  accepted_of_selected 13 22949 ⟨82630, by decide⟩ ⟨13, 2, 0, 82630, 22949, 1173, 16384⟩
    (by decide) selected_cut_02633

theorem selected_cut_02634 : selected 8 ⟨82662, by decide⟩
    (prefixPartial 13 22950) = some ⟨13, 2, 0, 82662, 22950, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_22950_82662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22950 ⟨82662, by decide⟩ :=
  accepted_of_selected 13 22950 ⟨82662, by decide⟩ ⟨13, 2, 0, 82662, 22950, 2421, 16384⟩
    (by decide) selected_cut_02634

theorem selected_cut_02635 : selected 8 ⟨82673, by decide⟩
    (prefixPartial 13 22951) = some ⟨13, 2, 0, 82673, 22951, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_22951_82673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22951 ⟨82673, by decide⟩ :=
  accepted_of_selected 13 22951 ⟨82673, by decide⟩ ⟨13, 2, 0, 82673, 22951, 1269, 16384⟩
    (by decide) selected_cut_02635

theorem unmarked_context_12_5737_82674 : frontier 9 ⟨82674, by decide⟩
    (prefixCache 12 5737) (prefixPartial 12 5737) = false := by
  decide +kernel

theorem node_context_12_5737_82674 : EJMOriginalGlobalDAGData.nodes 9 ⟨82674, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82630, by decide⟩,⟨82662, by decide⟩,⟨82673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5737_82674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5737 ⟨82674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5737
    ⟨82674, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82630, by decide⟩,⟨82662, by decide⟩,⟨82673, by decide⟩]) unmarked_context_12_5737_82674 node_context_12_5737_82674
  intro a
  fin_cases a
  · exact context_13_22948_3444
  · exact context_13_22949_82630
  · exact context_13_22950_82662
  · exact context_13_22951_82673

theorem selected_cut_02636 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22952) = some ⟨13, 1, 0, 3444, 22952, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22952_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22952 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22952 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22952, 1, 16384⟩
    (by decide) selected_cut_02636

theorem selected_cut_02637 : selected 8 ⟨82704, by decide⟩
    (prefixPartial 13 22953) = some ⟨13, 2, 0, 82704, 22953, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_22953_82704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22953 ⟨82704, by decide⟩ :=
  accepted_of_selected 13 22953 ⟨82704, by decide⟩ ⟨13, 2, 0, 82704, 22953, 1733, 16384⟩
    (by decide) selected_cut_02637

theorem selected_cut_02638 : selected 8 ⟨82766, by decide⟩
    (prefixPartial 13 22954) = some ⟨13, 2, 0, 82766, 22954, 3617, 16384⟩ := by
  decide +kernel

theorem context_13_22954_82766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22954 ⟨82766, by decide⟩ :=
  accepted_of_selected 13 22954 ⟨82766, by decide⟩ ⟨13, 2, 0, 82766, 22954, 3617, 16384⟩
    (by decide) selected_cut_02638

theorem selected_cut_02639 : selected 8 ⟨82803, by decide⟩
    (prefixPartial 13 22955) = some ⟨13, 2, 0, 82803, 22955, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_22955_82803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22955 ⟨82803, by decide⟩ :=
  accepted_of_selected 13 22955 ⟨82803, by decide⟩ ⟨13, 2, 0, 82803, 22955, 1765, 16384⟩
    (by decide) selected_cut_02639

theorem unmarked_context_12_5738_82804 : frontier 9 ⟨82804, by decide⟩
    (prefixCache 12 5738) (prefixPartial 12 5738) = false := by
  decide +kernel

theorem node_context_12_5738_82804 : EJMOriginalGlobalDAGData.nodes 9 ⟨82804, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82704, by decide⟩,⟨82766, by decide⟩,⟨82803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5738_82804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5738 ⟨82804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5738
    ⟨82804, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82704, by decide⟩,⟨82766, by decide⟩,⟨82803, by decide⟩]) unmarked_context_12_5738_82804 node_context_12_5738_82804
  intro a
  fin_cases a
  · exact context_13_22952_3444
  · exact context_13_22953_82704
  · exact context_13_22954_82766
  · exact context_13_22955_82803

theorem selected_cut_02640 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22956) = some ⟨13, 1, 0, 3444, 22956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22956, 1, 16384⟩
    (by decide) selected_cut_02640

theorem selected_cut_02641 : selected 8 ⟨82817, by decide⟩
    (prefixPartial 13 22957) = some ⟨13, 2, 0, 82817, 22957, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_22957_82817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22957 ⟨82817, by decide⟩ :=
  accepted_of_selected 13 22957 ⟨82817, by decide⟩ ⟨13, 2, 0, 82817, 22957, 1145, 16384⟩
    (by decide) selected_cut_02641

theorem selected_cut_02642 : selected 8 ⟨82851, by decide⟩
    (prefixPartial 13 22958) = some ⟨13, 2, 0, 82851, 22958, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_22958_82851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22958 ⟨82851, by decide⟩ :=
  accepted_of_selected 13 22958 ⟨82851, by decide⟩ ⟨13, 2, 0, 82851, 22958, 2653, 16384⟩
    (by decide) selected_cut_02642

theorem selected_cut_02643 : selected 8 ⟨82864, by decide⟩
    (prefixPartial 13 22959) = some ⟨13, 2, 0, 82864, 22959, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_22959_82864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22959 ⟨82864, by decide⟩ :=
  accepted_of_selected 13 22959 ⟨82864, by decide⟩ ⟨13, 2, 0, 82864, 22959, 1105, 16384⟩
    (by decide) selected_cut_02643

theorem unmarked_context_12_5739_82865 : frontier 9 ⟨82865, by decide⟩
    (prefixCache 12 5739) (prefixPartial 12 5739) = false := by
  decide +kernel

theorem node_context_12_5739_82865 : EJMOriginalGlobalDAGData.nodes 9 ⟨82865, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82817, by decide⟩,⟨82851, by decide⟩,⟨82864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5739_82865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5739 ⟨82865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5739
    ⟨82865, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82817, by decide⟩,⟨82851, by decide⟩,⟨82864, by decide⟩]) unmarked_context_12_5739_82865 node_context_12_5739_82865
  intro a
  fin_cases a
  · exact context_13_22956_3444
  · exact context_13_22957_82817
  · exact context_13_22958_82851
  · exact context_13_22959_82864

theorem unmarked_context_11_1434_82866 : frontier 10 ⟨82866, by decide⟩
    (prefixCache 11 1434) (prefixPartial 11 1434) = false := by
  decide +kernel

theorem node_context_11_1434_82866 : EJMOriginalGlobalDAGData.nodes 10 ⟨82866, by decide⟩ =
    .split (coordinate 11) (![⟨82617, by decide⟩,⟨82674, by decide⟩,⟨82804, by decide⟩,⟨82865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1434_82866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1434 ⟨82866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1434
    ⟨82866, by decide⟩ (by decide) (![⟨82617, by decide⟩,⟨82674, by decide⟩,⟨82804, by decide⟩,⟨82865, by decide⟩]) unmarked_context_11_1434_82866 node_context_11_1434_82866
  intro a
  fin_cases a
  · exact context_12_5736_82617
  · exact context_12_5737_82674
  · exact context_12_5738_82804
  · exact context_12_5739_82865

theorem selected_cut_02644 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22960) = some ⟨13, 1, 0, 3444, 22960, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22960_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22960 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22960 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22960, 1, 16384⟩
    (by decide) selected_cut_02644

theorem selected_cut_02645 : selected 8 ⟨82879, by decide⟩
    (prefixPartial 13 22961) = some ⟨13, 2, 0, 82879, 22961, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_22961_82879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22961 ⟨82879, by decide⟩ :=
  accepted_of_selected 13 22961 ⟨82879, by decide⟩ ⟨13, 2, 0, 82879, 22961, 1057, 16384⟩
    (by decide) selected_cut_02645

theorem selected_cut_02646 : selected 8 ⟨82914, by decide⟩
    (prefixPartial 13 22962) = some ⟨13, 2, 0, 82914, 22962, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_22962_82914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22962 ⟨82914, by decide⟩ :=
  accepted_of_selected 13 22962 ⟨82914, by decide⟩ ⟨13, 2, 0, 82914, 22962, 2661, 16384⟩
    (by decide) selected_cut_02646

theorem selected_cut_02647 : selected 8 ⟨82923, by decide⟩
    (prefixPartial 13 22963) = some ⟨13, 2, 0, 82923, 22963, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_22963_82923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22963 ⟨82923, by decide⟩ :=
  accepted_of_selected 13 22963 ⟨82923, by decide⟩ ⟨13, 2, 0, 82923, 22963, 1173, 16384⟩
    (by decide) selected_cut_02647

theorem unmarked_context_12_5740_82924 : frontier 9 ⟨82924, by decide⟩
    (prefixCache 12 5740) (prefixPartial 12 5740) = false := by
  decide +kernel

theorem node_context_12_5740_82924 : EJMOriginalGlobalDAGData.nodes 9 ⟨82924, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82879, by decide⟩,⟨82914, by decide⟩,⟨82923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5740_82924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5740 ⟨82924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5740
    ⟨82924, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82879, by decide⟩,⟨82914, by decide⟩,⟨82923, by decide⟩]) unmarked_context_12_5740_82924 node_context_12_5740_82924
  intro a
  fin_cases a
  · exact context_13_22960_3444
  · exact context_13_22961_82879
  · exact context_13_22962_82914
  · exact context_13_22963_82923

theorem selected_cut_02648 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22964) = some ⟨13, 1, 0, 3444, 22964, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22964_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22964 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22964 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22964, 1, 16384⟩
    (by decide) selected_cut_02648

theorem selected_cut_02649 : selected 8 ⟨82940, by decide⟩
    (prefixPartial 13 22965) = some ⟨13, 2, 0, 82940, 22965, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_22965_82940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22965 ⟨82940, by decide⟩ :=
  accepted_of_selected 13 22965 ⟨82940, by decide⟩ ⟨13, 2, 0, 82940, 22965, 1133, 16384⟩
    (by decide) selected_cut_02649

theorem selected_cut_02650 : selected 8 ⟨82992, by decide⟩
    (prefixPartial 13 22966) = some ⟨13, 2, 0, 82992, 22966, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_22966_82992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22966 ⟨82992, by decide⟩ :=
  accepted_of_selected 13 22966 ⟨82992, by decide⟩ ⟨13, 2, 0, 82992, 22966, 2953, 16384⟩
    (by decide) selected_cut_02650

theorem selected_cut_02651 : selected 8 ⟨83013, by decide⟩
    (prefixPartial 13 22967) = some ⟨13, 2, 0, 83013, 22967, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_22967_83013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22967 ⟨83013, by decide⟩ :=
  accepted_of_selected 13 22967 ⟨83013, by decide⟩ ⟨13, 2, 0, 83013, 22967, 1341, 16384⟩
    (by decide) selected_cut_02651

theorem unmarked_context_12_5741_83014 : frontier 9 ⟨83014, by decide⟩
    (prefixCache 12 5741) (prefixPartial 12 5741) = false := by
  decide +kernel

theorem node_context_12_5741_83014 : EJMOriginalGlobalDAGData.nodes 9 ⟨83014, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨82940, by decide⟩,⟨82992, by decide⟩,⟨83013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5741_83014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5741 ⟨83014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5741
    ⟨83014, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨82940, by decide⟩,⟨82992, by decide⟩,⟨83013, by decide⟩]) unmarked_context_12_5741_83014 node_context_12_5741_83014
  intro a
  fin_cases a
  · exact context_13_22964_3444
  · exact context_13_22965_82940
  · exact context_13_22966_82992
  · exact context_13_22967_83013

theorem selected_cut_02652 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22968) = some ⟨13, 1, 0, 3444, 22968, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22968_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22968 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22968 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22968, 1, 16384⟩
    (by decide) selected_cut_02652

theorem selected_cut_02653 : selected 8 ⟨83023, by decide⟩
    (prefixPartial 13 22969) = some ⟨13, 2, 0, 83023, 22969, 989, 16384⟩ := by
  decide +kernel

theorem context_13_22969_83023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22969 ⟨83023, by decide⟩ :=
  accepted_of_selected 13 22969 ⟨83023, by decide⟩ ⟨13, 2, 0, 83023, 22969, 989, 16384⟩
    (by decide) selected_cut_02653

theorem selected_cut_02654 : selected 8 ⟨83049, by decide⟩
    (prefixPartial 13 22970) = some ⟨13, 2, 0, 83049, 22970, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_22970_83049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22970 ⟨83049, by decide⟩ :=
  accepted_of_selected 13 22970 ⟨83049, by decide⟩ ⟨13, 2, 0, 83049, 22970, 2505, 16384⟩
    (by decide) selected_cut_02654

theorem selected_cut_02655 : selected 8 ⟨83066, by decide⟩
    (prefixPartial 13 22971) = some ⟨13, 2, 0, 83066, 22971, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_22971_83066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22971 ⟨83066, by decide⟩ :=
  accepted_of_selected 13 22971 ⟨83066, by decide⟩ ⟨13, 2, 0, 83066, 22971, 1325, 16384⟩
    (by decide) selected_cut_02655

theorem unmarked_context_12_5742_83067 : frontier 9 ⟨83067, by decide⟩
    (prefixCache 12 5742) (prefixPartial 12 5742) = false := by
  decide +kernel

theorem node_context_12_5742_83067 : EJMOriginalGlobalDAGData.nodes 9 ⟨83067, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83023, by decide⟩,⟨83049, by decide⟩,⟨83066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5742_83067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5742 ⟨83067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5742
    ⟨83067, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83023, by decide⟩,⟨83049, by decide⟩,⟨83066, by decide⟩]) unmarked_context_12_5742_83067 node_context_12_5742_83067
  intro a
  fin_cases a
  · exact context_13_22968_3444
  · exact context_13_22969_83023
  · exact context_13_22970_83049
  · exact context_13_22971_83066

theorem selected_cut_02656 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22972) = some ⟨13, 1, 0, 3444, 22972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22972, 1, 16384⟩
    (by decide) selected_cut_02656

theorem selected_cut_02657 : selected 8 ⟨83079, by decide⟩
    (prefixPartial 13 22973) = some ⟨13, 2, 0, 83079, 22973, 993, 16384⟩ := by
  decide +kernel

theorem context_13_22973_83079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22973 ⟨83079, by decide⟩ :=
  accepted_of_selected 13 22973 ⟨83079, by decide⟩ ⟨13, 2, 0, 83079, 22973, 993, 16384⟩
    (by decide) selected_cut_02657

theorem selected_cut_02658 : selected 8 ⟨83115, by decide⟩
    (prefixPartial 13 22974) = some ⟨13, 2, 0, 83115, 22974, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_22974_83115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22974 ⟨83115, by decide⟩ :=
  accepted_of_selected 13 22974 ⟨83115, by decide⟩ ⟨13, 2, 0, 83115, 22974, 2969, 16384⟩
    (by decide) selected_cut_02658

theorem selected_cut_02659 : selected 8 ⟨83125, by decide⟩
    (prefixPartial 13 22975) = some ⟨13, 2, 0, 83125, 22975, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_22975_83125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22975 ⟨83125, by decide⟩ :=
  accepted_of_selected 13 22975 ⟨83125, by decide⟩ ⟨13, 2, 0, 83125, 22975, 1241, 16384⟩
    (by decide) selected_cut_02659

theorem unmarked_context_12_5743_83126 : frontier 9 ⟨83126, by decide⟩
    (prefixCache 12 5743) (prefixPartial 12 5743) = false := by
  decide +kernel

theorem node_context_12_5743_83126 : EJMOriginalGlobalDAGData.nodes 9 ⟨83126, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83079, by decide⟩,⟨83115, by decide⟩,⟨83125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5743_83126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5743 ⟨83126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5743
    ⟨83126, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83079, by decide⟩,⟨83115, by decide⟩,⟨83125, by decide⟩]) unmarked_context_12_5743_83126 node_context_12_5743_83126
  intro a
  fin_cases a
  · exact context_13_22972_3444
  · exact context_13_22973_83079
  · exact context_13_22974_83115
  · exact context_13_22975_83125

theorem unmarked_context_11_1435_83127 : frontier 10 ⟨83127, by decide⟩
    (prefixCache 11 1435) (prefixPartial 11 1435) = false := by
  decide +kernel

theorem node_context_11_1435_83127 : EJMOriginalGlobalDAGData.nodes 10 ⟨83127, by decide⟩ =
    .split (coordinate 11) (![⟨82924, by decide⟩,⟨83014, by decide⟩,⟨83067, by decide⟩,⟨83126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1435_83127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1435 ⟨83127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1435
    ⟨83127, by decide⟩ (by decide) (![⟨82924, by decide⟩,⟨83014, by decide⟩,⟨83067, by decide⟩,⟨83126, by decide⟩]) unmarked_context_11_1435_83127 node_context_11_1435_83127
  intro a
  fin_cases a
  · exact context_12_5740_82924
  · exact context_12_5741_83014
  · exact context_12_5742_83067
  · exact context_12_5743_83126

theorem unmarked_context_10_358_83128 : frontier 11 ⟨83128, by decide⟩
    (prefixCache 10 358) (prefixPartial 10 358) = false := by
  decide +kernel

theorem node_context_10_358_83128 : EJMOriginalGlobalDAGData.nodes 11 ⟨83128, by decide⟩ =
    .split (coordinate 10) (![⟨82325, by decide⟩,⟨82572, by decide⟩,⟨82866, by decide⟩,⟨83127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_358_83128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 358 ⟨83128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 358
    ⟨83128, by decide⟩ (by decide) (![⟨82325, by decide⟩,⟨82572, by decide⟩,⟨82866, by decide⟩,⟨83127, by decide⟩]) unmarked_context_10_358_83128 node_context_10_358_83128
  intro a
  fin_cases a
  · exact context_11_1432_82325
  · exact context_11_1433_82572
  · exact context_11_1434_82866
  · exact context_11_1435_83127

theorem selected_cut_02660 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22976) = some ⟨13, 1, 0, 3444, 22976, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22976_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22976 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22976 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22976, 1, 16384⟩
    (by decide) selected_cut_02660

theorem selected_cut_02661 : selected 8 ⟨83140, by decide⟩
    (prefixPartial 13 22977) = some ⟨13, 2, 0, 83140, 22977, 897, 16384⟩ := by
  decide +kernel

theorem context_13_22977_83140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22977 ⟨83140, by decide⟩ :=
  accepted_of_selected 13 22977 ⟨83140, by decide⟩ ⟨13, 2, 0, 83140, 22977, 897, 16384⟩
    (by decide) selected_cut_02661

theorem selected_cut_02662 : selected 8 ⟨83166, by decide⟩
    (prefixPartial 13 22978) = some ⟨13, 2, 0, 83166, 22978, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_22978_83166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22978 ⟨83166, by decide⟩ :=
  accepted_of_selected 13 22978 ⟨83166, by decide⟩ ⟨13, 2, 0, 83166, 22978, 2341, 16384⟩
    (by decide) selected_cut_02662

theorem selected_cut_02663 : selected 8 ⟨83175, by decide⟩
    (prefixPartial 13 22979) = some ⟨13, 2, 0, 83175, 22979, 941, 16384⟩ := by
  decide +kernel

theorem context_13_22979_83175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22979 ⟨83175, by decide⟩ :=
  accepted_of_selected 13 22979 ⟨83175, by decide⟩ ⟨13, 2, 0, 83175, 22979, 941, 16384⟩
    (by decide) selected_cut_02663

theorem unmarked_context_12_5744_83176 : frontier 9 ⟨83176, by decide⟩
    (prefixCache 12 5744) (prefixPartial 12 5744) = false := by
  decide +kernel

theorem node_context_12_5744_83176 : EJMOriginalGlobalDAGData.nodes 9 ⟨83176, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83140, by decide⟩,⟨83166, by decide⟩,⟨83175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5744_83176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5744 ⟨83176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5744
    ⟨83176, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83140, by decide⟩,⟨83166, by decide⟩,⟨83175, by decide⟩]) unmarked_context_12_5744_83176 node_context_12_5744_83176
  intro a
  fin_cases a
  · exact context_13_22976_3444
  · exact context_13_22977_83140
  · exact context_13_22978_83166
  · exact context_13_22979_83175

theorem selected_cut_02664 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22980) = some ⟨13, 1, 0, 3444, 22980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22980, 1, 16384⟩
    (by decide) selected_cut_02664

theorem selected_cut_02665 : selected 8 ⟨83193, by decide⟩
    (prefixPartial 13 22981) = some ⟨13, 2, 0, 83193, 22981, 997, 16384⟩ := by
  decide +kernel

theorem context_13_22981_83193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22981 ⟨83193, by decide⟩ :=
  accepted_of_selected 13 22981 ⟨83193, by decide⟩ ⟨13, 2, 0, 83193, 22981, 997, 16384⟩
    (by decide) selected_cut_02665

theorem selected_cut_02666 : selected 8 ⟨83234, by decide⟩
    (prefixPartial 13 22982) = some ⟨13, 2, 0, 83234, 22982, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_22982_83234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22982 ⟨83234, by decide⟩ :=
  accepted_of_selected 13 22982 ⟨83234, by decide⟩ ⟨13, 2, 0, 83234, 22982, 2517, 16384⟩
    (by decide) selected_cut_02666

theorem selected_cut_02667 : selected 8 ⟨83249, by decide⟩
    (prefixPartial 13 22983) = some ⟨13, 2, 0, 83249, 22983, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_22983_83249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22983 ⟨83249, by decide⟩ :=
  accepted_of_selected 13 22983 ⟨83249, by decide⟩ ⟨13, 2, 0, 83249, 22983, 1245, 16384⟩
    (by decide) selected_cut_02667

theorem unmarked_context_12_5745_83250 : frontier 9 ⟨83250, by decide⟩
    (prefixCache 12 5745) (prefixPartial 12 5745) = false := by
  decide +kernel

theorem node_context_12_5745_83250 : EJMOriginalGlobalDAGData.nodes 9 ⟨83250, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83193, by decide⟩,⟨83234, by decide⟩,⟨83249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5745_83250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5745 ⟨83250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5745
    ⟨83250, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83193, by decide⟩,⟨83234, by decide⟩,⟨83249, by decide⟩]) unmarked_context_12_5745_83250 node_context_12_5745_83250
  intro a
  fin_cases a
  · exact context_13_22980_3444
  · exact context_13_22981_83193
  · exact context_13_22982_83234
  · exact context_13_22983_83249

theorem selected_cut_02668 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22984) = some ⟨13, 1, 0, 3444, 22984, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22984_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22984 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22984 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22984, 1, 16384⟩
    (by decide) selected_cut_02668

theorem selected_cut_02669 : selected 8 ⟨83260, by decide⟩
    (prefixPartial 13 22985) = some ⟨13, 2, 0, 83260, 22985, 845, 16384⟩ := by
  decide +kernel

theorem context_13_22985_83260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22985 ⟨83260, by decide⟩ :=
  accepted_of_selected 13 22985 ⟨83260, by decide⟩ ⟨13, 2, 0, 83260, 22985, 845, 16384⟩
    (by decide) selected_cut_02669

theorem selected_cut_02670 : selected 8 ⟨83293, by decide⟩
    (prefixPartial 13 22986) = some ⟨13, 2, 0, 83293, 22986, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_22986_83293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22986 ⟨83293, by decide⟩ :=
  accepted_of_selected 13 22986 ⟨83293, by decide⟩ ⟨13, 2, 0, 83293, 22986, 2293, 16384⟩
    (by decide) selected_cut_02670

theorem selected_cut_02671 : selected 8 ⟨83310, by decide⟩
    (prefixPartial 13 22987) = some ⟨13, 2, 0, 83310, 22987, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_22987_83310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22987 ⟨83310, by decide⟩ :=
  accepted_of_selected 13 22987 ⟨83310, by decide⟩ ⟨13, 2, 0, 83310, 22987, 1289, 16384⟩
    (by decide) selected_cut_02671

theorem unmarked_context_12_5746_83311 : frontier 9 ⟨83311, by decide⟩
    (prefixCache 12 5746) (prefixPartial 12 5746) = false := by
  decide +kernel

theorem node_context_12_5746_83311 : EJMOriginalGlobalDAGData.nodes 9 ⟨83311, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83260, by decide⟩,⟨83293, by decide⟩,⟨83310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5746_83311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5746 ⟨83311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5746
    ⟨83311, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83260, by decide⟩,⟨83293, by decide⟩,⟨83310, by decide⟩]) unmarked_context_12_5746_83311 node_context_12_5746_83311
  intro a
  fin_cases a
  · exact context_13_22984_3444
  · exact context_13_22985_83260
  · exact context_13_22986_83293
  · exact context_13_22987_83310

theorem selected_cut_02672 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22988) = some ⟨13, 1, 0, 3444, 22988, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22988_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22988 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22988 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22988, 1, 16384⟩
    (by decide) selected_cut_02672

theorem selected_cut_02673 : selected 8 ⟨83329, by decide⟩
    (prefixPartial 13 22989) = some ⟨13, 2, 0, 83329, 22989, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_22989_83329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22989 ⟨83329, by decide⟩ :=
  accepted_of_selected 13 22989 ⟨83329, by decide⟩ ⟨13, 2, 0, 83329, 22989, 1037, 16384⟩
    (by decide) selected_cut_02673

theorem selected_cut_02674 : selected 8 ⟨83372, by decide⟩
    (prefixPartial 13 22990) = some ⟨13, 2, 0, 83372, 22990, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_22990_83372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22990 ⟨83372, by decide⟩ :=
  accepted_of_selected 13 22990 ⟨83372, by decide⟩ ⟨13, 2, 0, 83372, 22990, 2713, 16384⟩
    (by decide) selected_cut_02674

theorem selected_cut_02675 : selected 8 ⟨83387, by decide⟩
    (prefixPartial 13 22991) = some ⟨13, 2, 0, 83387, 22991, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_22991_83387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22991 ⟨83387, by decide⟩ :=
  accepted_of_selected 13 22991 ⟨83387, by decide⟩ ⟨13, 2, 0, 83387, 22991, 1101, 16384⟩
    (by decide) selected_cut_02675

theorem unmarked_context_12_5747_83388 : frontier 9 ⟨83388, by decide⟩
    (prefixCache 12 5747) (prefixPartial 12 5747) = false := by
  decide +kernel

theorem node_context_12_5747_83388 : EJMOriginalGlobalDAGData.nodes 9 ⟨83388, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83329, by decide⟩,⟨83372, by decide⟩,⟨83387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5747_83388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5747 ⟨83388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5747
    ⟨83388, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83329, by decide⟩,⟨83372, by decide⟩,⟨83387, by decide⟩]) unmarked_context_12_5747_83388 node_context_12_5747_83388
  intro a
  fin_cases a
  · exact context_13_22988_3444
  · exact context_13_22989_83329
  · exact context_13_22990_83372
  · exact context_13_22991_83387

theorem unmarked_context_11_1436_83389 : frontier 10 ⟨83389, by decide⟩
    (prefixCache 11 1436) (prefixPartial 11 1436) = false := by
  decide +kernel

theorem node_context_11_1436_83389 : EJMOriginalGlobalDAGData.nodes 10 ⟨83389, by decide⟩ =
    .split (coordinate 11) (![⟨83176, by decide⟩,⟨83250, by decide⟩,⟨83311, by decide⟩,⟨83388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1436_83389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1436 ⟨83389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1436
    ⟨83389, by decide⟩ (by decide) (![⟨83176, by decide⟩,⟨83250, by decide⟩,⟨83311, by decide⟩,⟨83388, by decide⟩]) unmarked_context_11_1436_83389 node_context_11_1436_83389
  intro a
  fin_cases a
  · exact context_12_5744_83176
  · exact context_12_5745_83250
  · exact context_12_5746_83311
  · exact context_12_5747_83388

theorem selected_cut_02676 : selected 9 ⟨83443, by decide⟩
    (prefixPartial 12 5748) = some ⟨12, 2, 0, 83443, 5748, 3969, 65536⟩ := by
  decide +kernel

theorem context_12_5748_83443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5748 ⟨83443, by decide⟩ :=
  accepted_of_selected 12 5748 ⟨83443, by decide⟩ ⟨12, 2, 0, 83443, 5748, 3969, 65536⟩
    (by decide) selected_cut_02676

theorem selected_cut_02677 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22996) = some ⟨13, 1, 0, 3444, 22996, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22996_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22996 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22996 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22996, 1, 16384⟩
    (by decide) selected_cut_02677

theorem selected_cut_02678 : selected 8 ⟨83453, by decide⟩
    (prefixPartial 13 22997) = some ⟨13, 2, 0, 83453, 22997, 737, 16384⟩ := by
  decide +kernel

theorem context_13_22997_83453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22997 ⟨83453, by decide⟩ :=
  accepted_of_selected 13 22997 ⟨83453, by decide⟩ ⟨13, 2, 0, 83453, 22997, 737, 16384⟩
    (by decide) selected_cut_02678

theorem selected_cut_02679 : selected 8 ⟨83493, by decide⟩
    (prefixPartial 13 22998) = some ⟨13, 2, 0, 83493, 22998, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_22998_83493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22998 ⟨83493, by decide⟩ :=
  accepted_of_selected 13 22998 ⟨83493, by decide⟩ ⟨13, 2, 0, 83493, 22998, 2445, 16384⟩
    (by decide) selected_cut_02679

theorem selected_cut_02680 : selected 8 ⟨83505, by decide⟩
    (prefixPartial 13 22999) = some ⟨13, 2, 0, 83505, 22999, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_22999_83505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22999 ⟨83505, by decide⟩ :=
  accepted_of_selected 13 22999 ⟨83505, by decide⟩ ⟨13, 2, 0, 83505, 22999, 1105, 16384⟩
    (by decide) selected_cut_02680

theorem unmarked_context_12_5749_83506 : frontier 9 ⟨83506, by decide⟩
    (prefixCache 12 5749) (prefixPartial 12 5749) = false := by
  decide +kernel

theorem node_context_12_5749_83506 : EJMOriginalGlobalDAGData.nodes 9 ⟨83506, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83453, by decide⟩,⟨83493, by decide⟩,⟨83505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5749_83506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5749 ⟨83506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5749
    ⟨83506, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83453, by decide⟩,⟨83493, by decide⟩,⟨83505, by decide⟩]) unmarked_context_12_5749_83506 node_context_12_5749_83506
  intro a
  fin_cases a
  · exact context_13_22996_3444
  · exact context_13_22997_83453
  · exact context_13_22998_83493
  · exact context_13_22999_83505

theorem selected_cut_02681 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23000) = some ⟨13, 1, 0, 3444, 23000, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23000_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23000 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23000 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23000, 1, 16384⟩
    (by decide) selected_cut_02681

theorem selected_cut_02682 : selected 8 ⟨83514, by decide⟩
    (prefixPartial 13 23001) = some ⟨13, 2, 0, 83514, 23001, 645, 16384⟩ := by
  decide +kernel

theorem context_13_23001_83514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23001 ⟨83514, by decide⟩ :=
  accepted_of_selected 13 23001 ⟨83514, by decide⟩ ⟨13, 2, 0, 83514, 23001, 645, 16384⟩
    (by decide) selected_cut_02682

theorem selected_cut_02683 : selected 8 ⟨83541, by decide⟩
    (prefixPartial 13 23002) = some ⟨13, 2, 0, 83541, 23002, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_23002_83541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23002 ⟨83541, by decide⟩ :=
  accepted_of_selected 13 23002 ⟨83541, by decide⟩ ⟨13, 2, 0, 83541, 23002, 2269, 16384⟩
    (by decide) selected_cut_02683

theorem selected_cut_02684 : selected 8 ⟨83557, by decide⟩
    (prefixPartial 13 23003) = some ⟨13, 2, 0, 83557, 23003, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_23003_83557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23003 ⟨83557, by decide⟩ :=
  accepted_of_selected 13 23003 ⟨83557, by decide⟩ ⟨13, 2, 0, 83557, 23003, 1253, 16384⟩
    (by decide) selected_cut_02684

theorem unmarked_context_12_5750_83558 : frontier 9 ⟨83558, by decide⟩
    (prefixCache 12 5750) (prefixPartial 12 5750) = false := by
  decide +kernel

theorem node_context_12_5750_83558 : EJMOriginalGlobalDAGData.nodes 9 ⟨83558, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83514, by decide⟩,⟨83541, by decide⟩,⟨83557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5750_83558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5750 ⟨83558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5750
    ⟨83558, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83514, by decide⟩,⟨83541, by decide⟩,⟨83557, by decide⟩]) unmarked_context_12_5750_83558 node_context_12_5750_83558
  intro a
  fin_cases a
  · exact context_13_23000_3444
  · exact context_13_23001_83514
  · exact context_13_23002_83541
  · exact context_13_23003_83557

theorem selected_cut_02685 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23004) = some ⟨13, 1, 0, 3444, 23004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23004, 1, 16384⟩
    (by decide) selected_cut_02685

theorem selected_cut_02686 : selected 8 ⟨83570, by decide⟩
    (prefixPartial 13 23005) = some ⟨13, 2, 0, 83570, 23005, 713, 16384⟩ := by
  decide +kernel

theorem context_13_23005_83570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23005 ⟨83570, by decide⟩ :=
  accepted_of_selected 13 23005 ⟨83570, by decide⟩ ⟨13, 2, 0, 83570, 23005, 713, 16384⟩
    (by decide) selected_cut_02686

theorem selected_cut_02687 : selected 8 ⟨83626, by decide⟩
    (prefixPartial 13 23006) = some ⟨13, 2, 0, 83626, 23006, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_23006_83626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23006 ⟨83626, by decide⟩ :=
  accepted_of_selected 13 23006 ⟨83626, by decide⟩ ⟨13, 2, 0, 83626, 23006, 3013, 16384⟩
    (by decide) selected_cut_02687

theorem selected_cut_02688 : selected 8 ⟨83640, by decide⟩
    (prefixPartial 13 23007) = some ⟨13, 2, 0, 83640, 23007, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_23007_83640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23007 ⟨83640, by decide⟩ :=
  accepted_of_selected 13 23007 ⟨83640, by decide⟩ ⟨13, 2, 0, 83640, 23007, 1041, 16384⟩
    (by decide) selected_cut_02688

theorem unmarked_context_12_5751_83641 : frontier 9 ⟨83641, by decide⟩
    (prefixCache 12 5751) (prefixPartial 12 5751) = false := by
  decide +kernel

theorem node_context_12_5751_83641 : EJMOriginalGlobalDAGData.nodes 9 ⟨83641, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83570, by decide⟩,⟨83626, by decide⟩,⟨83640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5751_83641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5751 ⟨83641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5751
    ⟨83641, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83570, by decide⟩,⟨83626, by decide⟩,⟨83640, by decide⟩]) unmarked_context_12_5751_83641 node_context_12_5751_83641
  intro a
  fin_cases a
  · exact context_13_23004_3444
  · exact context_13_23005_83570
  · exact context_13_23006_83626
  · exact context_13_23007_83640

theorem unmarked_context_11_1437_83642 : frontier 10 ⟨83642, by decide⟩
    (prefixCache 11 1437) (prefixPartial 11 1437) = false := by
  decide +kernel

theorem node_context_11_1437_83642 : EJMOriginalGlobalDAGData.nodes 10 ⟨83642, by decide⟩ =
    .split (coordinate 11) (![⟨83443, by decide⟩,⟨83506, by decide⟩,⟨83558, by decide⟩,⟨83641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1437_83642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1437 ⟨83642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1437
    ⟨83642, by decide⟩ (by decide) (![⟨83443, by decide⟩,⟨83506, by decide⟩,⟨83558, by decide⟩,⟨83641, by decide⟩]) unmarked_context_11_1437_83642 node_context_11_1437_83642
  intro a
  fin_cases a
  · exact context_12_5748_83443
  · exact context_12_5749_83506
  · exact context_12_5750_83558
  · exact context_12_5751_83641

theorem selected_cut_02689 : selected 9 ⟨83685, by decide⟩
    (prefixPartial 12 5752) = some ⟨12, 2, 0, 83685, 5752, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_5752_83685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5752 ⟨83685, by decide⟩ :=
  accepted_of_selected 12 5752 ⟨83685, by decide⟩ ⟨12, 2, 0, 83685, 5752, 3897, 65536⟩
    (by decide) selected_cut_02689

theorem selected_cut_02690 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23012) = some ⟨13, 1, 0, 3444, 23012, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23012_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23012 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23012 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23012, 1, 16384⟩
    (by decide) selected_cut_02690

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
