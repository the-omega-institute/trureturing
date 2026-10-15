/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover221
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21314 : selected 10 ⟨545303, by decide⟩
    (prefixPartial 11 18737) = some ⟨11, 2, 0, 545303, 18737, 2637, 262144⟩ := by
  decide +kernel

theorem context_11_18737_545303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18737 ⟨545303, by decide⟩ :=
  accepted_of_selected 11 18737 ⟨545303, by decide⟩ ⟨11, 2, 0, 545303, 18737, 2637, 262144⟩
    (by decide) selected_cut_21314

theorem selected_cut_21315 : selected 10 ⟨545330, by decide⟩
    (prefixPartial 11 18738) = some ⟨11, 2, 0, 545330, 18738, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_18738_545330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18738 ⟨545330, by decide⟩ :=
  accepted_of_selected 11 18738 ⟨545330, by decide⟩ ⟨11, 2, 0, 545330, 18738, 2625, 262144⟩
    (by decide) selected_cut_21315

theorem selected_cut_21316 : selected 10 ⟨545361, by decide⟩
    (prefixPartial 11 18739) = some ⟨11, 2, 0, 545361, 18739, 2605, 262144⟩ := by
  decide +kernel

theorem context_11_18739_545361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18739 ⟨545361, by decide⟩ :=
  accepted_of_selected 11 18739 ⟨545361, by decide⟩ ⟨11, 2, 0, 545361, 18739, 2605, 262144⟩
    (by decide) selected_cut_21316

theorem unmarked_context_10_4684_545362 : frontier 11 ⟨545362, by decide⟩
    (prefixCache 10 4684) (prefixPartial 10 4684) = false := by
  decide +kernel

theorem node_context_10_4684_545362 : EJMOriginalGlobalDAGData.nodes 11 ⟨545362, by decide⟩ =
    .split (coordinate 10) (![⟨545276, by decide⟩,⟨545303, by decide⟩,⟨545330, by decide⟩,⟨545361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4684_545362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4684 ⟨545362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4684
    ⟨545362, by decide⟩ (by decide) (![⟨545276, by decide⟩,⟨545303, by decide⟩,⟨545330, by decide⟩,⟨545361, by decide⟩]) unmarked_context_10_4684_545362 node_context_10_4684_545362
  intro a
  fin_cases a
  · exact context_11_18736_545276
  · exact context_11_18737_545303
  · exact context_11_18738_545330
  · exact context_11_18739_545361

theorem selected_cut_21317 : selected 10 ⟨545389, by decide⟩
    (prefixPartial 11 18740) = some ⟨11, 2, 0, 545389, 18740, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_18740_545389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18740 ⟨545389, by decide⟩ :=
  accepted_of_selected 11 18740 ⟨545389, by decide⟩ ⟨11, 2, 0, 545389, 18740, 2565, 262144⟩
    (by decide) selected_cut_21317

theorem selected_cut_21318 : selected 10 ⟨545410, by decide⟩
    (prefixPartial 11 18741) = some ⟨11, 2, 0, 545410, 18741, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_18741_545410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18741 ⟨545410, by decide⟩ :=
  accepted_of_selected 11 18741 ⟨545410, by decide⟩ ⟨11, 2, 0, 545410, 18741, 2149, 262144⟩
    (by decide) selected_cut_21318

theorem selected_cut_21319 : selected 10 ⟨545430, by decide⟩
    (prefixPartial 11 18742) = some ⟨11, 2, 0, 545430, 18742, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_18742_545430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18742 ⟨545430, by decide⟩ :=
  accepted_of_selected 11 18742 ⟨545430, by decide⟩ ⟨11, 2, 0, 545430, 18742, 2193, 262144⟩
    (by decide) selected_cut_21319

theorem selected_cut_21320 : selected 10 ⟨545454, by decide⟩
    (prefixPartial 11 18743) = some ⟨11, 2, 0, 545454, 18743, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_18743_545454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18743 ⟨545454, by decide⟩ :=
  accepted_of_selected 11 18743 ⟨545454, by decide⟩ ⟨11, 2, 0, 545454, 18743, 1849, 262144⟩
    (by decide) selected_cut_21320

theorem unmarked_context_10_4685_545455 : frontier 11 ⟨545455, by decide⟩
    (prefixCache 10 4685) (prefixPartial 10 4685) = false := by
  decide +kernel

theorem node_context_10_4685_545455 : EJMOriginalGlobalDAGData.nodes 11 ⟨545455, by decide⟩ =
    .split (coordinate 10) (![⟨545389, by decide⟩,⟨545410, by decide⟩,⟨545430, by decide⟩,⟨545454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4685_545455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4685 ⟨545455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4685
    ⟨545455, by decide⟩ (by decide) (![⟨545389, by decide⟩,⟨545410, by decide⟩,⟨545430, by decide⟩,⟨545454, by decide⟩]) unmarked_context_10_4685_545455 node_context_10_4685_545455
  intro a
  fin_cases a
  · exact context_11_18740_545389
  · exact context_11_18741_545410
  · exact context_11_18742_545430
  · exact context_11_18743_545454

theorem selected_cut_21321 : selected 10 ⟨545472, by decide⟩
    (prefixPartial 11 18744) = some ⟨11, 2, 0, 545472, 18744, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_18744_545472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18744 ⟨545472, by decide⟩ :=
  accepted_of_selected 11 18744 ⟨545472, by decide⟩ ⟨11, 2, 0, 545472, 18744, 1533, 262144⟩
    (by decide) selected_cut_21321

theorem selected_cut_21322 : selected 10 ⟨545489, by decide⟩
    (prefixPartial 11 18745) = some ⟨11, 2, 0, 545489, 18745, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_18745_545489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18745 ⟨545489, by decide⟩ :=
  accepted_of_selected 11 18745 ⟨545489, by decide⟩ ⟨11, 2, 0, 545489, 18745, 1449, 262144⟩
    (by decide) selected_cut_21322

theorem selected_cut_21323 : selected 10 ⟨545505, by decide⟩
    (prefixPartial 11 18746) = some ⟨11, 2, 0, 545505, 18746, 1137, 262144⟩ := by
  decide +kernel

theorem context_11_18746_545505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18746 ⟨545505, by decide⟩ :=
  accepted_of_selected 11 18746 ⟨545505, by decide⟩ ⟨11, 2, 0, 545505, 18746, 1137, 262144⟩
    (by decide) selected_cut_21323

theorem selected_cut_21324 : selected 10 ⟨545520, by decide⟩
    (prefixPartial 11 18747) = some ⟨11, 2, 0, 545520, 18747, 933, 262144⟩ := by
  decide +kernel

theorem context_11_18747_545520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18747 ⟨545520, by decide⟩ :=
  accepted_of_selected 11 18747 ⟨545520, by decide⟩ ⟨11, 2, 0, 545520, 18747, 933, 262144⟩
    (by decide) selected_cut_21324

theorem unmarked_context_10_4686_545521 : frontier 11 ⟨545521, by decide⟩
    (prefixCache 10 4686) (prefixPartial 10 4686) = false := by
  decide +kernel

theorem node_context_10_4686_545521 : EJMOriginalGlobalDAGData.nodes 11 ⟨545521, by decide⟩ =
    .split (coordinate 10) (![⟨545472, by decide⟩,⟨545489, by decide⟩,⟨545505, by decide⟩,⟨545520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4686_545521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4686 ⟨545521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4686
    ⟨545521, by decide⟩ (by decide) (![⟨545472, by decide⟩,⟨545489, by decide⟩,⟨545505, by decide⟩,⟨545520, by decide⟩]) unmarked_context_10_4686_545521 node_context_10_4686_545521
  intro a
  fin_cases a
  · exact context_11_18744_545472
  · exact context_11_18745_545489
  · exact context_11_18746_545505
  · exact context_11_18747_545520

theorem selected_cut_21325 : selected 11 ⟨545536, by decide⟩
    (prefixPartial 10 4687) = some ⟨10, 2, 0, 545536, 4687, 1385, 1048576⟩ := by
  decide +kernel

theorem context_10_4687_545536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4687 ⟨545536, by decide⟩ :=
  accepted_of_selected 10 4687 ⟨545536, by decide⟩ ⟨10, 2, 0, 545536, 4687, 1385, 1048576⟩
    (by decide) selected_cut_21325

theorem unmarked_context_9_1171_545537 : frontier 12 ⟨545537, by decide⟩
    (prefixCache 9 1171) (prefixPartial 9 1171) = false := by
  decide +kernel

theorem node_context_9_1171_545537 : EJMOriginalGlobalDAGData.nodes 12 ⟨545537, by decide⟩ =
    .split (coordinate 9) (![⟨545362, by decide⟩,⟨545455, by decide⟩,⟨545521, by decide⟩,⟨545536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1171_545537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1171 ⟨545537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1171
    ⟨545537, by decide⟩ (by decide) (![⟨545362, by decide⟩,⟨545455, by decide⟩,⟨545521, by decide⟩,⟨545536, by decide⟩]) unmarked_context_9_1171_545537 node_context_9_1171_545537
  intro a
  fin_cases a
  · exact context_10_4684_545362
  · exact context_10_4685_545455
  · exact context_10_4686_545521
  · exact context_10_4687_545536

theorem unmarked_context_8_292_545538 : frontier 13 ⟨545538, by decide⟩
    (prefixCache 8 292) (prefixPartial 8 292) = false := by
  decide +kernel

theorem node_context_8_292_545538 : EJMOriginalGlobalDAGData.nodes 13 ⟨545538, by decide⟩ =
    .split (coordinate 8) (![⟨541165, by decide⟩,⟨543991, by decide⟩,⟨545251, by decide⟩,⟨545537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_292_545538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 292 ⟨545538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 292
    ⟨545538, by decide⟩ (by decide) (![⟨541165, by decide⟩,⟨543991, by decide⟩,⟨545251, by decide⟩,⟨545537, by decide⟩]) unmarked_context_8_292_545538 node_context_8_292_545538
  intro a
  fin_cases a
  · exact context_9_1168_541165
  · exact context_9_1169_543991
  · exact context_9_1170_545251
  · exact context_9_1171_545537

theorem selected_cut_21326 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18752) = some ⟨11, 1, 0, 434745, 18752, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18752_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18752 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18752 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18752, 1, 262144⟩
    (by decide) selected_cut_21326

theorem selected_cut_21327 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75012) = some ⟨12, 1, 0, 448748, 75012, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75012_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75012 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75012 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75012, 1, 65536⟩
    (by decide) selected_cut_21327

theorem selected_cut_21328 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 75013) = some ⟨12, 1, 0, 34034, 75013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75013_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75013 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 75013 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 75013, 1, 65536⟩
    (by decide) selected_cut_21328

theorem selected_cut_21329 : selected 8 ⟨545626, by decide⟩
    (prefixPartial 13 300056) = some ⟨13, 2, 0, 545626, 300056, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_300056_545626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300056 ⟨545626, by decide⟩ :=
  accepted_of_selected 13 300056 ⟨545626, by decide⟩ ⟨13, 2, 0, 545626, 300056, 3233, 16384⟩
    (by decide) selected_cut_21329

theorem selected_cut_21330 : selected 8 ⟨545664, by decide⟩
    (prefixPartial 13 300057) = some ⟨13, 2, 0, 545664, 300057, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_300057_545664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300057 ⟨545664, by decide⟩ :=
  accepted_of_selected 13 300057 ⟨545664, by decide⟩ ⟨13, 2, 0, 545664, 300057, 2353, 16384⟩
    (by decide) selected_cut_21330

theorem selected_cut_21331 : selected 8 ⟨545696, by decide⟩
    (prefixPartial 13 300058) = some ⟨13, 2, 0, 545696, 300058, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_300058_545696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300058 ⟨545696, by decide⟩ :=
  accepted_of_selected 13 300058 ⟨545696, by decide⟩ ⟨13, 2, 0, 545696, 300058, 1973, 16384⟩
    (by decide) selected_cut_21331

theorem selected_cut_21332 : selected 8 ⟨545739, by decide⟩
    (prefixPartial 13 300059) = some ⟨13, 2, 0, 545739, 300059, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_300059_545739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300059 ⟨545739, by decide⟩ :=
  accepted_of_selected 13 300059 ⟨545739, by decide⟩ ⟨13, 2, 0, 545739, 300059, 1189, 16384⟩
    (by decide) selected_cut_21332

theorem unmarked_context_12_75014_545740 : frontier 9 ⟨545740, by decide⟩
    (prefixCache 12 75014) (prefixPartial 12 75014) = false := by
  decide +kernel

theorem node_context_12_75014_545740 : EJMOriginalGlobalDAGData.nodes 9 ⟨545740, by decide⟩ =
    .split (coordinate 12) (![⟨545626, by decide⟩,⟨545664, by decide⟩,⟨545696, by decide⟩,⟨545739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75014_545740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75014 ⟨545740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75014
    ⟨545740, by decide⟩ (by decide) (![⟨545626, by decide⟩,⟨545664, by decide⟩,⟨545696, by decide⟩,⟨545739, by decide⟩]) unmarked_context_12_75014_545740 node_context_12_75014_545740
  intro a
  fin_cases a
  · exact context_13_300056_545626
  · exact context_13_300057_545664
  · exact context_13_300058_545696
  · exact context_13_300059_545739

theorem selected_cut_21333 : selected 8 ⟨545815, by decide⟩
    (prefixPartial 13 300060) = some ⟨13, 2, 0, 545815, 300060, 3409, 16384⟩ := by
  decide +kernel

theorem context_13_300060_545815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300060 ⟨545815, by decide⟩ :=
  accepted_of_selected 13 300060 ⟨545815, by decide⟩ ⟨13, 2, 0, 545815, 300060, 3409, 16384⟩
    (by decide) selected_cut_21333

theorem selected_cut_21334 : selected 8 ⟨545856, by decide⟩
    (prefixPartial 13 300061) = some ⟨13, 2, 0, 545856, 300061, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_300061_545856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300061 ⟨545856, by decide⟩ :=
  accepted_of_selected 13 300061 ⟨545856, by decide⟩ ⟨13, 2, 0, 545856, 300061, 2601, 16384⟩
    (by decide) selected_cut_21334

theorem selected_cut_21335 : selected 8 ⟨545922, by decide⟩
    (prefixPartial 13 300062) = some ⟨13, 2, 0, 545922, 300062, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_300062_545922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300062 ⟨545922, by decide⟩ :=
  accepted_of_selected 13 300062 ⟨545922, by decide⟩ ⟨13, 2, 0, 545922, 300062, 2457, 16384⟩
    (by decide) selected_cut_21335

theorem selected_cut_21336 : selected 8 ⟨545941, by decide⟩
    (prefixPartial 13 300063) = some ⟨13, 2, 0, 545941, 300063, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_300063_545941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300063 ⟨545941, by decide⟩ :=
  accepted_of_selected 13 300063 ⟨545941, by decide⟩ ⟨13, 2, 0, 545941, 300063, 1113, 16384⟩
    (by decide) selected_cut_21336

theorem unmarked_context_12_75015_545942 : frontier 9 ⟨545942, by decide⟩
    (prefixCache 12 75015) (prefixPartial 12 75015) = false := by
  decide +kernel

theorem node_context_12_75015_545942 : EJMOriginalGlobalDAGData.nodes 9 ⟨545942, by decide⟩ =
    .split (coordinate 12) (![⟨545815, by decide⟩,⟨545856, by decide⟩,⟨545922, by decide⟩,⟨545941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75015_545942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75015 ⟨545942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75015
    ⟨545942, by decide⟩ (by decide) (![⟨545815, by decide⟩,⟨545856, by decide⟩,⟨545922, by decide⟩,⟨545941, by decide⟩]) unmarked_context_12_75015_545942 node_context_12_75015_545942
  intro a
  fin_cases a
  · exact context_13_300060_545815
  · exact context_13_300061_545856
  · exact context_13_300062_545922
  · exact context_13_300063_545941

theorem unmarked_context_11_18753_545943 : frontier 10 ⟨545943, by decide⟩
    (prefixCache 11 18753) (prefixPartial 11 18753) = false := by
  decide +kernel

theorem node_context_11_18753_545943 : EJMOriginalGlobalDAGData.nodes 10 ⟨545943, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨545740, by decide⟩,⟨545942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18753_545943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18753 ⟨545943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18753
    ⟨545943, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨545740, by decide⟩,⟨545942, by decide⟩]) unmarked_context_11_18753_545943 node_context_11_18753_545943
  intro a
  fin_cases a
  · exact context_12_75012_448748
  · exact context_12_75013_34034
  · exact context_12_75014_545740
  · exact context_12_75015_545942

theorem selected_cut_21337 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75016) = some ⟨12, 1, 0, 448748, 75016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75016_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75016 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75016 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75016, 1, 65536⟩
    (by decide) selected_cut_21337

theorem selected_cut_21338 : selected 8 ⟨546020, by decide⟩
    (prefixPartial 13 300068) = some ⟨13, 2, 0, 546020, 300068, 3249, 16384⟩ := by
  decide +kernel

theorem context_13_300068_546020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300068 ⟨546020, by decide⟩ :=
  accepted_of_selected 13 300068 ⟨546020, by decide⟩ ⟨13, 2, 0, 546020, 300068, 3249, 16384⟩
    (by decide) selected_cut_21338

theorem selected_cut_21339 : selected 8 ⟨546071, by decide⟩
    (prefixPartial 13 300069) = some ⟨13, 2, 0, 546071, 300069, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_300069_546071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300069 ⟨546071, by decide⟩ :=
  accepted_of_selected 13 300069 ⟨546071, by decide⟩ ⟨13, 2, 0, 546071, 300069, 2613, 16384⟩
    (by decide) selected_cut_21339

theorem selected_cut_21340 : selected 8 ⟨546114, by decide⟩
    (prefixPartial 13 300070) = some ⟨13, 2, 0, 546114, 300070, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_300070_546114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300070 ⟨546114, by decide⟩ :=
  accepted_of_selected 13 300070 ⟨546114, by decide⟩ ⟨13, 2, 0, 546114, 300070, 2193, 16384⟩
    (by decide) selected_cut_21340

theorem selected_cut_21341 : selected 8 ⟨546140, by decide⟩
    (prefixPartial 13 300071) = some ⟨13, 2, 0, 546140, 300071, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_300071_546140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300071 ⟨546140, by decide⟩ :=
  accepted_of_selected 13 300071 ⟨546140, by decide⟩ ⟨13, 2, 0, 546140, 300071, 1145, 16384⟩
    (by decide) selected_cut_21341

theorem unmarked_context_12_75017_546141 : frontier 9 ⟨546141, by decide⟩
    (prefixCache 12 75017) (prefixPartial 12 75017) = false := by
  decide +kernel

theorem node_context_12_75017_546141 : EJMOriginalGlobalDAGData.nodes 9 ⟨546141, by decide⟩ =
    .split (coordinate 12) (![⟨546020, by decide⟩,⟨546071, by decide⟩,⟨546114, by decide⟩,⟨546140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75017_546141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75017 ⟨546141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75017
    ⟨546141, by decide⟩ (by decide) (![⟨546020, by decide⟩,⟨546071, by decide⟩,⟨546114, by decide⟩,⟨546140, by decide⟩]) unmarked_context_12_75017_546141 node_context_12_75017_546141
  intro a
  fin_cases a
  · exact context_13_300068_546020
  · exact context_13_300069_546071
  · exact context_13_300070_546114
  · exact context_13_300071_546140

theorem selected_cut_21342 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 75018) = some ⟨12, 1, 0, 524302, 75018, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75018_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75018 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 75018 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 75018, 1, 65536⟩
    (by decide) selected_cut_21342

theorem selected_cut_21343 : selected 7 ⟨546153, by decide⟩
    (prefixPartial 14 1200304) = some ⟨14, 2, 0, 546153, 1200304, 377, 4096⟩ := by
  decide +kernel

theorem context_14_1200304_546153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1200304 ⟨546153, by decide⟩ :=
  accepted_of_selected 14 1200304 ⟨546153, by decide⟩ ⟨14, 2, 0, 546153, 1200304, 377, 4096⟩
    (by decide) selected_cut_21343

theorem selected_cut_21344 : selected 7 ⟨546187, by decide⟩
    (prefixPartial 14 1200305) = some ⟨14, 2, 0, 546187, 1200305, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_1200305_546187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1200305 ⟨546187, by decide⟩ :=
  accepted_of_selected 14 1200305 ⟨546187, by decide⟩ ⟨14, 2, 0, 546187, 1200305, 1333, 4096⟩
    (by decide) selected_cut_21344

theorem selected_cut_21345 : selected 7 ⟨546215, by decide⟩
    (prefixPartial 14 1200306) = some ⟨14, 2, 0, 546215, 1200306, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_1200306_546215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1200306 ⟨546215, by decide⟩ :=
  accepted_of_selected 14 1200306 ⟨546215, by decide⟩ ⟨14, 2, 0, 546215, 1200306, 1221, 4096⟩
    (by decide) selected_cut_21345

theorem selected_cut_21346 : selected 7 ⟨546245, by decide⟩
    (prefixPartial 14 1200307) = some ⟨14, 2, 0, 546245, 1200307, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_1200307_546245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1200307 ⟨546245, by decide⟩ :=
  accepted_of_selected 14 1200307 ⟨546245, by decide⟩ ⟨14, 2, 0, 546245, 1200307, 1301, 4096⟩
    (by decide) selected_cut_21346

theorem unmarked_context_13_300076_546246 : frontier 8 ⟨546246, by decide⟩
    (prefixCache 13 300076) (prefixPartial 13 300076) = false := by
  decide +kernel

theorem node_context_13_300076_546246 : EJMOriginalGlobalDAGData.nodes 8 ⟨546246, by decide⟩ =
    .split (coordinate 13) (![⟨546153, by decide⟩,⟨546187, by decide⟩,⟨546215, by decide⟩,⟨546245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_300076_546246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300076 ⟨546246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 300076
    ⟨546246, by decide⟩ (by decide) (![⟨546153, by decide⟩,⟨546187, by decide⟩,⟨546215, by decide⟩,⟨546245, by decide⟩]) unmarked_context_13_300076_546246 node_context_13_300076_546246
  intro a
  fin_cases a
  · exact context_14_1200304_546153
  · exact context_14_1200305_546187
  · exact context_14_1200306_546215
  · exact context_14_1200307_546245

theorem selected_cut_21347 : selected 8 ⟨546300, by decide⟩
    (prefixPartial 13 300077) = some ⟨13, 2, 0, 546300, 300077, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_300077_546300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300077 ⟨546300, by decide⟩ :=
  accepted_of_selected 13 300077 ⟨546300, by decide⟩ ⟨13, 2, 0, 546300, 300077, 3137, 16384⟩
    (by decide) selected_cut_21347

theorem selected_cut_21348 : selected 8 ⟨546364, by decide⟩
    (prefixPartial 13 300078) = some ⟨13, 2, 0, 546364, 300078, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_300078_546364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300078 ⟨546364, by decide⟩ :=
  accepted_of_selected 13 300078 ⟨546364, by decide⟩ ⟨13, 2, 0, 546364, 300078, 2757, 16384⟩
    (by decide) selected_cut_21348

theorem selected_cut_21349 : selected 8 ⟨546404, by decide⟩
    (prefixPartial 13 300079) = some ⟨13, 2, 0, 546404, 300079, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_300079_546404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300079 ⟨546404, by decide⟩ :=
  accepted_of_selected 13 300079 ⟨546404, by decide⟩ ⟨13, 2, 0, 546404, 300079, 1325, 16384⟩
    (by decide) selected_cut_21349

theorem unmarked_context_12_75019_546405 : frontier 9 ⟨546405, by decide⟩
    (prefixCache 12 75019) (prefixPartial 12 75019) = false := by
  decide +kernel

theorem node_context_12_75019_546405 : EJMOriginalGlobalDAGData.nodes 9 ⟨546405, by decide⟩ =
    .split (coordinate 12) (![⟨546246, by decide⟩,⟨546300, by decide⟩,⟨546364, by decide⟩,⟨546404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75019_546405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75019 ⟨546405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75019
    ⟨546405, by decide⟩ (by decide) (![⟨546246, by decide⟩,⟨546300, by decide⟩,⟨546364, by decide⟩,⟨546404, by decide⟩]) unmarked_context_12_75019_546405 node_context_12_75019_546405
  intro a
  fin_cases a
  · exact context_13_300076_546246
  · exact context_13_300077_546300
  · exact context_13_300078_546364
  · exact context_13_300079_546404

theorem unmarked_context_11_18754_546406 : frontier 10 ⟨546406, by decide⟩
    (prefixCache 11 18754) (prefixPartial 11 18754) = false := by
  decide +kernel

theorem node_context_11_18754_546406 : EJMOriginalGlobalDAGData.nodes 10 ⟨546406, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨546141, by decide⟩,⟨524302, by decide⟩,⟨546405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18754_546406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18754 ⟨546406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18754
    ⟨546406, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨546141, by decide⟩,⟨524302, by decide⟩,⟨546405, by decide⟩]) unmarked_context_11_18754_546406 node_context_11_18754_546406
  intro a
  fin_cases a
  · exact context_12_75016_448748
  · exact context_12_75017_546141
  · exact context_12_75018_524302
  · exact context_12_75019_546405

theorem selected_cut_21350 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75020) = some ⟨12, 1, 0, 448748, 75020, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75020_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75020 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75020 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75020, 1, 65536⟩
    (by decide) selected_cut_21350

theorem selected_cut_21351 : selected 8 ⟨546442, by decide⟩
    (prefixPartial 13 300084) = some ⟨13, 2, 0, 546442, 300084, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_300084_546442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300084 ⟨546442, by decide⟩ :=
  accepted_of_selected 13 300084 ⟨546442, by decide⟩ ⟨13, 2, 0, 546442, 300084, 1309, 16384⟩
    (by decide) selected_cut_21351

theorem selected_cut_21352 : selected 8 ⟨546472, by decide⟩
    (prefixPartial 13 300085) = some ⟨13, 2, 0, 546472, 300085, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_300085_546472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300085 ⟨546472, by decide⟩ :=
  accepted_of_selected 13 300085 ⟨546472, by decide⟩ ⟨13, 2, 0, 546472, 300085, 1361, 16384⟩
    (by decide) selected_cut_21352

theorem selected_cut_21353 : selected 8 ⟨546510, by decide⟩
    (prefixPartial 13 300086) = some ⟨13, 2, 0, 546510, 300086, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_300086_546510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300086 ⟨546510, by decide⟩ :=
  accepted_of_selected 13 300086 ⟨546510, by decide⟩ ⟨13, 2, 0, 546510, 300086, 1645, 16384⟩
    (by decide) selected_cut_21353

theorem selected_cut_21354 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 300087) = some ⟨13, 1, 0, 265883, 300087, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300087_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300087 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 300087 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 300087, 1, 16384⟩
    (by decide) selected_cut_21354

theorem unmarked_context_12_75021_546511 : frontier 9 ⟨546511, by decide⟩
    (prefixCache 12 75021) (prefixPartial 12 75021) = false := by
  decide +kernel

theorem node_context_12_75021_546511 : EJMOriginalGlobalDAGData.nodes 9 ⟨546511, by decide⟩ =
    .split (coordinate 12) (![⟨546442, by decide⟩,⟨546472, by decide⟩,⟨546510, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75021_546511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75021 ⟨546511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75021
    ⟨546511, by decide⟩ (by decide) (![⟨546442, by decide⟩,⟨546472, by decide⟩,⟨546510, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_75021_546511 node_context_12_75021_546511
  intro a
  fin_cases a
  · exact context_13_300084_546442
  · exact context_13_300085_546472
  · exact context_13_300086_546510
  · exact context_13_300087_265883

theorem selected_cut_21355 : selected 8 ⟨546580, by decide⟩
    (prefixPartial 13 300088) = some ⟨13, 2, 0, 546580, 300088, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_300088_546580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300088 ⟨546580, by decide⟩ :=
  accepted_of_selected 13 300088 ⟨546580, by decide⟩ ⟨13, 2, 0, 546580, 300088, 3193, 16384⟩
    (by decide) selected_cut_21355

theorem selected_cut_21356 : selected 8 ⟨546636, by decide⟩
    (prefixPartial 13 300089) = some ⟨13, 2, 0, 546636, 300089, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_300089_546636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300089 ⟨546636, by decide⟩ :=
  accepted_of_selected 13 300089 ⟨546636, by decide⟩ ⟨13, 2, 0, 546636, 300089, 2917, 16384⟩
    (by decide) selected_cut_21356

theorem selected_cut_21357 : selected 8 ⟨546676, by decide⟩
    (prefixPartial 13 300090) = some ⟨13, 2, 0, 546676, 300090, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_300090_546676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300090 ⟨546676, by decide⟩ :=
  accepted_of_selected 13 300090 ⟨546676, by decide⟩ ⟨13, 2, 0, 546676, 300090, 2229, 16384⟩
    (by decide) selected_cut_21357

theorem selected_cut_21358 : selected 8 ⟨546710, by decide⟩
    (prefixPartial 13 300091) = some ⟨13, 2, 0, 546710, 300091, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_300091_546710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300091 ⟨546710, by decide⟩ :=
  accepted_of_selected 13 300091 ⟨546710, by decide⟩ ⟨13, 2, 0, 546710, 300091, 1321, 16384⟩
    (by decide) selected_cut_21358

theorem unmarked_context_12_75022_546711 : frontier 9 ⟨546711, by decide⟩
    (prefixCache 12 75022) (prefixPartial 12 75022) = false := by
  decide +kernel

theorem node_context_12_75022_546711 : EJMOriginalGlobalDAGData.nodes 9 ⟨546711, by decide⟩ =
    .split (coordinate 12) (![⟨546580, by decide⟩,⟨546636, by decide⟩,⟨546676, by decide⟩,⟨546710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75022_546711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75022 ⟨546711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75022
    ⟨546711, by decide⟩ (by decide) (![⟨546580, by decide⟩,⟨546636, by decide⟩,⟨546676, by decide⟩,⟨546710, by decide⟩]) unmarked_context_12_75022_546711 node_context_12_75022_546711
  intro a
  fin_cases a
  · exact context_13_300088_546580
  · exact context_13_300089_546636
  · exact context_13_300090_546676
  · exact context_13_300091_546710

theorem selected_cut_21359 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 75023) = some ⟨12, 1, 0, 518278, 75023, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75023_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75023 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 75023 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 75023, 1, 65536⟩
    (by decide) selected_cut_21359

theorem unmarked_context_11_18755_546712 : frontier 10 ⟨546712, by decide⟩
    (prefixCache 11 18755) (prefixPartial 11 18755) = false := by
  decide +kernel

theorem node_context_11_18755_546712 : EJMOriginalGlobalDAGData.nodes 10 ⟨546712, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨546511, by decide⟩,⟨546711, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18755_546712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18755 ⟨546712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18755
    ⟨546712, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨546511, by decide⟩,⟨546711, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_18755_546712 node_context_11_18755_546712
  intro a
  fin_cases a
  · exact context_12_75020_448748
  · exact context_12_75021_546511
  · exact context_12_75022_546711
  · exact context_12_75023_518278

theorem unmarked_context_10_4688_546713 : frontier 11 ⟨546713, by decide⟩
    (prefixCache 10 4688) (prefixPartial 10 4688) = false := by
  decide +kernel

theorem node_context_10_4688_546713 : EJMOriginalGlobalDAGData.nodes 11 ⟨546713, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨545943, by decide⟩,⟨546406, by decide⟩,⟨546712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4688_546713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4688 ⟨546713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4688
    ⟨546713, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨545943, by decide⟩,⟨546406, by decide⟩,⟨546712, by decide⟩]) unmarked_context_10_4688_546713 node_context_10_4688_546713
  intro a
  fin_cases a
  · exact context_11_18752_434745
  · exact context_11_18753_545943
  · exact context_11_18754_546406
  · exact context_11_18755_546712

theorem selected_cut_21360 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75024) = some ⟨12, 1, 0, 435160, 75024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75024_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75024 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75024 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75024, 1, 65536⟩
    (by decide) selected_cut_21360

theorem selected_cut_21361 : selected 8 ⟨546737, by decide⟩
    (prefixPartial 13 300100) = some ⟨13, 2, 0, 546737, 300100, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_300100_546737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300100 ⟨546737, by decide⟩ :=
  accepted_of_selected 13 300100 ⟨546737, by decide⟩ ⟨13, 2, 0, 546737, 300100, 1349, 16384⟩
    (by decide) selected_cut_21361

theorem selected_cut_21362 : selected 8 ⟨546760, by decide⟩
    (prefixPartial 13 300101) = some ⟨13, 2, 0, 546760, 300101, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_300101_546760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300101 ⟨546760, by decide⟩ :=
  accepted_of_selected 13 300101 ⟨546760, by decide⟩ ⟨13, 2, 0, 546760, 300101, 1729, 16384⟩
    (by decide) selected_cut_21362

theorem selected_cut_21363 : selected 8 ⟨546778, by decide⟩
    (prefixPartial 13 300102) = some ⟨13, 2, 0, 546778, 300102, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_300102_546778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300102 ⟨546778, by decide⟩ :=
  accepted_of_selected 13 300102 ⟨546778, by decide⟩ ⟨13, 2, 0, 546778, 300102, 1249, 16384⟩
    (by decide) selected_cut_21363

theorem selected_cut_21364 : selected 8 ⟨546785, by decide⟩
    (prefixPartial 13 300103) = some ⟨13, 2, 0, 546785, 300103, 681, 16384⟩ := by
  decide +kernel

theorem context_13_300103_546785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300103 ⟨546785, by decide⟩ :=
  accepted_of_selected 13 300103 ⟨546785, by decide⟩ ⟨13, 2, 0, 546785, 300103, 681, 16384⟩
    (by decide) selected_cut_21364

theorem unmarked_context_12_75025_546786 : frontier 9 ⟨546786, by decide⟩
    (prefixCache 12 75025) (prefixPartial 12 75025) = false := by
  decide +kernel

theorem node_context_12_75025_546786 : EJMOriginalGlobalDAGData.nodes 9 ⟨546786, by decide⟩ =
    .split (coordinate 12) (![⟨546737, by decide⟩,⟨546760, by decide⟩,⟨546778, by decide⟩,⟨546785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75025_546786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75025 ⟨546786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75025
    ⟨546786, by decide⟩ (by decide) (![⟨546737, by decide⟩,⟨546760, by decide⟩,⟨546778, by decide⟩,⟨546785, by decide⟩]) unmarked_context_12_75025_546786 node_context_12_75025_546786
  intro a
  fin_cases a
  · exact context_13_300100_546737
  · exact context_13_300101_546760
  · exact context_13_300102_546778
  · exact context_13_300103_546785

theorem selected_cut_21365 : selected 8 ⟨546822, by decide⟩
    (prefixPartial 13 300104) = some ⟨13, 2, 0, 546822, 300104, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_300104_546822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300104 ⟨546822, by decide⟩ :=
  accepted_of_selected 13 300104 ⟨546822, by decide⟩ ⟨13, 2, 0, 546822, 300104, 1785, 16384⟩
    (by decide) selected_cut_21365

theorem selected_cut_21366 : selected 8 ⟨546850, by decide⟩
    (prefixPartial 13 300105) = some ⟨13, 2, 0, 546850, 300105, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_300105_546850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300105 ⟨546850, by decide⟩ :=
  accepted_of_selected 13 300105 ⟨546850, by decide⟩ ⟨13, 2, 0, 546850, 300105, 2285, 16384⟩
    (by decide) selected_cut_21366

theorem selected_cut_21367 : selected 8 ⟨546873, by decide⟩
    (prefixPartial 13 300106) = some ⟨13, 2, 0, 546873, 300106, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_300106_546873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300106 ⟨546873, by decide⟩ :=
  accepted_of_selected 13 300106 ⟨546873, by decide⟩ ⟨13, 2, 0, 546873, 300106, 1565, 16384⟩
    (by decide) selected_cut_21367

theorem selected_cut_21368 : selected 8 ⟨546881, by decide⟩
    (prefixPartial 13 300107) = some ⟨13, 2, 0, 546881, 300107, 849, 16384⟩ := by
  decide +kernel

theorem context_13_300107_546881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300107 ⟨546881, by decide⟩ :=
  accepted_of_selected 13 300107 ⟨546881, by decide⟩ ⟨13, 2, 0, 546881, 300107, 849, 16384⟩
    (by decide) selected_cut_21368

theorem unmarked_context_12_75026_546882 : frontier 9 ⟨546882, by decide⟩
    (prefixCache 12 75026) (prefixPartial 12 75026) = false := by
  decide +kernel

theorem node_context_12_75026_546882 : EJMOriginalGlobalDAGData.nodes 9 ⟨546882, by decide⟩ =
    .split (coordinate 12) (![⟨546822, by decide⟩,⟨546850, by decide⟩,⟨546873, by decide⟩,⟨546881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75026_546882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75026 ⟨546882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75026
    ⟨546882, by decide⟩ (by decide) (![⟨546822, by decide⟩,⟨546850, by decide⟩,⟨546873, by decide⟩,⟨546881, by decide⟩]) unmarked_context_12_75026_546882 node_context_12_75026_546882
  intro a
  fin_cases a
  · exact context_13_300104_546822
  · exact context_13_300105_546850
  · exact context_13_300106_546873
  · exact context_13_300107_546881

theorem selected_cut_21369 : selected 8 ⟨546915, by decide⟩
    (prefixPartial 13 300108) = some ⟨13, 2, 0, 546915, 300108, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_300108_546915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300108 ⟨546915, by decide⟩ :=
  accepted_of_selected 13 300108 ⟨546915, by decide⟩ ⟨13, 2, 0, 546915, 300108, 2017, 16384⟩
    (by decide) selected_cut_21369

theorem selected_cut_21370 : selected 8 ⟨546942, by decide⟩
    (prefixPartial 13 300109) = some ⟨13, 2, 0, 546942, 300109, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_300109_546942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300109 ⟨546942, by decide⟩ :=
  accepted_of_selected 13 300109 ⟨546942, by decide⟩ ⟨13, 2, 0, 546942, 300109, 2501, 16384⟩
    (by decide) selected_cut_21370

theorem selected_cut_21371 : selected 8 ⟨546967, by decide⟩
    (prefixPartial 13 300110) = some ⟨13, 2, 0, 546967, 300110, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_300110_546967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300110 ⟨546967, by decide⟩ :=
  accepted_of_selected 13 300110 ⟨546967, by decide⟩ ⟨13, 2, 0, 546967, 300110, 1809, 16384⟩
    (by decide) selected_cut_21371

theorem selected_cut_21372 : selected 8 ⟨546974, by decide⟩
    (prefixPartial 13 300111) = some ⟨13, 2, 0, 546974, 300111, 917, 16384⟩ := by
  decide +kernel

theorem context_13_300111_546974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300111 ⟨546974, by decide⟩ :=
  accepted_of_selected 13 300111 ⟨546974, by decide⟩ ⟨13, 2, 0, 546974, 300111, 917, 16384⟩
    (by decide) selected_cut_21372

theorem unmarked_context_12_75027_546975 : frontier 9 ⟨546975, by decide⟩
    (prefixCache 12 75027) (prefixPartial 12 75027) = false := by
  decide +kernel

theorem node_context_12_75027_546975 : EJMOriginalGlobalDAGData.nodes 9 ⟨546975, by decide⟩ =
    .split (coordinate 12) (![⟨546915, by decide⟩,⟨546942, by decide⟩,⟨546967, by decide⟩,⟨546974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75027_546975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75027 ⟨546975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75027
    ⟨546975, by decide⟩ (by decide) (![⟨546915, by decide⟩,⟨546942, by decide⟩,⟨546967, by decide⟩,⟨546974, by decide⟩]) unmarked_context_12_75027_546975 node_context_12_75027_546975
  intro a
  fin_cases a
  · exact context_13_300108_546915
  · exact context_13_300109_546942
  · exact context_13_300110_546967
  · exact context_13_300111_546974

theorem unmarked_context_11_18756_546976 : frontier 10 ⟨546976, by decide⟩
    (prefixCache 11 18756) (prefixPartial 11 18756) = false := by
  decide +kernel

theorem node_context_11_18756_546976 : EJMOriginalGlobalDAGData.nodes 10 ⟨546976, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨546786, by decide⟩,⟨546882, by decide⟩,⟨546975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18756_546976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18756 ⟨546976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18756
    ⟨546976, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨546786, by decide⟩,⟨546882, by decide⟩,⟨546975, by decide⟩]) unmarked_context_11_18756_546976 node_context_11_18756_546976
  intro a
  fin_cases a
  · exact context_12_75024_435160
  · exact context_12_75025_546786
  · exact context_12_75026_546882
  · exact context_12_75027_546975

theorem selected_cut_21373 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75028) = some ⟨12, 1, 0, 435160, 75028, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75028_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75028 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75028 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75028, 1, 65536⟩
    (by decide) selected_cut_21373

theorem selected_cut_21374 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 75029) = some ⟨12, 1, 0, 449506, 75029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75029_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75029 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 75029 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 75029, 1, 65536⟩
    (by decide) selected_cut_21374

theorem selected_cut_21375 : selected 8 ⟨547055, by decide⟩
    (prefixPartial 13 300120) = some ⟨13, 2, 0, 547055, 300120, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_300120_547055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300120 ⟨547055, by decide⟩ :=
  accepted_of_selected 13 300120 ⟨547055, by decide⟩ ⟨13, 2, 0, 547055, 300120, 2781, 16384⟩
    (by decide) selected_cut_21375

theorem selected_cut_21376 : selected 8 ⟨547091, by decide⟩
    (prefixPartial 13 300121) = some ⟨13, 2, 0, 547091, 300121, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_300121_547091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300121 ⟨547091, by decide⟩ :=
  accepted_of_selected 13 300121 ⟨547091, by decide⟩ ⟨13, 2, 0, 547091, 300121, 2585, 16384⟩
    (by decide) selected_cut_21376

theorem selected_cut_21377 : selected 8 ⟨547126, by decide⟩
    (prefixPartial 13 300122) = some ⟨13, 2, 0, 547126, 300122, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_300122_547126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300122 ⟨547126, by decide⟩ :=
  accepted_of_selected 13 300122 ⟨547126, by decide⟩ ⟨13, 2, 0, 547126, 300122, 1913, 16384⟩
    (by decide) selected_cut_21377

theorem selected_cut_21378 : selected 8 ⟨547145, by decide⟩
    (prefixPartial 13 300123) = some ⟨13, 2, 0, 547145, 300123, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_300123_547145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300123 ⟨547145, by decide⟩ :=
  accepted_of_selected 13 300123 ⟨547145, by decide⟩ ⟨13, 2, 0, 547145, 300123, 1157, 16384⟩
    (by decide) selected_cut_21378

theorem unmarked_context_12_75030_547146 : frontier 9 ⟨547146, by decide⟩
    (prefixCache 12 75030) (prefixPartial 12 75030) = false := by
  decide +kernel

theorem node_context_12_75030_547146 : EJMOriginalGlobalDAGData.nodes 9 ⟨547146, by decide⟩ =
    .split (coordinate 12) (![⟨547055, by decide⟩,⟨547091, by decide⟩,⟨547126, by decide⟩,⟨547145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75030_547146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75030 ⟨547146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75030
    ⟨547146, by decide⟩ (by decide) (![⟨547055, by decide⟩,⟨547091, by decide⟩,⟨547126, by decide⟩,⟨547145, by decide⟩]) unmarked_context_12_75030_547146 node_context_12_75030_547146
  intro a
  fin_cases a
  · exact context_13_300120_547055
  · exact context_13_300121_547091
  · exact context_13_300122_547126
  · exact context_13_300123_547145

theorem selected_cut_21379 : selected 8 ⟨547215, by decide⟩
    (prefixPartial 13 300124) = some ⟨13, 2, 0, 547215, 300124, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_300124_547215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300124 ⟨547215, by decide⟩ :=
  accepted_of_selected 13 300124 ⟨547215, by decide⟩ ⟨13, 2, 0, 547215, 300124, 2925, 16384⟩
    (by decide) selected_cut_21379

theorem selected_cut_21380 : selected 8 ⟨547257, by decide⟩
    (prefixPartial 13 300125) = some ⟨13, 2, 0, 547257, 300125, 2937, 16384⟩ := by
  decide +kernel

theorem context_13_300125_547257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300125 ⟨547257, by decide⟩ :=
  accepted_of_selected 13 300125 ⟨547257, by decide⟩ ⟨13, 2, 0, 547257, 300125, 2937, 16384⟩
    (by decide) selected_cut_21380

theorem selected_cut_21381 : selected 8 ⟨547308, by decide⟩
    (prefixPartial 13 300126) = some ⟨13, 2, 0, 547308, 300126, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_300126_547308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300126 ⟨547308, by decide⟩ :=
  accepted_of_selected 13 300126 ⟨547308, by decide⟩ ⟨13, 2, 0, 547308, 300126, 2421, 16384⟩
    (by decide) selected_cut_21381

theorem selected_cut_21382 : selected 8 ⟨547321, by decide⟩
    (prefixPartial 13 300127) = some ⟨13, 2, 0, 547321, 300127, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_300127_547321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300127 ⟨547321, by decide⟩ :=
  accepted_of_selected 13 300127 ⟨547321, by decide⟩ ⟨13, 2, 0, 547321, 300127, 1065, 16384⟩
    (by decide) selected_cut_21382

theorem unmarked_context_12_75031_547322 : frontier 9 ⟨547322, by decide⟩
    (prefixCache 12 75031) (prefixPartial 12 75031) = false := by
  decide +kernel

theorem node_context_12_75031_547322 : EJMOriginalGlobalDAGData.nodes 9 ⟨547322, by decide⟩ =
    .split (coordinate 12) (![⟨547215, by decide⟩,⟨547257, by decide⟩,⟨547308, by decide⟩,⟨547321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75031_547322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75031 ⟨547322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75031
    ⟨547322, by decide⟩ (by decide) (![⟨547215, by decide⟩,⟨547257, by decide⟩,⟨547308, by decide⟩,⟨547321, by decide⟩]) unmarked_context_12_75031_547322 node_context_12_75031_547322
  intro a
  fin_cases a
  · exact context_13_300124_547215
  · exact context_13_300125_547257
  · exact context_13_300126_547308
  · exact context_13_300127_547321

theorem unmarked_context_11_18757_547323 : frontier 10 ⟨547323, by decide⟩
    (prefixCache 11 18757) (prefixPartial 11 18757) = false := by
  decide +kernel

theorem node_context_11_18757_547323 : EJMOriginalGlobalDAGData.nodes 10 ⟨547323, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨547146, by decide⟩,⟨547322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18757_547323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18757 ⟨547323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18757
    ⟨547323, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨547146, by decide⟩,⟨547322, by decide⟩]) unmarked_context_11_18757_547323 node_context_11_18757_547323
  intro a
  fin_cases a
  · exact context_12_75028_435160
  · exact context_12_75029_449506
  · exact context_12_75030_547146
  · exact context_12_75031_547322

theorem selected_cut_21383 : selected 8 ⟨547360, by decide⟩
    (prefixPartial 13 300128) = some ⟨13, 2, 0, 547360, 300128, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_300128_547360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300128 ⟨547360, by decide⟩ :=
  accepted_of_selected 13 300128 ⟨547360, by decide⟩ ⟨13, 2, 0, 547360, 300128, 1105, 16384⟩
    (by decide) selected_cut_21383

theorem selected_cut_21384 : selected 8 ⟨547407, by decide⟩
    (prefixPartial 13 300129) = some ⟨13, 2, 0, 547407, 300129, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_300129_547407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300129 ⟨547407, by decide⟩ :=
  accepted_of_selected 13 300129 ⟨547407, by decide⟩ ⟨13, 2, 0, 547407, 300129, 1945, 16384⟩
    (by decide) selected_cut_21384

theorem selected_cut_21385 : selected 8 ⟨547458, by decide⟩
    (prefixPartial 13 300130) = some ⟨13, 2, 0, 547458, 300130, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_300130_547458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300130 ⟨547458, by decide⟩ :=
  accepted_of_selected 13 300130 ⟨547458, by decide⟩ ⟨13, 2, 0, 547458, 300130, 1625, 16384⟩
    (by decide) selected_cut_21385

theorem selected_cut_21386 : selected 8 ⟨547517, by decide⟩
    (prefixPartial 13 300131) = some ⟨13, 2, 0, 547517, 300131, 945, 16384⟩ := by
  decide +kernel

theorem context_13_300131_547517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300131 ⟨547517, by decide⟩ :=
  accepted_of_selected 13 300131 ⟨547517, by decide⟩ ⟨13, 2, 0, 547517, 300131, 945, 16384⟩
    (by decide) selected_cut_21386

theorem unmarked_context_12_75032_547518 : frontier 9 ⟨547518, by decide⟩
    (prefixCache 12 75032) (prefixPartial 12 75032) = false := by
  decide +kernel

theorem node_context_12_75032_547518 : EJMOriginalGlobalDAGData.nodes 9 ⟨547518, by decide⟩ =
    .split (coordinate 12) (![⟨547360, by decide⟩,⟨547407, by decide⟩,⟨547458, by decide⟩,⟨547517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75032_547518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75032 ⟨547518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75032
    ⟨547518, by decide⟩ (by decide) (![⟨547360, by decide⟩,⟨547407, by decide⟩,⟨547458, by decide⟩,⟨547517, by decide⟩]) unmarked_context_12_75032_547518 node_context_12_75032_547518
  intro a
  fin_cases a
  · exact context_13_300128_547360
  · exact context_13_300129_547407
  · exact context_13_300130_547458
  · exact context_13_300131_547517

theorem selected_cut_21387 : selected 8 ⟨547548, by decide⟩
    (prefixPartial 13 300132) = some ⟨13, 2, 0, 547548, 300132, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_300132_547548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300132 ⟨547548, by decide⟩ :=
  accepted_of_selected 13 300132 ⟨547548, by decide⟩ ⟨13, 2, 0, 547548, 300132, 1429, 16384⟩
    (by decide) selected_cut_21387

theorem selected_cut_21388 : selected 8 ⟨547569, by decide⟩
    (prefixPartial 13 300133) = some ⟨13, 2, 0, 547569, 300133, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_300133_547569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300133 ⟨547569, by decide⟩ :=
  accepted_of_selected 13 300133 ⟨547569, by decide⟩ ⟨13, 2, 0, 547569, 300133, 1661, 16384⟩
    (by decide) selected_cut_21388

theorem selected_cut_21389 : selected 8 ⟨547588, by decide⟩
    (prefixPartial 13 300134) = some ⟨13, 2, 0, 547588, 300134, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_300134_547588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300134 ⟨547588, by decide⟩ :=
  accepted_of_selected 13 300134 ⟨547588, by decide⟩ ⟨13, 2, 0, 547588, 300134, 1609, 16384⟩
    (by decide) selected_cut_21389

theorem selected_cut_21390 : selected 8 ⟨547595, by decide⟩
    (prefixPartial 13 300135) = some ⟨13, 2, 0, 547595, 300135, 869, 16384⟩ := by
  decide +kernel

theorem context_13_300135_547595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300135 ⟨547595, by decide⟩ :=
  accepted_of_selected 13 300135 ⟨547595, by decide⟩ ⟨13, 2, 0, 547595, 300135, 869, 16384⟩
    (by decide) selected_cut_21390

theorem unmarked_context_12_75033_547596 : frontier 9 ⟨547596, by decide⟩
    (prefixCache 12 75033) (prefixPartial 12 75033) = false := by
  decide +kernel

theorem node_context_12_75033_547596 : EJMOriginalGlobalDAGData.nodes 9 ⟨547596, by decide⟩ =
    .split (coordinate 12) (![⟨547548, by decide⟩,⟨547569, by decide⟩,⟨547588, by decide⟩,⟨547595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75033_547596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75033 ⟨547596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75033
    ⟨547596, by decide⟩ (by decide) (![⟨547548, by decide⟩,⟨547569, by decide⟩,⟨547588, by decide⟩,⟨547595, by decide⟩]) unmarked_context_12_75033_547596 node_context_12_75033_547596
  intro a
  fin_cases a
  · exact context_13_300132_547548
  · exact context_13_300133_547569
  · exact context_13_300134_547588
  · exact context_13_300135_547595

theorem selected_cut_21391 : selected 8 ⟨547635, by decide⟩
    (prefixPartial 13 300136) = some ⟨13, 2, 0, 547635, 300136, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_300136_547635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300136 ⟨547635, by decide⟩ :=
  accepted_of_selected 13 300136 ⟨547635, by decide⟩ ⟨13, 2, 0, 547635, 300136, 1729, 16384⟩
    (by decide) selected_cut_21391

theorem selected_cut_21392 : selected 8 ⟨547657, by decide⟩
    (prefixPartial 13 300137) = some ⟨13, 2, 0, 547657, 300137, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_300137_547657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300137 ⟨547657, by decide⟩ :=
  accepted_of_selected 13 300137 ⟨547657, by decide⟩ ⟨13, 2, 0, 547657, 300137, 2057, 16384⟩
    (by decide) selected_cut_21392

theorem selected_cut_21393 : selected 8 ⟨547678, by decide⟩
    (prefixPartial 13 300138) = some ⟨13, 2, 0, 547678, 300138, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_300138_547678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300138 ⟨547678, by decide⟩ :=
  accepted_of_selected 13 300138 ⟨547678, by decide⟩ ⟨13, 2, 0, 547678, 300138, 1677, 16384⟩
    (by decide) selected_cut_21393

theorem selected_cut_21394 : selected 8 ⟨547686, by decide⟩
    (prefixPartial 13 300139) = some ⟨13, 2, 0, 547686, 300139, 977, 16384⟩ := by
  decide +kernel

theorem context_13_300139_547686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300139 ⟨547686, by decide⟩ :=
  accepted_of_selected 13 300139 ⟨547686, by decide⟩ ⟨13, 2, 0, 547686, 300139, 977, 16384⟩
    (by decide) selected_cut_21394

theorem unmarked_context_12_75034_547687 : frontier 9 ⟨547687, by decide⟩
    (prefixCache 12 75034) (prefixPartial 12 75034) = false := by
  decide +kernel

theorem node_context_12_75034_547687 : EJMOriginalGlobalDAGData.nodes 9 ⟨547687, by decide⟩ =
    .split (coordinate 12) (![⟨547635, by decide⟩,⟨547657, by decide⟩,⟨547678, by decide⟩,⟨547686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75034_547687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75034 ⟨547687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75034
    ⟨547687, by decide⟩ (by decide) (![⟨547635, by decide⟩,⟨547657, by decide⟩,⟨547678, by decide⟩,⟨547686, by decide⟩]) unmarked_context_12_75034_547687 node_context_12_75034_547687
  intro a
  fin_cases a
  · exact context_13_300136_547635
  · exact context_13_300137_547657
  · exact context_13_300138_547678
  · exact context_13_300139_547686

theorem selected_cut_21395 : selected 8 ⟨547723, by decide⟩
    (prefixPartial 13 300140) = some ⟨13, 2, 0, 547723, 300140, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_300140_547723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300140 ⟨547723, by decide⟩ :=
  accepted_of_selected 13 300140 ⟨547723, by decide⟩ ⟨13, 2, 0, 547723, 300140, 1913, 16384⟩
    (by decide) selected_cut_21395

theorem selected_cut_21396 : selected 8 ⟨547749, by decide⟩
    (prefixPartial 13 300141) = some ⟨13, 2, 0, 547749, 300141, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_300141_547749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300141 ⟨547749, by decide⟩ :=
  accepted_of_selected 13 300141 ⟨547749, by decide⟩ ⟨13, 2, 0, 547749, 300141, 2465, 16384⟩
    (by decide) selected_cut_21396

theorem selected_cut_21397 : selected 8 ⟨547772, by decide⟩
    (prefixPartial 13 300142) = some ⟨13, 2, 0, 547772, 300142, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_300142_547772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300142 ⟨547772, by decide⟩ :=
  accepted_of_selected 13 300142 ⟨547772, by decide⟩ ⟨13, 2, 0, 547772, 300142, 2049, 16384⟩
    (by decide) selected_cut_21397

theorem selected_cut_21398 : selected 8 ⟨547778, by decide⟩
    (prefixPartial 13 300143) = some ⟨13, 2, 0, 547778, 300143, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_300143_547778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300143 ⟨547778, by decide⟩ :=
  accepted_of_selected 13 300143 ⟨547778, by decide⟩ ⟨13, 2, 0, 547778, 300143, 1009, 16384⟩
    (by decide) selected_cut_21398

theorem unmarked_context_12_75035_547779 : frontier 9 ⟨547779, by decide⟩
    (prefixCache 12 75035) (prefixPartial 12 75035) = false := by
  decide +kernel

theorem node_context_12_75035_547779 : EJMOriginalGlobalDAGData.nodes 9 ⟨547779, by decide⟩ =
    .split (coordinate 12) (![⟨547723, by decide⟩,⟨547749, by decide⟩,⟨547772, by decide⟩,⟨547778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75035_547779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75035 ⟨547779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75035
    ⟨547779, by decide⟩ (by decide) (![⟨547723, by decide⟩,⟨547749, by decide⟩,⟨547772, by decide⟩,⟨547778, by decide⟩]) unmarked_context_12_75035_547779 node_context_12_75035_547779
  intro a
  fin_cases a
  · exact context_13_300140_547723
  · exact context_13_300141_547749
  · exact context_13_300142_547772
  · exact context_13_300143_547778

theorem unmarked_context_11_18758_547780 : frontier 10 ⟨547780, by decide⟩
    (prefixCache 11 18758) (prefixPartial 11 18758) = false := by
  decide +kernel

theorem node_context_11_18758_547780 : EJMOriginalGlobalDAGData.nodes 10 ⟨547780, by decide⟩ =
    .split (coordinate 11) (![⟨547518, by decide⟩,⟨547596, by decide⟩,⟨547687, by decide⟩,⟨547779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18758_547780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18758 ⟨547780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18758
    ⟨547780, by decide⟩ (by decide) (![⟨547518, by decide⟩,⟨547596, by decide⟩,⟨547687, by decide⟩,⟨547779, by decide⟩]) unmarked_context_11_18758_547780 node_context_11_18758_547780
  intro a
  fin_cases a
  · exact context_12_75032_547518
  · exact context_12_75033_547596
  · exact context_12_75034_547687
  · exact context_12_75035_547779

theorem selected_cut_21399 : selected 8 ⟨547803, by decide⟩
    (prefixPartial 13 300144) = some ⟨13, 2, 0, 547803, 300144, 733, 16384⟩ := by
  decide +kernel

theorem context_13_300144_547803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300144 ⟨547803, by decide⟩ :=
  accepted_of_selected 13 300144 ⟨547803, by decide⟩ ⟨13, 2, 0, 547803, 300144, 733, 16384⟩
    (by decide) selected_cut_21399

theorem selected_cut_21400 : selected 8 ⟨547848, by decide⟩
    (prefixPartial 13 300145) = some ⟨13, 2, 0, 547848, 300145, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_300145_547848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300145 ⟨547848, by decide⟩ :=
  accepted_of_selected 13 300145 ⟨547848, by decide⟩ ⟨13, 2, 0, 547848, 300145, 1889, 16384⟩
    (by decide) selected_cut_21400

theorem selected_cut_21401 : selected 8 ⟨547927, by decide⟩
    (prefixPartial 13 300146) = some ⟨13, 2, 0, 547927, 300146, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_300146_547927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300146 ⟨547927, by decide⟩ :=
  accepted_of_selected 13 300146 ⟨547927, by decide⟩ ⟨13, 2, 0, 547927, 300146, 2449, 16384⟩
    (by decide) selected_cut_21401

theorem selected_cut_21402 : selected 8 ⟨508985, by decide⟩
    (prefixPartial 13 300147) = some ⟨13, 1, 0, 508985, 300147, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300147_508985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300147 ⟨508985, by decide⟩ :=
  accepted_of_selected 13 300147 ⟨508985, by decide⟩ ⟨13, 1, 0, 508985, 300147, 1, 16384⟩
    (by decide) selected_cut_21402

theorem unmarked_context_12_75036_547928 : frontier 9 ⟨547928, by decide⟩
    (prefixCache 12 75036) (prefixPartial 12 75036) = false := by
  decide +kernel

theorem node_context_12_75036_547928 : EJMOriginalGlobalDAGData.nodes 9 ⟨547928, by decide⟩ =
    .split (coordinate 12) (![⟨547803, by decide⟩,⟨547848, by decide⟩,⟨547927, by decide⟩,⟨508985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75036_547928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75036 ⟨547928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75036
    ⟨547928, by decide⟩ (by decide) (![⟨547803, by decide⟩,⟨547848, by decide⟩,⟨547927, by decide⟩,⟨508985, by decide⟩]) unmarked_context_12_75036_547928 node_context_12_75036_547928
  intro a
  fin_cases a
  · exact context_13_300144_547803
  · exact context_13_300145_547848
  · exact context_13_300146_547927
  · exact context_13_300147_508985

theorem selected_cut_21403 : selected 8 ⟨547951, by decide⟩
    (prefixPartial 13 300148) = some ⟨13, 2, 0, 547951, 300148, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_300148_547951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300148 ⟨547951, by decide⟩ :=
  accepted_of_selected 13 300148 ⟨547951, by decide⟩ ⟨13, 2, 0, 547951, 300148, 1093, 16384⟩
    (by decide) selected_cut_21403

theorem selected_cut_21404 : selected 8 ⟨547978, by decide⟩
    (prefixPartial 13 300149) = some ⟨13, 2, 0, 547978, 300149, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_300149_547978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300149 ⟨547978, by decide⟩ :=
  accepted_of_selected 13 300149 ⟨547978, by decide⟩ ⟨13, 2, 0, 547978, 300149, 1909, 16384⟩
    (by decide) selected_cut_21404

theorem selected_cut_21405 : selected 8 ⟨547993, by decide⟩
    (prefixPartial 13 300150) = some ⟨13, 2, 0, 547993, 300150, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_300150_547993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300150 ⟨547993, by decide⟩ :=
  accepted_of_selected 13 300150 ⟨547993, by decide⟩ ⟨13, 2, 0, 547993, 300150, 1409, 16384⟩
    (by decide) selected_cut_21405

theorem selected_cut_21406 : selected 8 ⟨547997, by decide⟩
    (prefixPartial 13 300151) = some ⟨13, 2, 0, 547997, 300151, 709, 16384⟩ := by
  decide +kernel

theorem context_13_300151_547997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300151 ⟨547997, by decide⟩ :=
  accepted_of_selected 13 300151 ⟨547997, by decide⟩ ⟨13, 2, 0, 547997, 300151, 709, 16384⟩
    (by decide) selected_cut_21406

theorem unmarked_context_12_75037_547998 : frontier 9 ⟨547998, by decide⟩
    (prefixCache 12 75037) (prefixPartial 12 75037) = false := by
  decide +kernel

theorem node_context_12_75037_547998 : EJMOriginalGlobalDAGData.nodes 9 ⟨547998, by decide⟩ =
    .split (coordinate 12) (![⟨547951, by decide⟩,⟨547978, by decide⟩,⟨547993, by decide⟩,⟨547997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75037_547998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75037 ⟨547998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75037
    ⟨547998, by decide⟩ (by decide) (![⟨547951, by decide⟩,⟨547978, by decide⟩,⟨547993, by decide⟩,⟨547997, by decide⟩]) unmarked_context_12_75037_547998 node_context_12_75037_547998
  intro a
  fin_cases a
  · exact context_13_300148_547951
  · exact context_13_300149_547978
  · exact context_13_300150_547993
  · exact context_13_300151_547997

theorem selected_cut_21407 : selected 8 ⟨548025, by decide⟩
    (prefixPartial 13 300152) = some ⟨13, 2, 0, 548025, 300152, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_300152_548025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300152 ⟨548025, by decide⟩ :=
  accepted_of_selected 13 300152 ⟨548025, by decide⟩ ⟨13, 2, 0, 548025, 300152, 1601, 16384⟩
    (by decide) selected_cut_21407

theorem selected_cut_21408 : selected 8 ⟨548050, by decide⟩
    (prefixPartial 13 300153) = some ⟨13, 2, 0, 548050, 300153, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_300153_548050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300153 ⟨548050, by decide⟩ :=
  accepted_of_selected 13 300153 ⟨548050, by decide⟩ ⟨13, 2, 0, 548050, 300153, 2485, 16384⟩
    (by decide) selected_cut_21408

theorem selected_cut_21409 : selected 8 ⟨548073, by decide⟩
    (prefixPartial 13 300154) = some ⟨13, 2, 0, 548073, 300154, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_300154_548073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300154 ⟨548073, by decide⟩ :=
  accepted_of_selected 13 300154 ⟨548073, by decide⟩ ⟨13, 2, 0, 548073, 300154, 1677, 16384⟩
    (by decide) selected_cut_21409

theorem selected_cut_21410 : selected 8 ⟨548079, by decide⟩
    (prefixPartial 13 300155) = some ⟨13, 2, 0, 548079, 300155, 941, 16384⟩ := by
  decide +kernel

theorem context_13_300155_548079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300155 ⟨548079, by decide⟩ :=
  accepted_of_selected 13 300155 ⟨548079, by decide⟩ ⟨13, 2, 0, 548079, 300155, 941, 16384⟩
    (by decide) selected_cut_21410

theorem unmarked_context_12_75038_548080 : frontier 9 ⟨548080, by decide⟩
    (prefixCache 12 75038) (prefixPartial 12 75038) = false := by
  decide +kernel

theorem node_context_12_75038_548080 : EJMOriginalGlobalDAGData.nodes 9 ⟨548080, by decide⟩ =
    .split (coordinate 12) (![⟨548025, by decide⟩,⟨548050, by decide⟩,⟨548073, by decide⟩,⟨548079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75038_548080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75038 ⟨548080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75038
    ⟨548080, by decide⟩ (by decide) (![⟨548025, by decide⟩,⟨548050, by decide⟩,⟨548073, by decide⟩,⟨548079, by decide⟩]) unmarked_context_12_75038_548080 node_context_12_75038_548080
  intro a
  fin_cases a
  · exact context_13_300152_548025
  · exact context_13_300153_548050
  · exact context_13_300154_548073
  · exact context_13_300155_548079

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
