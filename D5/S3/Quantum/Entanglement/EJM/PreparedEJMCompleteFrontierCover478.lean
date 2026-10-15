/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover477
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_92316_1276196 : frontier 10 ⟨1276196, by decide⟩
    (prefixCache 11 92316) (prefixPartial 11 92316) = false := by
  decide +kernel

theorem node_context_11_92316_1276196 : EJMOriginalGlobalDAGData.nodes 10 ⟨1276196, by decide⟩ =
    .split (coordinate 11) (![⟨1276139, by decide⟩,⟨1276160, by decide⟩,⟨1276171, by decide⟩,⟨1276195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92316_1276196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92316 ⟨1276196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92316
    ⟨1276196, by decide⟩ (by decide) (![⟨1276139, by decide⟩,⟨1276160, by decide⟩,⟨1276171, by decide⟩,⟨1276195, by decide⟩]) unmarked_context_11_92316_1276196 node_context_11_92316_1276196
  intro a
  fin_cases a
  · exact context_12_369264_1276139
  · exact context_12_369265_1276160
  · exact context_12_369266_1276171
  · exact context_12_369267_1276195

theorem selected_cut_45892 : selected 10 ⟨1276261, by decide⟩
    (prefixPartial 11 92317) = some ⟨11, 2, 0, 1276261, 92317, 3701, 262144⟩ := by
  decide +kernel

theorem context_11_92317_1276261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92317 ⟨1276261, by decide⟩ :=
  accepted_of_selected 11 92317 ⟨1276261, by decide⟩ ⟨11, 2, 0, 1276261, 92317, 3701, 262144⟩
    (by decide) selected_cut_45892

theorem selected_cut_45893 : selected 10 ⟨1276313, by decide⟩
    (prefixPartial 11 92318) = some ⟨11, 2, 0, 1276313, 92318, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_92318_1276313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92318 ⟨1276313, by decide⟩ :=
  accepted_of_selected 11 92318 ⟨1276313, by decide⟩ ⟨11, 2, 0, 1276313, 92318, 2397, 262144⟩
    (by decide) selected_cut_45893

theorem selected_cut_45894 : selected 10 ⟨1276369, by decide⟩
    (prefixPartial 11 92319) = some ⟨11, 2, 0, 1276369, 92319, 3085, 262144⟩ := by
  decide +kernel

theorem context_11_92319_1276369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92319 ⟨1276369, by decide⟩ :=
  accepted_of_selected 11 92319 ⟨1276369, by decide⟩ ⟨11, 2, 0, 1276369, 92319, 3085, 262144⟩
    (by decide) selected_cut_45894

theorem unmarked_context_10_23079_1276370 : frontier 11 ⟨1276370, by decide⟩
    (prefixCache 10 23079) (prefixPartial 10 23079) = false := by
  decide +kernel

theorem node_context_10_23079_1276370 : EJMOriginalGlobalDAGData.nodes 11 ⟨1276370, by decide⟩ =
    .split (coordinate 10) (![⟨1276196, by decide⟩,⟨1276261, by decide⟩,⟨1276313, by decide⟩,⟨1276369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23079_1276370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23079 ⟨1276370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23079
    ⟨1276370, by decide⟩ (by decide) (![⟨1276196, by decide⟩,⟨1276261, by decide⟩,⟨1276313, by decide⟩,⟨1276369, by decide⟩]) unmarked_context_10_23079_1276370 node_context_10_23079_1276370
  intro a
  fin_cases a
  · exact context_11_92316_1276196
  · exact context_11_92317_1276261
  · exact context_11_92318_1276313
  · exact context_11_92319_1276369

theorem unmarked_context_9_5769_1276371 : frontier 12 ⟨1276371, by decide⟩
    (prefixCache 9 5769) (prefixPartial 9 5769) = false := by
  decide +kernel

theorem node_context_9_5769_1276371 : EJMOriginalGlobalDAGData.nodes 12 ⟨1276371, by decide⟩ =
    .split (coordinate 9) (![⟨1275849, by decide⟩,⟨893098, by decide⟩,⟨1276119, by decide⟩,⟨1276370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5769_1276371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5769 ⟨1276371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5769
    ⟨1276371, by decide⟩ (by decide) (![⟨1275849, by decide⟩,⟨893098, by decide⟩,⟨1276119, by decide⟩,⟨1276370, by decide⟩]) unmarked_context_9_5769_1276371 node_context_9_5769_1276371
  intro a
  fin_cases a
  · exact context_10_23076_1275849
  · exact context_10_23077_893098
  · exact context_10_23078_1276119
  · exact context_10_23079_1276370

theorem selected_cut_45895 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92320) = some ⟨11, 1, 0, 907917, 92320, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92320_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92320 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92320 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92320, 1, 262144⟩
    (by decide) selected_cut_45895

theorem selected_cut_45896 : selected 10 ⟨1276423, by decide⟩
    (prefixPartial 11 92321) = some ⟨11, 2, 0, 1276423, 92321, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_92321_1276423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92321 ⟨1276423, by decide⟩ :=
  accepted_of_selected 11 92321 ⟨1276423, by decide⟩ ⟨11, 2, 0, 1276423, 92321, 2241, 262144⟩
    (by decide) selected_cut_45896

theorem selected_cut_45897 : selected 10 ⟨1276478, by decide⟩
    (prefixPartial 11 92322) = some ⟨11, 2, 0, 1276478, 92322, 2793, 262144⟩ := by
  decide +kernel

theorem context_11_92322_1276478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92322 ⟨1276478, by decide⟩ :=
  accepted_of_selected 11 92322 ⟨1276478, by decide⟩ ⟨11, 2, 0, 1276478, 92322, 2793, 262144⟩
    (by decide) selected_cut_45897

theorem selected_cut_45898 : selected 10 ⟨1276517, by decide⟩
    (prefixPartial 11 92323) = some ⟨11, 2, 0, 1276517, 92323, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_92323_1276517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92323 ⟨1276517, by decide⟩ :=
  accepted_of_selected 11 92323 ⟨1276517, by decide⟩ ⟨11, 2, 0, 1276517, 92323, 1949, 262144⟩
    (by decide) selected_cut_45898

theorem unmarked_context_10_23080_1276518 : frontier 11 ⟨1276518, by decide⟩
    (prefixCache 10 23080) (prefixPartial 10 23080) = false := by
  decide +kernel

theorem node_context_10_23080_1276518 : EJMOriginalGlobalDAGData.nodes 11 ⟨1276518, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1276423, by decide⟩,⟨1276478, by decide⟩,⟨1276517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23080_1276518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23080 ⟨1276518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23080
    ⟨1276518, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1276423, by decide⟩,⟨1276478, by decide⟩,⟨1276517, by decide⟩]) unmarked_context_10_23080_1276518 node_context_10_23080_1276518
  intro a
  fin_cases a
  · exact context_11_92320_907917
  · exact context_11_92321_1276423
  · exact context_11_92322_1276478
  · exact context_11_92323_1276517

theorem selected_cut_45899 : selected 10 ⟨1276550, by decide⟩
    (prefixPartial 11 92324) = some ⟨11, 2, 0, 1276550, 92324, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_92324_1276550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92324 ⟨1276550, by decide⟩ :=
  accepted_of_selected 11 92324 ⟨1276550, by decide⟩ ⟨11, 2, 0, 1276550, 92324, 1757, 262144⟩
    (by decide) selected_cut_45899

theorem selected_cut_45900 : selected 10 ⟨1276601, by decide⟩
    (prefixPartial 11 92325) = some ⟨11, 2, 0, 1276601, 92325, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_92325_1276601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92325 ⟨1276601, by decide⟩ :=
  accepted_of_selected 11 92325 ⟨1276601, by decide⟩ ⟨11, 2, 0, 1276601, 92325, 1281, 262144⟩
    (by decide) selected_cut_45900

theorem selected_cut_45901 : selected 10 ⟨1276641, by decide⟩
    (prefixPartial 11 92326) = some ⟨11, 2, 0, 1276641, 92326, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_92326_1276641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92326 ⟨1276641, by decide⟩ :=
  accepted_of_selected 11 92326 ⟨1276641, by decide⟩ ⟨11, 2, 0, 1276641, 92326, 2425, 262144⟩
    (by decide) selected_cut_45901

theorem selected_cut_45902 : selected 10 ⟨1276672, by decide⟩
    (prefixPartial 11 92327) = some ⟨11, 2, 0, 1276672, 92327, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_92327_1276672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92327 ⟨1276672, by decide⟩ :=
  accepted_of_selected 11 92327 ⟨1276672, by decide⟩ ⟨11, 2, 0, 1276672, 92327, 1673, 262144⟩
    (by decide) selected_cut_45902

theorem unmarked_context_10_23081_1276673 : frontier 11 ⟨1276673, by decide⟩
    (prefixCache 10 23081) (prefixPartial 10 23081) = false := by
  decide +kernel

theorem node_context_10_23081_1276673 : EJMOriginalGlobalDAGData.nodes 11 ⟨1276673, by decide⟩ =
    .split (coordinate 10) (![⟨1276550, by decide⟩,⟨1276601, by decide⟩,⟨1276641, by decide⟩,⟨1276672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23081_1276673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23081 ⟨1276673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23081
    ⟨1276673, by decide⟩ (by decide) (![⟨1276550, by decide⟩,⟨1276601, by decide⟩,⟨1276641, by decide⟩,⟨1276672, by decide⟩]) unmarked_context_10_23081_1276673 node_context_10_23081_1276673
  intro a
  fin_cases a
  · exact context_11_92324_1276550
  · exact context_11_92325_1276601
  · exact context_11_92326_1276641
  · exact context_11_92327_1276672

theorem selected_cut_45903 : selected 11 ⟨1276723, by decide⟩
    (prefixPartial 10 23082) = some ⟨10, 2, 0, 1276723, 23082, 2329, 1048576⟩ := by
  decide +kernel

theorem context_10_23082_1276723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23082 ⟨1276723, by decide⟩ :=
  accepted_of_selected 10 23082 ⟨1276723, by decide⟩ ⟨10, 2, 0, 1276723, 23082, 2329, 1048576⟩
    (by decide) selected_cut_45903

theorem selected_cut_45904 : selected 10 ⟨1276741, by decide⟩
    (prefixPartial 11 92332) = some ⟨11, 2, 0, 1276741, 92332, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_92332_1276741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92332 ⟨1276741, by decide⟩ :=
  accepted_of_selected 11 92332 ⟨1276741, by decide⟩ ⟨11, 2, 0, 1276741, 92332, 1217, 262144⟩
    (by decide) selected_cut_45904

theorem selected_cut_45905 : selected 10 ⟨1276762, by decide⟩
    (prefixPartial 11 92333) = some ⟨11, 2, 0, 1276762, 92333, 1253, 262144⟩ := by
  decide +kernel

theorem context_11_92333_1276762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92333 ⟨1276762, by decide⟩ :=
  accepted_of_selected 11 92333 ⟨1276762, by decide⟩ ⟨11, 2, 0, 1276762, 92333, 1253, 262144⟩
    (by decide) selected_cut_45905

theorem selected_cut_45906 : selected 10 ⟨1276785, by decide⟩
    (prefixPartial 11 92334) = some ⟨11, 2, 0, 1276785, 92334, 1577, 262144⟩ := by
  decide +kernel

theorem context_11_92334_1276785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92334 ⟨1276785, by decide⟩ :=
  accepted_of_selected 11 92334 ⟨1276785, by decide⟩ ⟨11, 2, 0, 1276785, 92334, 1577, 262144⟩
    (by decide) selected_cut_45906

theorem selected_cut_45907 : selected 10 ⟨1276800, by decide⟩
    (prefixPartial 11 92335) = some ⟨11, 2, 0, 1276800, 92335, 993, 262144⟩ := by
  decide +kernel

theorem context_11_92335_1276800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92335 ⟨1276800, by decide⟩ :=
  accepted_of_selected 11 92335 ⟨1276800, by decide⟩ ⟨11, 2, 0, 1276800, 92335, 993, 262144⟩
    (by decide) selected_cut_45907

theorem unmarked_context_10_23083_1276801 : frontier 11 ⟨1276801, by decide⟩
    (prefixCache 10 23083) (prefixPartial 10 23083) = false := by
  decide +kernel

theorem node_context_10_23083_1276801 : EJMOriginalGlobalDAGData.nodes 11 ⟨1276801, by decide⟩ =
    .split (coordinate 10) (![⟨1276741, by decide⟩,⟨1276762, by decide⟩,⟨1276785, by decide⟩,⟨1276800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23083_1276801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23083 ⟨1276801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23083
    ⟨1276801, by decide⟩ (by decide) (![⟨1276741, by decide⟩,⟨1276762, by decide⟩,⟨1276785, by decide⟩,⟨1276800, by decide⟩]) unmarked_context_10_23083_1276801 node_context_10_23083_1276801
  intro a
  fin_cases a
  · exact context_11_92332_1276741
  · exact context_11_92333_1276762
  · exact context_11_92334_1276785
  · exact context_11_92335_1276800

theorem unmarked_context_9_5770_1276802 : frontier 12 ⟨1276802, by decide⟩
    (prefixCache 9 5770) (prefixPartial 9 5770) = false := by
  decide +kernel

theorem node_context_9_5770_1276802 : EJMOriginalGlobalDAGData.nodes 12 ⟨1276802, by decide⟩ =
    .split (coordinate 9) (![⟨1276518, by decide⟩,⟨1276673, by decide⟩,⟨1276723, by decide⟩,⟨1276801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5770_1276802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5770 ⟨1276802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5770
    ⟨1276802, by decide⟩ (by decide) (![⟨1276518, by decide⟩,⟨1276673, by decide⟩,⟨1276723, by decide⟩,⟨1276801, by decide⟩]) unmarked_context_9_5770_1276802 node_context_9_5770_1276802
  intro a
  fin_cases a
  · exact context_10_23080_1276518
  · exact context_10_23081_1276673
  · exact context_10_23082_1276723
  · exact context_10_23083_1276801

theorem selected_cut_45908 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92336) = some ⟨11, 1, 0, 907917, 92336, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92336_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92336 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92336 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92336, 1, 262144⟩
    (by decide) selected_cut_45908

theorem selected_cut_45909 : selected 10 ⟨1276838, by decide⟩
    (prefixPartial 11 92337) = some ⟨11, 2, 0, 1276838, 92337, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_92337_1276838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92337 ⟨1276838, by decide⟩ :=
  accepted_of_selected 11 92337 ⟨1276838, by decide⟩ ⟨11, 2, 0, 1276838, 92337, 2097, 262144⟩
    (by decide) selected_cut_45909

theorem selected_cut_45910 : selected 10 ⟨1276851, by decide⟩
    (prefixPartial 11 92338) = some ⟨11, 2, 0, 1276851, 92338, 797, 262144⟩ := by
  decide +kernel

theorem context_11_92338_1276851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92338 ⟨1276851, by decide⟩ :=
  accepted_of_selected 11 92338 ⟨1276851, by decide⟩ ⟨11, 2, 0, 1276851, 92338, 797, 262144⟩
    (by decide) selected_cut_45910

theorem selected_cut_45911 : selected 10 ⟨1276874, by decide⟩
    (prefixPartial 11 92339) = some ⟨11, 2, 0, 1276874, 92339, 1265, 262144⟩ := by
  decide +kernel

theorem context_11_92339_1276874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92339 ⟨1276874, by decide⟩ :=
  accepted_of_selected 11 92339 ⟨1276874, by decide⟩ ⟨11, 2, 0, 1276874, 92339, 1265, 262144⟩
    (by decide) selected_cut_45911

theorem unmarked_context_10_23084_1276875 : frontier 11 ⟨1276875, by decide⟩
    (prefixCache 10 23084) (prefixPartial 10 23084) = false := by
  decide +kernel

theorem node_context_10_23084_1276875 : EJMOriginalGlobalDAGData.nodes 11 ⟨1276875, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1276838, by decide⟩,⟨1276851, by decide⟩,⟨1276874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23084_1276875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23084 ⟨1276875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23084
    ⟨1276875, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1276838, by decide⟩,⟨1276851, by decide⟩,⟨1276874, by decide⟩]) unmarked_context_10_23084_1276875 node_context_10_23084_1276875
  intro a
  fin_cases a
  · exact context_11_92336_907917
  · exact context_11_92337_1276838
  · exact context_11_92338_1276851
  · exact context_11_92339_1276874

theorem selected_cut_45912 : selected 11 ⟨1276932, by decide⟩
    (prefixPartial 10 23085) = some ⟨10, 2, 0, 1276932, 23085, 3553, 1048576⟩ := by
  decide +kernel

theorem context_10_23085_1276932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23085 ⟨1276932, by decide⟩ :=
  accepted_of_selected 10 23085 ⟨1276932, by decide⟩ ⟨10, 2, 0, 1276932, 23085, 3553, 1048576⟩
    (by decide) selected_cut_45912

theorem selected_cut_45913 : selected 11 ⟨1276969, by decide⟩
    (prefixPartial 10 23086) = some ⟨10, 2, 0, 1276969, 23086, 1705, 1048576⟩ := by
  decide +kernel

theorem context_10_23086_1276969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23086 ⟨1276969, by decide⟩ :=
  accepted_of_selected 10 23086 ⟨1276969, by decide⟩ ⟨10, 2, 0, 1276969, 23086, 1705, 1048576⟩
    (by decide) selected_cut_45913

theorem selected_cut_45914 : selected 11 ⟨1276984, by decide⟩
    (prefixPartial 10 23087) = some ⟨10, 2, 0, 1276984, 23087, 409, 1048576⟩ := by
  decide +kernel

theorem context_10_23087_1276984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23087 ⟨1276984, by decide⟩ :=
  accepted_of_selected 10 23087 ⟨1276984, by decide⟩ ⟨10, 2, 0, 1276984, 23087, 409, 1048576⟩
    (by decide) selected_cut_45914

theorem unmarked_context_9_5771_1276985 : frontier 12 ⟨1276985, by decide⟩
    (prefixCache 9 5771) (prefixPartial 9 5771) = false := by
  decide +kernel

theorem node_context_9_5771_1276985 : EJMOriginalGlobalDAGData.nodes 12 ⟨1276985, by decide⟩ =
    .split (coordinate 9) (![⟨1276875, by decide⟩,⟨1276932, by decide⟩,⟨1276969, by decide⟩,⟨1276984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5771_1276985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5771 ⟨1276985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5771
    ⟨1276985, by decide⟩ (by decide) (![⟨1276875, by decide⟩,⟨1276932, by decide⟩,⟨1276969, by decide⟩,⟨1276984, by decide⟩]) unmarked_context_9_5771_1276985 node_context_9_5771_1276985
  intro a
  fin_cases a
  · exact context_10_23084_1276875
  · exact context_10_23085_1276932
  · exact context_10_23086_1276969
  · exact context_10_23087_1276984

theorem unmarked_context_8_1442_1276986 : frontier 13 ⟨1276986, by decide⟩
    (prefixCache 8 1442) (prefixPartial 8 1442) = false := by
  decide +kernel

theorem node_context_8_1442_1276986 : EJMOriginalGlobalDAGData.nodes 13 ⟨1276986, by decide⟩ =
    .split (coordinate 8) (![⟨1275500, by decide⟩,⟨1276371, by decide⟩,⟨1276802, by decide⟩,⟨1276985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1442_1276986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1442 ⟨1276986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1442
    ⟨1276986, by decide⟩ (by decide) (![⟨1275500, by decide⟩,⟨1276371, by decide⟩,⟨1276802, by decide⟩,⟨1276985, by decide⟩]) unmarked_context_8_1442_1276986 node_context_8_1442_1276986
  intro a
  fin_cases a
  · exact context_9_5768_1275500
  · exact context_9_5769_1276371
  · exact context_9_5770_1276802
  · exact context_9_5771_1276985

theorem selected_cut_45915 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92352) = some ⟨11, 1, 0, 434745, 92352, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92352_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92352 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92352 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92352, 1, 262144⟩
    (by decide) selected_cut_45915

theorem selected_cut_45916 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 92353) = some ⟨11, 1, 0, 167448, 92353, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92353_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92353 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 92353 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 92353, 1, 262144⟩
    (by decide) selected_cut_45916

theorem selected_cut_45917 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369416) = some ⟨12, 1, 0, 448748, 369416, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369416_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369416 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369416 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369416, 1, 65536⟩
    (by decide) selected_cut_45917

theorem selected_cut_45918 : selected 9 ⟨1277092, by decide⟩
    (prefixPartial 12 369417) = some ⟨12, 2, 0, 1277092, 369417, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_369417_1277092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369417 ⟨1277092, by decide⟩ :=
  accepted_of_selected 12 369417 ⟨1277092, by decide⟩ ⟨12, 2, 0, 1277092, 369417, 3577, 65536⟩
    (by decide) selected_cut_45918

theorem selected_cut_45919 : selected 9 ⟨1277152, by decide⟩
    (prefixPartial 12 369418) = some ⟨12, 2, 0, 1277152, 369418, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_369418_1277152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369418 ⟨1277152, by decide⟩ :=
  accepted_of_selected 12 369418 ⟨1277152, by decide⟩ ⟨12, 2, 0, 1277152, 369418, 2781, 65536⟩
    (by decide) selected_cut_45919

theorem selected_cut_45920 : selected 9 ⟨1277235, by decide⟩
    (prefixPartial 12 369419) = some ⟨12, 2, 0, 1277235, 369419, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_369419_1277235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369419 ⟨1277235, by decide⟩ :=
  accepted_of_selected 12 369419 ⟨1277235, by decide⟩ ⟨12, 2, 0, 1277235, 369419, 3401, 65536⟩
    (by decide) selected_cut_45920

theorem unmarked_context_11_92354_1277236 : frontier 10 ⟨1277236, by decide⟩
    (prefixCache 11 92354) (prefixPartial 11 92354) = false := by
  decide +kernel

theorem node_context_11_92354_1277236 : EJMOriginalGlobalDAGData.nodes 10 ⟨1277236, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1277092, by decide⟩,⟨1277152, by decide⟩,⟨1277235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92354_1277236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92354 ⟨1277236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92354
    ⟨1277236, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1277092, by decide⟩,⟨1277152, by decide⟩,⟨1277235, by decide⟩]) unmarked_context_11_92354_1277236 node_context_11_92354_1277236
  intro a
  fin_cases a
  · exact context_12_369416_448748
  · exact context_12_369417_1277092
  · exact context_12_369418_1277152
  · exact context_12_369419_1277235

theorem selected_cut_45921 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369420) = some ⟨12, 1, 0, 448748, 369420, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369420_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369420 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369420 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369420, 1, 65536⟩
    (by decide) selected_cut_45921

theorem selected_cut_45922 : selected 9 ⟨1277290, by decide⟩
    (prefixPartial 12 369421) = some ⟨12, 2, 0, 1277290, 369421, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_369421_1277290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369421 ⟨1277290, by decide⟩ :=
  accepted_of_selected 12 369421 ⟨1277290, by decide⟩ ⟨12, 2, 0, 1277290, 369421, 3113, 65536⟩
    (by decide) selected_cut_45922

theorem selected_cut_45923 : selected 9 ⟨1277346, by decide⟩
    (prefixPartial 12 369422) = some ⟨12, 2, 0, 1277346, 369422, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_369422_1277346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369422 ⟨1277346, by decide⟩ :=
  accepted_of_selected 12 369422 ⟨1277346, by decide⟩ ⟨12, 2, 0, 1277346, 369422, 2825, 65536⟩
    (by decide) selected_cut_45923

theorem selected_cut_45924 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 369423) = some ⟨12, 1, 0, 903806, 369423, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369423_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369423 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 369423 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 369423, 1, 65536⟩
    (by decide) selected_cut_45924

theorem unmarked_context_11_92355_1277347 : frontier 10 ⟨1277347, by decide⟩
    (prefixCache 11 92355) (prefixPartial 11 92355) = false := by
  decide +kernel

theorem node_context_11_92355_1277347 : EJMOriginalGlobalDAGData.nodes 10 ⟨1277347, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1277290, by decide⟩,⟨1277346, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92355_1277347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92355 ⟨1277347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92355
    ⟨1277347, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1277290, by decide⟩,⟨1277346, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92355_1277347 node_context_11_92355_1277347
  intro a
  fin_cases a
  · exact context_12_369420_448748
  · exact context_12_369421_1277290
  · exact context_12_369422_1277346
  · exact context_12_369423_903806

theorem unmarked_context_10_23088_1277348 : frontier 11 ⟨1277348, by decide⟩
    (prefixCache 10 23088) (prefixPartial 10 23088) = false := by
  decide +kernel

theorem node_context_10_23088_1277348 : EJMOriginalGlobalDAGData.nodes 11 ⟨1277348, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1277236, by decide⟩,⟨1277347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23088_1277348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23088 ⟨1277348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23088
    ⟨1277348, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1277236, by decide⟩,⟨1277347, by decide⟩]) unmarked_context_10_23088_1277348 node_context_10_23088_1277348
  intro a
  fin_cases a
  · exact context_11_92352_434745
  · exact context_11_92353_167448
  · exact context_11_92354_1277236
  · exact context_11_92355_1277347

theorem selected_cut_45925 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 369424) = some ⟨12, 1, 0, 1255011, 369424, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369424_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369424 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 369424 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 369424, 1, 65536⟩
    (by decide) selected_cut_45925

theorem selected_cut_45926 : selected 9 ⟨1277409, by decide⟩
    (prefixPartial 12 369425) = some ⟨12, 2, 0, 1277409, 369425, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_369425_1277409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369425 ⟨1277409, by decide⟩ :=
  accepted_of_selected 12 369425 ⟨1277409, by decide⟩ ⟨12, 2, 0, 1277409, 369425, 3361, 65536⟩
    (by decide) selected_cut_45926

theorem selected_cut_45927 : selected 9 ⟨1277463, by decide⟩
    (prefixPartial 12 369426) = some ⟨12, 2, 0, 1277463, 369426, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_369426_1277463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369426 ⟨1277463, by decide⟩ :=
  accepted_of_selected 12 369426 ⟨1277463, by decide⟩ ⟨12, 2, 0, 1277463, 369426, 2901, 65536⟩
    (by decide) selected_cut_45927

theorem selected_cut_45928 : selected 9 ⟨1277517, by decide⟩
    (prefixPartial 12 369427) = some ⟨12, 2, 0, 1277517, 369427, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_369427_1277517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369427 ⟨1277517, by decide⟩ :=
  accepted_of_selected 12 369427 ⟨1277517, by decide⟩ ⟨12, 2, 0, 1277517, 369427, 3293, 65536⟩
    (by decide) selected_cut_45928

theorem unmarked_context_11_92356_1277518 : frontier 10 ⟨1277518, by decide⟩
    (prefixCache 11 92356) (prefixPartial 11 92356) = false := by
  decide +kernel

theorem node_context_11_92356_1277518 : EJMOriginalGlobalDAGData.nodes 10 ⟨1277518, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1277409, by decide⟩,⟨1277463, by decide⟩,⟨1277517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92356_1277518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92356 ⟨1277518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92356
    ⟨1277518, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1277409, by decide⟩,⟨1277463, by decide⟩,⟨1277517, by decide⟩]) unmarked_context_11_92356_1277518 node_context_11_92356_1277518
  intro a
  fin_cases a
  · exact context_12_369424_1255011
  · exact context_12_369425_1277409
  · exact context_12_369426_1277463
  · exact context_12_369427_1277517

theorem selected_cut_45929 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 92357) = some ⟨11, 1, 0, 815620, 92357, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92357_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92357 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 92357 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 92357, 1, 262144⟩
    (by decide) selected_cut_45929

theorem selected_cut_45930 : selected 9 ⟨1277579, by decide⟩
    (prefixPartial 12 369432) = some ⟨12, 2, 0, 1277579, 369432, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_369432_1277579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369432 ⟨1277579, by decide⟩ :=
  accepted_of_selected 12 369432 ⟨1277579, by decide⟩ ⟨12, 2, 0, 1277579, 369432, 3509, 65536⟩
    (by decide) selected_cut_45930

theorem selected_cut_45931 : selected 9 ⟨1277658, by decide⟩
    (prefixPartial 12 369433) = some ⟨12, 2, 0, 1277658, 369433, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_369433_1277658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369433 ⟨1277658, by decide⟩ :=
  accepted_of_selected 12 369433 ⟨1277658, by decide⟩ ⟨12, 2, 0, 1277658, 369433, 3693, 65536⟩
    (by decide) selected_cut_45931

theorem selected_cut_45932 : selected 9 ⟨1277711, by decide⟩
    (prefixPartial 12 369434) = some ⟨12, 2, 0, 1277711, 369434, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_369434_1277711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369434 ⟨1277711, by decide⟩ :=
  accepted_of_selected 12 369434 ⟨1277711, by decide⟩ ⟨12, 2, 0, 1277711, 369434, 3009, 65536⟩
    (by decide) selected_cut_45932

theorem selected_cut_45933 : selected 9 ⟨1277782, by decide⟩
    (prefixPartial 12 369435) = some ⟨12, 2, 0, 1277782, 369435, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_369435_1277782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369435 ⟨1277782, by decide⟩ :=
  accepted_of_selected 12 369435 ⟨1277782, by decide⟩ ⟨12, 2, 0, 1277782, 369435, 3585, 65536⟩
    (by decide) selected_cut_45933

theorem unmarked_context_11_92358_1277783 : frontier 10 ⟨1277783, by decide⟩
    (prefixCache 11 92358) (prefixPartial 11 92358) = false := by
  decide +kernel

theorem node_context_11_92358_1277783 : EJMOriginalGlobalDAGData.nodes 10 ⟨1277783, by decide⟩ =
    .split (coordinate 11) (![⟨1277579, by decide⟩,⟨1277658, by decide⟩,⟨1277711, by decide⟩,⟨1277782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92358_1277783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92358 ⟨1277783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92358
    ⟨1277783, by decide⟩ (by decide) (![⟨1277579, by decide⟩,⟨1277658, by decide⟩,⟨1277711, by decide⟩,⟨1277782, by decide⟩]) unmarked_context_11_92358_1277783 node_context_11_92358_1277783
  intro a
  fin_cases a
  · exact context_12_369432_1277579
  · exact context_12_369433_1277658
  · exact context_12_369434_1277711
  · exact context_12_369435_1277782

theorem selected_cut_45934 : selected 9 ⟨1277840, by decide⟩
    (prefixPartial 12 369436) = some ⟨12, 2, 0, 1277840, 369436, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_369436_1277840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369436 ⟨1277840, by decide⟩ :=
  accepted_of_selected 12 369436 ⟨1277840, by decide⟩ ⟨12, 2, 0, 1277840, 369436, 3357, 65536⟩
    (by decide) selected_cut_45934

theorem selected_cut_45935 : selected 9 ⟨1277896, by decide⟩
    (prefixPartial 12 369437) = some ⟨12, 2, 0, 1277896, 369437, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_369437_1277896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369437 ⟨1277896, by decide⟩ :=
  accepted_of_selected 12 369437 ⟨1277896, by decide⟩ ⟨12, 2, 0, 1277896, 369437, 3361, 65536⟩
    (by decide) selected_cut_45935

theorem selected_cut_45936 : selected 9 ⟨1277954, by decide⟩
    (prefixPartial 12 369438) = some ⟨12, 2, 0, 1277954, 369438, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_369438_1277954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369438 ⟨1277954, by decide⟩ :=
  accepted_of_selected 12 369438 ⟨1277954, by decide⟩ ⟨12, 2, 0, 1277954, 369438, 3177, 65536⟩
    (by decide) selected_cut_45936

theorem selected_cut_45937 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 369439) = some ⟨12, 1, 0, 903806, 369439, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369439_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369439 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 369439 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 369439, 1, 65536⟩
    (by decide) selected_cut_45937

theorem unmarked_context_11_92359_1277955 : frontier 10 ⟨1277955, by decide⟩
    (prefixCache 11 92359) (prefixPartial 11 92359) = false := by
  decide +kernel

theorem node_context_11_92359_1277955 : EJMOriginalGlobalDAGData.nodes 10 ⟨1277955, by decide⟩ =
    .split (coordinate 11) (![⟨1277840, by decide⟩,⟨1277896, by decide⟩,⟨1277954, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92359_1277955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92359 ⟨1277955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92359
    ⟨1277955, by decide⟩ (by decide) (![⟨1277840, by decide⟩,⟨1277896, by decide⟩,⟨1277954, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92359_1277955 node_context_11_92359_1277955
  intro a
  fin_cases a
  · exact context_12_369436_1277840
  · exact context_12_369437_1277896
  · exact context_12_369438_1277954
  · exact context_12_369439_903806

theorem unmarked_context_10_23089_1277956 : frontier 11 ⟨1277956, by decide⟩
    (prefixCache 10 23089) (prefixPartial 10 23089) = false := by
  decide +kernel

theorem node_context_10_23089_1277956 : EJMOriginalGlobalDAGData.nodes 11 ⟨1277956, by decide⟩ =
    .split (coordinate 10) (![⟨1277518, by decide⟩,⟨815620, by decide⟩,⟨1277783, by decide⟩,⟨1277955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23089_1277956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23089 ⟨1277956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23089
    ⟨1277956, by decide⟩ (by decide) (![⟨1277518, by decide⟩,⟨815620, by decide⟩,⟨1277783, by decide⟩,⟨1277955, by decide⟩]) unmarked_context_10_23089_1277956 node_context_10_23089_1277956
  intro a
  fin_cases a
  · exact context_11_92356_1277518
  · exact context_11_92357_815620
  · exact context_11_92358_1277783
  · exact context_11_92359_1277955

theorem selected_cut_45938 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 369440) = some ⟨12, 1, 0, 435790, 369440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369440_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369440 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 369440 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 369440, 1, 65536⟩
    (by decide) selected_cut_45938

theorem selected_cut_45939 : selected 9 ⟨1278003, by decide⟩
    (prefixPartial 12 369441) = some ⟨12, 2, 0, 1278003, 369441, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_369441_1278003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369441 ⟨1278003, by decide⟩ :=
  accepted_of_selected 12 369441 ⟨1278003, by decide⟩ ⟨12, 2, 0, 1278003, 369441, 3077, 65536⟩
    (by decide) selected_cut_45939

theorem selected_cut_45940 : selected 9 ⟨1278045, by decide⟩
    (prefixPartial 12 369442) = some ⟨12, 2, 0, 1278045, 369442, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_369442_1278045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369442 ⟨1278045, by decide⟩ :=
  accepted_of_selected 12 369442 ⟨1278045, by decide⟩ ⟨12, 2, 0, 1278045, 369442, 2605, 65536⟩
    (by decide) selected_cut_45940

theorem selected_cut_45941 : selected 9 ⟨1278090, by decide⟩
    (prefixPartial 12 369443) = some ⟨12, 2, 0, 1278090, 369443, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_369443_1278090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369443 ⟨1278090, by decide⟩ :=
  accepted_of_selected 12 369443 ⟨1278090, by decide⟩ ⟨12, 2, 0, 1278090, 369443, 2897, 65536⟩
    (by decide) selected_cut_45941

theorem unmarked_context_11_92360_1278091 : frontier 10 ⟨1278091, by decide⟩
    (prefixCache 11 92360) (prefixPartial 11 92360) = false := by
  decide +kernel

theorem node_context_11_92360_1278091 : EJMOriginalGlobalDAGData.nodes 10 ⟨1278091, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1278003, by decide⟩,⟨1278045, by decide⟩,⟨1278090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92360_1278091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92360 ⟨1278091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92360
    ⟨1278091, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1278003, by decide⟩,⟨1278045, by decide⟩,⟨1278090, by decide⟩]) unmarked_context_11_92360_1278091 node_context_11_92360_1278091
  intro a
  fin_cases a
  · exact context_12_369440_435790
  · exact context_12_369441_1278003
  · exact context_12_369442_1278045
  · exact context_12_369443_1278090

theorem selected_cut_45942 : selected 8 ⟨1278137, by decide⟩
    (prefixPartial 13 1477776) = some ⟨13, 2, 0, 1278137, 1477776, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_1477776_1278137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1477776 ⟨1278137, by decide⟩ :=
  accepted_of_selected 13 1477776 ⟨1278137, by decide⟩ ⟨13, 2, 0, 1278137, 1477776, 1625, 16384⟩
    (by decide) selected_cut_45942

theorem selected_cut_45943 : selected 8 ⟨1278168, by decide⟩
    (prefixPartial 13 1477777) = some ⟨13, 2, 0, 1278168, 1477777, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_1477777_1278168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1477777 ⟨1278168, by decide⟩ :=
  accepted_of_selected 13 1477777 ⟨1278168, by decide⟩ ⟨13, 2, 0, 1278168, 1477777, 1373, 16384⟩
    (by decide) selected_cut_45943

theorem selected_cut_45944 : selected 8 ⟨1278183, by decide⟩
    (prefixPartial 13 1477778) = some ⟨13, 2, 0, 1278183, 1477778, 909, 16384⟩ := by
  decide +kernel

theorem context_13_1477778_1278183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1477778 ⟨1278183, by decide⟩ :=
  accepted_of_selected 13 1477778 ⟨1278183, by decide⟩ ⟨13, 2, 0, 1278183, 1477778, 909, 16384⟩
    (by decide) selected_cut_45944

theorem selected_cut_45945 : selected 8 ⟨1278190, by decide⟩
    (prefixPartial 13 1477779) = some ⟨13, 2, 0, 1278190, 1477779, 509, 16384⟩ := by
  decide +kernel

theorem context_13_1477779_1278190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1477779 ⟨1278190, by decide⟩ :=
  accepted_of_selected 13 1477779 ⟨1278190, by decide⟩ ⟨13, 2, 0, 1278190, 1477779, 509, 16384⟩
    (by decide) selected_cut_45945

theorem unmarked_context_12_369444_1278191 : frontier 9 ⟨1278191, by decide⟩
    (prefixCache 12 369444) (prefixPartial 12 369444) = false := by
  decide +kernel

theorem node_context_12_369444_1278191 : EJMOriginalGlobalDAGData.nodes 9 ⟨1278191, by decide⟩ =
    .split (coordinate 12) (![⟨1278137, by decide⟩,⟨1278168, by decide⟩,⟨1278183, by decide⟩,⟨1278190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_369444_1278191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369444 ⟨1278191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 369444
    ⟨1278191, by decide⟩ (by decide) (![⟨1278137, by decide⟩,⟨1278168, by decide⟩,⟨1278183, by decide⟩,⟨1278190, by decide⟩]) unmarked_context_12_369444_1278191 node_context_12_369444_1278191
  intro a
  fin_cases a
  · exact context_13_1477776_1278137
  · exact context_13_1477777_1278168
  · exact context_13_1477778_1278183
  · exact context_13_1477779_1278190

theorem selected_cut_45946 : selected 9 ⟨1278276, by decide⟩
    (prefixPartial 12 369445) = some ⟨12, 2, 0, 1278276, 369445, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_369445_1278276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369445 ⟨1278276, by decide⟩ :=
  accepted_of_selected 12 369445 ⟨1278276, by decide⟩ ⟨12, 2, 0, 1278276, 369445, 4073, 65536⟩
    (by decide) selected_cut_45946

theorem selected_cut_45947 : selected 9 ⟨1278345, by decide⟩
    (prefixPartial 12 369446) = some ⟨12, 2, 0, 1278345, 369446, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_369446_1278345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369446 ⟨1278345, by decide⟩ :=
  accepted_of_selected 12 369446 ⟨1278345, by decide⟩ ⟨12, 2, 0, 1278345, 369446, 3585, 65536⟩
    (by decide) selected_cut_45947

theorem selected_cut_45948 : selected 9 ⟨1278413, by decide⟩
    (prefixPartial 12 369447) = some ⟨12, 2, 0, 1278413, 369447, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_369447_1278413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369447 ⟨1278413, by decide⟩ :=
  accepted_of_selected 12 369447 ⟨1278413, by decide⟩ ⟨12, 2, 0, 1278413, 369447, 3921, 65536⟩
    (by decide) selected_cut_45948

theorem unmarked_context_11_92361_1278414 : frontier 10 ⟨1278414, by decide⟩
    (prefixCache 11 92361) (prefixPartial 11 92361) = false := by
  decide +kernel

theorem node_context_11_92361_1278414 : EJMOriginalGlobalDAGData.nodes 10 ⟨1278414, by decide⟩ =
    .split (coordinate 11) (![⟨1278191, by decide⟩,⟨1278276, by decide⟩,⟨1278345, by decide⟩,⟨1278413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92361_1278414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92361 ⟨1278414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92361
    ⟨1278414, by decide⟩ (by decide) (![⟨1278191, by decide⟩,⟨1278276, by decide⟩,⟨1278345, by decide⟩,⟨1278413, by decide⟩]) unmarked_context_11_92361_1278414 node_context_11_92361_1278414
  intro a
  fin_cases a
  · exact context_12_369444_1278191
  · exact context_12_369445_1278276
  · exact context_12_369446_1278345
  · exact context_12_369447_1278413

theorem selected_cut_45949 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 369448) = some ⟨12, 1, 0, 435790, 369448, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369448_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369448 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 369448 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 369448, 1, 65536⟩
    (by decide) selected_cut_45949

theorem selected_cut_45950 : selected 9 ⟨1278475, by decide⟩
    (prefixPartial 12 369449) = some ⟨12, 2, 0, 1278475, 369449, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_369449_1278475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369449 ⟨1278475, by decide⟩ :=
  accepted_of_selected 12 369449 ⟨1278475, by decide⟩ ⟨12, 2, 0, 1278475, 369449, 3045, 65536⟩
    (by decide) selected_cut_45950

theorem selected_cut_45951 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 369450) = some ⟨12, 1, 0, 224365, 369450, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369450_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369450 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 369450 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 369450, 1, 65536⟩
    (by decide) selected_cut_45951

theorem selected_cut_45952 : selected 9 ⟨1278530, by decide⟩
    (prefixPartial 12 369451) = some ⟨12, 2, 0, 1278530, 369451, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_369451_1278530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369451 ⟨1278530, by decide⟩ :=
  accepted_of_selected 12 369451 ⟨1278530, by decide⟩ ⟨12, 2, 0, 1278530, 369451, 2881, 65536⟩
    (by decide) selected_cut_45952

theorem unmarked_context_11_92362_1278531 : frontier 10 ⟨1278531, by decide⟩
    (prefixCache 11 92362) (prefixPartial 11 92362) = false := by
  decide +kernel

theorem node_context_11_92362_1278531 : EJMOriginalGlobalDAGData.nodes 10 ⟨1278531, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1278475, by decide⟩,⟨224365, by decide⟩,⟨1278530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92362_1278531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92362 ⟨1278531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92362
    ⟨1278531, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1278475, by decide⟩,⟨224365, by decide⟩,⟨1278530, by decide⟩]) unmarked_context_11_92362_1278531 node_context_11_92362_1278531
  intro a
  fin_cases a
  · exact context_12_369448_435790
  · exact context_12_369449_1278475
  · exact context_12_369450_224365
  · exact context_12_369451_1278530

theorem selected_cut_45953 : selected 9 ⟨1278590, by decide⟩
    (prefixPartial 12 369452) = some ⟨12, 2, 0, 1278590, 369452, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_369452_1278590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369452 ⟨1278590, by decide⟩ :=
  accepted_of_selected 12 369452 ⟨1278590, by decide⟩ ⟨12, 2, 0, 1278590, 369452, 3209, 65536⟩
    (by decide) selected_cut_45953

theorem selected_cut_45954 : selected 9 ⟨1278644, by decide⟩
    (prefixPartial 12 369453) = some ⟨12, 2, 0, 1278644, 369453, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_369453_1278644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369453 ⟨1278644, by decide⟩ :=
  accepted_of_selected 12 369453 ⟨1278644, by decide⟩ ⟨12, 2, 0, 1278644, 369453, 3081, 65536⟩
    (by decide) selected_cut_45954

theorem selected_cut_45955 : selected 9 ⟨1278690, by decide⟩
    (prefixPartial 12 369454) = some ⟨12, 2, 0, 1278690, 369454, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_369454_1278690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369454 ⟨1278690, by decide⟩ :=
  accepted_of_selected 12 369454 ⟨1278690, by decide⟩ ⟨12, 2, 0, 1278690, 369454, 2929, 65536⟩
    (by decide) selected_cut_45955

theorem selected_cut_45956 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 369455) = some ⟨12, 1, 0, 903806, 369455, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369455_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369455 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 369455 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 369455, 1, 65536⟩
    (by decide) selected_cut_45956

theorem unmarked_context_11_92363_1278691 : frontier 10 ⟨1278691, by decide⟩
    (prefixCache 11 92363) (prefixPartial 11 92363) = false := by
  decide +kernel

theorem node_context_11_92363_1278691 : EJMOriginalGlobalDAGData.nodes 10 ⟨1278691, by decide⟩ =
    .split (coordinate 11) (![⟨1278590, by decide⟩,⟨1278644, by decide⟩,⟨1278690, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92363_1278691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92363 ⟨1278691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92363
    ⟨1278691, by decide⟩ (by decide) (![⟨1278590, by decide⟩,⟨1278644, by decide⟩,⟨1278690, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92363_1278691 node_context_11_92363_1278691
  intro a
  fin_cases a
  · exact context_12_369452_1278590
  · exact context_12_369453_1278644
  · exact context_12_369454_1278690
  · exact context_12_369455_903806

theorem unmarked_context_10_23090_1278692 : frontier 11 ⟨1278692, by decide⟩
    (prefixCache 10 23090) (prefixPartial 10 23090) = false := by
  decide +kernel

theorem node_context_10_23090_1278692 : EJMOriginalGlobalDAGData.nodes 11 ⟨1278692, by decide⟩ =
    .split (coordinate 10) (![⟨1278091, by decide⟩,⟨1278414, by decide⟩,⟨1278531, by decide⟩,⟨1278691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23090_1278692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23090 ⟨1278692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23090
    ⟨1278692, by decide⟩ (by decide) (![⟨1278091, by decide⟩,⟨1278414, by decide⟩,⟨1278531, by decide⟩,⟨1278691, by decide⟩]) unmarked_context_10_23090_1278692 node_context_10_23090_1278692
  intro a
  fin_cases a
  · exact context_11_92360_1278091
  · exact context_11_92361_1278414
  · exact context_11_92362_1278531
  · exact context_11_92363_1278691

theorem selected_cut_45957 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 369456) = some ⟨12, 1, 0, 792260, 369456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369456_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369456 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 369456 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 369456, 1, 65536⟩
    (by decide) selected_cut_45957

theorem selected_cut_45958 : selected 9 ⟨1278738, by decide⟩
    (prefixPartial 12 369457) = some ⟨12, 2, 0, 1278738, 369457, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_369457_1278738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369457 ⟨1278738, by decide⟩ :=
  accepted_of_selected 12 369457 ⟨1278738, by decide⟩ ⟨12, 2, 0, 1278738, 369457, 2477, 65536⟩
    (by decide) selected_cut_45958

theorem selected_cut_45959 : selected 9 ⟨1278775, by decide⟩
    (prefixPartial 12 369458) = some ⟨12, 2, 0, 1278775, 369458, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_369458_1278775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369458 ⟨1278775, by decide⟩ :=
  accepted_of_selected 12 369458 ⟨1278775, by decide⟩ ⟨12, 2, 0, 1278775, 369458, 2233, 65536⟩
    (by decide) selected_cut_45959

theorem selected_cut_45960 : selected 9 ⟨1278814, by decide⟩
    (prefixPartial 12 369459) = some ⟨12, 2, 0, 1278814, 369459, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_369459_1278814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369459 ⟨1278814, by decide⟩ :=
  accepted_of_selected 12 369459 ⟨1278814, by decide⟩ ⟨12, 2, 0, 1278814, 369459, 2493, 65536⟩
    (by decide) selected_cut_45960

theorem unmarked_context_11_92364_1278815 : frontier 10 ⟨1278815, by decide⟩
    (prefixCache 11 92364) (prefixPartial 11 92364) = false := by
  decide +kernel

theorem node_context_11_92364_1278815 : EJMOriginalGlobalDAGData.nodes 10 ⟨1278815, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨1278738, by decide⟩,⟨1278775, by decide⟩,⟨1278814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92364_1278815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92364 ⟨1278815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92364
    ⟨1278815, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨1278738, by decide⟩,⟨1278775, by decide⟩,⟨1278814, by decide⟩]) unmarked_context_11_92364_1278815 node_context_11_92364_1278815
  intro a
  fin_cases a
  · exact context_12_369456_792260
  · exact context_12_369457_1278738
  · exact context_12_369458_1278775
  · exact context_12_369459_1278814

theorem selected_cut_45961 : selected 9 ⟨1278868, by decide⟩
    (prefixPartial 12 369460) = some ⟨12, 2, 0, 1278868, 369460, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_369460_1278868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369460 ⟨1278868, by decide⟩ :=
  accepted_of_selected 12 369460 ⟨1278868, by decide⟩ ⟨12, 2, 0, 1278868, 369460, 3077, 65536⟩
    (by decide) selected_cut_45961

theorem selected_cut_45962 : selected 9 ⟨1278925, by decide⟩
    (prefixPartial 12 369461) = some ⟨12, 2, 0, 1278925, 369461, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_369461_1278925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369461 ⟨1278925, by decide⟩ :=
  accepted_of_selected 12 369461 ⟨1278925, by decide⟩ ⟨12, 2, 0, 1278925, 369461, 2945, 65536⟩
    (by decide) selected_cut_45962

theorem selected_cut_45963 : selected 9 ⟨1278973, by decide⟩
    (prefixPartial 12 369462) = some ⟨12, 2, 0, 1278973, 369462, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_369462_1278973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369462 ⟨1278973, by decide⟩ :=
  accepted_of_selected 12 369462 ⟨1278973, by decide⟩ ⟨12, 2, 0, 1278973, 369462, 2717, 65536⟩
    (by decide) selected_cut_45963

theorem selected_cut_45964 : selected 9 ⟨1279032, by decide⟩
    (prefixPartial 12 369463) = some ⟨12, 2, 0, 1279032, 369463, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_369463_1279032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369463 ⟨1279032, by decide⟩ :=
  accepted_of_selected 12 369463 ⟨1279032, by decide⟩ ⟨12, 2, 0, 1279032, 369463, 3041, 65536⟩
    (by decide) selected_cut_45964

theorem unmarked_context_11_92365_1279033 : frontier 10 ⟨1279033, by decide⟩
    (prefixCache 11 92365) (prefixPartial 11 92365) = false := by
  decide +kernel

theorem node_context_11_92365_1279033 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279033, by decide⟩ =
    .split (coordinate 11) (![⟨1278868, by decide⟩,⟨1278925, by decide⟩,⟨1278973, by decide⟩,⟨1279032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92365_1279033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92365 ⟨1279033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92365
    ⟨1279033, by decide⟩ (by decide) (![⟨1278868, by decide⟩,⟨1278925, by decide⟩,⟨1278973, by decide⟩,⟨1279032, by decide⟩]) unmarked_context_11_92365_1279033 node_context_11_92365_1279033
  intro a
  fin_cases a
  · exact context_12_369460_1278868
  · exact context_12_369461_1278925
  · exact context_12_369462_1278973
  · exact context_12_369463_1279032

theorem selected_cut_45965 : selected 9 ⟨1279080, by decide⟩
    (prefixPartial 12 369464) = some ⟨12, 2, 0, 1279080, 369464, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_369464_1279080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369464 ⟨1279080, by decide⟩ :=
  accepted_of_selected 12 369464 ⟨1279080, by decide⟩ ⟨12, 2, 0, 1279080, 369464, 2561, 65536⟩
    (by decide) selected_cut_45965

theorem selected_cut_45966 : selected 9 ⟨1279150, by decide⟩
    (prefixPartial 12 369465) = some ⟨12, 2, 0, 1279150, 369465, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_369465_1279150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369465 ⟨1279150, by decide⟩ :=
  accepted_of_selected 12 369465 ⟨1279150, by decide⟩ ⟨12, 2, 0, 1279150, 369465, 2821, 65536⟩
    (by decide) selected_cut_45966

theorem selected_cut_45967 : selected 9 ⟨1279241, by decide⟩
    (prefixPartial 12 369466) = some ⟨12, 2, 0, 1279241, 369466, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_369466_1279241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369466 ⟨1279241, by decide⟩ :=
  accepted_of_selected 12 369466 ⟨1279241, by decide⟩ ⟨12, 2, 0, 1279241, 369466, 1389, 65536⟩
    (by decide) selected_cut_45967

theorem selected_cut_45968 : selected 9 ⟨1279299, by decide⟩
    (prefixPartial 12 369467) = some ⟨12, 2, 0, 1279299, 369467, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_369467_1279299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369467 ⟨1279299, by decide⟩ :=
  accepted_of_selected 12 369467 ⟨1279299, by decide⟩ ⟨12, 2, 0, 1279299, 369467, 2669, 65536⟩
    (by decide) selected_cut_45968

theorem unmarked_context_11_92366_1279300 : frontier 10 ⟨1279300, by decide⟩
    (prefixCache 11 92366) (prefixPartial 11 92366) = false := by
  decide +kernel

theorem node_context_11_92366_1279300 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279300, by decide⟩ =
    .split (coordinate 11) (![⟨1279080, by decide⟩,⟨1279150, by decide⟩,⟨1279241, by decide⟩,⟨1279299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92366_1279300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92366 ⟨1279300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92366
    ⟨1279300, by decide⟩ (by decide) (![⟨1279080, by decide⟩,⟨1279150, by decide⟩,⟨1279241, by decide⟩,⟨1279299, by decide⟩]) unmarked_context_11_92366_1279300 node_context_11_92366_1279300
  intro a
  fin_cases a
  · exact context_12_369464_1279080
  · exact context_12_369465_1279150
  · exact context_12_369466_1279241
  · exact context_12_369467_1279299

theorem selected_cut_45969 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 369468) = some ⟨12, 1, 0, 399383, 369468, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369468_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369468 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 369468 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 369468, 1, 65536⟩
    (by decide) selected_cut_45969

theorem selected_cut_45970 : selected 9 ⟨1279362, by decide⟩
    (prefixPartial 12 369469) = some ⟨12, 2, 0, 1279362, 369469, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_369469_1279362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369469 ⟨1279362, by decide⟩ :=
  accepted_of_selected 12 369469 ⟨1279362, by decide⟩ ⟨12, 2, 0, 1279362, 369469, 1825, 65536⟩
    (by decide) selected_cut_45970

theorem selected_cut_45971 : selected 9 ⟨1279414, by decide⟩
    (prefixPartial 12 369470) = some ⟨12, 2, 0, 1279414, 369470, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_369470_1279414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369470 ⟨1279414, by decide⟩ :=
  accepted_of_selected 12 369470 ⟨1279414, by decide⟩ ⟨12, 2, 0, 1279414, 369470, 2329, 65536⟩
    (by decide) selected_cut_45971

theorem selected_cut_45972 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 369471) = some ⟨12, 1, 0, 399383, 369471, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369471_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369471 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 369471 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 369471, 1, 65536⟩
    (by decide) selected_cut_45972

theorem unmarked_context_11_92367_1279415 : frontier 10 ⟨1279415, by decide⟩
    (prefixCache 11 92367) (prefixPartial 11 92367) = false := by
  decide +kernel

theorem node_context_11_92367_1279415 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279415, by decide⟩ =
    .split (coordinate 11) (![⟨399383, by decide⟩,⟨1279362, by decide⟩,⟨1279414, by decide⟩,⟨399383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92367_1279415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92367 ⟨1279415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92367
    ⟨1279415, by decide⟩ (by decide) (![⟨399383, by decide⟩,⟨1279362, by decide⟩,⟨1279414, by decide⟩,⟨399383, by decide⟩]) unmarked_context_11_92367_1279415 node_context_11_92367_1279415
  intro a
  fin_cases a
  · exact context_12_369468_399383
  · exact context_12_369469_1279362
  · exact context_12_369470_1279414
  · exact context_12_369471_399383

theorem unmarked_context_10_23091_1279416 : frontier 11 ⟨1279416, by decide⟩
    (prefixCache 10 23091) (prefixPartial 10 23091) = false := by
  decide +kernel

theorem node_context_10_23091_1279416 : EJMOriginalGlobalDAGData.nodes 11 ⟨1279416, by decide⟩ =
    .split (coordinate 10) (![⟨1278815, by decide⟩,⟨1279033, by decide⟩,⟨1279300, by decide⟩,⟨1279415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23091_1279416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23091 ⟨1279416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23091
    ⟨1279416, by decide⟩ (by decide) (![⟨1278815, by decide⟩,⟨1279033, by decide⟩,⟨1279300, by decide⟩,⟨1279415, by decide⟩]) unmarked_context_10_23091_1279416 node_context_10_23091_1279416
  intro a
  fin_cases a
  · exact context_11_92364_1278815
  · exact context_11_92365_1279033
  · exact context_11_92366_1279300
  · exact context_11_92367_1279415

theorem unmarked_context_9_5772_1279417 : frontier 12 ⟨1279417, by decide⟩
    (prefixCache 9 5772) (prefixPartial 9 5772) = false := by
  decide +kernel

theorem node_context_9_5772_1279417 : EJMOriginalGlobalDAGData.nodes 12 ⟨1279417, by decide⟩ =
    .split (coordinate 9) (![⟨1277348, by decide⟩,⟨1277956, by decide⟩,⟨1278692, by decide⟩,⟨1279416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5772_1279417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5772 ⟨1279417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5772
    ⟨1279417, by decide⟩ (by decide) (![⟨1277348, by decide⟩,⟨1277956, by decide⟩,⟨1278692, by decide⟩,⟨1279416, by decide⟩]) unmarked_context_9_5772_1279417 node_context_9_5772_1279417
  intro a
  fin_cases a
  · exact context_10_23088_1277348
  · exact context_10_23089_1277956
  · exact context_10_23090_1278692
  · exact context_10_23091_1279416

theorem selected_cut_45973 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92368) = some ⟨11, 1, 0, 907917, 92368, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92368_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92368 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92368 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92368, 1, 262144⟩
    (by decide) selected_cut_45973

theorem selected_cut_45974 : selected 9 ⟨1279459, by decide⟩
    (prefixPartial 12 369476) = some ⟨12, 2, 0, 1279459, 369476, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_369476_1279459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369476 ⟨1279459, by decide⟩ :=
  accepted_of_selected 12 369476 ⟨1279459, by decide⟩ ⟨12, 2, 0, 1279459, 369476, 2185, 65536⟩
    (by decide) selected_cut_45974

theorem selected_cut_45975 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 369477) = some ⟨12, 1, 0, 1257136, 369477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369477_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369477 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 369477 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 369477, 1, 65536⟩
    (by decide) selected_cut_45975

theorem selected_cut_45976 : selected 9 ⟨1279495, by decide⟩
    (prefixPartial 12 369478) = some ⟨12, 2, 0, 1279495, 369478, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_369478_1279495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369478 ⟨1279495, by decide⟩ :=
  accepted_of_selected 12 369478 ⟨1279495, by decide⟩ ⟨12, 2, 0, 1279495, 369478, 1945, 65536⟩
    (by decide) selected_cut_45976

theorem selected_cut_45977 : selected 9 ⟨1279532, by decide⟩
    (prefixPartial 12 369479) = some ⟨12, 2, 0, 1279532, 369479, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_369479_1279532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369479 ⟨1279532, by decide⟩ :=
  accepted_of_selected 12 369479 ⟨1279532, by decide⟩ ⟨12, 2, 0, 1279532, 369479, 2269, 65536⟩
    (by decide) selected_cut_45977

theorem unmarked_context_11_92369_1279533 : frontier 10 ⟨1279533, by decide⟩
    (prefixCache 11 92369) (prefixPartial 11 92369) = false := by
  decide +kernel

theorem node_context_11_92369_1279533 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279533, by decide⟩ =
    .split (coordinate 11) (![⟨1279459, by decide⟩,⟨1257136, by decide⟩,⟨1279495, by decide⟩,⟨1279532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92369_1279533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92369 ⟨1279533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92369
    ⟨1279533, by decide⟩ (by decide) (![⟨1279459, by decide⟩,⟨1257136, by decide⟩,⟨1279495, by decide⟩,⟨1279532, by decide⟩]) unmarked_context_11_92369_1279533 node_context_11_92369_1279533
  intro a
  fin_cases a
  · exact context_12_369476_1279459
  · exact context_12_369477_1257136
  · exact context_12_369478_1279495
  · exact context_12_369479_1279532

theorem selected_cut_45978 : selected 9 ⟨1279564, by decide⟩
    (prefixPartial 12 369480) = some ⟨12, 2, 0, 1279564, 369480, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_369480_1279564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369480 ⟨1279564, by decide⟩ :=
  accepted_of_selected 12 369480 ⟨1279564, by decide⟩ ⟨12, 2, 0, 1279564, 369480, 1901, 65536⟩
    (by decide) selected_cut_45978

theorem selected_cut_45979 : selected 9 ⟨1279595, by decide⟩
    (prefixPartial 12 369481) = some ⟨12, 2, 0, 1279595, 369481, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_369481_1279595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369481 ⟨1279595, by decide⟩ :=
  accepted_of_selected 12 369481 ⟨1279595, by decide⟩ ⟨12, 2, 0, 1279595, 369481, 1893, 65536⟩
    (by decide) selected_cut_45979

theorem selected_cut_45980 : selected 9 ⟨1279626, by decide⟩
    (prefixPartial 12 369482) = some ⟨12, 2, 0, 1279626, 369482, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_369482_1279626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369482 ⟨1279626, by decide⟩ :=
  accepted_of_selected 12 369482 ⟨1279626, by decide⟩ ⟨12, 2, 0, 1279626, 369482, 1669, 65536⟩
    (by decide) selected_cut_45980

theorem selected_cut_45981 : selected 9 ⟨1279660, by decide⟩
    (prefixPartial 12 369483) = some ⟨12, 2, 0, 1279660, 369483, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_369483_1279660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369483 ⟨1279660, by decide⟩ :=
  accepted_of_selected 12 369483 ⟨1279660, by decide⟩ ⟨12, 2, 0, 1279660, 369483, 1945, 65536⟩
    (by decide) selected_cut_45981

theorem unmarked_context_11_92370_1279661 : frontier 10 ⟨1279661, by decide⟩
    (prefixCache 11 92370) (prefixPartial 11 92370) = false := by
  decide +kernel

theorem node_context_11_92370_1279661 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279661, by decide⟩ =
    .split (coordinate 11) (![⟨1279564, by decide⟩,⟨1279595, by decide⟩,⟨1279626, by decide⟩,⟨1279660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92370_1279661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92370 ⟨1279661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92370
    ⟨1279661, by decide⟩ (by decide) (![⟨1279564, by decide⟩,⟨1279595, by decide⟩,⟨1279626, by decide⟩,⟨1279660, by decide⟩]) unmarked_context_11_92370_1279661 node_context_11_92370_1279661
  intro a
  fin_cases a
  · exact context_12_369480_1279564
  · exact context_12_369481_1279595
  · exact context_12_369482_1279626
  · exact context_12_369483_1279660

theorem selected_cut_45982 : selected 9 ⟨1279687, by decide⟩
    (prefixPartial 12 369484) = some ⟨12, 2, 0, 1279687, 369484, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_369484_1279687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369484 ⟨1279687, by decide⟩ :=
  accepted_of_selected 12 369484 ⟨1279687, by decide⟩ ⟨12, 2, 0, 1279687, 369484, 1745, 65536⟩
    (by decide) selected_cut_45982

theorem selected_cut_45983 : selected 9 ⟨1279714, by decide⟩
    (prefixPartial 12 369485) = some ⟨12, 2, 0, 1279714, 369485, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_369485_1279714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369485 ⟨1279714, by decide⟩ :=
  accepted_of_selected 12 369485 ⟨1279714, by decide⟩ ⟨12, 2, 0, 1279714, 369485, 1649, 65536⟩
    (by decide) selected_cut_45983

theorem selected_cut_45984 : selected 9 ⟨1279743, by decide⟩
    (prefixPartial 12 369486) = some ⟨12, 2, 0, 1279743, 369486, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_369486_1279743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369486 ⟨1279743, by decide⟩ :=
  accepted_of_selected 12 369486 ⟨1279743, by decide⟩ ⟨12, 2, 0, 1279743, 369486, 1645, 65536⟩
    (by decide) selected_cut_45984

theorem selected_cut_45985 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 369487) = some ⟨12, 1, 0, 903806, 369487, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369487_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369487 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 369487 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 369487, 1, 65536⟩
    (by decide) selected_cut_45985

theorem unmarked_context_11_92371_1279744 : frontier 10 ⟨1279744, by decide⟩
    (prefixCache 11 92371) (prefixPartial 11 92371) = false := by
  decide +kernel

theorem node_context_11_92371_1279744 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279744, by decide⟩ =
    .split (coordinate 11) (![⟨1279687, by decide⟩,⟨1279714, by decide⟩,⟨1279743, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92371_1279744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92371 ⟨1279744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92371
    ⟨1279744, by decide⟩ (by decide) (![⟨1279687, by decide⟩,⟨1279714, by decide⟩,⟨1279743, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92371_1279744 node_context_11_92371_1279744
  intro a
  fin_cases a
  · exact context_12_369484_1279687
  · exact context_12_369485_1279714
  · exact context_12_369486_1279743
  · exact context_12_369487_903806

theorem unmarked_context_10_23092_1279745 : frontier 11 ⟨1279745, by decide⟩
    (prefixCache 10 23092) (prefixPartial 10 23092) = false := by
  decide +kernel

theorem node_context_10_23092_1279745 : EJMOriginalGlobalDAGData.nodes 11 ⟨1279745, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1279533, by decide⟩,⟨1279661, by decide⟩,⟨1279744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23092_1279745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23092 ⟨1279745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23092
    ⟨1279745, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1279533, by decide⟩,⟨1279661, by decide⟩,⟨1279744, by decide⟩]) unmarked_context_10_23092_1279745 node_context_10_23092_1279745
  intro a
  fin_cases a
  · exact context_11_92368_907917
  · exact context_11_92369_1279533
  · exact context_11_92370_1279661
  · exact context_11_92371_1279744

theorem selected_cut_45986 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23093) = some ⟨10, 1, 0, 893098, 23093, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23093_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23093 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23093 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23093, 1, 1048576⟩
    (by decide) selected_cut_45986

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
