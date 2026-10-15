/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover106
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10275 : selected 8 ⟨279944, by decide⟩
    (prefixPartial 13 99741) = some ⟨13, 2, 0, 279944, 99741, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_99741_279944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99741 ⟨279944, by decide⟩ :=
  accepted_of_selected 13 99741 ⟨279944, by decide⟩ ⟨13, 2, 0, 279944, 99741, 1185, 16384⟩
    (by decide) selected_cut_10275

theorem selected_cut_10276 : selected 8 ⟨279966, by decide⟩
    (prefixPartial 13 99742) = some ⟨13, 2, 0, 279966, 99742, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_99742_279966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99742 ⟨279966, by decide⟩ :=
  accepted_of_selected 13 99742 ⟨279966, by decide⟩ ⟨13, 2, 0, 279966, 99742, 1901, 16384⟩
    (by decide) selected_cut_10276

theorem selected_cut_10277 : selected 8 ⟨279974, by decide⟩
    (prefixPartial 13 99743) = some ⟨13, 2, 0, 279974, 99743, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_99743_279974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99743 ⟨279974, by decide⟩ :=
  accepted_of_selected 13 99743 ⟨279974, by decide⟩ ⟨13, 2, 0, 279974, 99743, 1037, 16384⟩
    (by decide) selected_cut_10277

theorem unmarked_context_12_24935_279975 : frontier 9 ⟨279975, by decide⟩
    (prefixCache 12 24935) (prefixPartial 12 24935) = false := by
  decide +kernel

theorem node_context_12_24935_279975 : EJMOriginalGlobalDAGData.nodes 9 ⟨279975, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279944, by decide⟩,⟨279966, by decide⟩,⟨279974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24935_279975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24935 ⟨279975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24935
    ⟨279975, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279944, by decide⟩,⟨279966, by decide⟩,⟨279974, by decide⟩]) unmarked_context_12_24935_279975 node_context_12_24935_279975
  intro a
  fin_cases a
  · exact context_13_99740_3444
  · exact context_13_99741_279944
  · exact context_13_99742_279966
  · exact context_13_99743_279974

theorem unmarked_context_11_6233_279976 : frontier 10 ⟨279976, by decide⟩
    (prefixCache 11 6233) (prefixPartial 11 6233) = false := by
  decide +kernel

theorem node_context_11_6233_279976 : EJMOriginalGlobalDAGData.nodes 10 ⟨279976, by decide⟩ =
    .split (coordinate 11) (![⟨279877, by decide⟩,⟨126884, by decide⟩,⟨279930, by decide⟩,⟨279975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6233_279976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6233 ⟨279976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6233
    ⟨279976, by decide⟩ (by decide) (![⟨279877, by decide⟩,⟨126884, by decide⟩,⟨279930, by decide⟩,⟨279975, by decide⟩]) unmarked_context_11_6233_279976 node_context_11_6233_279976
  intro a
  fin_cases a
  · exact context_12_24932_279877
  · exact context_12_24933_126884
  · exact context_12_24934_279930
  · exact context_12_24935_279975

theorem selected_cut_10278 : selected 9 ⟨280011, by decide⟩
    (prefixPartial 12 24936) = some ⟨12, 2, 0, 280011, 24936, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_24936_280011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24936 ⟨280011, by decide⟩ :=
  accepted_of_selected 12 24936 ⟨280011, by decide⟩ ⟨12, 2, 0, 280011, 24936, 3657, 65536⟩
    (by decide) selected_cut_10278

theorem selected_cut_10279 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99748) = some ⟨13, 1, 0, 3444, 99748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99748, 1, 16384⟩
    (by decide) selected_cut_10279

theorem selected_cut_10280 : selected 8 ⟨280023, by decide⟩
    (prefixPartial 13 99749) = some ⟨13, 2, 0, 280023, 99749, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_99749_280023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99749 ⟨280023, by decide⟩ :=
  accepted_of_selected 13 99749 ⟨280023, by decide⟩ ⟨13, 2, 0, 280023, 99749, 1129, 16384⟩
    (by decide) selected_cut_10280

theorem selected_cut_10281 : selected 8 ⟨280064, by decide⟩
    (prefixPartial 13 99750) = some ⟨13, 2, 0, 280064, 99750, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_99750_280064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99750 ⟨280064, by decide⟩ :=
  accepted_of_selected 13 99750 ⟨280064, by decide⟩ ⟨13, 2, 0, 280064, 99750, 2569, 16384⟩
    (by decide) selected_cut_10281

theorem selected_cut_10282 : selected 8 ⟨280084, by decide⟩
    (prefixPartial 13 99751) = some ⟨13, 2, 0, 280084, 99751, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_99751_280084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99751 ⟨280084, by decide⟩ :=
  accepted_of_selected 13 99751 ⟨280084, by decide⟩ ⟨13, 2, 0, 280084, 99751, 1257, 16384⟩
    (by decide) selected_cut_10282

theorem unmarked_context_12_24937_280085 : frontier 9 ⟨280085, by decide⟩
    (prefixCache 12 24937) (prefixPartial 12 24937) = false := by
  decide +kernel

theorem node_context_12_24937_280085 : EJMOriginalGlobalDAGData.nodes 9 ⟨280085, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280023, by decide⟩,⟨280064, by decide⟩,⟨280084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24937_280085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24937 ⟨280085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24937
    ⟨280085, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280023, by decide⟩,⟨280064, by decide⟩,⟨280084, by decide⟩]) unmarked_context_12_24937_280085 node_context_12_24937_280085
  intro a
  fin_cases a
  · exact context_13_99748_3444
  · exact context_13_99749_280023
  · exact context_13_99750_280064
  · exact context_13_99751_280084

theorem selected_cut_10283 : selected 9 ⟨280126, by decide⟩
    (prefixPartial 12 24938) = some ⟨12, 2, 0, 280126, 24938, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_24938_280126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24938 ⟨280126, by decide⟩ :=
  accepted_of_selected 12 24938 ⟨280126, by decide⟩ ⟨12, 2, 0, 280126, 24938, 3885, 65536⟩
    (by decide) selected_cut_10283

theorem selected_cut_10284 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99756) = some ⟨13, 1, 0, 3444, 99756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99756, 1, 16384⟩
    (by decide) selected_cut_10284

theorem selected_cut_10285 : selected 8 ⟨280143, by decide⟩
    (prefixPartial 13 99757) = some ⟨13, 2, 0, 280143, 99757, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_99757_280143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99757 ⟨280143, by decide⟩ :=
  accepted_of_selected 13 99757 ⟨280143, by decide⟩ ⟨13, 2, 0, 280143, 99757, 1005, 16384⟩
    (by decide) selected_cut_10285

theorem selected_cut_10286 : selected 8 ⟨280161, by decide⟩
    (prefixPartial 13 99758) = some ⟨13, 2, 0, 280161, 99758, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_99758_280161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99758 ⟨280161, by decide⟩ :=
  accepted_of_selected 13 99758 ⟨280161, by decide⟩ ⟨13, 2, 0, 280161, 99758, 2141, 16384⟩
    (by decide) selected_cut_10286

theorem selected_cut_10287 : selected 8 ⟨280169, by decide⟩
    (prefixPartial 13 99759) = some ⟨13, 2, 0, 280169, 99759, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_99759_280169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99759 ⟨280169, by decide⟩ :=
  accepted_of_selected 13 99759 ⟨280169, by decide⟩ ⟨13, 2, 0, 280169, 99759, 1041, 16384⟩
    (by decide) selected_cut_10287

theorem unmarked_context_12_24939_280170 : frontier 9 ⟨280170, by decide⟩
    (prefixCache 12 24939) (prefixPartial 12 24939) = false := by
  decide +kernel

theorem node_context_12_24939_280170 : EJMOriginalGlobalDAGData.nodes 9 ⟨280170, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280143, by decide⟩,⟨280161, by decide⟩,⟨280169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24939_280170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24939 ⟨280170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24939
    ⟨280170, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280143, by decide⟩,⟨280161, by decide⟩,⟨280169, by decide⟩]) unmarked_context_12_24939_280170 node_context_12_24939_280170
  intro a
  fin_cases a
  · exact context_13_99756_3444
  · exact context_13_99757_280143
  · exact context_13_99758_280161
  · exact context_13_99759_280169

theorem unmarked_context_11_6234_280171 : frontier 10 ⟨280171, by decide⟩
    (prefixCache 11 6234) (prefixPartial 11 6234) = false := by
  decide +kernel

theorem node_context_11_6234_280171 : EJMOriginalGlobalDAGData.nodes 10 ⟨280171, by decide⟩ =
    .split (coordinate 11) (![⟨280011, by decide⟩,⟨280085, by decide⟩,⟨280126, by decide⟩,⟨280170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6234_280171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6234 ⟨280171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6234
    ⟨280171, by decide⟩ (by decide) (![⟨280011, by decide⟩,⟨280085, by decide⟩,⟨280126, by decide⟩,⟨280170, by decide⟩]) unmarked_context_11_6234_280171 node_context_11_6234_280171
  intro a
  fin_cases a
  · exact context_12_24936_280011
  · exact context_12_24937_280085
  · exact context_12_24938_280126
  · exact context_12_24939_280170

theorem selected_cut_10288 : selected 9 ⟨280209, by decide⟩
    (prefixPartial 12 24940) = some ⟨12, 2, 0, 280209, 24940, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_24940_280209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24940 ⟨280209, by decide⟩ :=
  accepted_of_selected 12 24940 ⟨280209, by decide⟩ ⟨12, 2, 0, 280209, 24940, 3717, 65536⟩
    (by decide) selected_cut_10288

theorem selected_cut_10289 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99764) = some ⟨13, 1, 0, 3444, 99764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99764, 1, 16384⟩
    (by decide) selected_cut_10289

theorem selected_cut_10290 : selected 8 ⟨280222, by decide⟩
    (prefixPartial 13 99765) = some ⟨13, 2, 0, 280222, 99765, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_99765_280222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99765 ⟨280222, by decide⟩ :=
  accepted_of_selected 13 99765 ⟨280222, by decide⟩ ⟨13, 2, 0, 280222, 99765, 1029, 16384⟩
    (by decide) selected_cut_10290

theorem selected_cut_10291 : selected 8 ⟨280254, by decide⟩
    (prefixPartial 13 99766) = some ⟨13, 2, 0, 280254, 99766, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_99766_280254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99766 ⟨280254, by decide⟩ :=
  accepted_of_selected 13 99766 ⟨280254, by decide⟩ ⟨13, 2, 0, 280254, 99766, 2617, 16384⟩
    (by decide) selected_cut_10291

theorem selected_cut_10292 : selected 8 ⟨280285, by decide⟩
    (prefixPartial 13 99767) = some ⟨13, 2, 0, 280285, 99767, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_99767_280285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99767 ⟨280285, by decide⟩ :=
  accepted_of_selected 13 99767 ⟨280285, by decide⟩ ⟨13, 2, 0, 280285, 99767, 1489, 16384⟩
    (by decide) selected_cut_10292

theorem unmarked_context_12_24941_280286 : frontier 9 ⟨280286, by decide⟩
    (prefixCache 12 24941) (prefixPartial 12 24941) = false := by
  decide +kernel

theorem node_context_12_24941_280286 : EJMOriginalGlobalDAGData.nodes 9 ⟨280286, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280222, by decide⟩,⟨280254, by decide⟩,⟨280285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24941_280286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24941 ⟨280286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24941
    ⟨280286, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280222, by decide⟩,⟨280254, by decide⟩,⟨280285, by decide⟩]) unmarked_context_12_24941_280286 node_context_12_24941_280286
  intro a
  fin_cases a
  · exact context_13_99764_3444
  · exact context_13_99765_280222
  · exact context_13_99766_280254
  · exact context_13_99767_280285

theorem selected_cut_10293 : selected 9 ⟨280338, by decide⟩
    (prefixPartial 12 24942) = some ⟨12, 2, 0, 280338, 24942, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_24942_280338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24942 ⟨280338, by decide⟩ :=
  accepted_of_selected 12 24942 ⟨280338, by decide⟩ ⟨12, 2, 0, 280338, 24942, 3997, 65536⟩
    (by decide) selected_cut_10293

theorem selected_cut_10294 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99772) = some ⟨13, 1, 0, 3444, 99772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99772, 1, 16384⟩
    (by decide) selected_cut_10294

theorem selected_cut_10295 : selected 8 ⟨280346, by decide⟩
    (prefixPartial 13 99773) = some ⟨13, 2, 0, 280346, 99773, 821, 16384⟩ := by
  decide +kernel

theorem context_13_99773_280346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99773 ⟨280346, by decide⟩ :=
  accepted_of_selected 13 99773 ⟨280346, by decide⟩ ⟨13, 2, 0, 280346, 99773, 821, 16384⟩
    (by decide) selected_cut_10295

theorem selected_cut_10296 : selected 8 ⟨280370, by decide⟩
    (prefixPartial 13 99774) = some ⟨13, 2, 0, 280370, 99774, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_99774_280370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99774 ⟨280370, by decide⟩ :=
  accepted_of_selected 13 99774 ⟨280370, by decide⟩ ⟨13, 2, 0, 280370, 99774, 2097, 16384⟩
    (by decide) selected_cut_10296

theorem selected_cut_10297 : selected 8 ⟨280380, by decide⟩
    (prefixPartial 13 99775) = some ⟨13, 2, 0, 280380, 99775, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_99775_280380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99775 ⟨280380, by decide⟩ :=
  accepted_of_selected 13 99775 ⟨280380, by decide⟩ ⟨13, 2, 0, 280380, 99775, 1237, 16384⟩
    (by decide) selected_cut_10297

theorem unmarked_context_12_24943_280381 : frontier 9 ⟨280381, by decide⟩
    (prefixCache 12 24943) (prefixPartial 12 24943) = false := by
  decide +kernel

theorem node_context_12_24943_280381 : EJMOriginalGlobalDAGData.nodes 9 ⟨280381, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280346, by decide⟩,⟨280370, by decide⟩,⟨280380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24943_280381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24943 ⟨280381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24943
    ⟨280381, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280346, by decide⟩,⟨280370, by decide⟩,⟨280380, by decide⟩]) unmarked_context_12_24943_280381 node_context_12_24943_280381
  intro a
  fin_cases a
  · exact context_13_99772_3444
  · exact context_13_99773_280346
  · exact context_13_99774_280370
  · exact context_13_99775_280380

theorem unmarked_context_11_6235_280382 : frontier 10 ⟨280382, by decide⟩
    (prefixCache 11 6235) (prefixPartial 11 6235) = false := by
  decide +kernel

theorem node_context_11_6235_280382 : EJMOriginalGlobalDAGData.nodes 10 ⟨280382, by decide⟩ =
    .split (coordinate 11) (![⟨280209, by decide⟩,⟨280286, by decide⟩,⟨280338, by decide⟩,⟨280381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6235_280382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6235 ⟨280382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6235
    ⟨280382, by decide⟩ (by decide) (![⟨280209, by decide⟩,⟨280286, by decide⟩,⟨280338, by decide⟩,⟨280381, by decide⟩]) unmarked_context_11_6235_280382 node_context_11_6235_280382
  intro a
  fin_cases a
  · exact context_12_24940_280209
  · exact context_12_24941_280286
  · exact context_12_24942_280338
  · exact context_12_24943_280381

theorem unmarked_context_10_1558_280383 : frontier 11 ⟨280383, by decide⟩
    (prefixCache 10 1558) (prefixPartial 10 1558) = false := by
  decide +kernel

theorem node_context_10_1558_280383 : EJMOriginalGlobalDAGData.nodes 11 ⟨280383, by decide⟩ =
    .split (coordinate 10) (![⟨279837, by decide⟩,⟨279976, by decide⟩,⟨280171, by decide⟩,⟨280382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1558_280383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1558 ⟨280383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1558
    ⟨280383, by decide⟩ (by decide) (![⟨279837, by decide⟩,⟨279976, by decide⟩,⟨280171, by decide⟩,⟨280382, by decide⟩]) unmarked_context_10_1558_280383 node_context_10_1558_280383
  intro a
  fin_cases a
  · exact context_11_6232_279837
  · exact context_11_6233_279976
  · exact context_11_6234_280171
  · exact context_11_6235_280382

theorem selected_cut_10298 : selected 9 ⟨280417, by decide⟩
    (prefixPartial 12 24944) = some ⟨12, 2, 0, 280417, 24944, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_24944_280417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24944 ⟨280417, by decide⟩ :=
  accepted_of_selected 12 24944 ⟨280417, by decide⟩ ⟨12, 2, 0, 280417, 24944, 3081, 65536⟩
    (by decide) selected_cut_10298

theorem selected_cut_10299 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99780) = some ⟨13, 1, 0, 3444, 99780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99780, 1, 16384⟩
    (by decide) selected_cut_10299

theorem selected_cut_10300 : selected 8 ⟨280426, by decide⟩
    (prefixPartial 13 99781) = some ⟨13, 2, 0, 280426, 99781, 749, 16384⟩ := by
  decide +kernel

theorem context_13_99781_280426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99781 ⟨280426, by decide⟩ :=
  accepted_of_selected 13 99781 ⟨280426, by decide⟩ ⟨13, 2, 0, 280426, 99781, 749, 16384⟩
    (by decide) selected_cut_10300

theorem selected_cut_10301 : selected 8 ⟨280473, by decide⟩
    (prefixPartial 13 99782) = some ⟨13, 2, 0, 280473, 99782, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_99782_280473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99782 ⟨280473, by decide⟩ :=
  accepted_of_selected 13 99782 ⟨280473, by decide⟩ ⟨13, 2, 0, 280473, 99782, 2737, 16384⟩
    (by decide) selected_cut_10301

theorem selected_cut_10302 : selected 8 ⟨280480, by decide⟩
    (prefixPartial 13 99783) = some ⟨13, 2, 0, 280480, 99783, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_99783_280480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99783 ⟨280480, by decide⟩ :=
  accepted_of_selected 13 99783 ⟨280480, by decide⟩ ⟨13, 2, 0, 280480, 99783, 1077, 16384⟩
    (by decide) selected_cut_10302

theorem unmarked_context_12_24945_280481 : frontier 9 ⟨280481, by decide⟩
    (prefixCache 12 24945) (prefixPartial 12 24945) = false := by
  decide +kernel

theorem node_context_12_24945_280481 : EJMOriginalGlobalDAGData.nodes 9 ⟨280481, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280426, by decide⟩,⟨280473, by decide⟩,⟨280480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24945_280481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24945 ⟨280481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24945
    ⟨280481, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280426, by decide⟩,⟨280473, by decide⟩,⟨280480, by decide⟩]) unmarked_context_12_24945_280481 node_context_12_24945_280481
  intro a
  fin_cases a
  · exact context_13_99780_3444
  · exact context_13_99781_280426
  · exact context_13_99782_280473
  · exact context_13_99783_280480

theorem selected_cut_10303 : selected 9 ⟨280527, by decide⟩
    (prefixPartial 12 24946) = some ⟨12, 2, 0, 280527, 24946, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_24946_280527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24946 ⟨280527, by decide⟩ :=
  accepted_of_selected 12 24946 ⟨280527, by decide⟩ ⟨12, 2, 0, 280527, 24946, 3733, 65536⟩
    (by decide) selected_cut_10303

theorem selected_cut_10304 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99788) = some ⟨13, 1, 0, 3444, 99788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99788, 1, 16384⟩
    (by decide) selected_cut_10304

theorem selected_cut_10305 : selected 8 ⟨280535, by decide⟩
    (prefixPartial 13 99789) = some ⟨13, 2, 0, 280535, 99789, 657, 16384⟩ := by
  decide +kernel

theorem context_13_99789_280535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99789 ⟨280535, by decide⟩ :=
  accepted_of_selected 13 99789 ⟨280535, by decide⟩ ⟨13, 2, 0, 280535, 99789, 657, 16384⟩
    (by decide) selected_cut_10305

theorem selected_cut_10306 : selected 8 ⟨280572, by decide⟩
    (prefixPartial 13 99790) = some ⟨13, 2, 0, 280572, 99790, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_99790_280572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99790 ⟨280572, by decide⟩ :=
  accepted_of_selected 13 99790 ⟨280572, by decide⟩ ⟨13, 2, 0, 280572, 99790, 2477, 16384⟩
    (by decide) selected_cut_10306

theorem selected_cut_10307 : selected 8 ⟨280583, by decide⟩
    (prefixPartial 13 99791) = some ⟨13, 2, 0, 280583, 99791, 981, 16384⟩ := by
  decide +kernel

theorem context_13_99791_280583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99791 ⟨280583, by decide⟩ :=
  accepted_of_selected 13 99791 ⟨280583, by decide⟩ ⟨13, 2, 0, 280583, 99791, 981, 16384⟩
    (by decide) selected_cut_10307

theorem unmarked_context_12_24947_280584 : frontier 9 ⟨280584, by decide⟩
    (prefixCache 12 24947) (prefixPartial 12 24947) = false := by
  decide +kernel

theorem node_context_12_24947_280584 : EJMOriginalGlobalDAGData.nodes 9 ⟨280584, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280535, by decide⟩,⟨280572, by decide⟩,⟨280583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24947_280584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24947 ⟨280584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24947
    ⟨280584, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280535, by decide⟩,⟨280572, by decide⟩,⟨280583, by decide⟩]) unmarked_context_12_24947_280584 node_context_12_24947_280584
  intro a
  fin_cases a
  · exact context_13_99788_3444
  · exact context_13_99789_280535
  · exact context_13_99790_280572
  · exact context_13_99791_280583

theorem unmarked_context_11_6236_280585 : frontier 10 ⟨280585, by decide⟩
    (prefixCache 11 6236) (prefixPartial 11 6236) = false := by
  decide +kernel

theorem node_context_11_6236_280585 : EJMOriginalGlobalDAGData.nodes 10 ⟨280585, by decide⟩ =
    .split (coordinate 11) (![⟨280417, by decide⟩,⟨280481, by decide⟩,⟨280527, by decide⟩,⟨280584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6236_280585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6236 ⟨280585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6236
    ⟨280585, by decide⟩ (by decide) (![⟨280417, by decide⟩,⟨280481, by decide⟩,⟨280527, by decide⟩,⟨280584, by decide⟩]) unmarked_context_11_6236_280585 node_context_11_6236_280585
  intro a
  fin_cases a
  · exact context_12_24944_280417
  · exact context_12_24945_280481
  · exact context_12_24946_280527
  · exact context_12_24947_280584

theorem selected_cut_10308 : selected 9 ⟨280616, by decide⟩
    (prefixPartial 12 24948) = some ⟨12, 2, 0, 280616, 24948, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_24948_280616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24948 ⟨280616, by decide⟩ :=
  accepted_of_selected 12 24948 ⟨280616, by decide⟩ ⟨12, 2, 0, 280616, 24948, 2497, 65536⟩
    (by decide) selected_cut_10308

theorem selected_cut_10309 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 24949) = some ⟨12, 1, 0, 126884, 24949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24949_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24949 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 24949 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 24949, 1, 65536⟩
    (by decide) selected_cut_10309

theorem selected_cut_10310 : selected 9 ⟨280654, by decide⟩
    (prefixPartial 12 24950) = some ⟨12, 2, 0, 280654, 24950, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_24950_280654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24950 ⟨280654, by decide⟩ :=
  accepted_of_selected 12 24950 ⟨280654, by decide⟩ ⟨12, 2, 0, 280654, 24950, 3137, 65536⟩
    (by decide) selected_cut_10310

theorem selected_cut_10311 : selected 9 ⟨280687, by decide⟩
    (prefixPartial 12 24951) = some ⟨12, 2, 0, 280687, 24951, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_24951_280687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24951 ⟨280687, by decide⟩ :=
  accepted_of_selected 12 24951 ⟨280687, by decide⟩ ⟨12, 2, 0, 280687, 24951, 3593, 65536⟩
    (by decide) selected_cut_10311

theorem unmarked_context_11_6237_280688 : frontier 10 ⟨280688, by decide⟩
    (prefixCache 11 6237) (prefixPartial 11 6237) = false := by
  decide +kernel

theorem node_context_11_6237_280688 : EJMOriginalGlobalDAGData.nodes 10 ⟨280688, by decide⟩ =
    .split (coordinate 11) (![⟨280616, by decide⟩,⟨126884, by decide⟩,⟨280654, by decide⟩,⟨280687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6237_280688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6237 ⟨280688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6237
    ⟨280688, by decide⟩ (by decide) (![⟨280616, by decide⟩,⟨126884, by decide⟩,⟨280654, by decide⟩,⟨280687, by decide⟩]) unmarked_context_11_6237_280688 node_context_11_6237_280688
  intro a
  fin_cases a
  · exact context_12_24948_280616
  · exact context_12_24949_126884
  · exact context_12_24950_280654
  · exact context_12_24951_280687

theorem selected_cut_10312 : selected 9 ⟨280722, by decide⟩
    (prefixPartial 12 24952) = some ⟨12, 2, 0, 280722, 24952, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_24952_280722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24952 ⟨280722, by decide⟩ :=
  accepted_of_selected 12 24952 ⟨280722, by decide⟩ ⟨12, 2, 0, 280722, 24952, 3277, 65536⟩
    (by decide) selected_cut_10312

theorem selected_cut_10313 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99812) = some ⟨13, 1, 0, 3444, 99812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99812, 1, 16384⟩
    (by decide) selected_cut_10313

theorem selected_cut_10314 : selected 8 ⟨280727, by decide⟩
    (prefixPartial 13 99813) = some ⟨13, 2, 0, 280727, 99813, 377, 16384⟩ := by
  decide +kernel

theorem context_13_99813_280727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99813 ⟨280727, by decide⟩ :=
  accepted_of_selected 13 99813 ⟨280727, by decide⟩ ⟨13, 2, 0, 280727, 99813, 377, 16384⟩
    (by decide) selected_cut_10314

theorem selected_cut_10315 : selected 8 ⟨280775, by decide⟩
    (prefixPartial 13 99814) = some ⟨13, 2, 0, 280775, 99814, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_99814_280775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99814 ⟨280775, by decide⟩ :=
  accepted_of_selected 13 99814 ⟨280775, by decide⟩ ⟨13, 2, 0, 280775, 99814, 2817, 16384⟩
    (by decide) selected_cut_10315

theorem selected_cut_10316 : selected 8 ⟨280791, by decide⟩
    (prefixPartial 13 99815) = some ⟨13, 2, 0, 280791, 99815, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_99815_280791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99815 ⟨280791, by decide⟩ :=
  accepted_of_selected 13 99815 ⟨280791, by decide⟩ ⟨13, 2, 0, 280791, 99815, 1145, 16384⟩
    (by decide) selected_cut_10316

theorem unmarked_context_12_24953_280792 : frontier 9 ⟨280792, by decide⟩
    (prefixCache 12 24953) (prefixPartial 12 24953) = false := by
  decide +kernel

theorem node_context_12_24953_280792 : EJMOriginalGlobalDAGData.nodes 9 ⟨280792, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨280727, by decide⟩,⟨280775, by decide⟩,⟨280791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24953_280792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24953 ⟨280792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24953
    ⟨280792, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨280727, by decide⟩,⟨280775, by decide⟩,⟨280791, by decide⟩]) unmarked_context_12_24953_280792 node_context_12_24953_280792
  intro a
  fin_cases a
  · exact context_13_99812_3444
  · exact context_13_99813_280727
  · exact context_13_99814_280775
  · exact context_13_99815_280791

theorem selected_cut_10317 : selected 9 ⟨280826, by decide⟩
    (prefixPartial 12 24954) = some ⟨12, 2, 0, 280826, 24954, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_24954_280826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24954 ⟨280826, by decide⟩ :=
  accepted_of_selected 12 24954 ⟨280826, by decide⟩ ⟨12, 2, 0, 280826, 24954, 3449, 65536⟩
    (by decide) selected_cut_10317

theorem selected_cut_10318 : selected 9 ⟨280867, by decide⟩
    (prefixPartial 12 24955) = some ⟨12, 2, 0, 280867, 24955, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_24955_280867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24955 ⟨280867, by decide⟩ :=
  accepted_of_selected 12 24955 ⟨280867, by decide⟩ ⟨12, 2, 0, 280867, 24955, 3773, 65536⟩
    (by decide) selected_cut_10318

theorem unmarked_context_11_6238_280868 : frontier 10 ⟨280868, by decide⟩
    (prefixCache 11 6238) (prefixPartial 11 6238) = false := by
  decide +kernel

theorem node_context_11_6238_280868 : EJMOriginalGlobalDAGData.nodes 10 ⟨280868, by decide⟩ =
    .split (coordinate 11) (![⟨280722, by decide⟩,⟨280792, by decide⟩,⟨280826, by decide⟩,⟨280867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6238_280868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6238 ⟨280868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6238
    ⟨280868, by decide⟩ (by decide) (![⟨280722, by decide⟩,⟨280792, by decide⟩,⟨280826, by decide⟩,⟨280867, by decide⟩]) unmarked_context_11_6238_280868 node_context_11_6238_280868
  intro a
  fin_cases a
  · exact context_12_24952_280722
  · exact context_12_24953_280792
  · exact context_12_24954_280826
  · exact context_12_24955_280867

theorem selected_cut_10319 : selected 9 ⟨280901, by decide⟩
    (prefixPartial 12 24956) = some ⟨12, 2, 0, 280901, 24956, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_24956_280901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24956 ⟨280901, by decide⟩ :=
  accepted_of_selected 12 24956 ⟨280901, by decide⟩ ⟨12, 2, 0, 280901, 24956, 3069, 65536⟩
    (by decide) selected_cut_10319

theorem selected_cut_10320 : selected 9 ⟨280959, by decide⟩
    (prefixPartial 12 24957) = some ⟨12, 2, 0, 280959, 24957, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_24957_280959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24957 ⟨280959, by decide⟩ :=
  accepted_of_selected 12 24957 ⟨280959, by decide⟩ ⟨12, 2, 0, 280959, 24957, 4045, 65536⟩
    (by decide) selected_cut_10320

theorem selected_cut_10321 : selected 9 ⟨281000, by decide⟩
    (prefixPartial 12 24958) = some ⟨12, 2, 0, 281000, 24958, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_24958_281000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24958 ⟨281000, by decide⟩ :=
  accepted_of_selected 12 24958 ⟨281000, by decide⟩ ⟨12, 2, 0, 281000, 24958, 3161, 65536⟩
    (by decide) selected_cut_10321

theorem selected_cut_10322 : selected 9 ⟨281033, by decide⟩
    (prefixPartial 12 24959) = some ⟨12, 2, 0, 281033, 24959, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_24959_281033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24959 ⟨281033, by decide⟩ :=
  accepted_of_selected 12 24959 ⟨281033, by decide⟩ ⟨12, 2, 0, 281033, 24959, 3541, 65536⟩
    (by decide) selected_cut_10322

theorem unmarked_context_11_6239_281034 : frontier 10 ⟨281034, by decide⟩
    (prefixCache 11 6239) (prefixPartial 11 6239) = false := by
  decide +kernel

theorem node_context_11_6239_281034 : EJMOriginalGlobalDAGData.nodes 10 ⟨281034, by decide⟩ =
    .split (coordinate 11) (![⟨280901, by decide⟩,⟨280959, by decide⟩,⟨281000, by decide⟩,⟨281033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6239_281034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6239 ⟨281034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6239
    ⟨281034, by decide⟩ (by decide) (![⟨280901, by decide⟩,⟨280959, by decide⟩,⟨281000, by decide⟩,⟨281033, by decide⟩]) unmarked_context_11_6239_281034 node_context_11_6239_281034
  intro a
  fin_cases a
  · exact context_12_24956_280901
  · exact context_12_24957_280959
  · exact context_12_24958_281000
  · exact context_12_24959_281033

theorem unmarked_context_10_1559_281035 : frontier 11 ⟨281035, by decide⟩
    (prefixCache 10 1559) (prefixPartial 10 1559) = false := by
  decide +kernel

theorem node_context_10_1559_281035 : EJMOriginalGlobalDAGData.nodes 11 ⟨281035, by decide⟩ =
    .split (coordinate 10) (![⟨280585, by decide⟩,⟨280688, by decide⟩,⟨280868, by decide⟩,⟨281034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1559_281035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1559 ⟨281035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1559
    ⟨281035, by decide⟩ (by decide) (![⟨280585, by decide⟩,⟨280688, by decide⟩,⟨280868, by decide⟩,⟨281034, by decide⟩]) unmarked_context_10_1559_281035 node_context_10_1559_281035
  intro a
  fin_cases a
  · exact context_11_6236_280585
  · exact context_11_6237_280688
  · exact context_11_6238_280868
  · exact context_11_6239_281034

theorem unmarked_context_9_389_281036 : frontier 12 ⟨281036, by decide⟩
    (prefixCache 9 389) (prefixPartial 9 389) = false := by
  decide +kernel

theorem node_context_9_389_281036 : EJMOriginalGlobalDAGData.nodes 12 ⟨281036, by decide⟩ =
    .split (coordinate 9) (![⟨278953, by decide⟩,⟨279610, by decide⟩,⟨280383, by decide⟩,⟨281035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_389_281036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 389 ⟨281036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 389
    ⟨281036, by decide⟩ (by decide) (![⟨278953, by decide⟩,⟨279610, by decide⟩,⟨280383, by decide⟩,⟨281035, by decide⟩]) unmarked_context_9_389_281036 node_context_9_389_281036
  intro a
  fin_cases a
  · exact context_10_1556_278953
  · exact context_10_1557_279610
  · exact context_10_1558_280383
  · exact context_10_1559_281035

theorem selected_cut_10323 : selected 9 ⟨281106, by decide⟩
    (prefixPartial 12 24960) = some ⟨12, 2, 0, 281106, 24960, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_24960_281106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24960 ⟨281106, by decide⟩ :=
  accepted_of_selected 12 24960 ⟨281106, by decide⟩ ⟨12, 2, 0, 281106, 24960, 1397, 65536⟩
    (by decide) selected_cut_10323

theorem selected_cut_10324 : selected 9 ⟨281169, by decide⟩
    (prefixPartial 12 24961) = some ⟨12, 2, 0, 281169, 24961, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_24961_281169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24961 ⟨281169, by decide⟩ :=
  accepted_of_selected 12 24961 ⟨281169, by decide⟩ ⟨12, 2, 0, 281169, 24961, 3629, 65536⟩
    (by decide) selected_cut_10324

theorem selected_cut_10325 : selected 9 ⟨281225, by decide⟩
    (prefixPartial 12 24962) = some ⟨12, 2, 0, 281225, 24962, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_24962_281225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24962 ⟨281225, by decide⟩ :=
  accepted_of_selected 12 24962 ⟨281225, by decide⟩ ⟨12, 2, 0, 281225, 24962, 3569, 65536⟩
    (by decide) selected_cut_10325

theorem selected_cut_10326 : selected 9 ⟨281274, by decide⟩
    (prefixPartial 12 24963) = some ⟨12, 2, 0, 281274, 24963, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_24963_281274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24963 ⟨281274, by decide⟩ :=
  accepted_of_selected 12 24963 ⟨281274, by decide⟩ ⟨12, 2, 0, 281274, 24963, 3733, 65536⟩
    (by decide) selected_cut_10326

theorem unmarked_context_11_6240_281275 : frontier 10 ⟨281275, by decide⟩
    (prefixCache 11 6240) (prefixPartial 11 6240) = false := by
  decide +kernel

theorem node_context_11_6240_281275 : EJMOriginalGlobalDAGData.nodes 10 ⟨281275, by decide⟩ =
    .split (coordinate 11) (![⟨281106, by decide⟩,⟨281169, by decide⟩,⟨281225, by decide⟩,⟨281274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6240_281275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6240 ⟨281275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6240
    ⟨281275, by decide⟩ (by decide) (![⟨281106, by decide⟩,⟨281169, by decide⟩,⟨281225, by decide⟩,⟨281274, by decide⟩]) unmarked_context_11_6240_281275 node_context_11_6240_281275
  intro a
  fin_cases a
  · exact context_12_24960_281106
  · exact context_12_24961_281169
  · exact context_12_24962_281225
  · exact context_12_24963_281274

theorem selected_cut_10327 : selected 9 ⟨281304, by decide⟩
    (prefixPartial 12 24964) = some ⟨12, 2, 0, 281304, 24964, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_24964_281304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24964 ⟨281304, by decide⟩ :=
  accepted_of_selected 12 24964 ⟨281304, by decide⟩ ⟨12, 2, 0, 281304, 24964, 2073, 65536⟩
    (by decide) selected_cut_10327

theorem selected_cut_10328 : selected 9 ⟨281334, by decide⟩
    (prefixPartial 12 24965) = some ⟨12, 2, 0, 281334, 24965, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_24965_281334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24965 ⟨281334, by decide⟩ :=
  accepted_of_selected 12 24965 ⟨281334, by decide⟩ ⟨12, 2, 0, 281334, 24965, 3233, 65536⟩
    (by decide) selected_cut_10328

theorem selected_cut_10329 : selected 9 ⟨281363, by decide⟩
    (prefixPartial 12 24966) = some ⟨12, 2, 0, 281363, 24966, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_24966_281363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24966 ⟨281363, by decide⟩ :=
  accepted_of_selected 12 24966 ⟨281363, by decide⟩ ⟨12, 2, 0, 281363, 24966, 2321, 65536⟩
    (by decide) selected_cut_10329

theorem selected_cut_10330 : selected 9 ⟨281391, by decide⟩
    (prefixPartial 12 24967) = some ⟨12, 2, 0, 281391, 24967, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_24967_281391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24967 ⟨281391, by decide⟩ :=
  accepted_of_selected 12 24967 ⟨281391, by decide⟩ ⟨12, 2, 0, 281391, 24967, 2425, 65536⟩
    (by decide) selected_cut_10330

theorem unmarked_context_11_6241_281392 : frontier 10 ⟨281392, by decide⟩
    (prefixCache 11 6241) (prefixPartial 11 6241) = false := by
  decide +kernel

theorem node_context_11_6241_281392 : EJMOriginalGlobalDAGData.nodes 10 ⟨281392, by decide⟩ =
    .split (coordinate 11) (![⟨281304, by decide⟩,⟨281334, by decide⟩,⟨281363, by decide⟩,⟨281391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6241_281392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6241 ⟨281392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6241
    ⟨281392, by decide⟩ (by decide) (![⟨281304, by decide⟩,⟨281334, by decide⟩,⟨281363, by decide⟩,⟨281391, by decide⟩]) unmarked_context_11_6241_281392 node_context_11_6241_281392
  intro a
  fin_cases a
  · exact context_12_24964_281304
  · exact context_12_24965_281334
  · exact context_12_24966_281363
  · exact context_12_24967_281391

theorem selected_cut_10331 : selected 9 ⟨281432, by decide⟩
    (prefixPartial 12 24968) = some ⟨12, 2, 0, 281432, 24968, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_24968_281432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24968 ⟨281432, by decide⟩ :=
  accepted_of_selected 12 24968 ⟨281432, by decide⟩ ⟨12, 2, 0, 281432, 24968, 2401, 65536⟩
    (by decide) selected_cut_10331

theorem selected_cut_10332 : selected 9 ⟨281468, by decide⟩
    (prefixPartial 12 24969) = some ⟨12, 2, 0, 281468, 24969, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_24969_281468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24969 ⟨281468, by decide⟩ :=
  accepted_of_selected 12 24969 ⟨281468, by decide⟩ ⟨12, 2, 0, 281468, 24969, 2545, 65536⟩
    (by decide) selected_cut_10332

theorem selected_cut_10333 : selected 9 ⟨281505, by decide⟩
    (prefixPartial 12 24970) = some ⟨12, 2, 0, 281505, 24970, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_24970_281505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24970 ⟨281505, by decide⟩ :=
  accepted_of_selected 12 24970 ⟨281505, by decide⟩ ⟨12, 2, 0, 281505, 24970, 2361, 65536⟩
    (by decide) selected_cut_10333

theorem selected_cut_10334 : selected 9 ⟨281539, by decide⟩
    (prefixPartial 12 24971) = some ⟨12, 2, 0, 281539, 24971, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_24971_281539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24971 ⟨281539, by decide⟩ :=
  accepted_of_selected 12 24971 ⟨281539, by decide⟩ ⟨12, 2, 0, 281539, 24971, 2557, 65536⟩
    (by decide) selected_cut_10334

theorem unmarked_context_11_6242_281540 : frontier 10 ⟨281540, by decide⟩
    (prefixCache 11 6242) (prefixPartial 11 6242) = false := by
  decide +kernel

theorem node_context_11_6242_281540 : EJMOriginalGlobalDAGData.nodes 10 ⟨281540, by decide⟩ =
    .split (coordinate 11) (![⟨281432, by decide⟩,⟨281468, by decide⟩,⟨281505, by decide⟩,⟨281539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6242_281540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6242 ⟨281540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6242
    ⟨281540, by decide⟩ (by decide) (![⟨281432, by decide⟩,⟨281468, by decide⟩,⟨281505, by decide⟩,⟨281539, by decide⟩]) unmarked_context_11_6242_281540 node_context_11_6242_281540
  intro a
  fin_cases a
  · exact context_12_24968_281432
  · exact context_12_24969_281468
  · exact context_12_24970_281505
  · exact context_12_24971_281539

theorem selected_cut_10335 : selected 9 ⟨281572, by decide⟩
    (prefixPartial 12 24972) = some ⟨12, 2, 0, 281572, 24972, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_24972_281572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24972 ⟨281572, by decide⟩ :=
  accepted_of_selected 12 24972 ⟨281572, by decide⟩ ⟨12, 2, 0, 281572, 24972, 2149, 65536⟩
    (by decide) selected_cut_10335

theorem selected_cut_10336 : selected 9 ⟨281601, by decide⟩
    (prefixPartial 12 24973) = some ⟨12, 2, 0, 281601, 24973, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_24973_281601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24973 ⟨281601, by decide⟩ :=
  accepted_of_selected 12 24973 ⟨281601, by decide⟩ ⟨12, 2, 0, 281601, 24973, 2245, 65536⟩
    (by decide) selected_cut_10336

theorem selected_cut_10337 : selected 9 ⟨281631, by decide⟩
    (prefixPartial 12 24974) = some ⟨12, 2, 0, 281631, 24974, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_24974_281631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24974 ⟨281631, by decide⟩ :=
  accepted_of_selected 12 24974 ⟨281631, by decide⟩ ⟨12, 2, 0, 281631, 24974, 2137, 65536⟩
    (by decide) selected_cut_10337

theorem selected_cut_10338 : selected 9 ⟨281660, by decide⟩
    (prefixPartial 12 24975) = some ⟨12, 2, 0, 281660, 24975, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_24975_281660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24975 ⟨281660, by decide⟩ :=
  accepted_of_selected 12 24975 ⟨281660, by decide⟩ ⟨12, 2, 0, 281660, 24975, 2261, 65536⟩
    (by decide) selected_cut_10338

theorem unmarked_context_11_6243_281661 : frontier 10 ⟨281661, by decide⟩
    (prefixCache 11 6243) (prefixPartial 11 6243) = false := by
  decide +kernel

theorem node_context_11_6243_281661 : EJMOriginalGlobalDAGData.nodes 10 ⟨281661, by decide⟩ =
    .split (coordinate 11) (![⟨281572, by decide⟩,⟨281601, by decide⟩,⟨281631, by decide⟩,⟨281660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6243_281661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6243 ⟨281661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6243
    ⟨281661, by decide⟩ (by decide) (![⟨281572, by decide⟩,⟨281601, by decide⟩,⟨281631, by decide⟩,⟨281660, by decide⟩]) unmarked_context_11_6243_281661 node_context_11_6243_281661
  intro a
  fin_cases a
  · exact context_12_24972_281572
  · exact context_12_24973_281601
  · exact context_12_24974_281631
  · exact context_12_24975_281660

theorem unmarked_context_10_1560_281662 : frontier 11 ⟨281662, by decide⟩
    (prefixCache 10 1560) (prefixPartial 10 1560) = false := by
  decide +kernel

theorem node_context_10_1560_281662 : EJMOriginalGlobalDAGData.nodes 11 ⟨281662, by decide⟩ =
    .split (coordinate 10) (![⟨281275, by decide⟩,⟨281392, by decide⟩,⟨281540, by decide⟩,⟨281661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1560_281662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1560 ⟨281662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1560
    ⟨281662, by decide⟩ (by decide) (![⟨281275, by decide⟩,⟨281392, by decide⟩,⟨281540, by decide⟩,⟨281661, by decide⟩]) unmarked_context_10_1560_281662 node_context_10_1560_281662
  intro a
  fin_cases a
  · exact context_11_6240_281275
  · exact context_11_6241_281392
  · exact context_11_6242_281540
  · exact context_11_6243_281661

theorem selected_cut_10339 : selected 9 ⟨281677, by decide⟩
    (prefixPartial 12 24976) = some ⟨12, 2, 0, 281677, 24976, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_24976_281677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24976 ⟨281677, by decide⟩ :=
  accepted_of_selected 12 24976 ⟨281677, by decide⟩ ⟨12, 2, 0, 281677, 24976, 1637, 65536⟩
    (by decide) selected_cut_10339

theorem selected_cut_10340 : selected 9 ⟨281697, by decide⟩
    (prefixPartial 12 24977) = some ⟨12, 2, 0, 281697, 24977, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_24977_281697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24977 ⟨281697, by decide⟩ :=
  accepted_of_selected 12 24977 ⟨281697, by decide⟩ ⟨12, 2, 0, 281697, 24977, 1849, 65536⟩
    (by decide) selected_cut_10340

theorem selected_cut_10341 : selected 9 ⟨281718, by decide⟩
    (prefixPartial 12 24978) = some ⟨12, 2, 0, 281718, 24978, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_24978_281718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24978 ⟨281718, by decide⟩ :=
  accepted_of_selected 12 24978 ⟨281718, by decide⟩ ⟨12, 2, 0, 281718, 24978, 1973, 65536⟩
    (by decide) selected_cut_10341

theorem selected_cut_10342 : selected 9 ⟨281740, by decide⟩
    (prefixPartial 12 24979) = some ⟨12, 2, 0, 281740, 24979, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_24979_281740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24979 ⟨281740, by decide⟩ :=
  accepted_of_selected 12 24979 ⟨281740, by decide⟩ ⟨12, 2, 0, 281740, 24979, 1993, 65536⟩
    (by decide) selected_cut_10342

theorem unmarked_context_11_6244_281741 : frontier 10 ⟨281741, by decide⟩
    (prefixCache 11 6244) (prefixPartial 11 6244) = false := by
  decide +kernel

theorem node_context_11_6244_281741 : EJMOriginalGlobalDAGData.nodes 10 ⟨281741, by decide⟩ =
    .split (coordinate 11) (![⟨281677, by decide⟩,⟨281697, by decide⟩,⟨281718, by decide⟩,⟨281740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6244_281741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6244 ⟨281741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6244
    ⟨281741, by decide⟩ (by decide) (![⟨281677, by decide⟩,⟨281697, by decide⟩,⟨281718, by decide⟩,⟨281740, by decide⟩]) unmarked_context_11_6244_281741 node_context_11_6244_281741
  intro a
  fin_cases a
  · exact context_12_24976_281677
  · exact context_12_24977_281697
  · exact context_12_24978_281718
  · exact context_12_24979_281740

theorem selected_cut_10343 : selected 9 ⟨281758, by decide⟩
    (prefixPartial 12 24980) = some ⟨12, 2, 0, 281758, 24980, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_24980_281758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24980 ⟨281758, by decide⟩ :=
  accepted_of_selected 12 24980 ⟨281758, by decide⟩ ⟨12, 2, 0, 281758, 24980, 1565, 65536⟩
    (by decide) selected_cut_10343

theorem selected_cut_10344 : selected 9 ⟨281818, by decide⟩
    (prefixPartial 12 24981) = some ⟨12, 2, 0, 281818, 24981, 789, 65536⟩ := by
  decide +kernel

theorem context_12_24981_281818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24981 ⟨281818, by decide⟩ :=
  accepted_of_selected 12 24981 ⟨281818, by decide⟩ ⟨12, 2, 0, 281818, 24981, 789, 65536⟩
    (by decide) selected_cut_10344

theorem selected_cut_10345 : selected 9 ⟨281837, by decide⟩
    (prefixPartial 12 24982) = some ⟨12, 2, 0, 281837, 24982, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_24982_281837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24982 ⟨281837, by decide⟩ :=
  accepted_of_selected 12 24982 ⟨281837, by decide⟩ ⟨12, 2, 0, 281837, 24982, 1877, 65536⟩
    (by decide) selected_cut_10345

theorem selected_cut_10346 : selected 9 ⟨281858, by decide⟩
    (prefixPartial 12 24983) = some ⟨12, 2, 0, 281858, 24983, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_24983_281858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24983 ⟨281858, by decide⟩ :=
  accepted_of_selected 12 24983 ⟨281858, by decide⟩ ⟨12, 2, 0, 281858, 24983, 1869, 65536⟩
    (by decide) selected_cut_10346

theorem unmarked_context_11_6245_281859 : frontier 10 ⟨281859, by decide⟩
    (prefixCache 11 6245) (prefixPartial 11 6245) = false := by
  decide +kernel

theorem node_context_11_6245_281859 : EJMOriginalGlobalDAGData.nodes 10 ⟨281859, by decide⟩ =
    .split (coordinate 11) (![⟨281758, by decide⟩,⟨281818, by decide⟩,⟨281837, by decide⟩,⟨281858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6245_281859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6245 ⟨281859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6245
    ⟨281859, by decide⟩ (by decide) (![⟨281758, by decide⟩,⟨281818, by decide⟩,⟨281837, by decide⟩,⟨281858, by decide⟩]) unmarked_context_11_6245_281859 node_context_11_6245_281859
  intro a
  fin_cases a
  · exact context_12_24980_281758
  · exact context_12_24981_281818
  · exact context_12_24982_281837
  · exact context_12_24983_281858

theorem selected_cut_10347 : selected 9 ⟨281878, by decide⟩
    (prefixPartial 12 24984) = some ⟨12, 2, 0, 281878, 24984, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_24984_281878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24984 ⟨281878, by decide⟩ :=
  accepted_of_selected 12 24984 ⟨281878, by decide⟩ ⟨12, 2, 0, 281878, 24984, 1685, 65536⟩
    (by decide) selected_cut_10347

theorem selected_cut_10348 : selected 9 ⟨281905, by decide⟩
    (prefixPartial 12 24985) = some ⟨12, 2, 0, 281905, 24985, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_24985_281905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24985 ⟨281905, by decide⟩ :=
  accepted_of_selected 12 24985 ⟨281905, by decide⟩ ⟨12, 2, 0, 281905, 24985, 1777, 65536⟩
    (by decide) selected_cut_10348

theorem selected_cut_10349 : selected 9 ⟨281932, by decide⟩
    (prefixPartial 12 24986) = some ⟨12, 2, 0, 281932, 24986, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_24986_281932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24986 ⟨281932, by decide⟩ :=
  accepted_of_selected 12 24986 ⟨281932, by decide⟩ ⟨12, 2, 0, 281932, 24986, 1825, 65536⟩
    (by decide) selected_cut_10349

theorem selected_cut_10350 : selected 9 ⟨281953, by decide⟩
    (prefixPartial 12 24987) = some ⟨12, 2, 0, 281953, 24987, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_24987_281953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24987 ⟨281953, by decide⟩ :=
  accepted_of_selected 12 24987 ⟨281953, by decide⟩ ⟨12, 2, 0, 281953, 24987, 1797, 65536⟩
    (by decide) selected_cut_10350

theorem unmarked_context_11_6246_281954 : frontier 10 ⟨281954, by decide⟩
    (prefixCache 11 6246) (prefixPartial 11 6246) = false := by
  decide +kernel

theorem node_context_11_6246_281954 : EJMOriginalGlobalDAGData.nodes 10 ⟨281954, by decide⟩ =
    .split (coordinate 11) (![⟨281878, by decide⟩,⟨281905, by decide⟩,⟨281932, by decide⟩,⟨281953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6246_281954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6246 ⟨281954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6246
    ⟨281954, by decide⟩ (by decide) (![⟨281878, by decide⟩,⟨281905, by decide⟩,⟨281932, by decide⟩,⟨281953, by decide⟩]) unmarked_context_11_6246_281954 node_context_11_6246_281954
  intro a
  fin_cases a
  · exact context_12_24984_281878
  · exact context_12_24985_281905
  · exact context_12_24986_281932
  · exact context_12_24987_281953

theorem selected_cut_10351 : selected 9 ⟨281978, by decide⟩
    (prefixPartial 12 24988) = some ⟨12, 2, 0, 281978, 24988, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_24988_281978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24988 ⟨281978, by decide⟩ :=
  accepted_of_selected 12 24988 ⟨281978, by decide⟩ ⟨12, 2, 0, 281978, 24988, 1621, 65536⟩
    (by decide) selected_cut_10351

theorem selected_cut_10352 : selected 9 ⟨282000, by decide⟩
    (prefixPartial 12 24989) = some ⟨12, 2, 0, 282000, 24989, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_24989_282000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24989 ⟨282000, by decide⟩ :=
  accepted_of_selected 12 24989 ⟨282000, by decide⟩ ⟨12, 2, 0, 282000, 24989, 1625, 65536⟩
    (by decide) selected_cut_10352

theorem selected_cut_10353 : selected 9 ⟨282021, by decide⟩
    (prefixPartial 12 24990) = some ⟨12, 2, 0, 282021, 24990, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_24990_282021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24990 ⟨282021, by decide⟩ :=
  accepted_of_selected 12 24990 ⟨282021, by decide⟩ ⟨12, 2, 0, 282021, 24990, 1665, 65536⟩
    (by decide) selected_cut_10353

theorem selected_cut_10354 : selected 9 ⟨282041, by decide⟩
    (prefixPartial 12 24991) = some ⟨12, 2, 0, 282041, 24991, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_24991_282041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24991 ⟨282041, by decide⟩ :=
  accepted_of_selected 12 24991 ⟨282041, by decide⟩ ⟨12, 2, 0, 282041, 24991, 1681, 65536⟩
    (by decide) selected_cut_10354

theorem unmarked_context_11_6247_282042 : frontier 10 ⟨282042, by decide⟩
    (prefixCache 11 6247) (prefixPartial 11 6247) = false := by
  decide +kernel

theorem node_context_11_6247_282042 : EJMOriginalGlobalDAGData.nodes 10 ⟨282042, by decide⟩ =
    .split (coordinate 11) (![⟨281978, by decide⟩,⟨282000, by decide⟩,⟨282021, by decide⟩,⟨282041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6247_282042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6247 ⟨282042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6247
    ⟨282042, by decide⟩ (by decide) (![⟨281978, by decide⟩,⟨282000, by decide⟩,⟨282021, by decide⟩,⟨282041, by decide⟩]) unmarked_context_11_6247_282042 node_context_11_6247_282042
  intro a
  fin_cases a
  · exact context_12_24988_281978
  · exact context_12_24989_282000
  · exact context_12_24990_282021
  · exact context_12_24991_282041

theorem unmarked_context_10_1561_282043 : frontier 11 ⟨282043, by decide⟩
    (prefixCache 10 1561) (prefixPartial 10 1561) = false := by
  decide +kernel

theorem node_context_10_1561_282043 : EJMOriginalGlobalDAGData.nodes 11 ⟨282043, by decide⟩ =
    .split (coordinate 10) (![⟨281741, by decide⟩,⟨281859, by decide⟩,⟨281954, by decide⟩,⟨282042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1561_282043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1561 ⟨282043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1561
    ⟨282043, by decide⟩ (by decide) (![⟨281741, by decide⟩,⟨281859, by decide⟩,⟨281954, by decide⟩,⟨282042, by decide⟩]) unmarked_context_10_1561_282043 node_context_10_1561_282043
  intro a
  fin_cases a
  · exact context_11_6244_281741
  · exact context_11_6245_281859
  · exact context_11_6246_281954
  · exact context_11_6247_282042

theorem selected_cut_10355 : selected 9 ⟨282058, by decide⟩
    (prefixPartial 12 24992) = some ⟨12, 2, 0, 282058, 24992, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_24992_282058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24992 ⟨282058, by decide⟩ :=
  accepted_of_selected 12 24992 ⟨282058, by decide⟩ ⟨12, 2, 0, 282058, 24992, 1293, 65536⟩
    (by decide) selected_cut_10355

theorem selected_cut_10356 : selected 9 ⟨282076, by decide⟩
    (prefixPartial 12 24993) = some ⟨12, 2, 0, 282076, 24993, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_24993_282076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24993 ⟨282076, by decide⟩ :=
  accepted_of_selected 12 24993 ⟨282076, by decide⟩ ⟨12, 2, 0, 282076, 24993, 1625, 65536⟩
    (by decide) selected_cut_10356

theorem selected_cut_10357 : selected 9 ⟨282098, by decide⟩
    (prefixPartial 12 24994) = some ⟨12, 2, 0, 282098, 24994, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_24994_282098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24994 ⟨282098, by decide⟩ :=
  accepted_of_selected 12 24994 ⟨282098, by decide⟩ ⟨12, 2, 0, 282098, 24994, 1545, 65536⟩
    (by decide) selected_cut_10357

theorem selected_cut_10358 : selected 9 ⟨282115, by decide⟩
    (prefixPartial 12 24995) = some ⟨12, 2, 0, 282115, 24995, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_24995_282115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24995 ⟨282115, by decide⟩ :=
  accepted_of_selected 12 24995 ⟨282115, by decide⟩ ⟨12, 2, 0, 282115, 24995, 1581, 65536⟩
    (by decide) selected_cut_10358

theorem unmarked_context_11_6248_282116 : frontier 10 ⟨282116, by decide⟩
    (prefixCache 11 6248) (prefixPartial 11 6248) = false := by
  decide +kernel

theorem node_context_11_6248_282116 : EJMOriginalGlobalDAGData.nodes 10 ⟨282116, by decide⟩ =
    .split (coordinate 11) (![⟨282058, by decide⟩,⟨282076, by decide⟩,⟨282098, by decide⟩,⟨282115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6248_282116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6248 ⟨282116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6248
    ⟨282116, by decide⟩ (by decide) (![⟨282058, by decide⟩,⟨282076, by decide⟩,⟨282098, by decide⟩,⟨282115, by decide⟩]) unmarked_context_11_6248_282116 node_context_11_6248_282116
  intro a
  fin_cases a
  · exact context_12_24992_282058
  · exact context_12_24993_282076
  · exact context_12_24994_282098
  · exact context_12_24995_282115

theorem selected_cut_10359 : selected 9 ⟨282132, by decide⟩
    (prefixPartial 12 24996) = some ⟨12, 2, 0, 282132, 24996, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_24996_282132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24996 ⟨282132, by decide⟩ :=
  accepted_of_selected 12 24996 ⟨282132, by decide⟩ ⟨12, 2, 0, 282132, 24996, 1309, 65536⟩
    (by decide) selected_cut_10359

theorem selected_cut_10360 : selected 9 ⟨282158, by decide⟩
    (prefixPartial 12 24997) = some ⟨12, 2, 0, 282158, 24997, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_24997_282158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24997 ⟨282158, by decide⟩ :=
  accepted_of_selected 12 24997 ⟨282158, by decide⟩ ⟨12, 2, 0, 282158, 24997, 2113, 65536⟩
    (by decide) selected_cut_10360

theorem selected_cut_10361 : selected 9 ⟨282175, by decide⟩
    (prefixPartial 12 24998) = some ⟨12, 2, 0, 282175, 24998, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_24998_282175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24998 ⟨282175, by decide⟩ :=
  accepted_of_selected 12 24998 ⟨282175, by decide⟩ ⟨12, 2, 0, 282175, 24998, 1445, 65536⟩
    (by decide) selected_cut_10361

theorem selected_cut_10362 : selected 9 ⟨282190, by decide⟩
    (prefixPartial 12 24999) = some ⟨12, 2, 0, 282190, 24999, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_24999_282190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24999 ⟨282190, by decide⟩ :=
  accepted_of_selected 12 24999 ⟨282190, by decide⟩ ⟨12, 2, 0, 282190, 24999, 1521, 65536⟩
    (by decide) selected_cut_10362

theorem unmarked_context_11_6249_282191 : frontier 10 ⟨282191, by decide⟩
    (prefixCache 11 6249) (prefixPartial 11 6249) = false := by
  decide +kernel

theorem node_context_11_6249_282191 : EJMOriginalGlobalDAGData.nodes 10 ⟨282191, by decide⟩ =
    .split (coordinate 11) (![⟨282132, by decide⟩,⟨282158, by decide⟩,⟨282175, by decide⟩,⟨282190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6249_282191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6249 ⟨282191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6249
    ⟨282191, by decide⟩ (by decide) (![⟨282132, by decide⟩,⟨282158, by decide⟩,⟨282175, by decide⟩,⟨282190, by decide⟩]) unmarked_context_11_6249_282191 node_context_11_6249_282191
  intro a
  fin_cases a
  · exact context_12_24996_282132
  · exact context_12_24997_282158
  · exact context_12_24998_282175
  · exact context_12_24999_282190

theorem selected_cut_10363 : selected 9 ⟨282206, by decide⟩
    (prefixPartial 12 25000) = some ⟨12, 2, 0, 282206, 25000, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_25000_282206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25000 ⟨282206, by decide⟩ :=
  accepted_of_selected 12 25000 ⟨282206, by decide⟩ ⟨12, 2, 0, 282206, 25000, 1337, 65536⟩
    (by decide) selected_cut_10363

theorem selected_cut_10364 : selected 9 ⟨282226, by decide⟩
    (prefixPartial 12 25001) = some ⟨12, 2, 0, 282226, 25001, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_25001_282226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25001 ⟨282226, by decide⟩ :=
  accepted_of_selected 12 25001 ⟨282226, by decide⟩ ⟨12, 2, 0, 282226, 25001, 1477, 65536⟩
    (by decide) selected_cut_10364

theorem selected_cut_10365 : selected 9 ⟨282243, by decide⟩
    (prefixPartial 12 25002) = some ⟨12, 2, 0, 282243, 25002, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_25002_282243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25002 ⟨282243, by decide⟩ :=
  accepted_of_selected 12 25002 ⟨282243, by decide⟩ ⟨12, 2, 0, 282243, 25002, 1317, 65536⟩
    (by decide) selected_cut_10365

theorem selected_cut_10366 : selected 9 ⟨282259, by decide⟩
    (prefixPartial 12 25003) = some ⟨12, 2, 0, 282259, 25003, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_25003_282259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25003 ⟨282259, by decide⟩ :=
  accepted_of_selected 12 25003 ⟨282259, by decide⟩ ⟨12, 2, 0, 282259, 25003, 1417, 65536⟩
    (by decide) selected_cut_10366

theorem unmarked_context_11_6250_282260 : frontier 10 ⟨282260, by decide⟩
    (prefixCache 11 6250) (prefixPartial 11 6250) = false := by
  decide +kernel

theorem node_context_11_6250_282260 : EJMOriginalGlobalDAGData.nodes 10 ⟨282260, by decide⟩ =
    .split (coordinate 11) (![⟨282206, by decide⟩,⟨282226, by decide⟩,⟨282243, by decide⟩,⟨282259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6250_282260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6250 ⟨282260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6250
    ⟨282260, by decide⟩ (by decide) (![⟨282206, by decide⟩,⟨282226, by decide⟩,⟨282243, by decide⟩,⟨282259, by decide⟩]) unmarked_context_11_6250_282260 node_context_11_6250_282260
  intro a
  fin_cases a
  · exact context_12_25000_282206
  · exact context_12_25001_282226
  · exact context_12_25002_282243
  · exact context_12_25003_282259

theorem selected_cut_10367 : selected 9 ⟨282278, by decide⟩
    (prefixPartial 12 25004) = some ⟨12, 2, 0, 282278, 25004, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_25004_282278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25004 ⟨282278, by decide⟩ :=
  accepted_of_selected 12 25004 ⟨282278, by decide⟩ ⟨12, 2, 0, 282278, 25004, 1457, 65536⟩
    (by decide) selected_cut_10367

theorem selected_cut_10368 : selected 9 ⟨282296, by decide⟩
    (prefixPartial 12 25005) = some ⟨12, 2, 0, 282296, 25005, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_25005_282296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25005 ⟨282296, by decide⟩ :=
  accepted_of_selected 12 25005 ⟨282296, by decide⟩ ⟨12, 2, 0, 282296, 25005, 1497, 65536⟩
    (by decide) selected_cut_10368

theorem selected_cut_10369 : selected 9 ⟨282316, by decide⟩
    (prefixPartial 12 25006) = some ⟨12, 2, 0, 282316, 25006, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_25006_282316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25006 ⟨282316, by decide⟩ :=
  accepted_of_selected 12 25006 ⟨282316, by decide⟩ ⟨12, 2, 0, 282316, 25006, 1421, 65536⟩
    (by decide) selected_cut_10369

theorem selected_cut_10370 : selected 9 ⟨282331, by decide⟩
    (prefixPartial 12 25007) = some ⟨12, 2, 0, 282331, 25007, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_25007_282331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25007 ⟨282331, by decide⟩ :=
  accepted_of_selected 12 25007 ⟨282331, by decide⟩ ⟨12, 2, 0, 282331, 25007, 1553, 65536⟩
    (by decide) selected_cut_10370

theorem unmarked_context_11_6251_282332 : frontier 10 ⟨282332, by decide⟩
    (prefixCache 11 6251) (prefixPartial 11 6251) = false := by
  decide +kernel

theorem node_context_11_6251_282332 : EJMOriginalGlobalDAGData.nodes 10 ⟨282332, by decide⟩ =
    .split (coordinate 11) (![⟨282278, by decide⟩,⟨282296, by decide⟩,⟨282316, by decide⟩,⟨282331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6251_282332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6251 ⟨282332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6251
    ⟨282332, by decide⟩ (by decide) (![⟨282278, by decide⟩,⟨282296, by decide⟩,⟨282316, by decide⟩,⟨282331, by decide⟩]) unmarked_context_11_6251_282332 node_context_11_6251_282332
  intro a
  fin_cases a
  · exact context_12_25004_282278
  · exact context_12_25005_282296
  · exact context_12_25006_282316
  · exact context_12_25007_282331

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
