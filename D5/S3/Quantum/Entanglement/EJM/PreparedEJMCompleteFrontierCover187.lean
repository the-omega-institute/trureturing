/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover186
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17954 : selected 9 ⟨459943, by decide⟩
    (prefixPartial 12 71000) = some ⟨12, 2, 0, 459943, 71000, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_71000_459943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71000 ⟨459943, by decide⟩ :=
  accepted_of_selected 12 71000 ⟨459943, by decide⟩ ⟨12, 2, 0, 459943, 71000, 3665, 65536⟩
    (by decide) selected_cut_17954

theorem selected_cut_17955 : selected 9 ⟨460000, by decide⟩
    (prefixPartial 12 71001) = some ⟨12, 2, 0, 460000, 71001, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_71001_460000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71001 ⟨460000, by decide⟩ :=
  accepted_of_selected 12 71001 ⟨460000, by decide⟩ ⟨12, 2, 0, 460000, 71001, 3197, 65536⟩
    (by decide) selected_cut_17955

theorem selected_cut_17956 : selected 9 ⟨460041, by decide⟩
    (prefixPartial 12 71002) = some ⟨12, 2, 0, 460041, 71002, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_71002_460041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71002 ⟨460041, by decide⟩ :=
  accepted_of_selected 12 71002 ⟨460041, by decide⟩ ⟨12, 2, 0, 460041, 71002, 3617, 65536⟩
    (by decide) selected_cut_17956

theorem selected_cut_17957 : selected 9 ⟨460091, by decide⟩
    (prefixPartial 12 71003) = some ⟨12, 2, 0, 460091, 71003, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_71003_460091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71003 ⟨460091, by decide⟩ :=
  accepted_of_selected 12 71003 ⟨460091, by decide⟩ ⟨12, 2, 0, 460091, 71003, 3513, 65536⟩
    (by decide) selected_cut_17957

theorem unmarked_context_11_17750_460092 : frontier 10 ⟨460092, by decide⟩
    (prefixCache 11 17750) (prefixPartial 11 17750) = false := by
  decide +kernel

theorem node_context_11_17750_460092 : EJMOriginalGlobalDAGData.nodes 10 ⟨460092, by decide⟩ =
    .split (coordinate 11) (![⟨459943, by decide⟩,⟨460000, by decide⟩,⟨460041, by decide⟩,⟨460091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17750_460092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17750 ⟨460092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17750
    ⟨460092, by decide⟩ (by decide) (![⟨459943, by decide⟩,⟨460000, by decide⟩,⟨460041, by decide⟩,⟨460091, by decide⟩]) unmarked_context_11_17750_460092 node_context_11_17750_460092
  intro a
  fin_cases a
  · exact context_12_71000_459943
  · exact context_12_71001_460000
  · exact context_12_71002_460041
  · exact context_12_71003_460091

theorem selected_cut_17958 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17751) = some ⟨11, 1, 0, 1736, 17751, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17751_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17751 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17751 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17751, 1, 262144⟩
    (by decide) selected_cut_17958

theorem unmarked_context_10_4437_460093 : frontier 11 ⟨460093, by decide⟩
    (prefixCache 10 4437) (prefixPartial 10 4437) = false := by
  decide +kernel

theorem node_context_10_4437_460093 : EJMOriginalGlobalDAGData.nodes 11 ⟨460093, by decide⟩ =
    .split (coordinate 10) (![⟨459882, by decide⟩,⟨459416, by decide⟩,⟨460092, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4437_460093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4437 ⟨460093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4437
    ⟨460093, by decide⟩ (by decide) (![⟨459882, by decide⟩,⟨459416, by decide⟩,⟨460092, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4437_460093 node_context_10_4437_460093
  intro a
  fin_cases a
  · exact context_11_17748_459882
  · exact context_11_17749_459416
  · exact context_11_17750_460092
  · exact context_11_17751_1736

theorem selected_cut_17959 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 71008) = some ⟨12, 1, 0, 455939, 71008, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71008_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71008 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 71008 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 71008, 1, 65536⟩
    (by decide) selected_cut_17959

theorem selected_cut_17960 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 71009) = some ⟨12, 1, 0, 455939, 71009, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71009_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71009 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 71009 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 71009, 1, 65536⟩
    (by decide) selected_cut_17960

theorem selected_cut_17961 : selected 9 ⟨460152, by decide⟩
    (prefixPartial 12 71010) = some ⟨12, 2, 0, 460152, 71010, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_71010_460152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71010 ⟨460152, by decide⟩ :=
  accepted_of_selected 12 71010 ⟨460152, by decide⟩ ⟨12, 2, 0, 460152, 71010, 2057, 65536⟩
    (by decide) selected_cut_17961

theorem selected_cut_17962 : selected 9 ⟨460214, by decide⟩
    (prefixPartial 12 71011) = some ⟨12, 2, 0, 460214, 71011, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_71011_460214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71011 ⟨460214, by decide⟩ :=
  accepted_of_selected 12 71011 ⟨460214, by decide⟩ ⟨12, 2, 0, 460214, 71011, 2177, 65536⟩
    (by decide) selected_cut_17962

theorem unmarked_context_11_17752_460215 : frontier 10 ⟨460215, by decide⟩
    (prefixCache 11 17752) (prefixPartial 11 17752) = false := by
  decide +kernel

theorem node_context_11_17752_460215 : EJMOriginalGlobalDAGData.nodes 10 ⟨460215, by decide⟩ =
    .split (coordinate 11) (![⟨455939, by decide⟩,⟨455939, by decide⟩,⟨460152, by decide⟩,⟨460214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17752_460215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17752 ⟨460215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17752
    ⟨460215, by decide⟩ (by decide) (![⟨455939, by decide⟩,⟨455939, by decide⟩,⟨460152, by decide⟩,⟨460214, by decide⟩]) unmarked_context_11_17752_460215 node_context_11_17752_460215
  intro a
  fin_cases a
  · exact context_12_71008_455939
  · exact context_12_71009_455939
  · exact context_12_71010_460152
  · exact context_12_71011_460214

theorem selected_cut_17963 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 17753) = some ⟨11, 1, 0, 459416, 17753, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17753_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17753 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 17753 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 17753, 1, 262144⟩
    (by decide) selected_cut_17963

theorem selected_cut_17964 : selected 9 ⟨460274, by decide⟩
    (prefixPartial 12 71016) = some ⟨12, 2, 0, 460274, 71016, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_71016_460274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71016 ⟨460274, by decide⟩ :=
  accepted_of_selected 12 71016 ⟨460274, by decide⟩ ⟨12, 2, 0, 460274, 71016, 2985, 65536⟩
    (by decide) selected_cut_17964

theorem selected_cut_17965 : selected 9 ⟨460319, by decide⟩
    (prefixPartial 12 71017) = some ⟨12, 2, 0, 460319, 71017, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_71017_460319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71017 ⟨460319, by decide⟩ :=
  accepted_of_selected 12 71017 ⟨460319, by decide⟩ ⟨12, 2, 0, 460319, 71017, 2601, 65536⟩
    (by decide) selected_cut_17965

theorem selected_cut_17966 : selected 9 ⟨460367, by decide⟩
    (prefixPartial 12 71018) = some ⟨12, 2, 0, 460367, 71018, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_71018_460367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71018 ⟨460367, by decide⟩ :=
  accepted_of_selected 12 71018 ⟨460367, by decide⟩ ⟨12, 2, 0, 460367, 71018, 2593, 65536⟩
    (by decide) selected_cut_17966

theorem selected_cut_17967 : selected 9 ⟨460399, by decide⟩
    (prefixPartial 12 71019) = some ⟨12, 2, 0, 460399, 71019, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_71019_460399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71019 ⟨460399, by decide⟩ :=
  accepted_of_selected 12 71019 ⟨460399, by decide⟩ ⟨12, 2, 0, 460399, 71019, 2597, 65536⟩
    (by decide) selected_cut_17967

theorem unmarked_context_11_17754_460400 : frontier 10 ⟨460400, by decide⟩
    (prefixCache 11 17754) (prefixPartial 11 17754) = false := by
  decide +kernel

theorem node_context_11_17754_460400 : EJMOriginalGlobalDAGData.nodes 10 ⟨460400, by decide⟩ =
    .split (coordinate 11) (![⟨460274, by decide⟩,⟨460319, by decide⟩,⟨460367, by decide⟩,⟨460399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17754_460400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17754 ⟨460400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17754
    ⟨460400, by decide⟩ (by decide) (![⟨460274, by decide⟩,⟨460319, by decide⟩,⟨460367, by decide⟩,⟨460399, by decide⟩]) unmarked_context_11_17754_460400 node_context_11_17754_460400
  intro a
  fin_cases a
  · exact context_12_71016_460274
  · exact context_12_71017_460319
  · exact context_12_71018_460367
  · exact context_12_71019_460399

theorem selected_cut_17968 : selected 9 ⟨460451, by decide⟩
    (prefixPartial 12 71020) = some ⟨12, 2, 0, 460451, 71020, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_71020_460451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71020 ⟨460451, by decide⟩ :=
  accepted_of_selected 12 71020 ⟨460451, by decide⟩ ⟨12, 2, 0, 460451, 71020, 2425, 65536⟩
    (by decide) selected_cut_17968

theorem selected_cut_17969 : selected 9 ⟨460485, by decide⟩
    (prefixPartial 12 71021) = some ⟨12, 2, 0, 460485, 71021, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_71021_460485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71021 ⟨460485, by decide⟩ :=
  accepted_of_selected 12 71021 ⟨460485, by decide⟩ ⟨12, 2, 0, 460485, 71021, 2153, 65536⟩
    (by decide) selected_cut_17969

theorem selected_cut_17970 : selected 9 ⟨460523, by decide⟩
    (prefixPartial 12 71022) = some ⟨12, 2, 0, 460523, 71022, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_71022_460523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71022 ⟨460523, by decide⟩ :=
  accepted_of_selected 12 71022 ⟨460523, by decide⟩ ⟨12, 2, 0, 460523, 71022, 2045, 65536⟩
    (by decide) selected_cut_17970

theorem selected_cut_17971 : selected 9 ⟨460551, by decide⟩
    (prefixPartial 12 71023) = some ⟨12, 2, 0, 460551, 71023, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_71023_460551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71023 ⟨460551, by decide⟩ :=
  accepted_of_selected 12 71023 ⟨460551, by decide⟩ ⟨12, 2, 0, 460551, 71023, 1953, 65536⟩
    (by decide) selected_cut_17971

theorem unmarked_context_11_17755_460552 : frontier 10 ⟨460552, by decide⟩
    (prefixCache 11 17755) (prefixPartial 11 17755) = false := by
  decide +kernel

theorem node_context_11_17755_460552 : EJMOriginalGlobalDAGData.nodes 10 ⟨460552, by decide⟩ =
    .split (coordinate 11) (![⟨460451, by decide⟩,⟨460485, by decide⟩,⟨460523, by decide⟩,⟨460551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17755_460552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17755 ⟨460552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17755
    ⟨460552, by decide⟩ (by decide) (![⟨460451, by decide⟩,⟨460485, by decide⟩,⟨460523, by decide⟩,⟨460551, by decide⟩]) unmarked_context_11_17755_460552 node_context_11_17755_460552
  intro a
  fin_cases a
  · exact context_12_71020_460451
  · exact context_12_71021_460485
  · exact context_12_71022_460523
  · exact context_12_71023_460551

theorem unmarked_context_10_4438_460553 : frontier 11 ⟨460553, by decide⟩
    (prefixCache 10 4438) (prefixPartial 10 4438) = false := by
  decide +kernel

theorem node_context_10_4438_460553 : EJMOriginalGlobalDAGData.nodes 11 ⟨460553, by decide⟩ =
    .split (coordinate 10) (![⟨460215, by decide⟩,⟨459416, by decide⟩,⟨460400, by decide⟩,⟨460552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4438_460553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4438 ⟨460553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4438
    ⟨460553, by decide⟩ (by decide) (![⟨460215, by decide⟩,⟨459416, by decide⟩,⟨460400, by decide⟩,⟨460552, by decide⟩]) unmarked_context_10_4438_460553 node_context_10_4438_460553
  intro a
  fin_cases a
  · exact context_11_17752_460215
  · exact context_11_17753_459416
  · exact context_11_17754_460400
  · exact context_11_17755_460552

theorem selected_cut_17972 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4439) = some ⟨10, 1, 0, 3440, 4439, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4439_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4439 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4439 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4439, 1, 1048576⟩
    (by decide) selected_cut_17972

theorem unmarked_context_9_1109_460554 : frontier 12 ⟨460554, by decide⟩
    (prefixCache 9 1109) (prefixPartial 9 1109) = false := by
  decide +kernel

theorem node_context_9_1109_460554 : EJMOriginalGlobalDAGData.nodes 12 ⟨460554, by decide⟩ =
    .split (coordinate 9) (![⟨459766, by decide⟩,⟨460093, by decide⟩,⟨460553, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1109_460554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1109 ⟨460554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1109
    ⟨460554, by decide⟩ (by decide) (![⟨459766, by decide⟩,⟨460093, by decide⟩,⟨460553, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1109_460554 node_context_9_1109_460554
  intro a
  fin_cases a
  · exact context_10_4436_459766
  · exact context_10_4437_460093
  · exact context_10_4438_460553
  · exact context_10_4439_3440

theorem selected_cut_17973 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 17760) = some ⟨11, 1, 0, 459416, 17760, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17760_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17760 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 17760 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 17760, 1, 262144⟩
    (by decide) selected_cut_17973

theorem selected_cut_17974 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 17761) = some ⟨11, 1, 0, 459416, 17761, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17761_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17761 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 17761 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 17761, 1, 262144⟩
    (by decide) selected_cut_17974

theorem selected_cut_17975 : selected 9 ⟨460638, by decide⟩
    (prefixPartial 12 71048) = some ⟨12, 2, 0, 460638, 71048, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_71048_460638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71048 ⟨460638, by decide⟩ :=
  accepted_of_selected 12 71048 ⟨460638, by decide⟩ ⟨12, 2, 0, 460638, 71048, 1717, 65536⟩
    (by decide) selected_cut_17975

theorem selected_cut_17976 : selected 9 ⟨460687, by decide⟩
    (prefixPartial 12 71049) = some ⟨12, 2, 0, 460687, 71049, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_71049_460687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71049 ⟨460687, by decide⟩ :=
  accepted_of_selected 12 71049 ⟨460687, by decide⟩ ⟨12, 2, 0, 460687, 71049, 1009, 65536⟩
    (by decide) selected_cut_17976

theorem selected_cut_17977 : selected 9 ⟨460729, by decide⟩
    (prefixPartial 12 71050) = some ⟨12, 2, 0, 460729, 71050, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_71050_460729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71050 ⟨460729, by decide⟩ :=
  accepted_of_selected 12 71050 ⟨460729, by decide⟩ ⟨12, 2, 0, 460729, 71050, 1505, 65536⟩
    (by decide) selected_cut_17977

theorem selected_cut_17978 : selected 9 ⟨460770, by decide⟩
    (prefixPartial 12 71051) = some ⟨12, 2, 0, 460770, 71051, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_71051_460770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71051 ⟨460770, by decide⟩ :=
  accepted_of_selected 12 71051 ⟨460770, by decide⟩ ⟨12, 2, 0, 460770, 71051, 1481, 65536⟩
    (by decide) selected_cut_17978

theorem unmarked_context_11_17762_460771 : frontier 10 ⟨460771, by decide⟩
    (prefixCache 11 17762) (prefixPartial 11 17762) = false := by
  decide +kernel

theorem node_context_11_17762_460771 : EJMOriginalGlobalDAGData.nodes 10 ⟨460771, by decide⟩ =
    .split (coordinate 11) (![⟨460638, by decide⟩,⟨460687, by decide⟩,⟨460729, by decide⟩,⟨460770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17762_460771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17762 ⟨460771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17762
    ⟨460771, by decide⟩ (by decide) (![⟨460638, by decide⟩,⟨460687, by decide⟩,⟨460729, by decide⟩,⟨460770, by decide⟩]) unmarked_context_11_17762_460771 node_context_11_17762_460771
  intro a
  fin_cases a
  · exact context_12_71048_460638
  · exact context_12_71049_460687
  · exact context_12_71050_460729
  · exact context_12_71051_460770

theorem selected_cut_17979 : selected 9 ⟨460816, by decide⟩
    (prefixPartial 12 71052) = some ⟨12, 2, 0, 460816, 71052, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_71052_460816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71052 ⟨460816, by decide⟩ :=
  accepted_of_selected 12 71052 ⟨460816, by decide⟩ ⟨12, 2, 0, 460816, 71052, 1301, 65536⟩
    (by decide) selected_cut_17979

theorem selected_cut_17980 : selected 9 ⟨460862, by decide⟩
    (prefixPartial 12 71053) = some ⟨12, 2, 0, 460862, 71053, 761, 65536⟩ := by
  decide +kernel

theorem context_12_71053_460862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71053 ⟨460862, by decide⟩ :=
  accepted_of_selected 12 71053 ⟨460862, by decide⟩ ⟨12, 2, 0, 460862, 71053, 761, 65536⟩
    (by decide) selected_cut_17980

theorem selected_cut_17981 : selected 9 ⟨460893, by decide⟩
    (prefixPartial 12 71054) = some ⟨12, 2, 0, 460893, 71054, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_71054_460893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71054 ⟨460893, by decide⟩ :=
  accepted_of_selected 12 71054 ⟨460893, by decide⟩ ⟨12, 2, 0, 460893, 71054, 1133, 65536⟩
    (by decide) selected_cut_17981

theorem selected_cut_17982 : selected 9 ⟨460913, by decide⟩
    (prefixPartial 12 71055) = some ⟨12, 2, 0, 460913, 71055, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_71055_460913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71055 ⟨460913, by decide⟩ :=
  accepted_of_selected 12 71055 ⟨460913, by decide⟩ ⟨12, 2, 0, 460913, 71055, 1077, 65536⟩
    (by decide) selected_cut_17982

theorem unmarked_context_11_17763_460914 : frontier 10 ⟨460914, by decide⟩
    (prefixCache 11 17763) (prefixPartial 11 17763) = false := by
  decide +kernel

theorem node_context_11_17763_460914 : EJMOriginalGlobalDAGData.nodes 10 ⟨460914, by decide⟩ =
    .split (coordinate 11) (![⟨460816, by decide⟩,⟨460862, by decide⟩,⟨460893, by decide⟩,⟨460913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17763_460914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17763 ⟨460914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17763
    ⟨460914, by decide⟩ (by decide) (![⟨460816, by decide⟩,⟨460862, by decide⟩,⟨460893, by decide⟩,⟨460913, by decide⟩]) unmarked_context_11_17763_460914 node_context_11_17763_460914
  intro a
  fin_cases a
  · exact context_12_71052_460816
  · exact context_12_71053_460862
  · exact context_12_71054_460893
  · exact context_12_71055_460913

theorem unmarked_context_10_4440_460915 : frontier 11 ⟨460915, by decide⟩
    (prefixCache 10 4440) (prefixPartial 10 4440) = false := by
  decide +kernel

theorem node_context_10_4440_460915 : EJMOriginalGlobalDAGData.nodes 11 ⟨460915, by decide⟩ =
    .split (coordinate 10) (![⟨459416, by decide⟩,⟨459416, by decide⟩,⟨460771, by decide⟩,⟨460914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4440_460915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4440 ⟨460915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4440
    ⟨460915, by decide⟩ (by decide) (![⟨459416, by decide⟩,⟨459416, by decide⟩,⟨460771, by decide⟩,⟨460914, by decide⟩]) unmarked_context_10_4440_460915 node_context_10_4440_460915
  intro a
  fin_cases a
  · exact context_11_17760_459416
  · exact context_11_17761_459416
  · exact context_11_17762_460771
  · exact context_11_17763_460914

theorem selected_cut_17983 : selected 11 ⟨461146, by decide⟩
    (prefixPartial 10 4441) = some ⟨10, 2, 0, 461146, 4441, 4049, 1048576⟩ := by
  decide +kernel

theorem context_10_4441_461146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4441 ⟨461146, by decide⟩ :=
  accepted_of_selected 10 4441 ⟨461146, by decide⟩ ⟨10, 2, 0, 461146, 4441, 4049, 1048576⟩
    (by decide) selected_cut_17983

theorem selected_cut_17984 : selected 11 ⟨461231, by decide⟩
    (prefixPartial 10 4442) = some ⟨10, 2, 0, 461231, 4442, 877, 1048576⟩ := by
  decide +kernel

theorem context_10_4442_461231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4442 ⟨461231, by decide⟩ :=
  accepted_of_selected 10 4442 ⟨461231, by decide⟩ ⟨10, 2, 0, 461231, 4442, 877, 1048576⟩
    (by decide) selected_cut_17984

theorem selected_cut_17985 : selected 11 ⟨461250, by decide⟩
    (prefixPartial 10 4443) = some ⟨10, 2, 0, 461250, 4443, 145, 1048576⟩ := by
  decide +kernel

theorem context_10_4443_461250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4443 ⟨461250, by decide⟩ :=
  accepted_of_selected 10 4443 ⟨461250, by decide⟩ ⟨10, 2, 0, 461250, 4443, 145, 1048576⟩
    (by decide) selected_cut_17985

theorem unmarked_context_9_1110_461251 : frontier 12 ⟨461251, by decide⟩
    (prefixCache 9 1110) (prefixPartial 9 1110) = false := by
  decide +kernel

theorem node_context_9_1110_461251 : EJMOriginalGlobalDAGData.nodes 12 ⟨461251, by decide⟩ =
    .split (coordinate 9) (![⟨460915, by decide⟩,⟨461146, by decide⟩,⟨461231, by decide⟩,⟨461250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1110_461251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1110 ⟨461251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1110
    ⟨461251, by decide⟩ (by decide) (![⟨460915, by decide⟩,⟨461146, by decide⟩,⟨461231, by decide⟩,⟨461250, by decide⟩]) unmarked_context_9_1110_461251 node_context_9_1110_461251
  intro a
  fin_cases a
  · exact context_10_4440_460915
  · exact context_10_4441_461146
  · exact context_10_4442_461231
  · exact context_10_4443_461250

theorem selected_cut_17986 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 1111) = some ⟨9, 1, 0, 4601, 1111, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_1111_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1111 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 1111 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 1111, 1, 4194304⟩
    (by decide) selected_cut_17986

theorem unmarked_context_8_277_461252 : frontier 13 ⟨461252, by decide⟩
    (prefixCache 8 277) (prefixPartial 8 277) = false := by
  decide +kernel

theorem node_context_8_277_461252 : EJMOriginalGlobalDAGData.nodes 13 ⟨461252, by decide⟩ =
    .split (coordinate 8) (![⟨459106, by decide⟩,⟨460554, by decide⟩,⟨461251, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_277_461252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 277 ⟨461252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 277
    ⟨461252, by decide⟩ (by decide) (![⟨459106, by decide⟩,⟨460554, by decide⟩,⟨461251, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_277_461252 node_context_8_277_461252
  intro a
  fin_cases a
  · exact context_9_1108_459106
  · exact context_9_1109_460554
  · exact context_9_1110_461251
  · exact context_9_1111_4601

theorem selected_cut_17987 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17792) = some ⟨11, 1, 0, 434745, 17792, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17792_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17792 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17792 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17792, 1, 262144⟩
    (by decide) selected_cut_17987

theorem selected_cut_17988 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71172) = some ⟨12, 1, 0, 448748, 71172, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71172_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71172 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71172 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71172, 1, 65536⟩
    (by decide) selected_cut_17988

theorem selected_cut_17989 : selected 8 ⟨461323, by decide⟩
    (prefixPartial 13 284692) = some ⟨13, 2, 0, 461323, 284692, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_284692_461323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284692 ⟨461323, by decide⟩ :=
  accepted_of_selected 13 284692 ⟨461323, by decide⟩ ⟨13, 2, 0, 461323, 284692, 2949, 16384⟩
    (by decide) selected_cut_17989

theorem selected_cut_17990 : selected 8 ⟨461356, by decide⟩
    (prefixPartial 13 284693) = some ⟨13, 2, 0, 461356, 284693, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_284693_461356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284693 ⟨461356, by decide⟩ :=
  accepted_of_selected 13 284693 ⟨461356, by decide⟩ ⟨13, 2, 0, 461356, 284693, 2317, 16384⟩
    (by decide) selected_cut_17990

theorem selected_cut_17991 : selected 8 ⟨461376, by decide⟩
    (prefixPartial 13 284694) = some ⟨13, 2, 0, 461376, 284694, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_284694_461376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284694 ⟨461376, by decide⟩ :=
  accepted_of_selected 13 284694 ⟨461376, by decide⟩ ⟨13, 2, 0, 461376, 284694, 1425, 16384⟩
    (by decide) selected_cut_17991

theorem selected_cut_17992 : selected 8 ⟨461390, by decide⟩
    (prefixPartial 13 284695) = some ⟨13, 2, 0, 461390, 284695, 993, 16384⟩ := by
  decide +kernel

theorem context_13_284695_461390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284695 ⟨461390, by decide⟩ :=
  accepted_of_selected 13 284695 ⟨461390, by decide⟩ ⟨13, 2, 0, 461390, 284695, 993, 16384⟩
    (by decide) selected_cut_17992

theorem unmarked_context_12_71173_461391 : frontier 9 ⟨461391, by decide⟩
    (prefixCache 12 71173) (prefixPartial 12 71173) = false := by
  decide +kernel

theorem node_context_12_71173_461391 : EJMOriginalGlobalDAGData.nodes 9 ⟨461391, by decide⟩ =
    .split (coordinate 12) (![⟨461323, by decide⟩,⟨461356, by decide⟩,⟨461376, by decide⟩,⟨461390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71173_461391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71173 ⟨461391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71173
    ⟨461391, by decide⟩ (by decide) (![⟨461323, by decide⟩,⟨461356, by decide⟩,⟨461376, by decide⟩,⟨461390, by decide⟩]) unmarked_context_12_71173_461391 node_context_12_71173_461391
  intro a
  fin_cases a
  · exact context_13_284692_461323
  · exact context_13_284693_461356
  · exact context_13_284694_461376
  · exact context_13_284695_461390

theorem selected_cut_17993 : selected 8 ⟨461459, by decide⟩
    (prefixPartial 13 284696) = some ⟨13, 2, 0, 461459, 284696, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_284696_461459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284696 ⟨461459, by decide⟩ :=
  accepted_of_selected 13 284696 ⟨461459, by decide⟩ ⟨13, 2, 0, 461459, 284696, 3041, 16384⟩
    (by decide) selected_cut_17993

theorem selected_cut_17994 : selected 8 ⟨461487, by decide⟩
    (prefixPartial 13 284697) = some ⟨13, 2, 0, 461487, 284697, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_284697_461487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284697 ⟨461487, by decide⟩ :=
  accepted_of_selected 13 284697 ⟨461487, by decide⟩ ⟨13, 2, 0, 461487, 284697, 2457, 16384⟩
    (by decide) selected_cut_17994

theorem selected_cut_17995 : selected 8 ⟨461509, by decide⟩
    (prefixPartial 13 284698) = some ⟨13, 2, 0, 461509, 284698, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_284698_461509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284698 ⟨461509, by decide⟩ :=
  accepted_of_selected 13 284698 ⟨461509, by decide⟩ ⟨13, 2, 0, 461509, 284698, 1621, 16384⟩
    (by decide) selected_cut_17995

theorem selected_cut_17996 : selected 8 ⟨461525, by decide⟩
    (prefixPartial 13 284699) = some ⟨13, 2, 0, 461525, 284699, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_284699_461525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284699 ⟨461525, by decide⟩ :=
  accepted_of_selected 13 284699 ⟨461525, by decide⟩ ⟨13, 2, 0, 461525, 284699, 1125, 16384⟩
    (by decide) selected_cut_17996

theorem unmarked_context_12_71174_461526 : frontier 9 ⟨461526, by decide⟩
    (prefixCache 12 71174) (prefixPartial 12 71174) = false := by
  decide +kernel

theorem node_context_12_71174_461526 : EJMOriginalGlobalDAGData.nodes 9 ⟨461526, by decide⟩ =
    .split (coordinate 12) (![⟨461459, by decide⟩,⟨461487, by decide⟩,⟨461509, by decide⟩,⟨461525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71174_461526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71174 ⟨461526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71174
    ⟨461526, by decide⟩ (by decide) (![⟨461459, by decide⟩,⟨461487, by decide⟩,⟨461509, by decide⟩,⟨461525, by decide⟩]) unmarked_context_12_71174_461526 node_context_12_71174_461526
  intro a
  fin_cases a
  · exact context_13_284696_461459
  · exact context_13_284697_461487
  · exact context_13_284698_461509
  · exact context_13_284699_461525

theorem selected_cut_17997 : selected 8 ⟨461606, by decide⟩
    (prefixPartial 13 284700) = some ⟨13, 2, 0, 461606, 284700, 3609, 16384⟩ := by
  decide +kernel

theorem context_13_284700_461606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284700 ⟨461606, by decide⟩ :=
  accepted_of_selected 13 284700 ⟨461606, by decide⟩ ⟨13, 2, 0, 461606, 284700, 3609, 16384⟩
    (by decide) selected_cut_17997

theorem selected_cut_17998 : selected 8 ⟨461641, by decide⟩
    (prefixPartial 13 284701) = some ⟨13, 2, 0, 461641, 284701, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_284701_461641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284701 ⟨461641, by decide⟩ :=
  accepted_of_selected 13 284701 ⟨461641, by decide⟩ ⟨13, 2, 0, 461641, 284701, 2533, 16384⟩
    (by decide) selected_cut_17998

theorem selected_cut_17999 : selected 8 ⟨461663, by decide⟩
    (prefixPartial 13 284702) = some ⟨13, 2, 0, 461663, 284702, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_284702_461663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284702 ⟨461663, by decide⟩ :=
  accepted_of_selected 13 284702 ⟨461663, by decide⟩ ⟨13, 2, 0, 461663, 284702, 1725, 16384⟩
    (by decide) selected_cut_17999

theorem selected_cut_18000 : selected 8 ⟨461674, by decide⟩
    (prefixPartial 13 284703) = some ⟨13, 2, 0, 461674, 284703, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_284703_461674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284703 ⟨461674, by decide⟩ :=
  accepted_of_selected 13 284703 ⟨461674, by decide⟩ ⟨13, 2, 0, 461674, 284703, 1089, 16384⟩
    (by decide) selected_cut_18000

theorem unmarked_context_12_71175_461675 : frontier 9 ⟨461675, by decide⟩
    (prefixCache 12 71175) (prefixPartial 12 71175) = false := by
  decide +kernel

theorem node_context_12_71175_461675 : EJMOriginalGlobalDAGData.nodes 9 ⟨461675, by decide⟩ =
    .split (coordinate 12) (![⟨461606, by decide⟩,⟨461641, by decide⟩,⟨461663, by decide⟩,⟨461674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71175_461675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71175 ⟨461675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71175
    ⟨461675, by decide⟩ (by decide) (![⟨461606, by decide⟩,⟨461641, by decide⟩,⟨461663, by decide⟩,⟨461674, by decide⟩]) unmarked_context_12_71175_461675 node_context_12_71175_461675
  intro a
  fin_cases a
  · exact context_13_284700_461606
  · exact context_13_284701_461641
  · exact context_13_284702_461663
  · exact context_13_284703_461674

theorem unmarked_context_11_17793_461676 : frontier 10 ⟨461676, by decide⟩
    (prefixCache 11 17793) (prefixPartial 11 17793) = false := by
  decide +kernel

theorem node_context_11_17793_461676 : EJMOriginalGlobalDAGData.nodes 10 ⟨461676, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨461391, by decide⟩,⟨461526, by decide⟩,⟨461675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17793_461676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17793 ⟨461676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17793
    ⟨461676, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨461391, by decide⟩,⟨461526, by decide⟩,⟨461675, by decide⟩]) unmarked_context_11_17793_461676 node_context_11_17793_461676
  intro a
  fin_cases a
  · exact context_12_71172_448748
  · exact context_12_71173_461391
  · exact context_12_71174_461526
  · exact context_12_71175_461675

theorem selected_cut_18001 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71176) = some ⟨12, 1, 0, 448748, 71176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71176_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71176 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71176 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71176, 1, 65536⟩
    (by decide) selected_cut_18001

theorem selected_cut_18002 : selected 8 ⟨461745, by decide⟩
    (prefixPartial 13 284708) = some ⟨13, 2, 0, 461745, 284708, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_284708_461745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284708 ⟨461745, by decide⟩ :=
  accepted_of_selected 13 284708 ⟨461745, by decide⟩ ⟨13, 2, 0, 461745, 284708, 2865, 16384⟩
    (by decide) selected_cut_18002

theorem selected_cut_18003 : selected 8 ⟨461782, by decide⟩
    (prefixPartial 13 284709) = some ⟨13, 2, 0, 461782, 284709, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_284709_461782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284709 ⟨461782, by decide⟩ :=
  accepted_of_selected 13 284709 ⟨461782, by decide⟩ ⟨13, 2, 0, 461782, 284709, 2593, 16384⟩
    (by decide) selected_cut_18003

theorem selected_cut_18004 : selected 8 ⟨461802, by decide⟩
    (prefixPartial 13 284710) = some ⟨13, 2, 0, 461802, 284710, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_284710_461802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284710 ⟨461802, by decide⟩ :=
  accepted_of_selected 13 284710 ⟨461802, by decide⟩ ⟨13, 2, 0, 461802, 284710, 1505, 16384⟩
    (by decide) selected_cut_18004

theorem selected_cut_18005 : selected 8 ⟨461817, by decide⟩
    (prefixPartial 13 284711) = some ⟨13, 2, 0, 461817, 284711, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_284711_461817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284711 ⟨461817, by decide⟩ :=
  accepted_of_selected 13 284711 ⟨461817, by decide⟩ ⟨13, 2, 0, 461817, 284711, 1073, 16384⟩
    (by decide) selected_cut_18005

theorem unmarked_context_12_71177_461818 : frontier 9 ⟨461818, by decide⟩
    (prefixCache 12 71177) (prefixPartial 12 71177) = false := by
  decide +kernel

theorem node_context_12_71177_461818 : EJMOriginalGlobalDAGData.nodes 9 ⟨461818, by decide⟩ =
    .split (coordinate 12) (![⟨461745, by decide⟩,⟨461782, by decide⟩,⟨461802, by decide⟩,⟨461817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71177_461818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71177 ⟨461818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71177
    ⟨461818, by decide⟩ (by decide) (![⟨461745, by decide⟩,⟨461782, by decide⟩,⟨461802, by decide⟩,⟨461817, by decide⟩]) unmarked_context_12_71177_461818 node_context_12_71177_461818
  intro a
  fin_cases a
  · exact context_13_284708_461745
  · exact context_13_284709_461782
  · exact context_13_284710_461802
  · exact context_13_284711_461817

theorem selected_cut_18006 : selected 7 ⟨461842, by decide⟩
    (prefixPartial 14 1138848) = some ⟨14, 2, 0, 461842, 1138848, 789, 4096⟩ := by
  decide +kernel

theorem context_14_1138848_461842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138848 ⟨461842, by decide⟩ :=
  accepted_of_selected 14 1138848 ⟨461842, by decide⟩ ⟨14, 2, 0, 461842, 1138848, 789, 4096⟩
    (by decide) selected_cut_18006

theorem selected_cut_18007 : selected 7 ⟨461884, by decide⟩
    (prefixPartial 14 1138849) = some ⟨14, 2, 0, 461884, 1138849, 1657, 4096⟩ := by
  decide +kernel

theorem context_14_1138849_461884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138849 ⟨461884, by decide⟩ :=
  accepted_of_selected 14 1138849 ⟨461884, by decide⟩ ⟨14, 2, 0, 461884, 1138849, 1657, 4096⟩
    (by decide) selected_cut_18007

theorem selected_cut_18008 : selected 7 ⟨461913, by decide⟩
    (prefixPartial 14 1138850) = some ⟨14, 2, 0, 461913, 1138850, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_1138850_461913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138850 ⟨461913, by decide⟩ :=
  accepted_of_selected 14 1138850 ⟨461913, by decide⟩ ⟨14, 2, 0, 461913, 1138850, 1265, 4096⟩
    (by decide) selected_cut_18008

theorem selected_cut_18009 : selected 7 ⟨461945, by decide⟩
    (prefixPartial 14 1138851) = some ⟨14, 2, 0, 461945, 1138851, 1613, 4096⟩ := by
  decide +kernel

theorem context_14_1138851_461945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138851 ⟨461945, by decide⟩ :=
  accepted_of_selected 14 1138851 ⟨461945, by decide⟩ ⟨14, 2, 0, 461945, 1138851, 1613, 4096⟩
    (by decide) selected_cut_18009

theorem unmarked_context_13_284712_461946 : frontier 8 ⟨461946, by decide⟩
    (prefixCache 13 284712) (prefixPartial 13 284712) = false := by
  decide +kernel

theorem node_context_13_284712_461946 : EJMOriginalGlobalDAGData.nodes 8 ⟨461946, by decide⟩ =
    .split (coordinate 13) (![⟨461842, by decide⟩,⟨461884, by decide⟩,⟨461913, by decide⟩,⟨461945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_284712_461946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284712 ⟨461946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 284712
    ⟨461946, by decide⟩ (by decide) (![⟨461842, by decide⟩,⟨461884, by decide⟩,⟨461913, by decide⟩,⟨461945, by decide⟩]) unmarked_context_13_284712_461946 node_context_13_284712_461946
  intro a
  fin_cases a
  · exact context_14_1138848_461842
  · exact context_14_1138849_461884
  · exact context_14_1138850_461913
  · exact context_14_1138851_461945

theorem selected_cut_18010 : selected 7 ⟨461964, by decide⟩
    (prefixPartial 14 1138852) = some ⟨14, 2, 0, 461964, 1138852, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_1138852_461964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138852 ⟨461964, by decide⟩ :=
  accepted_of_selected 14 1138852 ⟨461964, by decide⟩ ⟨14, 2, 0, 461964, 1138852, 1009, 4096⟩
    (by decide) selected_cut_18010

theorem selected_cut_18011 : selected 7 ⟨461990, by decide⟩
    (prefixPartial 14 1138853) = some ⟨14, 2, 0, 461990, 1138853, 921, 4096⟩ := by
  decide +kernel

theorem context_14_1138853_461990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138853 ⟨461990, by decide⟩ :=
  accepted_of_selected 14 1138853 ⟨461990, by decide⟩ ⟨14, 2, 0, 461990, 1138853, 921, 4096⟩
    (by decide) selected_cut_18011

theorem selected_cut_18012 : selected 7 ⟨462028, by decide⟩
    (prefixPartial 14 1138854) = some ⟨14, 2, 0, 462028, 1138854, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_1138854_462028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138854 ⟨462028, by decide⟩ :=
  accepted_of_selected 14 1138854 ⟨462028, by decide⟩ ⟨14, 2, 0, 462028, 1138854, 1269, 4096⟩
    (by decide) selected_cut_18012

theorem selected_cut_18013 : selected 7 ⟨462056, by decide⟩
    (prefixPartial 14 1138855) = some ⟨14, 2, 0, 462056, 1138855, 1165, 4096⟩ := by
  decide +kernel

theorem context_14_1138855_462056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1138855 ⟨462056, by decide⟩ :=
  accepted_of_selected 14 1138855 ⟨462056, by decide⟩ ⟨14, 2, 0, 462056, 1138855, 1165, 4096⟩
    (by decide) selected_cut_18013

theorem unmarked_context_13_284713_462057 : frontier 8 ⟨462057, by decide⟩
    (prefixCache 13 284713) (prefixPartial 13 284713) = false := by
  decide +kernel

theorem node_context_13_284713_462057 : EJMOriginalGlobalDAGData.nodes 8 ⟨462057, by decide⟩ =
    .split (coordinate 13) (![⟨461964, by decide⟩,⟨461990, by decide⟩,⟨462028, by decide⟩,⟨462056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_284713_462057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284713 ⟨462057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 284713
    ⟨462057, by decide⟩ (by decide) (![⟨461964, by decide⟩,⟨461990, by decide⟩,⟨462028, by decide⟩,⟨462056, by decide⟩]) unmarked_context_13_284713_462057 node_context_13_284713_462057
  intro a
  fin_cases a
  · exact context_14_1138852_461964
  · exact context_14_1138853_461990
  · exact context_14_1138854_462028
  · exact context_14_1138855_462056

theorem selected_cut_18014 : selected 8 ⟨462103, by decide⟩
    (prefixPartial 13 284714) = some ⟨13, 2, 0, 462103, 284714, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_284714_462103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284714 ⟨462103, by decide⟩ :=
  accepted_of_selected 13 284714 ⟨462103, by decide⟩ ⟨13, 2, 0, 462103, 284714, 2433, 16384⟩
    (by decide) selected_cut_18014

theorem selected_cut_18015 : selected 8 ⟨462145, by decide⟩
    (prefixPartial 13 284715) = some ⟨13, 2, 0, 462145, 284715, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_284715_462145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284715 ⟨462145, by decide⟩ :=
  accepted_of_selected 13 284715 ⟨462145, by decide⟩ ⟨13, 2, 0, 462145, 284715, 1561, 16384⟩
    (by decide) selected_cut_18015

theorem unmarked_context_12_71178_462146 : frontier 9 ⟨462146, by decide⟩
    (prefixCache 12 71178) (prefixPartial 12 71178) = false := by
  decide +kernel

theorem node_context_12_71178_462146 : EJMOriginalGlobalDAGData.nodes 9 ⟨462146, by decide⟩ =
    .split (coordinate 12) (![⟨461946, by decide⟩,⟨462057, by decide⟩,⟨462103, by decide⟩,⟨462145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71178_462146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71178 ⟨462146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71178
    ⟨462146, by decide⟩ (by decide) (![⟨461946, by decide⟩,⟨462057, by decide⟩,⟨462103, by decide⟩,⟨462145, by decide⟩]) unmarked_context_12_71178_462146 node_context_12_71178_462146
  intro a
  fin_cases a
  · exact context_13_284712_461946
  · exact context_13_284713_462057
  · exact context_13_284714_462103
  · exact context_13_284715_462145

theorem selected_cut_18016 : selected 8 ⟨462225, by decide⟩
    (prefixPartial 13 284716) = some ⟨13, 2, 0, 462225, 284716, 3445, 16384⟩ := by
  decide +kernel

theorem context_13_284716_462225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284716 ⟨462225, by decide⟩ :=
  accepted_of_selected 13 284716 ⟨462225, by decide⟩ ⟨13, 2, 0, 462225, 284716, 3445, 16384⟩
    (by decide) selected_cut_18016

theorem selected_cut_18017 : selected 8 ⟨462275, by decide⟩
    (prefixPartial 13 284717) = some ⟨13, 2, 0, 462275, 284717, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_284717_462275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284717 ⟨462275, by decide⟩ :=
  accepted_of_selected 13 284717 ⟨462275, by decide⟩ ⟨13, 2, 0, 462275, 284717, 3117, 16384⟩
    (by decide) selected_cut_18017

theorem selected_cut_18018 : selected 8 ⟨462295, by decide⟩
    (prefixPartial 13 284718) = some ⟨13, 2, 0, 462295, 284718, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_284718_462295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284718 ⟨462295, by decide⟩ :=
  accepted_of_selected 13 284718 ⟨462295, by decide⟩ ⟨13, 2, 0, 462295, 284718, 1657, 16384⟩
    (by decide) selected_cut_18018

theorem selected_cut_18019 : selected 8 ⟨462307, by decide⟩
    (prefixPartial 13 284719) = some ⟨13, 2, 0, 462307, 284719, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_284719_462307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284719 ⟨462307, by decide⟩ :=
  accepted_of_selected 13 284719 ⟨462307, by decide⟩ ⟨13, 2, 0, 462307, 284719, 1021, 16384⟩
    (by decide) selected_cut_18019

theorem unmarked_context_12_71179_462308 : frontier 9 ⟨462308, by decide⟩
    (prefixCache 12 71179) (prefixPartial 12 71179) = false := by
  decide +kernel

theorem node_context_12_71179_462308 : EJMOriginalGlobalDAGData.nodes 9 ⟨462308, by decide⟩ =
    .split (coordinate 12) (![⟨462225, by decide⟩,⟨462275, by decide⟩,⟨462295, by decide⟩,⟨462307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71179_462308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71179 ⟨462308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71179
    ⟨462308, by decide⟩ (by decide) (![⟨462225, by decide⟩,⟨462275, by decide⟩,⟨462295, by decide⟩,⟨462307, by decide⟩]) unmarked_context_12_71179_462308 node_context_12_71179_462308
  intro a
  fin_cases a
  · exact context_13_284716_462225
  · exact context_13_284717_462275
  · exact context_13_284718_462295
  · exact context_13_284719_462307

theorem unmarked_context_11_17794_462309 : frontier 10 ⟨462309, by decide⟩
    (prefixCache 11 17794) (prefixPartial 11 17794) = false := by
  decide +kernel

theorem node_context_11_17794_462309 : EJMOriginalGlobalDAGData.nodes 10 ⟨462309, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨461818, by decide⟩,⟨462146, by decide⟩,⟨462308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17794_462309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17794 ⟨462309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17794
    ⟨462309, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨461818, by decide⟩,⟨462146, by decide⟩,⟨462308, by decide⟩]) unmarked_context_11_17794_462309 node_context_11_17794_462309
  intro a
  fin_cases a
  · exact context_12_71176_448748
  · exact context_12_71177_461818
  · exact context_12_71178_462146
  · exact context_12_71179_462308

theorem selected_cut_18020 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71180) = some ⟨12, 1, 0, 448748, 71180, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71180_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71180 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71180 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71180, 1, 65536⟩
    (by decide) selected_cut_18020

theorem selected_cut_18021 : selected 8 ⟨462366, by decide⟩
    (prefixPartial 13 284724) = some ⟨13, 2, 0, 462366, 284724, 2845, 16384⟩ := by
  decide +kernel

theorem context_13_284724_462366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284724 ⟨462366, by decide⟩ :=
  accepted_of_selected 13 284724 ⟨462366, by decide⟩ ⟨13, 2, 0, 462366, 284724, 2845, 16384⟩
    (by decide) selected_cut_18021

theorem selected_cut_18022 : selected 8 ⟨462416, by decide⟩
    (prefixPartial 13 284725) = some ⟨13, 2, 0, 462416, 284725, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_284725_462416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284725 ⟨462416, by decide⟩ :=
  accepted_of_selected 13 284725 ⟨462416, by decide⟩ ⟨13, 2, 0, 462416, 284725, 2913, 16384⟩
    (by decide) selected_cut_18022

theorem selected_cut_18023 : selected 8 ⟨462433, by decide⟩
    (prefixPartial 13 284726) = some ⟨13, 2, 0, 462433, 284726, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_284726_462433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284726 ⟨462433, by decide⟩ :=
  accepted_of_selected 13 284726 ⟨462433, by decide⟩ ⟨13, 2, 0, 462433, 284726, 1489, 16384⟩
    (by decide) selected_cut_18023

theorem selected_cut_18024 : selected 8 ⟨462446, by decide⟩
    (prefixPartial 13 284727) = some ⟨13, 2, 0, 462446, 284727, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_284727_462446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284727 ⟨462446, by decide⟩ :=
  accepted_of_selected 13 284727 ⟨462446, by decide⟩ ⟨13, 2, 0, 462446, 284727, 1081, 16384⟩
    (by decide) selected_cut_18024

theorem unmarked_context_12_71181_462447 : frontier 9 ⟨462447, by decide⟩
    (prefixCache 12 71181) (prefixPartial 12 71181) = false := by
  decide +kernel

theorem node_context_12_71181_462447 : EJMOriginalGlobalDAGData.nodes 9 ⟨462447, by decide⟩ =
    .split (coordinate 12) (![⟨462366, by decide⟩,⟨462416, by decide⟩,⟨462433, by decide⟩,⟨462446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71181_462447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71181 ⟨462447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71181
    ⟨462447, by decide⟩ (by decide) (![⟨462366, by decide⟩,⟨462416, by decide⟩,⟨462433, by decide⟩,⟨462446, by decide⟩]) unmarked_context_12_71181_462447 node_context_12_71181_462447
  intro a
  fin_cases a
  · exact context_13_284724_462366
  · exact context_13_284725_462416
  · exact context_13_284726_462433
  · exact context_13_284727_462446

theorem selected_cut_18025 : selected 8 ⟨462507, by decide⟩
    (prefixPartial 13 284728) = some ⟨13, 2, 0, 462507, 284728, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_284728_462507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284728 ⟨462507, by decide⟩ :=
  accepted_of_selected 13 284728 ⟨462507, by decide⟩ ⟨13, 2, 0, 462507, 284728, 2813, 16384⟩
    (by decide) selected_cut_18025

theorem selected_cut_18026 : selected 8 ⟨462546, by decide⟩
    (prefixPartial 13 284729) = some ⟨13, 2, 0, 462546, 284729, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_284729_462546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284729 ⟨462546, by decide⟩ :=
  accepted_of_selected 13 284729 ⟨462546, by decide⟩ ⟨13, 2, 0, 462546, 284729, 3061, 16384⟩
    (by decide) selected_cut_18026

theorem selected_cut_18027 : selected 8 ⟨462568, by decide⟩
    (prefixPartial 13 284730) = some ⟨13, 2, 0, 462568, 284730, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_284730_462568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284730 ⟨462568, by decide⟩ :=
  accepted_of_selected 13 284730 ⟨462568, by decide⟩ ⟨13, 2, 0, 462568, 284730, 1641, 16384⟩
    (by decide) selected_cut_18027

theorem selected_cut_18028 : selected 8 ⟨462577, by decide⟩
    (prefixPartial 13 284731) = some ⟨13, 2, 0, 462577, 284731, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_284731_462577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284731 ⟨462577, by decide⟩ :=
  accepted_of_selected 13 284731 ⟨462577, by decide⟩ ⟨13, 2, 0, 462577, 284731, 1073, 16384⟩
    (by decide) selected_cut_18028

theorem unmarked_context_12_71182_462578 : frontier 9 ⟨462578, by decide⟩
    (prefixCache 12 71182) (prefixPartial 12 71182) = false := by
  decide +kernel

theorem node_context_12_71182_462578 : EJMOriginalGlobalDAGData.nodes 9 ⟨462578, by decide⟩ =
    .split (coordinate 12) (![⟨462507, by decide⟩,⟨462546, by decide⟩,⟨462568, by decide⟩,⟨462577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71182_462578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71182 ⟨462578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71182
    ⟨462578, by decide⟩ (by decide) (![⟨462507, by decide⟩,⟨462546, by decide⟩,⟨462568, by decide⟩,⟨462577, by decide⟩]) unmarked_context_12_71182_462578 node_context_12_71182_462578
  intro a
  fin_cases a
  · exact context_13_284728_462507
  · exact context_13_284729_462546
  · exact context_13_284730_462568
  · exact context_13_284731_462577

theorem selected_cut_18029 : selected 8 ⟨462644, by decide⟩
    (prefixPartial 13 284732) = some ⟨13, 2, 0, 462644, 284732, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_284732_462644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284732 ⟨462644, by decide⟩ :=
  accepted_of_selected 13 284732 ⟨462644, by decide⟩ ⟨13, 2, 0, 462644, 284732, 3389, 16384⟩
    (by decide) selected_cut_18029

theorem selected_cut_18030 : selected 8 ⟨462694, by decide⟩
    (prefixPartial 13 284733) = some ⟨13, 2, 0, 462694, 284733, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_284733_462694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284733 ⟨462694, by decide⟩ :=
  accepted_of_selected 13 284733 ⟨462694, by decide⟩ ⟨13, 2, 0, 462694, 284733, 3165, 16384⟩
    (by decide) selected_cut_18030

theorem selected_cut_18031 : selected 8 ⟨462713, by decide⟩
    (prefixPartial 13 284734) = some ⟨13, 2, 0, 462713, 284734, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_284734_462713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284734 ⟨462713, by decide⟩ :=
  accepted_of_selected 13 284734 ⟨462713, by decide⟩ ⟨13, 2, 0, 462713, 284734, 1733, 16384⟩
    (by decide) selected_cut_18031

theorem selected_cut_18032 : selected 8 ⟨462722, by decide⟩
    (prefixPartial 13 284735) = some ⟨13, 2, 0, 462722, 284735, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_284735_462722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284735 ⟨462722, by decide⟩ :=
  accepted_of_selected 13 284735 ⟨462722, by decide⟩ ⟨13, 2, 0, 462722, 284735, 1049, 16384⟩
    (by decide) selected_cut_18032

theorem unmarked_context_12_71183_462723 : frontier 9 ⟨462723, by decide⟩
    (prefixCache 12 71183) (prefixPartial 12 71183) = false := by
  decide +kernel

theorem node_context_12_71183_462723 : EJMOriginalGlobalDAGData.nodes 9 ⟨462723, by decide⟩ =
    .split (coordinate 12) (![⟨462644, by decide⟩,⟨462694, by decide⟩,⟨462713, by decide⟩,⟨462722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71183_462723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71183 ⟨462723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71183
    ⟨462723, by decide⟩ (by decide) (![⟨462644, by decide⟩,⟨462694, by decide⟩,⟨462713, by decide⟩,⟨462722, by decide⟩]) unmarked_context_12_71183_462723 node_context_12_71183_462723
  intro a
  fin_cases a
  · exact context_13_284732_462644
  · exact context_13_284733_462694
  · exact context_13_284734_462713
  · exact context_13_284735_462722

theorem unmarked_context_11_17795_462724 : frontier 10 ⟨462724, by decide⟩
    (prefixCache 11 17795) (prefixPartial 11 17795) = false := by
  decide +kernel

theorem node_context_11_17795_462724 : EJMOriginalGlobalDAGData.nodes 10 ⟨462724, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨462447, by decide⟩,⟨462578, by decide⟩,⟨462723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17795_462724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17795 ⟨462724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17795
    ⟨462724, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨462447, by decide⟩,⟨462578, by decide⟩,⟨462723, by decide⟩]) unmarked_context_11_17795_462724 node_context_11_17795_462724
  intro a
  fin_cases a
  · exact context_12_71180_448748
  · exact context_12_71181_462447
  · exact context_12_71182_462578
  · exact context_12_71183_462723

theorem unmarked_context_10_4448_462725 : frontier 11 ⟨462725, by decide⟩
    (prefixCache 10 4448) (prefixPartial 10 4448) = false := by
  decide +kernel

theorem node_context_10_4448_462725 : EJMOriginalGlobalDAGData.nodes 11 ⟨462725, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨461676, by decide⟩,⟨462309, by decide⟩,⟨462724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4448_462725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4448 ⟨462725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4448
    ⟨462725, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨461676, by decide⟩,⟨462309, by decide⟩,⟨462724, by decide⟩]) unmarked_context_10_4448_462725 node_context_10_4448_462725
  intro a
  fin_cases a
  · exact context_11_17792_434745
  · exact context_11_17793_461676
  · exact context_11_17794_462309
  · exact context_11_17795_462724

theorem selected_cut_18033 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 71184) = some ⟨12, 1, 0, 435160, 71184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71184_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71184 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 71184 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 71184, 1, 65536⟩
    (by decide) selected_cut_18033

theorem selected_cut_18034 : selected 8 ⟨462759, by decide⟩
    (prefixPartial 13 284740) = some ⟨13, 2, 0, 462759, 284740, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_284740_462759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284740 ⟨462759, by decide⟩ :=
  accepted_of_selected 13 284740 ⟨462759, by decide⟩ ⟨13, 2, 0, 462759, 284740, 1525, 16384⟩
    (by decide) selected_cut_18034

theorem selected_cut_18035 : selected 8 ⟨462781, by decide⟩
    (prefixPartial 13 284741) = some ⟨13, 2, 0, 462781, 284741, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_284741_462781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284741 ⟨462781, by decide⟩ :=
  accepted_of_selected 13 284741 ⟨462781, by decide⟩ ⟨13, 2, 0, 462781, 284741, 1645, 16384⟩
    (by decide) selected_cut_18035

theorem selected_cut_18036 : selected 8 ⟨462795, by decide⟩
    (prefixPartial 13 284742) = some ⟨13, 2, 0, 462795, 284742, 933, 16384⟩ := by
  decide +kernel

theorem context_13_284742_462795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284742 ⟨462795, by decide⟩ :=
  accepted_of_selected 13 284742 ⟨462795, by decide⟩ ⟨13, 2, 0, 462795, 284742, 933, 16384⟩
    (by decide) selected_cut_18036

theorem selected_cut_18037 : selected 8 ⟨462801, by decide⟩
    (prefixPartial 13 284743) = some ⟨13, 2, 0, 462801, 284743, 757, 16384⟩ := by
  decide +kernel

theorem context_13_284743_462801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284743 ⟨462801, by decide⟩ :=
  accepted_of_selected 13 284743 ⟨462801, by decide⟩ ⟨13, 2, 0, 462801, 284743, 757, 16384⟩
    (by decide) selected_cut_18037

theorem unmarked_context_12_71185_462802 : frontier 9 ⟨462802, by decide⟩
    (prefixCache 12 71185) (prefixPartial 12 71185) = false := by
  decide +kernel

theorem node_context_12_71185_462802 : EJMOriginalGlobalDAGData.nodes 9 ⟨462802, by decide⟩ =
    .split (coordinate 12) (![⟨462759, by decide⟩,⟨462781, by decide⟩,⟨462795, by decide⟩,⟨462801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71185_462802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71185 ⟨462802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71185
    ⟨462802, by decide⟩ (by decide) (![⟨462759, by decide⟩,⟨462781, by decide⟩,⟨462795, by decide⟩,⟨462801, by decide⟩]) unmarked_context_12_71185_462802 node_context_12_71185_462802
  intro a
  fin_cases a
  · exact context_13_284740_462759
  · exact context_13_284741_462781
  · exact context_13_284742_462795
  · exact context_13_284743_462801

theorem selected_cut_18038 : selected 8 ⟨462831, by decide⟩
    (prefixPartial 13 284744) = some ⟨13, 2, 0, 462831, 284744, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_284744_462831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284744 ⟨462831, by decide⟩ :=
  accepted_of_selected 13 284744 ⟨462831, by decide⟩ ⟨13, 2, 0, 462831, 284744, 1477, 16384⟩
    (by decide) selected_cut_18038

theorem selected_cut_18039 : selected 8 ⟨462850, by decide⟩
    (prefixPartial 13 284745) = some ⟨13, 2, 0, 462850, 284745, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_284745_462850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284745 ⟨462850, by decide⟩ :=
  accepted_of_selected 13 284745 ⟨462850, by decide⟩ ⟨13, 2, 0, 462850, 284745, 1633, 16384⟩
    (by decide) selected_cut_18039

theorem selected_cut_18040 : selected 8 ⟨462865, by decide⟩
    (prefixPartial 13 284746) = some ⟨13, 2, 0, 462865, 284746, 993, 16384⟩ := by
  decide +kernel

theorem context_13_284746_462865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284746 ⟨462865, by decide⟩ :=
  accepted_of_selected 13 284746 ⟨462865, by decide⟩ ⟨13, 2, 0, 462865, 284746, 993, 16384⟩
    (by decide) selected_cut_18040

theorem selected_cut_18041 : selected 8 ⟨462871, by decide⟩
    (prefixPartial 13 284747) = some ⟨13, 2, 0, 462871, 284747, 733, 16384⟩ := by
  decide +kernel

theorem context_13_284747_462871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284747 ⟨462871, by decide⟩ :=
  accepted_of_selected 13 284747 ⟨462871, by decide⟩ ⟨13, 2, 0, 462871, 284747, 733, 16384⟩
    (by decide) selected_cut_18041

theorem unmarked_context_12_71186_462872 : frontier 9 ⟨462872, by decide⟩
    (prefixCache 12 71186) (prefixPartial 12 71186) = false := by
  decide +kernel

theorem node_context_12_71186_462872 : EJMOriginalGlobalDAGData.nodes 9 ⟨462872, by decide⟩ =
    .split (coordinate 12) (![⟨462831, by decide⟩,⟨462850, by decide⟩,⟨462865, by decide⟩,⟨462871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71186_462872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71186 ⟨462872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71186
    ⟨462872, by decide⟩ (by decide) (![⟨462831, by decide⟩,⟨462850, by decide⟩,⟨462865, by decide⟩,⟨462871, by decide⟩]) unmarked_context_12_71186_462872 node_context_12_71186_462872
  intro a
  fin_cases a
  · exact context_13_284744_462831
  · exact context_13_284745_462850
  · exact context_13_284746_462865
  · exact context_13_284747_462871

theorem selected_cut_18042 : selected 8 ⟨462915, by decide⟩
    (prefixPartial 13 284748) = some ⟨13, 2, 0, 462915, 284748, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_284748_462915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284748 ⟨462915, by decide⟩ :=
  accepted_of_selected 13 284748 ⟨462915, by decide⟩ ⟨13, 2, 0, 462915, 284748, 1901, 16384⟩
    (by decide) selected_cut_18042

theorem selected_cut_18043 : selected 8 ⟨462938, by decide⟩
    (prefixPartial 13 284749) = some ⟨13, 2, 0, 462938, 284749, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_284749_462938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284749 ⟨462938, by decide⟩ :=
  accepted_of_selected 13 284749 ⟨462938, by decide⟩ ⟨13, 2, 0, 462938, 284749, 1809, 16384⟩
    (by decide) selected_cut_18043

theorem selected_cut_18044 : selected 8 ⟨462954, by decide⟩
    (prefixPartial 13 284750) = some ⟨13, 2, 0, 462954, 284750, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_284750_462954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284750 ⟨462954, by decide⟩ :=
  accepted_of_selected 13 284750 ⟨462954, by decide⟩ ⟨13, 2, 0, 462954, 284750, 1189, 16384⟩
    (by decide) selected_cut_18044

theorem selected_cut_18045 : selected 8 ⟨462960, by decide⟩
    (prefixPartial 13 284751) = some ⟨13, 2, 0, 462960, 284751, 809, 16384⟩ := by
  decide +kernel

theorem context_13_284751_462960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284751 ⟨462960, by decide⟩ :=
  accepted_of_selected 13 284751 ⟨462960, by decide⟩ ⟨13, 2, 0, 462960, 284751, 809, 16384⟩
    (by decide) selected_cut_18045

theorem unmarked_context_12_71187_462961 : frontier 9 ⟨462961, by decide⟩
    (prefixCache 12 71187) (prefixPartial 12 71187) = false := by
  decide +kernel

theorem node_context_12_71187_462961 : EJMOriginalGlobalDAGData.nodes 9 ⟨462961, by decide⟩ =
    .split (coordinate 12) (![⟨462915, by decide⟩,⟨462938, by decide⟩,⟨462954, by decide⟩,⟨462960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71187_462961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71187 ⟨462961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71187
    ⟨462961, by decide⟩ (by decide) (![⟨462915, by decide⟩,⟨462938, by decide⟩,⟨462954, by decide⟩,⟨462960, by decide⟩]) unmarked_context_12_71187_462961 node_context_12_71187_462961
  intro a
  fin_cases a
  · exact context_13_284748_462915
  · exact context_13_284749_462938
  · exact context_13_284750_462954
  · exact context_13_284751_462960

theorem unmarked_context_11_17796_462962 : frontier 10 ⟨462962, by decide⟩
    (prefixCache 11 17796) (prefixPartial 11 17796) = false := by
  decide +kernel

theorem node_context_11_17796_462962 : EJMOriginalGlobalDAGData.nodes 10 ⟨462962, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨462802, by decide⟩,⟨462872, by decide⟩,⟨462961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17796_462962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17796 ⟨462962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17796
    ⟨462962, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨462802, by decide⟩,⟨462872, by decide⟩,⟨462961, by decide⟩]) unmarked_context_11_17796_462962 node_context_11_17796_462962
  intro a
  fin_cases a
  · exact context_12_71184_435160
  · exact context_12_71185_462802
  · exact context_12_71186_462872
  · exact context_12_71187_462961

theorem selected_cut_18046 : selected 8 ⟨463044, by decide⟩
    (prefixPartial 13 284752) = some ⟨13, 2, 0, 463044, 284752, 3673, 16384⟩ := by
  decide +kernel

theorem context_13_284752_463044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284752 ⟨463044, by decide⟩ :=
  accepted_of_selected 13 284752 ⟨463044, by decide⟩ ⟨13, 2, 0, 463044, 284752, 3673, 16384⟩
    (by decide) selected_cut_18046

theorem selected_cut_18047 : selected 8 ⟨463110, by decide⟩
    (prefixPartial 13 284753) = some ⟨13, 2, 0, 463110, 284753, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_284753_463110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284753 ⟨463110, by decide⟩ :=
  accepted_of_selected 13 284753 ⟨463110, by decide⟩ ⟨13, 2, 0, 463110, 284753, 3381, 16384⟩
    (by decide) selected_cut_18047

theorem selected_cut_18048 : selected 8 ⟨463141, by decide⟩
    (prefixPartial 13 284754) = some ⟨13, 2, 0, 463141, 284754, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_284754_463141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284754 ⟨463141, by decide⟩ :=
  accepted_of_selected 13 284754 ⟨463141, by decide⟩ ⟨13, 2, 0, 463141, 284754, 2229, 16384⟩
    (by decide) selected_cut_18048

theorem selected_cut_18049 : selected 8 ⟨463173, by decide⟩
    (prefixPartial 13 284755) = some ⟨13, 2, 0, 463173, 284755, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_284755_463173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284755 ⟨463173, by decide⟩ :=
  accepted_of_selected 13 284755 ⟨463173, by decide⟩ ⟨13, 2, 0, 463173, 284755, 1409, 16384⟩
    (by decide) selected_cut_18049

theorem unmarked_context_12_71188_463174 : frontier 9 ⟨463174, by decide⟩
    (prefixCache 12 71188) (prefixPartial 12 71188) = false := by
  decide +kernel

theorem node_context_12_71188_463174 : EJMOriginalGlobalDAGData.nodes 9 ⟨463174, by decide⟩ =
    .split (coordinate 12) (![⟨463044, by decide⟩,⟨463110, by decide⟩,⟨463141, by decide⟩,⟨463173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71188_463174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71188 ⟨463174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71188
    ⟨463174, by decide⟩ (by decide) (![⟨463044, by decide⟩,⟨463110, by decide⟩,⟨463141, by decide⟩,⟨463173, by decide⟩]) unmarked_context_12_71188_463174 node_context_12_71188_463174
  intro a
  fin_cases a
  · exact context_13_284752_463044
  · exact context_13_284753_463110
  · exact context_13_284754_463141
  · exact context_13_284755_463173

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
