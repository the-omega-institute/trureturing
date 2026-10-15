/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover415
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39940 : selected 9 ⟨1084266, by decide⟩
    (prefixPartial 12 308077) = some ⟨12, 2, 0, 1084266, 308077, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_308077_1084266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308077 ⟨1084266, by decide⟩ :=
  accepted_of_selected 12 308077 ⟨1084266, by decide⟩ ⟨12, 2, 0, 1084266, 308077, 1857, 65536⟩
    (by decide) selected_cut_39940

theorem selected_cut_39941 : selected 9 ⟨1084294, by decide⟩
    (prefixPartial 12 308078) = some ⟨12, 2, 0, 1084294, 308078, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_308078_1084294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308078 ⟨1084294, by decide⟩ :=
  accepted_of_selected 12 308078 ⟨1084294, by decide⟩ ⟨12, 2, 0, 1084294, 308078, 1749, 65536⟩
    (by decide) selected_cut_39941

theorem selected_cut_39942 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 308079) = some ⟨12, 1, 0, 903806, 308079, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308079_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308079 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 308079 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 308079, 1, 65536⟩
    (by decide) selected_cut_39942

theorem unmarked_context_11_77019_1084295 : frontier 10 ⟨1084295, by decide⟩
    (prefixCache 11 77019) (prefixPartial 11 77019) = false := by
  decide +kernel

theorem node_context_11_77019_1084295 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084295, by decide⟩ =
    .split (coordinate 11) (![⟨1084234, by decide⟩,⟨1084266, by decide⟩,⟨1084294, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77019_1084295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77019 ⟨1084295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77019
    ⟨1084295, by decide⟩ (by decide) (![⟨1084234, by decide⟩,⟨1084266, by decide⟩,⟨1084294, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77019_1084295 node_context_11_77019_1084295
  intro a
  fin_cases a
  · exact context_12_308076_1084234
  · exact context_12_308077_1084266
  · exact context_12_308078_1084294
  · exact context_12_308079_903806

theorem unmarked_context_10_19254_1084296 : frontier 11 ⟨1084296, by decide⟩
    (prefixCache 10 19254) (prefixPartial 10 19254) = false := by
  decide +kernel

theorem node_context_10_19254_1084296 : EJMOriginalGlobalDAGData.nodes 11 ⟨1084296, by decide⟩ =
    .split (coordinate 10) (![⟨1083993, by decide⟩,⟨1084073, by decide⟩,⟨1084209, by decide⟩,⟨1084295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19254_1084296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19254 ⟨1084296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19254
    ⟨1084296, by decide⟩ (by decide) (![⟨1083993, by decide⟩,⟨1084073, by decide⟩,⟨1084209, by decide⟩,⟨1084295, by decide⟩]) unmarked_context_10_19254_1084296 node_context_10_19254_1084296
  intro a
  fin_cases a
  · exact context_11_77016_1083993
  · exact context_11_77017_1084073
  · exact context_11_77018_1084209
  · exact context_11_77019_1084295

theorem selected_cut_39943 : selected 9 ⟨1084318, by decide⟩
    (prefixPartial 12 308080) = some ⟨12, 2, 0, 1084318, 308080, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_308080_1084318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308080 ⟨1084318, by decide⟩ :=
  accepted_of_selected 12 308080 ⟨1084318, by decide⟩ ⟨12, 2, 0, 1084318, 308080, 1445, 65536⟩
    (by decide) selected_cut_39943

theorem selected_cut_39944 : selected 9 ⟨1084341, by decide⟩
    (prefixPartial 12 308081) = some ⟨12, 2, 0, 1084341, 308081, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_308081_1084341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308081 ⟨1084341, by decide⟩ :=
  accepted_of_selected 12 308081 ⟨1084341, by decide⟩ ⟨12, 2, 0, 1084341, 308081, 1581, 65536⟩
    (by decide) selected_cut_39944

theorem selected_cut_39945 : selected 9 ⟨1084360, by decide⟩
    (prefixPartial 12 308082) = some ⟨12, 2, 0, 1084360, 308082, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_308082_1084360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308082 ⟨1084360, by decide⟩ :=
  accepted_of_selected 12 308082 ⟨1084360, by decide⟩ ⟨12, 2, 0, 1084360, 308082, 1465, 65536⟩
    (by decide) selected_cut_39945

theorem selected_cut_39946 : selected 9 ⟨1084379, by decide⟩
    (prefixPartial 12 308083) = some ⟨12, 2, 0, 1084379, 308083, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_308083_1084379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308083 ⟨1084379, by decide⟩ :=
  accepted_of_selected 12 308083 ⟨1084379, by decide⟩ ⟨12, 2, 0, 1084379, 308083, 1273, 65536⟩
    (by decide) selected_cut_39946

theorem unmarked_context_11_77020_1084380 : frontier 10 ⟨1084380, by decide⟩
    (prefixCache 11 77020) (prefixPartial 11 77020) = false := by
  decide +kernel

theorem node_context_11_77020_1084380 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084380, by decide⟩ =
    .split (coordinate 11) (![⟨1084318, by decide⟩,⟨1084341, by decide⟩,⟨1084360, by decide⟩,⟨1084379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77020_1084380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77020 ⟨1084380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77020
    ⟨1084380, by decide⟩ (by decide) (![⟨1084318, by decide⟩,⟨1084341, by decide⟩,⟨1084360, by decide⟩,⟨1084379, by decide⟩]) unmarked_context_11_77020_1084380 node_context_11_77020_1084380
  intro a
  fin_cases a
  · exact context_12_308080_1084318
  · exact context_12_308081_1084341
  · exact context_12_308082_1084360
  · exact context_12_308083_1084379

theorem selected_cut_39947 : selected 9 ⟨1084404, by decide⟩
    (prefixPartial 12 308084) = some ⟨12, 2, 0, 1084404, 308084, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_308084_1084404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308084 ⟨1084404, by decide⟩ :=
  accepted_of_selected 12 308084 ⟨1084404, by decide⟩ ⟨12, 2, 0, 1084404, 308084, 1713, 65536⟩
    (by decide) selected_cut_39947

theorem selected_cut_39948 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 308085) = some ⟨12, 1, 0, 1084018, 308085, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308085_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308085 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 308085 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 308085, 1, 65536⟩
    (by decide) selected_cut_39948

theorem selected_cut_39949 : selected 9 ⟨1084431, by decide⟩
    (prefixPartial 12 308086) = some ⟨12, 2, 0, 1084431, 308086, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_308086_1084431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308086 ⟨1084431, by decide⟩ :=
  accepted_of_selected 12 308086 ⟨1084431, by decide⟩ ⟨12, 2, 0, 1084431, 308086, 1621, 65536⟩
    (by decide) selected_cut_39949

theorem selected_cut_39950 : selected 9 ⟨1084453, by decide⟩
    (prefixPartial 12 308087) = some ⟨12, 2, 0, 1084453, 308087, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_308087_1084453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308087 ⟨1084453, by decide⟩ :=
  accepted_of_selected 12 308087 ⟨1084453, by decide⟩ ⟨12, 2, 0, 1084453, 308087, 1613, 65536⟩
    (by decide) selected_cut_39950

theorem unmarked_context_11_77021_1084454 : frontier 10 ⟨1084454, by decide⟩
    (prefixCache 11 77021) (prefixPartial 11 77021) = false := by
  decide +kernel

theorem node_context_11_77021_1084454 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084454, by decide⟩ =
    .split (coordinate 11) (![⟨1084404, by decide⟩,⟨1084018, by decide⟩,⟨1084431, by decide⟩,⟨1084453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77021_1084454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77021 ⟨1084454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77021
    ⟨1084454, by decide⟩ (by decide) (![⟨1084404, by decide⟩,⟨1084018, by decide⟩,⟨1084431, by decide⟩,⟨1084453, by decide⟩]) unmarked_context_11_77021_1084454 node_context_11_77021_1084454
  intro a
  fin_cases a
  · exact context_12_308084_1084404
  · exact context_12_308085_1084018
  · exact context_12_308086_1084431
  · exact context_12_308087_1084453

theorem selected_cut_39951 : selected 9 ⟨1084478, by decide⟩
    (prefixPartial 12 308088) = some ⟨12, 2, 0, 1084478, 308088, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_308088_1084478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308088 ⟨1084478, by decide⟩ :=
  accepted_of_selected 12 308088 ⟨1084478, by decide⟩ ⟨12, 2, 0, 1084478, 308088, 1605, 65536⟩
    (by decide) selected_cut_39951

theorem selected_cut_39952 : selected 9 ⟨1084502, by decide⟩
    (prefixPartial 12 308089) = some ⟨12, 2, 0, 1084502, 308089, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_308089_1084502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308089 ⟨1084502, by decide⟩ :=
  accepted_of_selected 12 308089 ⟨1084502, by decide⟩ ⟨12, 2, 0, 1084502, 308089, 1677, 65536⟩
    (by decide) selected_cut_39952

theorem selected_cut_39953 : selected 9 ⟨1084521, by decide⟩
    (prefixPartial 12 308090) = some ⟨12, 2, 0, 1084521, 308090, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_308090_1084521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308090 ⟨1084521, by decide⟩ :=
  accepted_of_selected 12 308090 ⟨1084521, by decide⟩ ⟨12, 2, 0, 1084521, 308090, 1369, 65536⟩
    (by decide) selected_cut_39953

theorem selected_cut_39954 : selected 9 ⟨1084541, by decide⟩
    (prefixPartial 12 308091) = some ⟨12, 2, 0, 1084541, 308091, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_308091_1084541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308091 ⟨1084541, by decide⟩ :=
  accepted_of_selected 12 308091 ⟨1084541, by decide⟩ ⟨12, 2, 0, 1084541, 308091, 1421, 65536⟩
    (by decide) selected_cut_39954

theorem unmarked_context_11_77022_1084542 : frontier 10 ⟨1084542, by decide⟩
    (prefixCache 11 77022) (prefixPartial 11 77022) = false := by
  decide +kernel

theorem node_context_11_77022_1084542 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084542, by decide⟩ =
    .split (coordinate 11) (![⟨1084478, by decide⟩,⟨1084502, by decide⟩,⟨1084521, by decide⟩,⟨1084541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77022_1084542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77022 ⟨1084542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77022
    ⟨1084542, by decide⟩ (by decide) (![⟨1084478, by decide⟩,⟨1084502, by decide⟩,⟨1084521, by decide⟩,⟨1084541, by decide⟩]) unmarked_context_11_77022_1084542 node_context_11_77022_1084542
  intro a
  fin_cases a
  · exact context_12_308088_1084478
  · exact context_12_308089_1084502
  · exact context_12_308090_1084521
  · exact context_12_308091_1084541

theorem selected_cut_39955 : selected 9 ⟨1084570, by decide⟩
    (prefixPartial 12 308092) = some ⟨12, 2, 0, 1084570, 308092, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_308092_1084570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308092 ⟨1084570, by decide⟩ :=
  accepted_of_selected 12 308092 ⟨1084570, by decide⟩ ⟨12, 2, 0, 1084570, 308092, 1557, 65536⟩
    (by decide) selected_cut_39955

theorem selected_cut_39956 : selected 9 ⟨1084594, by decide⟩
    (prefixPartial 12 308093) = some ⟨12, 2, 0, 1084594, 308093, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_308093_1084594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308093 ⟨1084594, by decide⟩ :=
  accepted_of_selected 12 308093 ⟨1084594, by decide⟩ ⟨12, 2, 0, 1084594, 308093, 1585, 65536⟩
    (by decide) selected_cut_39956

theorem selected_cut_39957 : selected 9 ⟨1084617, by decide⟩
    (prefixPartial 12 308094) = some ⟨12, 2, 0, 1084617, 308094, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_308094_1084617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308094 ⟨1084617, by decide⟩ :=
  accepted_of_selected 12 308094 ⟨1084617, by decide⟩ ⟨12, 2, 0, 1084617, 308094, 1357, 65536⟩
    (by decide) selected_cut_39957

theorem selected_cut_39958 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 308095) = some ⟨12, 1, 0, 429285, 308095, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308095_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308095 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 308095 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 308095, 1, 65536⟩
    (by decide) selected_cut_39958

theorem unmarked_context_11_77023_1084618 : frontier 10 ⟨1084618, by decide⟩
    (prefixCache 11 77023) (prefixPartial 11 77023) = false := by
  decide +kernel

theorem node_context_11_77023_1084618 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084618, by decide⟩ =
    .split (coordinate 11) (![⟨1084570, by decide⟩,⟨1084594, by decide⟩,⟨1084617, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77023_1084618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77023 ⟨1084618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77023
    ⟨1084618, by decide⟩ (by decide) (![⟨1084570, by decide⟩,⟨1084594, by decide⟩,⟨1084617, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_77023_1084618 node_context_11_77023_1084618
  intro a
  fin_cases a
  · exact context_12_308092_1084570
  · exact context_12_308093_1084594
  · exact context_12_308094_1084617
  · exact context_12_308095_429285

theorem unmarked_context_10_19255_1084619 : frontier 11 ⟨1084619, by decide⟩
    (prefixCache 10 19255) (prefixPartial 10 19255) = false := by
  decide +kernel

theorem node_context_10_19255_1084619 : EJMOriginalGlobalDAGData.nodes 11 ⟨1084619, by decide⟩ =
    .split (coordinate 10) (![⟨1084380, by decide⟩,⟨1084454, by decide⟩,⟨1084542, by decide⟩,⟨1084618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19255_1084619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19255 ⟨1084619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19255
    ⟨1084619, by decide⟩ (by decide) (![⟨1084380, by decide⟩,⟨1084454, by decide⟩,⟨1084542, by decide⟩,⟨1084618, by decide⟩]) unmarked_context_10_19255_1084619 node_context_10_19255_1084619
  intro a
  fin_cases a
  · exact context_11_77020_1084380
  · exact context_11_77021_1084454
  · exact context_11_77022_1084542
  · exact context_11_77023_1084618

theorem unmarked_context_9_4813_1084620 : frontier 12 ⟨1084620, by decide⟩
    (prefixCache 9 4813) (prefixPartial 9 4813) = false := by
  decide +kernel

theorem node_context_9_4813_1084620 : EJMOriginalGlobalDAGData.nodes 12 ⟨1084620, by decide⟩ =
    .split (coordinate 9) (![⟨1083893, by decide⟩,⟨893098, by decide⟩,⟨1084296, by decide⟩,⟨1084619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4813_1084620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4813 ⟨1084620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4813
    ⟨1084620, by decide⟩ (by decide) (![⟨1083893, by decide⟩,⟨893098, by decide⟩,⟨1084296, by decide⟩,⟨1084619, by decide⟩]) unmarked_context_9_4813_1084620 node_context_9_4813_1084620
  intro a
  fin_cases a
  · exact context_10_19252_1083893
  · exact context_10_19253_893098
  · exact context_10_19254_1084296
  · exact context_10_19255_1084619

theorem selected_cut_39959 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 77024) = some ⟨11, 1, 0, 907917, 77024, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77024_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77024 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 77024 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 77024, 1, 262144⟩
    (by decide) selected_cut_39959

theorem selected_cut_39960 : selected 10 ⟨1084679, by decide⟩
    (prefixPartial 11 77025) = some ⟨11, 2, 0, 1084679, 77025, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_77025_1084679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77025 ⟨1084679, by decide⟩ :=
  accepted_of_selected 11 77025 ⟨1084679, by decide⟩ ⟨11, 2, 0, 1084679, 77025, 3337, 262144⟩
    (by decide) selected_cut_39960

theorem selected_cut_39961 : selected 10 ⟨1084729, by decide⟩
    (prefixPartial 11 77026) = some ⟨11, 2, 0, 1084729, 77026, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_77026_1084729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77026 ⟨1084729, by decide⟩ :=
  accepted_of_selected 11 77026 ⟨1084729, by decide⟩ ⟨11, 2, 0, 1084729, 77026, 3357, 262144⟩
    (by decide) selected_cut_39961

theorem selected_cut_39962 : selected 10 ⟨1084757, by decide⟩
    (prefixPartial 11 77027) = some ⟨11, 2, 0, 1084757, 77027, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_77027_1084757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77027 ⟨1084757, by decide⟩ :=
  accepted_of_selected 11 77027 ⟨1084757, by decide⟩ ⟨11, 2, 0, 1084757, 77027, 2145, 262144⟩
    (by decide) selected_cut_39962

theorem unmarked_context_10_19256_1084758 : frontier 11 ⟨1084758, by decide⟩
    (prefixCache 10 19256) (prefixPartial 10 19256) = false := by
  decide +kernel

theorem node_context_10_19256_1084758 : EJMOriginalGlobalDAGData.nodes 11 ⟨1084758, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1084679, by decide⟩,⟨1084729, by decide⟩,⟨1084757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19256_1084758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19256 ⟨1084758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19256
    ⟨1084758, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1084679, by decide⟩,⟨1084729, by decide⟩,⟨1084757, by decide⟩]) unmarked_context_10_19256_1084758 node_context_10_19256_1084758
  intro a
  fin_cases a
  · exact context_11_77024_907917
  · exact context_11_77025_1084679
  · exact context_11_77026_1084729
  · exact context_11_77027_1084757

theorem selected_cut_39963 : selected 10 ⟨1084793, by decide⟩
    (prefixPartial 11 77028) = some ⟨11, 2, 0, 1084793, 77028, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_77028_1084793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77028 ⟨1084793, by decide⟩ :=
  accepted_of_selected 11 77028 ⟨1084793, by decide⟩ ⟨11, 2, 0, 1084793, 77028, 2737, 262144⟩
    (by decide) selected_cut_39963

theorem selected_cut_39964 : selected 10 ⟨1084829, by decide⟩
    (prefixPartial 11 77029) = some ⟨11, 2, 0, 1084829, 77029, 2077, 262144⟩ := by
  decide +kernel

theorem context_11_77029_1084829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77029 ⟨1084829, by decide⟩ :=
  accepted_of_selected 11 77029 ⟨1084829, by decide⟩ ⟨11, 2, 0, 1084829, 77029, 2077, 262144⟩
    (by decide) selected_cut_39964

theorem selected_cut_39965 : selected 10 ⟨1084859, by decide⟩
    (prefixPartial 11 77030) = some ⟨11, 2, 0, 1084859, 77030, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_77030_1084859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77030 ⟨1084859, by decide⟩ :=
  accepted_of_selected 11 77030 ⟨1084859, by decide⟩ ⟨11, 2, 0, 1084859, 77030, 2569, 262144⟩
    (by decide) selected_cut_39965

theorem selected_cut_39966 : selected 10 ⟨1084881, by decide⟩
    (prefixPartial 11 77031) = some ⟨11, 2, 0, 1084881, 77031, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_77031_1084881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77031 ⟨1084881, by decide⟩ :=
  accepted_of_selected 11 77031 ⟨1084881, by decide⟩ ⟨11, 2, 0, 1084881, 77031, 1677, 262144⟩
    (by decide) selected_cut_39966

theorem unmarked_context_10_19257_1084882 : frontier 11 ⟨1084882, by decide⟩
    (prefixCache 10 19257) (prefixPartial 10 19257) = false := by
  decide +kernel

theorem node_context_10_19257_1084882 : EJMOriginalGlobalDAGData.nodes 11 ⟨1084882, by decide⟩ =
    .split (coordinate 10) (![⟨1084793, by decide⟩,⟨1084829, by decide⟩,⟨1084859, by decide⟩,⟨1084881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19257_1084882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19257 ⟨1084882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19257
    ⟨1084882, by decide⟩ (by decide) (![⟨1084793, by decide⟩,⟨1084829, by decide⟩,⟨1084859, by decide⟩,⟨1084881, by decide⟩]) unmarked_context_10_19257_1084882 node_context_10_19257_1084882
  intro a
  fin_cases a
  · exact context_11_77028_1084793
  · exact context_11_77029_1084829
  · exact context_11_77030_1084859
  · exact context_11_77031_1084881

theorem selected_cut_39967 : selected 10 ⟨1084903, by decide⟩
    (prefixPartial 11 77032) = some ⟨11, 2, 0, 1084903, 77032, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_77032_1084903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77032 ⟨1084903, by decide⟩ :=
  accepted_of_selected 11 77032 ⟨1084903, by decide⟩ ⟨11, 2, 0, 1084903, 77032, 2225, 262144⟩
    (by decide) selected_cut_39967

theorem selected_cut_39968 : selected 10 ⟨1084925, by decide⟩
    (prefixPartial 11 77033) = some ⟨11, 2, 0, 1084925, 77033, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_77033_1084925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77033 ⟨1084925, by decide⟩ :=
  accepted_of_selected 11 77033 ⟨1084925, by decide⟩ ⟨11, 2, 0, 1084925, 77033, 2169, 262144⟩
    (by decide) selected_cut_39968

theorem selected_cut_39969 : selected 10 ⟨1084937, by decide⟩
    (prefixPartial 11 77034) = some ⟨11, 2, 0, 1084937, 77034, 273, 262144⟩ := by
  decide +kernel

theorem context_11_77034_1084937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77034 ⟨1084937, by decide⟩ :=
  accepted_of_selected 11 77034 ⟨1084937, by decide⟩ ⟨11, 2, 0, 1084937, 77034, 273, 262144⟩
    (by decide) selected_cut_39969

theorem selected_cut_39970 : selected 10 ⟨1084958, by decide⟩
    (prefixPartial 11 77035) = some ⟨11, 2, 0, 1084958, 77035, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_77035_1084958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77035 ⟨1084958, by decide⟩ :=
  accepted_of_selected 11 77035 ⟨1084958, by decide⟩ ⟨11, 2, 0, 1084958, 77035, 1381, 262144⟩
    (by decide) selected_cut_39970

theorem unmarked_context_10_19258_1084959 : frontier 11 ⟨1084959, by decide⟩
    (prefixCache 10 19258) (prefixPartial 10 19258) = false := by
  decide +kernel

theorem node_context_10_19258_1084959 : EJMOriginalGlobalDAGData.nodes 11 ⟨1084959, by decide⟩ =
    .split (coordinate 10) (![⟨1084903, by decide⟩,⟨1084925, by decide⟩,⟨1084937, by decide⟩,⟨1084958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19258_1084959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19258 ⟨1084959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19258
    ⟨1084959, by decide⟩ (by decide) (![⟨1084903, by decide⟩,⟨1084925, by decide⟩,⟨1084937, by decide⟩,⟨1084958, by decide⟩]) unmarked_context_10_19258_1084959 node_context_10_19258_1084959
  intro a
  fin_cases a
  · exact context_11_77032_1084903
  · exact context_11_77033_1084925
  · exact context_11_77034_1084937
  · exact context_11_77035_1084958

theorem selected_cut_39971 : selected 10 ⟨1084986, by decide⟩
    (prefixPartial 11 77036) = some ⟨11, 2, 0, 1084986, 77036, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_77036_1084986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77036 ⟨1084986, by decide⟩ :=
  accepted_of_selected 11 77036 ⟨1084986, by decide⟩ ⟨11, 2, 0, 1084986, 77036, 1981, 262144⟩
    (by decide) selected_cut_39971

theorem selected_cut_39972 : selected 10 ⟨1085010, by decide⟩
    (prefixPartial 11 77037) = some ⟨11, 2, 0, 1085010, 77037, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_77037_1085010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77037 ⟨1085010, by decide⟩ :=
  accepted_of_selected 11 77037 ⟨1085010, by decide⟩ ⟨11, 2, 0, 1085010, 77037, 2021, 262144⟩
    (by decide) selected_cut_39972

theorem selected_cut_39973 : selected 10 ⟨1085034, by decide⟩
    (prefixPartial 11 77038) = some ⟨11, 2, 0, 1085034, 77038, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_77038_1085034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77038 ⟨1085034, by decide⟩ :=
  accepted_of_selected 11 77038 ⟨1085034, by decide⟩ ⟨11, 2, 0, 1085034, 77038, 1861, 262144⟩
    (by decide) selected_cut_39973

theorem selected_cut_39974 : selected 10 ⟨1085051, by decide⟩
    (prefixPartial 11 77039) = some ⟨11, 2, 0, 1085051, 77039, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_77039_1085051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77039 ⟨1085051, by decide⟩ :=
  accepted_of_selected 11 77039 ⟨1085051, by decide⟩ ⟨11, 2, 0, 1085051, 77039, 1169, 262144⟩
    (by decide) selected_cut_39974

theorem unmarked_context_10_19259_1085052 : frontier 11 ⟨1085052, by decide⟩
    (prefixCache 10 19259) (prefixPartial 10 19259) = false := by
  decide +kernel

theorem node_context_10_19259_1085052 : EJMOriginalGlobalDAGData.nodes 11 ⟨1085052, by decide⟩ =
    .split (coordinate 10) (![⟨1084986, by decide⟩,⟨1085010, by decide⟩,⟨1085034, by decide⟩,⟨1085051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19259_1085052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19259 ⟨1085052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19259
    ⟨1085052, by decide⟩ (by decide) (![⟨1084986, by decide⟩,⟨1085010, by decide⟩,⟨1085034, by decide⟩,⟨1085051, by decide⟩]) unmarked_context_10_19259_1085052 node_context_10_19259_1085052
  intro a
  fin_cases a
  · exact context_11_77036_1084986
  · exact context_11_77037_1085010
  · exact context_11_77038_1085034
  · exact context_11_77039_1085051

theorem unmarked_context_9_4814_1085053 : frontier 12 ⟨1085053, by decide⟩
    (prefixCache 9 4814) (prefixPartial 9 4814) = false := by
  decide +kernel

theorem node_context_9_4814_1085053 : EJMOriginalGlobalDAGData.nodes 12 ⟨1085053, by decide⟩ =
    .split (coordinate 9) (![⟨1084758, by decide⟩,⟨1084882, by decide⟩,⟨1084959, by decide⟩,⟨1085052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4814_1085053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4814 ⟨1085053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4814
    ⟨1085053, by decide⟩ (by decide) (![⟨1084758, by decide⟩,⟨1084882, by decide⟩,⟨1084959, by decide⟩,⟨1085052, by decide⟩]) unmarked_context_9_4814_1085053 node_context_9_4814_1085053
  intro a
  fin_cases a
  · exact context_10_19256_1084758
  · exact context_10_19257_1084882
  · exact context_10_19258_1084959
  · exact context_10_19259_1085052

theorem selected_cut_39975 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 77040) = some ⟨11, 1, 0, 907917, 77040, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77040_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77040 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 77040 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 77040, 1, 262144⟩
    (by decide) selected_cut_39975

theorem selected_cut_39976 : selected 10 ⟨1085074, by decide⟩
    (prefixPartial 11 77041) = some ⟨11, 2, 0, 1085074, 77041, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_77041_1085074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77041 ⟨1085074, by decide⟩ :=
  accepted_of_selected 11 77041 ⟨1085074, by decide⟩ ⟨11, 2, 0, 1085074, 77041, 1885, 262144⟩
    (by decide) selected_cut_39976

theorem selected_cut_39977 : selected 10 ⟨1085094, by decide⟩
    (prefixPartial 11 77042) = some ⟨11, 2, 0, 1085094, 77042, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_77042_1085094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77042 ⟨1085094, by decide⟩ :=
  accepted_of_selected 11 77042 ⟨1085094, by decide⟩ ⟨11, 2, 0, 1085094, 77042, 1673, 262144⟩
    (by decide) selected_cut_39977

theorem selected_cut_39978 : selected 10 ⟨1085113, by decide⟩
    (prefixPartial 11 77043) = some ⟨11, 2, 0, 1085113, 77043, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_77043_1085113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77043 ⟨1085113, by decide⟩ :=
  accepted_of_selected 11 77043 ⟨1085113, by decide⟩ ⟨11, 2, 0, 1085113, 77043, 1281, 262144⟩
    (by decide) selected_cut_39978

theorem unmarked_context_10_19260_1085114 : frontier 11 ⟨1085114, by decide⟩
    (prefixCache 10 19260) (prefixPartial 10 19260) = false := by
  decide +kernel

theorem node_context_10_19260_1085114 : EJMOriginalGlobalDAGData.nodes 11 ⟨1085114, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1085074, by decide⟩,⟨1085094, by decide⟩,⟨1085113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19260_1085114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19260 ⟨1085114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19260
    ⟨1085114, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1085074, by decide⟩,⟨1085094, by decide⟩,⟨1085113, by decide⟩]) unmarked_context_10_19260_1085114 node_context_10_19260_1085114
  intro a
  fin_cases a
  · exact context_11_77040_907917
  · exact context_11_77041_1085074
  · exact context_11_77042_1085094
  · exact context_11_77043_1085113

theorem selected_cut_39979 : selected 10 ⟨1085130, by decide⟩
    (prefixPartial 11 77044) = some ⟨11, 2, 0, 1085130, 77044, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_77044_1085130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77044 ⟨1085130, by decide⟩ :=
  accepted_of_selected 11 77044 ⟨1085130, by decide⟩ ⟨11, 2, 0, 1085130, 77044, 1313, 262144⟩
    (by decide) selected_cut_39979

theorem selected_cut_39980 : selected 10 ⟨1085142, by decide⟩
    (prefixPartial 11 77045) = some ⟨11, 2, 0, 1085142, 77045, 989, 262144⟩ := by
  decide +kernel

theorem context_11_77045_1085142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77045 ⟨1085142, by decide⟩ :=
  accepted_of_selected 11 77045 ⟨1085142, by decide⟩ ⟨11, 2, 0, 1085142, 77045, 989, 262144⟩
    (by decide) selected_cut_39980

theorem selected_cut_39981 : selected 10 ⟨1085158, by decide⟩
    (prefixPartial 11 77046) = some ⟨11, 2, 0, 1085158, 77046, 1125, 262144⟩ := by
  decide +kernel

theorem context_11_77046_1085158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77046 ⟨1085158, by decide⟩ :=
  accepted_of_selected 11 77046 ⟨1085158, by decide⟩ ⟨11, 2, 0, 1085158, 77046, 1125, 262144⟩
    (by decide) selected_cut_39981

theorem selected_cut_39982 : selected 10 ⟨1085169, by decide⟩
    (prefixPartial 11 77047) = some ⟨11, 2, 0, 1085169, 77047, 833, 262144⟩ := by
  decide +kernel

theorem context_11_77047_1085169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77047 ⟨1085169, by decide⟩ :=
  accepted_of_selected 11 77047 ⟨1085169, by decide⟩ ⟨11, 2, 0, 1085169, 77047, 833, 262144⟩
    (by decide) selected_cut_39982

theorem unmarked_context_10_19261_1085170 : frontier 11 ⟨1085170, by decide⟩
    (prefixCache 10 19261) (prefixPartial 10 19261) = false := by
  decide +kernel

theorem node_context_10_19261_1085170 : EJMOriginalGlobalDAGData.nodes 11 ⟨1085170, by decide⟩ =
    .split (coordinate 10) (![⟨1085130, by decide⟩,⟨1085142, by decide⟩,⟨1085158, by decide⟩,⟨1085169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19261_1085170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19261 ⟨1085170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19261
    ⟨1085170, by decide⟩ (by decide) (![⟨1085130, by decide⟩,⟨1085142, by decide⟩,⟨1085158, by decide⟩,⟨1085169, by decide⟩]) unmarked_context_10_19261_1085170 node_context_10_19261_1085170
  intro a
  fin_cases a
  · exact context_11_77044_1085130
  · exact context_11_77045_1085142
  · exact context_11_77046_1085158
  · exact context_11_77047_1085169

theorem selected_cut_39983 : selected 11 ⟨1085218, by decide⟩
    (prefixPartial 10 19262) = some ⟨10, 2, 0, 1085218, 19262, 2521, 1048576⟩ := by
  decide +kernel

theorem context_10_19262_1085218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19262 ⟨1085218, by decide⟩ :=
  accepted_of_selected 10 19262 ⟨1085218, by decide⟩ ⟨10, 2, 0, 1085218, 19262, 2521, 1048576⟩
    (by decide) selected_cut_39983

theorem selected_cut_39984 : selected 11 ⟨1085249, by decide⟩
    (prefixPartial 10 19263) = some ⟨10, 2, 0, 1085249, 19263, 593, 1048576⟩ := by
  decide +kernel

theorem context_10_19263_1085249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19263 ⟨1085249, by decide⟩ :=
  accepted_of_selected 10 19263 ⟨1085249, by decide⟩ ⟨10, 2, 0, 1085249, 19263, 593, 1048576⟩
    (by decide) selected_cut_39984

theorem unmarked_context_9_4815_1085250 : frontier 12 ⟨1085250, by decide⟩
    (prefixCache 9 4815) (prefixPartial 9 4815) = false := by
  decide +kernel

theorem node_context_9_4815_1085250 : EJMOriginalGlobalDAGData.nodes 12 ⟨1085250, by decide⟩ =
    .split (coordinate 9) (![⟨1085114, by decide⟩,⟨1085170, by decide⟩,⟨1085218, by decide⟩,⟨1085249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4815_1085250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4815 ⟨1085250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4815
    ⟨1085250, by decide⟩ (by decide) (![⟨1085114, by decide⟩,⟨1085170, by decide⟩,⟨1085218, by decide⟩,⟨1085249, by decide⟩]) unmarked_context_9_4815_1085250 node_context_9_4815_1085250
  intro a
  fin_cases a
  · exact context_10_19260_1085114
  · exact context_10_19261_1085170
  · exact context_10_19262_1085218
  · exact context_10_19263_1085249

theorem unmarked_context_8_1203_1085251 : frontier 13 ⟨1085251, by decide⟩
    (prefixCache 8 1203) (prefixPartial 8 1203) = false := by
  decide +kernel

theorem node_context_8_1203_1085251 : EJMOriginalGlobalDAGData.nodes 13 ⟨1085251, by decide⟩ =
    .split (coordinate 8) (![⟨1083437, by decide⟩,⟨1084620, by decide⟩,⟨1085053, by decide⟩,⟨1085250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1203_1085251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1203 ⟨1085251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1203
    ⟨1085251, by decide⟩ (by decide) (![⟨1083437, by decide⟩,⟨1084620, by decide⟩,⟨1085053, by decide⟩,⟨1085250, by decide⟩]) unmarked_context_8_1203_1085251 node_context_8_1203_1085251
  intro a
  fin_cases a
  · exact context_9_4812_1083437
  · exact context_9_4813_1084620
  · exact context_9_4814_1085053
  · exact context_9_4815_1085250

theorem unmarked_context_7_300_1085252 : frontier 14 ⟨1085252, by decide⟩
    (prefixCache 7 300) (prefixPartial 7 300) = false := by
  decide +kernel

theorem node_context_7_300_1085252 : EJMOriginalGlobalDAGData.nodes 14 ⟨1085252, by decide⟩ =
    .split (coordinate 7) (![⟨1072442, by decide⟩,⟨1076200, by decide⟩,⟨1080974, by decide⟩,⟨1085251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_300_1085252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 300 ⟨1085252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 300
    ⟨1085252, by decide⟩ (by decide) (![⟨1072442, by decide⟩,⟨1076200, by decide⟩,⟨1080974, by decide⟩,⟨1085251, by decide⟩]) unmarked_context_7_300_1085252 node_context_7_300_1085252
  intro a
  fin_cases a
  · exact context_8_1200_1072442
  · exact context_8_1201_1076200
  · exact context_8_1202_1080974
  · exact context_8_1203_1085251

theorem selected_cut_39985 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1204) = some ⟨8, 1, 0, 979897, 1204, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1204_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1204 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1204 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1204, 1, 16777216⟩
    (by decide) selected_cut_39985

theorem selected_cut_39986 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 77120) = some ⟨11, 1, 0, 167448, 77120, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77120_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77120 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 77120 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 77120, 1, 262144⟩
    (by decide) selected_cut_39986

theorem selected_cut_39987 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 308484) = some ⟨12, 1, 0, 34034, 308484, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308484_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308484 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 308484 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 308484, 1, 65536⟩
    (by decide) selected_cut_39987

theorem selected_cut_39988 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 308485) = some ⟨12, 1, 0, 891951, 308485, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308485_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308485 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 308485 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 308485, 1, 65536⟩
    (by decide) selected_cut_39988

theorem selected_cut_39989 : selected 9 ⟨1085310, by decide⟩
    (prefixPartial 12 308486) = some ⟨12, 2, 0, 1085310, 308486, 3709, 65536⟩ := by
  decide +kernel

theorem context_12_308486_1085310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308486 ⟨1085310, by decide⟩ :=
  accepted_of_selected 12 308486 ⟨1085310, by decide⟩ ⟨12, 2, 0, 1085310, 308486, 3709, 65536⟩
    (by decide) selected_cut_39989

theorem selected_cut_39990 : selected 9 ⟨1085360, by decide⟩
    (prefixPartial 12 308487) = some ⟨12, 2, 0, 1085360, 308487, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_308487_1085360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308487 ⟨1085360, by decide⟩ :=
  accepted_of_selected 12 308487 ⟨1085360, by decide⟩ ⟨12, 2, 0, 1085360, 308487, 3541, 65536⟩
    (by decide) selected_cut_39990

theorem unmarked_context_11_77121_1085361 : frontier 10 ⟨1085361, by decide⟩
    (prefixCache 11 77121) (prefixPartial 11 77121) = false := by
  decide +kernel

theorem node_context_11_77121_1085361 : EJMOriginalGlobalDAGData.nodes 10 ⟨1085361, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨1085310, by decide⟩,⟨1085360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77121_1085361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77121 ⟨1085361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77121
    ⟨1085361, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨1085310, by decide⟩,⟨1085360, by decide⟩]) unmarked_context_11_77121_1085361 node_context_11_77121_1085361
  intro a
  fin_cases a
  · exact context_12_308484_34034
  · exact context_12_308485_891951
  · exact context_12_308486_1085310
  · exact context_12_308487_1085360

theorem selected_cut_39991 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 308488) = some ⟨12, 1, 0, 34034, 308488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308488_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308488 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 308488 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 308488, 1, 65536⟩
    (by decide) selected_cut_39991

theorem selected_cut_39992 : selected 9 ⟨1085415, by decide⟩
    (prefixPartial 12 308489) = some ⟨12, 2, 0, 1085415, 308489, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_308489_1085415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308489 ⟨1085415, by decide⟩ :=
  accepted_of_selected 12 308489 ⟨1085415, by decide⟩ ⟨12, 2, 0, 1085415, 308489, 3777, 65536⟩
    (by decide) selected_cut_39992

theorem selected_cut_39993 : selected 8 ⟨1085435, by decide⟩
    (prefixPartial 13 1233960) = some ⟨13, 2, 0, 1085435, 1233960, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_1233960_1085435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233960 ⟨1085435, by decide⟩ :=
  accepted_of_selected 13 1233960 ⟨1085435, by decide⟩ ⟨13, 2, 0, 1085435, 1233960, 1393, 16384⟩
    (by decide) selected_cut_39993

theorem selected_cut_39994 : selected 8 ⟨1085452, by decide⟩
    (prefixPartial 13 1233961) = some ⟨13, 2, 0, 1085452, 1233961, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_1233961_1085452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233961 ⟨1085452, by decide⟩ :=
  accepted_of_selected 13 1233961 ⟨1085452, by decide⟩ ⟨13, 2, 0, 1085452, 1233961, 1413, 16384⟩
    (by decide) selected_cut_39994

theorem selected_cut_39995 : selected 8 ⟨1085464, by decide⟩
    (prefixPartial 13 1233962) = some ⟨13, 2, 0, 1085464, 1233962, 869, 16384⟩ := by
  decide +kernel

theorem context_13_1233962_1085464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233962 ⟨1085464, by decide⟩ :=
  accepted_of_selected 13 1233962 ⟨1085464, by decide⟩ ⟨13, 2, 0, 1085464, 1233962, 869, 16384⟩
    (by decide) selected_cut_39995

theorem selected_cut_39996 : selected 8 ⟨1085470, by decide⟩
    (prefixPartial 13 1233963) = some ⟨13, 2, 0, 1085470, 1233963, 509, 16384⟩ := by
  decide +kernel

theorem context_13_1233963_1085470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233963 ⟨1085470, by decide⟩ :=
  accepted_of_selected 13 1233963 ⟨1085470, by decide⟩ ⟨13, 2, 0, 1085470, 1233963, 509, 16384⟩
    (by decide) selected_cut_39996

theorem unmarked_context_12_308490_1085471 : frontier 9 ⟨1085471, by decide⟩
    (prefixCache 12 308490) (prefixPartial 12 308490) = false := by
  decide +kernel

theorem node_context_12_308490_1085471 : EJMOriginalGlobalDAGData.nodes 9 ⟨1085471, by decide⟩ =
    .split (coordinate 12) (![⟨1085435, by decide⟩,⟨1085452, by decide⟩,⟨1085464, by decide⟩,⟨1085470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308490_1085471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308490 ⟨1085471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308490
    ⟨1085471, by decide⟩ (by decide) (![⟨1085435, by decide⟩,⟨1085452, by decide⟩,⟨1085464, by decide⟩,⟨1085470, by decide⟩]) unmarked_context_12_308490_1085471 node_context_12_308490_1085471
  intro a
  fin_cases a
  · exact context_13_1233960_1085435
  · exact context_13_1233961_1085452
  · exact context_13_1233962_1085464
  · exact context_13_1233963_1085470

theorem selected_cut_39997 : selected 9 ⟨1085529, by decide⟩
    (prefixPartial 12 308491) = some ⟨12, 2, 0, 1085529, 308491, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_308491_1085529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308491 ⟨1085529, by decide⟩ :=
  accepted_of_selected 12 308491 ⟨1085529, by decide⟩ ⟨12, 2, 0, 1085529, 308491, 4073, 65536⟩
    (by decide) selected_cut_39997

theorem unmarked_context_11_77122_1085530 : frontier 10 ⟨1085530, by decide⟩
    (prefixCache 11 77122) (prefixPartial 11 77122) = false := by
  decide +kernel

theorem node_context_11_77122_1085530 : EJMOriginalGlobalDAGData.nodes 10 ⟨1085530, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1085415, by decide⟩,⟨1085471, by decide⟩,⟨1085529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77122_1085530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77122 ⟨1085530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77122
    ⟨1085530, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1085415, by decide⟩,⟨1085471, by decide⟩,⟨1085529, by decide⟩]) unmarked_context_11_77122_1085530 node_context_11_77122_1085530
  intro a
  fin_cases a
  · exact context_12_308488_34034
  · exact context_12_308489_1085415
  · exact context_12_308490_1085471
  · exact context_12_308491_1085529

theorem selected_cut_39998 : selected 8 ⟨1085549, by decide⟩
    (prefixPartial 13 1233968) = some ⟨13, 2, 0, 1085549, 1233968, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_1233968_1085549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233968 ⟨1085549, by decide⟩ :=
  accepted_of_selected 13 1233968 ⟨1085549, by decide⟩ ⟨13, 2, 0, 1085549, 1233968, 1185, 16384⟩
    (by decide) selected_cut_39998

theorem selected_cut_39999 : selected 8 ⟨1085594, by decide⟩
    (prefixPartial 13 1233969) = some ⟨13, 2, 0, 1085594, 1233969, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_1233969_1085594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233969 ⟨1085594, by decide⟩ :=
  accepted_of_selected 13 1233969 ⟨1085594, by decide⟩ ⟨13, 2, 0, 1085594, 1233969, 1917, 16384⟩
    (by decide) selected_cut_39999

theorem selected_cut_40000 : selected 8 ⟨1085613, by decide⟩
    (prefixPartial 13 1233970) = some ⟨13, 2, 0, 1085613, 1233970, 929, 16384⟩ := by
  decide +kernel

theorem context_13_1233970_1085613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233970 ⟨1085613, by decide⟩ :=
  accepted_of_selected 13 1233970 ⟨1085613, by decide⟩ ⟨13, 2, 0, 1085613, 1233970, 929, 16384⟩
    (by decide) selected_cut_40000

theorem selected_cut_40001 : selected 8 ⟨1085630, by decide⟩
    (prefixPartial 13 1233971) = some ⟨13, 2, 0, 1085630, 1233971, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1233971_1085630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233971 ⟨1085630, by decide⟩ :=
  accepted_of_selected 13 1233971 ⟨1085630, by decide⟩ ⟨13, 2, 0, 1085630, 1233971, 725, 16384⟩
    (by decide) selected_cut_40001

theorem unmarked_context_12_308492_1085631 : frontier 9 ⟨1085631, by decide⟩
    (prefixCache 12 308492) (prefixPartial 12 308492) = false := by
  decide +kernel

theorem node_context_12_308492_1085631 : EJMOriginalGlobalDAGData.nodes 9 ⟨1085631, by decide⟩ =
    .split (coordinate 12) (![⟨1085549, by decide⟩,⟨1085594, by decide⟩,⟨1085613, by decide⟩,⟨1085630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308492_1085631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308492 ⟨1085631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308492
    ⟨1085631, by decide⟩ (by decide) (![⟨1085549, by decide⟩,⟨1085594, by decide⟩,⟨1085613, by decide⟩,⟨1085630, by decide⟩]) unmarked_context_12_308492_1085631 node_context_12_308492_1085631
  intro a
  fin_cases a
  · exact context_13_1233968_1085549
  · exact context_13_1233969_1085594
  · exact context_13_1233970_1085613
  · exact context_13_1233971_1085630

theorem selected_cut_40002 : selected 9 ⟨1085688, by decide⟩
    (prefixPartial 12 308493) = some ⟨12, 2, 0, 1085688, 308493, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_308493_1085688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308493 ⟨1085688, by decide⟩ :=
  accepted_of_selected 12 308493 ⟨1085688, by decide⟩ ⟨12, 2, 0, 1085688, 308493, 3697, 65536⟩
    (by decide) selected_cut_40002

theorem selected_cut_40003 : selected 8 ⟨1085709, by decide⟩
    (prefixPartial 13 1233976) = some ⟨13, 2, 0, 1085709, 1233976, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_1233976_1085709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233976 ⟨1085709, by decide⟩ :=
  accepted_of_selected 13 1233976 ⟨1085709, by decide⟩ ⟨13, 2, 0, 1085709, 1233976, 1341, 16384⟩
    (by decide) selected_cut_40003

theorem selected_cut_40004 : selected 8 ⟨1085727, by decide⟩
    (prefixPartial 13 1233977) = some ⟨13, 2, 0, 1085727, 1233977, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_1233977_1085727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233977 ⟨1085727, by decide⟩ :=
  accepted_of_selected 13 1233977 ⟨1085727, by decide⟩ ⟨13, 2, 0, 1085727, 1233977, 1473, 16384⟩
    (by decide) selected_cut_40004

theorem selected_cut_40005 : selected 8 ⟨1085744, by decide⟩
    (prefixPartial 13 1233978) = some ⟨13, 2, 0, 1085744, 1233978, 749, 16384⟩ := by
  decide +kernel

theorem context_13_1233978_1085744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233978 ⟨1085744, by decide⟩ :=
  accepted_of_selected 13 1233978 ⟨1085744, by decide⟩ ⟨13, 2, 0, 1085744, 1233978, 749, 16384⟩
    (by decide) selected_cut_40005

theorem selected_cut_40006 : selected 8 ⟨1085753, by decide⟩
    (prefixPartial 13 1233979) = some ⟨13, 2, 0, 1085753, 1233979, 581, 16384⟩ := by
  decide +kernel

theorem context_13_1233979_1085753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1233979 ⟨1085753, by decide⟩ :=
  accepted_of_selected 13 1233979 ⟨1085753, by decide⟩ ⟨13, 2, 0, 1085753, 1233979, 581, 16384⟩
    (by decide) selected_cut_40006

theorem unmarked_context_12_308494_1085754 : frontier 9 ⟨1085754, by decide⟩
    (prefixCache 12 308494) (prefixPartial 12 308494) = false := by
  decide +kernel

theorem node_context_12_308494_1085754 : EJMOriginalGlobalDAGData.nodes 9 ⟨1085754, by decide⟩ =
    .split (coordinate 12) (![⟨1085709, by decide⟩,⟨1085727, by decide⟩,⟨1085744, by decide⟩,⟨1085753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308494_1085754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308494 ⟨1085754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308494
    ⟨1085754, by decide⟩ (by decide) (![⟨1085709, by decide⟩,⟨1085727, by decide⟩,⟨1085744, by decide⟩,⟨1085753, by decide⟩]) unmarked_context_12_308494_1085754 node_context_12_308494_1085754
  intro a
  fin_cases a
  · exact context_13_1233976_1085709
  · exact context_13_1233977_1085727
  · exact context_13_1233978_1085744
  · exact context_13_1233979_1085753

theorem selected_cut_40007 : selected 9 ⟨1085811, by decide⟩
    (prefixPartial 12 308495) = some ⟨12, 2, 0, 1085811, 308495, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_308495_1085811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308495 ⟨1085811, by decide⟩ :=
  accepted_of_selected 12 308495 ⟨1085811, by decide⟩ ⟨12, 2, 0, 1085811, 308495, 3909, 65536⟩
    (by decide) selected_cut_40007

theorem unmarked_context_11_77123_1085812 : frontier 10 ⟨1085812, by decide⟩
    (prefixCache 11 77123) (prefixPartial 11 77123) = false := by
  decide +kernel

theorem node_context_11_77123_1085812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1085812, by decide⟩ =
    .split (coordinate 11) (![⟨1085631, by decide⟩,⟨1085688, by decide⟩,⟨1085754, by decide⟩,⟨1085811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77123_1085812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77123 ⟨1085812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77123
    ⟨1085812, by decide⟩ (by decide) (![⟨1085631, by decide⟩,⟨1085688, by decide⟩,⟨1085754, by decide⟩,⟨1085811, by decide⟩]) unmarked_context_11_77123_1085812 node_context_11_77123_1085812
  intro a
  fin_cases a
  · exact context_12_308492_1085631
  · exact context_12_308493_1085688
  · exact context_12_308494_1085754
  · exact context_12_308495_1085811

theorem unmarked_context_10_19280_1085813 : frontier 11 ⟨1085813, by decide⟩
    (prefixCache 10 19280) (prefixPartial 10 19280) = false := by
  decide +kernel

theorem node_context_10_19280_1085813 : EJMOriginalGlobalDAGData.nodes 11 ⟨1085813, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1085361, by decide⟩,⟨1085530, by decide⟩,⟨1085812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19280_1085813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19280 ⟨1085813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19280
    ⟨1085813, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1085361, by decide⟩,⟨1085530, by decide⟩,⟨1085812, by decide⟩]) unmarked_context_10_19280_1085813 node_context_10_19280_1085813
  intro a
  fin_cases a
  · exact context_11_77120_167448
  · exact context_11_77121_1085361
  · exact context_11_77122_1085530
  · exact context_11_77123_1085812

theorem selected_cut_40008 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 308496) = some ⟨12, 1, 0, 1072955, 308496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308496_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308496 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 308496 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 308496, 1, 65536⟩
    (by decide) selected_cut_40008

theorem selected_cut_40009 : selected 9 ⟨1085858, by decide⟩
    (prefixPartial 12 308497) = some ⟨12, 2, 0, 1085858, 308497, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_308497_1085858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308497 ⟨1085858, by decide⟩ :=
  accepted_of_selected 12 308497 ⟨1085858, by decide⟩ ⟨12, 2, 0, 1085858, 308497, 2873, 65536⟩
    (by decide) selected_cut_40009

theorem selected_cut_40010 : selected 9 ⟨1085904, by decide⟩
    (prefixPartial 12 308498) = some ⟨12, 2, 0, 1085904, 308498, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_308498_1085904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308498 ⟨1085904, by decide⟩ :=
  accepted_of_selected 12 308498 ⟨1085904, by decide⟩ ⟨12, 2, 0, 1085904, 308498, 3021, 65536⟩
    (by decide) selected_cut_40010

theorem selected_cut_40011 : selected 9 ⟨1085951, by decide⟩
    (prefixPartial 12 308499) = some ⟨12, 2, 0, 1085951, 308499, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_308499_1085951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308499 ⟨1085951, by decide⟩ :=
  accepted_of_selected 12 308499 ⟨1085951, by decide⟩ ⟨12, 2, 0, 1085951, 308499, 3245, 65536⟩
    (by decide) selected_cut_40011

theorem unmarked_context_11_77124_1085952 : frontier 10 ⟨1085952, by decide⟩
    (prefixCache 11 77124) (prefixPartial 11 77124) = false := by
  decide +kernel

theorem node_context_11_77124_1085952 : EJMOriginalGlobalDAGData.nodes 10 ⟨1085952, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1085858, by decide⟩,⟨1085904, by decide⟩,⟨1085951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77124_1085952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77124 ⟨1085952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77124
    ⟨1085952, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1085858, by decide⟩,⟨1085904, by decide⟩,⟨1085951, by decide⟩]) unmarked_context_11_77124_1085952 node_context_11_77124_1085952
  intro a
  fin_cases a
  · exact context_12_308496_1072955
  · exact context_12_308497_1085858
  · exact context_12_308498_1085904
  · exact context_12_308499_1085951

theorem selected_cut_40012 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 77125) = some ⟨11, 1, 0, 892405, 77125, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77125_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77125 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 77125 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 77125, 1, 262144⟩
    (by decide) selected_cut_40012

theorem selected_cut_40013 : selected 9 ⟨1086001, by decide⟩
    (prefixPartial 12 308504) = some ⟨12, 2, 0, 1086001, 308504, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_308504_1086001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308504 ⟨1086001, by decide⟩ :=
  accepted_of_selected 12 308504 ⟨1086001, by decide⟩ ⟨12, 2, 0, 1086001, 308504, 3405, 65536⟩
    (by decide) selected_cut_40013

theorem selected_cut_40014 : selected 9 ⟨1086041, by decide⟩
    (prefixPartial 12 308505) = some ⟨12, 2, 0, 1086041, 308505, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_308505_1086041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308505 ⟨1086041, by decide⟩ :=
  accepted_of_selected 12 308505 ⟨1086041, by decide⟩ ⟨12, 2, 0, 1086041, 308505, 2881, 65536⟩
    (by decide) selected_cut_40014

theorem selected_cut_40015 : selected 9 ⟨1086089, by decide⟩
    (prefixPartial 12 308506) = some ⟨12, 2, 0, 1086089, 308506, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_308506_1086089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308506 ⟨1086089, by decide⟩ :=
  accepted_of_selected 12 308506 ⟨1086089, by decide⟩ ⟨12, 2, 0, 1086089, 308506, 3217, 65536⟩
    (by decide) selected_cut_40015

theorem selected_cut_40016 : selected 9 ⟨1086138, by decide⟩
    (prefixPartial 12 308507) = some ⟨12, 2, 0, 1086138, 308507, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_308507_1086138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308507 ⟨1086138, by decide⟩ :=
  accepted_of_selected 12 308507 ⟨1086138, by decide⟩ ⟨12, 2, 0, 1086138, 308507, 3313, 65536⟩
    (by decide) selected_cut_40016

theorem unmarked_context_11_77126_1086139 : frontier 10 ⟨1086139, by decide⟩
    (prefixCache 11 77126) (prefixPartial 11 77126) = false := by
  decide +kernel

theorem node_context_11_77126_1086139 : EJMOriginalGlobalDAGData.nodes 10 ⟨1086139, by decide⟩ =
    .split (coordinate 11) (![⟨1086001, by decide⟩,⟨1086041, by decide⟩,⟨1086089, by decide⟩,⟨1086138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77126_1086139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77126 ⟨1086139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77126
    ⟨1086139, by decide⟩ (by decide) (![⟨1086001, by decide⟩,⟨1086041, by decide⟩,⟨1086089, by decide⟩,⟨1086138, by decide⟩]) unmarked_context_11_77126_1086139 node_context_11_77126_1086139
  intro a
  fin_cases a
  · exact context_12_308504_1086001
  · exact context_12_308505_1086041
  · exact context_12_308506_1086089
  · exact context_12_308507_1086138

theorem selected_cut_40017 : selected 9 ⟨1086199, by decide⟩
    (prefixPartial 12 308508) = some ⟨12, 2, 0, 1086199, 308508, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_308508_1086199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308508 ⟨1086199, by decide⟩ :=
  accepted_of_selected 12 308508 ⟨1086199, by decide⟩ ⟨12, 2, 0, 1086199, 308508, 3733, 65536⟩
    (by decide) selected_cut_40017

theorem selected_cut_40018 : selected 9 ⟨1086246, by decide⟩
    (prefixPartial 12 308509) = some ⟨12, 2, 0, 1086246, 308509, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_308509_1086246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308509 ⟨1086246, by decide⟩ :=
  accepted_of_selected 12 308509 ⟨1086246, by decide⟩ ⟨12, 2, 0, 1086246, 308509, 3089, 65536⟩
    (by decide) selected_cut_40018

theorem selected_cut_40019 : selected 9 ⟨1086293, by decide⟩
    (prefixPartial 12 308510) = some ⟨12, 2, 0, 1086293, 308510, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_308510_1086293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308510 ⟨1086293, by decide⟩ :=
  accepted_of_selected 12 308510 ⟨1086293, by decide⟩ ⟨12, 2, 0, 1086293, 308510, 3393, 65536⟩
    (by decide) selected_cut_40019

theorem selected_cut_40020 : selected 9 ⟨1086344, by decide⟩
    (prefixPartial 12 308511) = some ⟨12, 2, 0, 1086344, 308511, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_308511_1086344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308511 ⟨1086344, by decide⟩ :=
  accepted_of_selected 12 308511 ⟨1086344, by decide⟩ ⟨12, 2, 0, 1086344, 308511, 3517, 65536⟩
    (by decide) selected_cut_40020

theorem unmarked_context_11_77127_1086345 : frontier 10 ⟨1086345, by decide⟩
    (prefixCache 11 77127) (prefixPartial 11 77127) = false := by
  decide +kernel

theorem node_context_11_77127_1086345 : EJMOriginalGlobalDAGData.nodes 10 ⟨1086345, by decide⟩ =
    .split (coordinate 11) (![⟨1086199, by decide⟩,⟨1086246, by decide⟩,⟨1086293, by decide⟩,⟨1086344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77127_1086345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77127 ⟨1086345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77127
    ⟨1086345, by decide⟩ (by decide) (![⟨1086199, by decide⟩,⟨1086246, by decide⟩,⟨1086293, by decide⟩,⟨1086344, by decide⟩]) unmarked_context_11_77127_1086345 node_context_11_77127_1086345
  intro a
  fin_cases a
  · exact context_12_308508_1086199
  · exact context_12_308509_1086246
  · exact context_12_308510_1086293
  · exact context_12_308511_1086344

theorem unmarked_context_10_19281_1086346 : frontier 11 ⟨1086346, by decide⟩
    (prefixCache 10 19281) (prefixPartial 10 19281) = false := by
  decide +kernel

theorem node_context_10_19281_1086346 : EJMOriginalGlobalDAGData.nodes 11 ⟨1086346, by decide⟩ =
    .split (coordinate 10) (![⟨1085952, by decide⟩,⟨892405, by decide⟩,⟨1086139, by decide⟩,⟨1086345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19281_1086346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19281 ⟨1086346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19281
    ⟨1086346, by decide⟩ (by decide) (![⟨1085952, by decide⟩,⟨892405, by decide⟩,⟨1086139, by decide⟩,⟨1086345, by decide⟩]) unmarked_context_10_19281_1086346 node_context_10_19281_1086346
  intro a
  fin_cases a
  · exact context_11_77124_1085952
  · exact context_11_77125_892405
  · exact context_11_77126_1086139
  · exact context_11_77127_1086345

theorem selected_cut_40021 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 308512) = some ⟨12, 1, 0, 1072955, 308512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308512_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308512 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 308512 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 308512, 1, 65536⟩
    (by decide) selected_cut_40021

theorem selected_cut_40022 : selected 9 ⟨1086400, by decide⟩
    (prefixPartial 12 308513) = some ⟨12, 2, 0, 1086400, 308513, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_308513_1086400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308513 ⟨1086400, by decide⟩ :=
  accepted_of_selected 12 308513 ⟨1086400, by decide⟩ ⟨12, 2, 0, 1086400, 308513, 3281, 65536⟩
    (by decide) selected_cut_40022

theorem selected_cut_40023 : selected 9 ⟨1086464, by decide⟩
    (prefixPartial 12 308514) = some ⟨12, 2, 0, 1086464, 308514, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_308514_1086464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308514 ⟨1086464, by decide⟩ :=
  accepted_of_selected 12 308514 ⟨1086464, by decide⟩ ⟨12, 2, 0, 1086464, 308514, 3461, 65536⟩
    (by decide) selected_cut_40023

theorem selected_cut_40024 : selected 9 ⟨1086518, by decide⟩
    (prefixPartial 12 308515) = some ⟨12, 2, 0, 1086518, 308515, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_308515_1086518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308515 ⟨1086518, by decide⟩ :=
  accepted_of_selected 12 308515 ⟨1086518, by decide⟩ ⟨12, 2, 0, 1086518, 308515, 3589, 65536⟩
    (by decide) selected_cut_40024

theorem unmarked_context_11_77128_1086519 : frontier 10 ⟨1086519, by decide⟩
    (prefixCache 11 77128) (prefixPartial 11 77128) = false := by
  decide +kernel

theorem node_context_11_77128_1086519 : EJMOriginalGlobalDAGData.nodes 10 ⟨1086519, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1086400, by decide⟩,⟨1086464, by decide⟩,⟨1086518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77128_1086519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77128 ⟨1086519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77128
    ⟨1086519, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1086400, by decide⟩,⟨1086464, by decide⟩,⟨1086518, by decide⟩]) unmarked_context_11_77128_1086519 node_context_11_77128_1086519
  intro a
  fin_cases a
  · exact context_12_308512_1072955
  · exact context_12_308513_1086400
  · exact context_12_308514_1086464
  · exact context_12_308515_1086518

theorem selected_cut_40025 : selected 9 ⟨1086583, by decide⟩
    (prefixPartial 12 308516) = some ⟨12, 2, 0, 1086583, 308516, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_308516_1086583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308516 ⟨1086583, by decide⟩ :=
  accepted_of_selected 12 308516 ⟨1086583, by decide⟩ ⟨12, 2, 0, 1086583, 308516, 3513, 65536⟩
    (by decide) selected_cut_40025

theorem selected_cut_40026 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 308517) = some ⟨12, 1, 0, 891951, 308517, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308517_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308517 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 308517 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 308517, 1, 65536⟩
    (by decide) selected_cut_40026

theorem selected_cut_40027 : selected 9 ⟨1086634, by decide⟩
    (prefixPartial 12 308518) = some ⟨12, 2, 0, 1086634, 308518, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_308518_1086634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308518 ⟨1086634, by decide⟩ :=
  accepted_of_selected 12 308518 ⟨1086634, by decide⟩ ⟨12, 2, 0, 1086634, 308518, 3285, 65536⟩
    (by decide) selected_cut_40027

theorem selected_cut_40028 : selected 9 ⟨1086685, by decide⟩
    (prefixPartial 12 308519) = some ⟨12, 2, 0, 1086685, 308519, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_308519_1086685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308519 ⟨1086685, by decide⟩ :=
  accepted_of_selected 12 308519 ⟨1086685, by decide⟩ ⟨12, 2, 0, 1086685, 308519, 3377, 65536⟩
    (by decide) selected_cut_40028

theorem unmarked_context_11_77129_1086686 : frontier 10 ⟨1086686, by decide⟩
    (prefixCache 11 77129) (prefixPartial 11 77129) = false := by
  decide +kernel

theorem node_context_11_77129_1086686 : EJMOriginalGlobalDAGData.nodes 10 ⟨1086686, by decide⟩ =
    .split (coordinate 11) (![⟨1086583, by decide⟩,⟨891951, by decide⟩,⟨1086634, by decide⟩,⟨1086685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77129_1086686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77129 ⟨1086686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77129
    ⟨1086686, by decide⟩ (by decide) (![⟨1086583, by decide⟩,⟨891951, by decide⟩,⟨1086634, by decide⟩,⟨1086685, by decide⟩]) unmarked_context_11_77129_1086686 node_context_11_77129_1086686
  intro a
  fin_cases a
  · exact context_12_308516_1086583
  · exact context_12_308517_891951
  · exact context_12_308518_1086634
  · exact context_12_308519_1086685

theorem selected_cut_40029 : selected 9 ⟨1086751, by decide⟩
    (prefixPartial 12 308520) = some ⟨12, 2, 0, 1086751, 308520, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_308520_1086751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308520 ⟨1086751, by decide⟩ :=
  accepted_of_selected 12 308520 ⟨1086751, by decide⟩ ⟨12, 2, 0, 1086751, 308520, 3797, 65536⟩
    (by decide) selected_cut_40029

theorem selected_cut_40030 : selected 9 ⟨1086804, by decide⟩
    (prefixPartial 12 308521) = some ⟨12, 2, 0, 1086804, 308521, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_308521_1086804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308521 ⟨1086804, by decide⟩ :=
  accepted_of_selected 12 308521 ⟨1086804, by decide⟩ ⟨12, 2, 0, 1086804, 308521, 3357, 65536⟩
    (by decide) selected_cut_40030

theorem selected_cut_40031 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 308522) = some ⟨12, 1, 0, 661671, 308522, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308522_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308522 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 308522 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 308522, 1, 65536⟩
    (by decide) selected_cut_40031

theorem selected_cut_40032 : selected 9 ⟨1086871, by decide⟩
    (prefixPartial 12 308523) = some ⟨12, 2, 0, 1086871, 308523, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_308523_1086871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308523 ⟨1086871, by decide⟩ :=
  accepted_of_selected 12 308523 ⟨1086871, by decide⟩ ⟨12, 2, 0, 1086871, 308523, 3821, 65536⟩
    (by decide) selected_cut_40032

theorem unmarked_context_11_77130_1086872 : frontier 10 ⟨1086872, by decide⟩
    (prefixCache 11 77130) (prefixPartial 11 77130) = false := by
  decide +kernel

theorem node_context_11_77130_1086872 : EJMOriginalGlobalDAGData.nodes 10 ⟨1086872, by decide⟩ =
    .split (coordinate 11) (![⟨1086751, by decide⟩,⟨1086804, by decide⟩,⟨661671, by decide⟩,⟨1086871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77130_1086872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77130 ⟨1086872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77130
    ⟨1086872, by decide⟩ (by decide) (![⟨1086751, by decide⟩,⟨1086804, by decide⟩,⟨661671, by decide⟩,⟨1086871, by decide⟩]) unmarked_context_11_77130_1086872 node_context_11_77130_1086872
  intro a
  fin_cases a
  · exact context_12_308520_1086751
  · exact context_12_308521_1086804
  · exact context_12_308522_661671
  · exact context_12_308523_1086871

theorem selected_cut_40033 : selected 9 ⟨1086931, by decide⟩
    (prefixPartial 12 308524) = some ⟨12, 2, 0, 1086931, 308524, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_308524_1086931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308524 ⟨1086931, by decide⟩ :=
  accepted_of_selected 12 308524 ⟨1086931, by decide⟩ ⟨12, 2, 0, 1086931, 308524, 3601, 65536⟩
    (by decide) selected_cut_40033

theorem selected_cut_40034 : selected 9 ⟨1086971, by decide⟩
    (prefixPartial 12 308525) = some ⟨12, 2, 0, 1086971, 308525, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_308525_1086971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308525 ⟨1086971, by decide⟩ :=
  accepted_of_selected 12 308525 ⟨1086971, by decide⟩ ⟨12, 2, 0, 1086971, 308525, 3117, 65536⟩
    (by decide) selected_cut_40034

theorem selected_cut_40035 : selected 9 ⟨1087027, by decide⟩
    (prefixPartial 12 308526) = some ⟨12, 2, 0, 1087027, 308526, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_308526_1087027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308526 ⟨1087027, by decide⟩ :=
  accepted_of_selected 12 308526 ⟨1087027, by decide⟩ ⟨12, 2, 0, 1087027, 308526, 3429, 65536⟩
    (by decide) selected_cut_40035

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
