/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover238
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22947 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 76074) = some ⟨12, 1, 0, 474208, 76074, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76074_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76074 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 76074 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 76074, 1, 65536⟩
    (by decide) selected_cut_22947

theorem selected_cut_22948 : selected 8 ⟨582132, by decide⟩
    (prefixPartial 13 304300) = some ⟨13, 2, 0, 582132, 304300, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_304300_582132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304300 ⟨582132, by decide⟩ :=
  accepted_of_selected 13 304300 ⟨582132, by decide⟩ ⟨13, 2, 0, 582132, 304300, 1297, 16384⟩
    (by decide) selected_cut_22948

theorem selected_cut_22949 : selected 8 ⟨582155, by decide⟩
    (prefixPartial 13 304301) = some ⟨13, 2, 0, 582155, 304301, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_304301_582155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304301 ⟨582155, by decide⟩ :=
  accepted_of_selected 13 304301 ⟨582155, by decide⟩ ⟨13, 2, 0, 582155, 304301, 2497, 16384⟩
    (by decide) selected_cut_22949

theorem selected_cut_22950 : selected 8 ⟨582169, by decide⟩
    (prefixPartial 13 304302) = some ⟨13, 2, 0, 582169, 304302, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_304302_582169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304302 ⟨582169, by decide⟩ :=
  accepted_of_selected 13 304302 ⟨582169, by decide⟩ ⟨13, 2, 0, 582169, 304302, 1833, 16384⟩
    (by decide) selected_cut_22950

theorem selected_cut_22951 : selected 8 ⟨582174, by decide⟩
    (prefixPartial 13 304303) = some ⟨13, 2, 0, 582174, 304303, 989, 16384⟩ := by
  decide +kernel

theorem context_13_304303_582174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304303 ⟨582174, by decide⟩ :=
  accepted_of_selected 13 304303 ⟨582174, by decide⟩ ⟨13, 2, 0, 582174, 304303, 989, 16384⟩
    (by decide) selected_cut_22951

theorem unmarked_context_12_76075_582175 : frontier 9 ⟨582175, by decide⟩
    (prefixCache 12 76075) (prefixPartial 12 76075) = false := by
  decide +kernel

theorem node_context_12_76075_582175 : EJMOriginalGlobalDAGData.nodes 9 ⟨582175, by decide⟩ =
    .split (coordinate 12) (![⟨582132, by decide⟩,⟨582155, by decide⟩,⟨582169, by decide⟩,⟨582174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76075_582175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76075 ⟨582175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76075
    ⟨582175, by decide⟩ (by decide) (![⟨582132, by decide⟩,⟨582155, by decide⟩,⟨582169, by decide⟩,⟨582174, by decide⟩]) unmarked_context_12_76075_582175 node_context_12_76075_582175
  intro a
  fin_cases a
  · exact context_13_304300_582132
  · exact context_13_304301_582155
  · exact context_13_304302_582169
  · exact context_13_304303_582174

theorem unmarked_context_11_19018_582176 : frontier 10 ⟨582176, by decide⟩
    (prefixCache 11 19018) (prefixPartial 11 19018) = false := by
  decide +kernel

theorem node_context_11_19018_582176 : EJMOriginalGlobalDAGData.nodes 10 ⟨582176, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨582107, by decide⟩,⟨474208, by decide⟩,⟨582175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19018_582176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19018 ⟨582176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19018
    ⟨582176, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨582107, by decide⟩,⟨474208, by decide⟩,⟨582175, by decide⟩]) unmarked_context_11_19018_582176 node_context_11_19018_582176
  intro a
  fin_cases a
  · exact context_12_76072_435790
  · exact context_12_76073_582107
  · exact context_12_76074_474208
  · exact context_12_76075_582175

theorem selected_cut_22952 : selected 8 ⟨582195, by decide⟩
    (prefixPartial 13 304304) = some ⟨13, 2, 0, 582195, 304304, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_304304_582195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304304 ⟨582195, by decide⟩ :=
  accepted_of_selected 13 304304 ⟨582195, by decide⟩ ⟨13, 2, 0, 582195, 304304, 1137, 16384⟩
    (by decide) selected_cut_22952

theorem selected_cut_22953 : selected 8 ⟨582222, by decide⟩
    (prefixPartial 13 304305) = some ⟨13, 2, 0, 582222, 304305, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_304305_582222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304305 ⟨582222, by decide⟩ :=
  accepted_of_selected 13 304305 ⟨582222, by decide⟩ ⟨13, 2, 0, 582222, 304305, 2737, 16384⟩
    (by decide) selected_cut_22953

theorem selected_cut_22954 : selected 8 ⟨582244, by decide⟩
    (prefixPartial 13 304306) = some ⟨13, 2, 0, 582244, 304306, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_304306_582244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304306 ⟨582244, by decide⟩ :=
  accepted_of_selected 13 304306 ⟨582244, by decide⟩ ⟨13, 2, 0, 582244, 304306, 1913, 16384⟩
    (by decide) selected_cut_22954

theorem selected_cut_22955 : selected 8 ⟨582253, by decide⟩
    (prefixPartial 13 304307) = some ⟨13, 2, 0, 582253, 304307, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_304307_582253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304307 ⟨582253, by decide⟩ :=
  accepted_of_selected 13 304307 ⟨582253, by decide⟩ ⟨13, 2, 0, 582253, 304307, 1089, 16384⟩
    (by decide) selected_cut_22955

theorem unmarked_context_12_76076_582254 : frontier 9 ⟨582254, by decide⟩
    (prefixCache 12 76076) (prefixPartial 12 76076) = false := by
  decide +kernel

theorem node_context_12_76076_582254 : EJMOriginalGlobalDAGData.nodes 9 ⟨582254, by decide⟩ =
    .split (coordinate 12) (![⟨582195, by decide⟩,⟨582222, by decide⟩,⟨582244, by decide⟩,⟨582253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76076_582254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76076 ⟨582254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76076
    ⟨582254, by decide⟩ (by decide) (![⟨582195, by decide⟩,⟨582222, by decide⟩,⟨582244, by decide⟩,⟨582253, by decide⟩]) unmarked_context_12_76076_582254 node_context_12_76076_582254
  intro a
  fin_cases a
  · exact context_13_304304_582195
  · exact context_13_304305_582222
  · exact context_13_304306_582244
  · exact context_13_304307_582253

theorem selected_cut_22956 : selected 8 ⟨582270, by decide⟩
    (prefixPartial 13 304308) = some ⟨13, 2, 0, 582270, 304308, 681, 16384⟩ := by
  decide +kernel

theorem context_13_304308_582270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304308 ⟨582270, by decide⟩ :=
  accepted_of_selected 13 304308 ⟨582270, by decide⟩ ⟨13, 2, 0, 582270, 304308, 681, 16384⟩
    (by decide) selected_cut_22956

theorem selected_cut_22957 : selected 8 ⟨582291, by decide⟩
    (prefixPartial 13 304309) = some ⟨13, 2, 0, 582291, 304309, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_304309_582291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304309 ⟨582291, by decide⟩ :=
  accepted_of_selected 13 304309 ⟨582291, by decide⟩ ⟨13, 2, 0, 582291, 304309, 1717, 16384⟩
    (by decide) selected_cut_22957

theorem selected_cut_22958 : selected 8 ⟨582309, by decide⟩
    (prefixPartial 13 304310) = some ⟨13, 2, 0, 582309, 304310, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_304310_582309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304310 ⟨582309, by decide⟩ :=
  accepted_of_selected 13 304310 ⟨582309, by decide⟩ ⟨13, 2, 0, 582309, 304310, 1413, 16384⟩
    (by decide) selected_cut_22958

theorem selected_cut_22959 : selected 8 ⟨582314, by decide⟩
    (prefixPartial 13 304311) = some ⟨13, 2, 0, 582314, 304311, 817, 16384⟩ := by
  decide +kernel

theorem context_13_304311_582314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304311 ⟨582314, by decide⟩ :=
  accepted_of_selected 13 304311 ⟨582314, by decide⟩ ⟨13, 2, 0, 582314, 304311, 817, 16384⟩
    (by decide) selected_cut_22959

theorem unmarked_context_12_76077_582315 : frontier 9 ⟨582315, by decide⟩
    (prefixCache 12 76077) (prefixPartial 12 76077) = false := by
  decide +kernel

theorem node_context_12_76077_582315 : EJMOriginalGlobalDAGData.nodes 9 ⟨582315, by decide⟩ =
    .split (coordinate 12) (![⟨582270, by decide⟩,⟨582291, by decide⟩,⟨582309, by decide⟩,⟨582314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76077_582315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76077 ⟨582315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76077
    ⟨582315, by decide⟩ (by decide) (![⟨582270, by decide⟩,⟨582291, by decide⟩,⟨582309, by decide⟩,⟨582314, by decide⟩]) unmarked_context_12_76077_582315 node_context_12_76077_582315
  intro a
  fin_cases a
  · exact context_13_304308_582270
  · exact context_13_304309_582291
  · exact context_13_304310_582309
  · exact context_13_304311_582314

theorem selected_cut_22960 : selected 8 ⟨582326, by decide⟩
    (prefixPartial 13 304312) = some ⟨13, 2, 0, 582326, 304312, 777, 16384⟩ := by
  decide +kernel

theorem context_13_304312_582326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304312 ⟨582326, by decide⟩ :=
  accepted_of_selected 13 304312 ⟨582326, by decide⟩ ⟨13, 2, 0, 582326, 304312, 777, 16384⟩
    (by decide) selected_cut_22960

theorem selected_cut_22961 : selected 8 ⟨582346, by decide⟩
    (prefixPartial 13 304313) = some ⟨13, 2, 0, 582346, 304313, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_304313_582346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304313 ⟨582346, by decide⟩ :=
  accepted_of_selected 13 304313 ⟨582346, by decide⟩ ⟨13, 2, 0, 582346, 304313, 1861, 16384⟩
    (by decide) selected_cut_22961

theorem selected_cut_22962 : selected 8 ⟨582366, by decide⟩
    (prefixPartial 13 304314) = some ⟨13, 2, 0, 582366, 304314, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_304314_582366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304314 ⟨582366, by decide⟩ :=
  accepted_of_selected 13 304314 ⟨582366, by decide⟩ ⟨13, 2, 0, 582366, 304314, 1449, 16384⟩
    (by decide) selected_cut_22962

theorem selected_cut_22963 : selected 8 ⟨582373, by decide⟩
    (prefixPartial 13 304315) = some ⟨13, 2, 0, 582373, 304315, 945, 16384⟩ := by
  decide +kernel

theorem context_13_304315_582373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304315 ⟨582373, by decide⟩ :=
  accepted_of_selected 13 304315 ⟨582373, by decide⟩ ⟨13, 2, 0, 582373, 304315, 945, 16384⟩
    (by decide) selected_cut_22963

theorem unmarked_context_12_76078_582374 : frontier 9 ⟨582374, by decide⟩
    (prefixCache 12 76078) (prefixPartial 12 76078) = false := by
  decide +kernel

theorem node_context_12_76078_582374 : EJMOriginalGlobalDAGData.nodes 9 ⟨582374, by decide⟩ =
    .split (coordinate 12) (![⟨582326, by decide⟩,⟨582346, by decide⟩,⟨582366, by decide⟩,⟨582373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76078_582374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76078 ⟨582374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76078
    ⟨582374, by decide⟩ (by decide) (![⟨582326, by decide⟩,⟨582346, by decide⟩,⟨582366, by decide⟩,⟨582373, by decide⟩]) unmarked_context_12_76078_582374 node_context_12_76078_582374
  intro a
  fin_cases a
  · exact context_13_304312_582326
  · exact context_13_304313_582346
  · exact context_13_304314_582366
  · exact context_13_304315_582373

theorem selected_cut_22964 : selected 8 ⟨582389, by decide⟩
    (prefixPartial 13 304316) = some ⟨13, 2, 0, 582389, 304316, 709, 16384⟩ := by
  decide +kernel

theorem context_13_304316_582389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304316 ⟨582389, by decide⟩ :=
  accepted_of_selected 13 304316 ⟨582389, by decide⟩ ⟨13, 2, 0, 582389, 304316, 709, 16384⟩
    (by decide) selected_cut_22964

theorem selected_cut_22965 : selected 8 ⟨582411, by decide⟩
    (prefixPartial 13 304317) = some ⟨13, 2, 0, 582411, 304317, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_304317_582411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304317 ⟨582411, by decide⟩ :=
  accepted_of_selected 13 304317 ⟨582411, by decide⟩ ⟨13, 2, 0, 582411, 304317, 1937, 16384⟩
    (by decide) selected_cut_22965

theorem selected_cut_22966 : selected 8 ⟨582429, by decide⟩
    (prefixPartial 13 304318) = some ⟨13, 2, 0, 582429, 304318, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_304318_582429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304318 ⟨582429, by decide⟩ :=
  accepted_of_selected 13 304318 ⟨582429, by decide⟩ ⟨13, 2, 0, 582429, 304318, 1533, 16384⟩
    (by decide) selected_cut_22966

theorem selected_cut_22967 : selected 8 ⟨582435, by decide⟩
    (prefixPartial 13 304319) = some ⟨13, 2, 0, 582435, 304319, 789, 16384⟩ := by
  decide +kernel

theorem context_13_304319_582435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304319 ⟨582435, by decide⟩ :=
  accepted_of_selected 13 304319 ⟨582435, by decide⟩ ⟨13, 2, 0, 582435, 304319, 789, 16384⟩
    (by decide) selected_cut_22967

theorem unmarked_context_12_76079_582436 : frontier 9 ⟨582436, by decide⟩
    (prefixCache 12 76079) (prefixPartial 12 76079) = false := by
  decide +kernel

theorem node_context_12_76079_582436 : EJMOriginalGlobalDAGData.nodes 9 ⟨582436, by decide⟩ =
    .split (coordinate 12) (![⟨582389, by decide⟩,⟨582411, by decide⟩,⟨582429, by decide⟩,⟨582435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76079_582436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76079 ⟨582436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76079
    ⟨582436, by decide⟩ (by decide) (![⟨582389, by decide⟩,⟨582411, by decide⟩,⟨582429, by decide⟩,⟨582435, by decide⟩]) unmarked_context_12_76079_582436 node_context_12_76079_582436
  intro a
  fin_cases a
  · exact context_13_304316_582389
  · exact context_13_304317_582411
  · exact context_13_304318_582429
  · exact context_13_304319_582435

theorem unmarked_context_11_19019_582437 : frontier 10 ⟨582437, by decide⟩
    (prefixCache 11 19019) (prefixPartial 11 19019) = false := by
  decide +kernel

theorem node_context_11_19019_582437 : EJMOriginalGlobalDAGData.nodes 10 ⟨582437, by decide⟩ =
    .split (coordinate 11) (![⟨582254, by decide⟩,⟨582315, by decide⟩,⟨582374, by decide⟩,⟨582436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19019_582437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19019 ⟨582437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19019
    ⟨582437, by decide⟩ (by decide) (![⟨582254, by decide⟩,⟨582315, by decide⟩,⟨582374, by decide⟩,⟨582436, by decide⟩]) unmarked_context_11_19019_582437 node_context_11_19019_582437
  intro a
  fin_cases a
  · exact context_12_76076_582254
  · exact context_12_76077_582315
  · exact context_12_76078_582374
  · exact context_12_76079_582436

theorem unmarked_context_10_4754_582438 : frontier 11 ⟨582438, by decide⟩
    (prefixCache 10 4754) (prefixPartial 10 4754) = false := by
  decide +kernel

theorem node_context_10_4754_582438 : EJMOriginalGlobalDAGData.nodes 11 ⟨582438, by decide⟩ =
    .split (coordinate 10) (![⟨581771, by decide⟩,⟨582038, by decide⟩,⟨582176, by decide⟩,⟨582437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4754_582438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4754 ⟨582438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4754
    ⟨582438, by decide⟩ (by decide) (![⟨581771, by decide⟩,⟨582038, by decide⟩,⟨582176, by decide⟩,⟨582437, by decide⟩]) unmarked_context_10_4754_582438 node_context_10_4754_582438
  intro a
  fin_cases a
  · exact context_11_19016_581771
  · exact context_11_19017_582038
  · exact context_11_19018_582176
  · exact context_11_19019_582437

theorem selected_cut_22968 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76080) = some ⟨12, 1, 0, 445562, 76080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76080_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76080 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76080 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76080, 1, 65536⟩
    (by decide) selected_cut_22968

theorem selected_cut_22969 : selected 8 ⟨582446, by decide⟩
    (prefixPartial 13 304324) = some ⟨13, 2, 0, 582446, 304324, 613, 16384⟩ := by
  decide +kernel

theorem context_13_304324_582446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304324 ⟨582446, by decide⟩ :=
  accepted_of_selected 13 304324 ⟨582446, by decide⟩ ⟨13, 2, 0, 582446, 304324, 613, 16384⟩
    (by decide) selected_cut_22969

theorem selected_cut_22970 : selected 8 ⟨582471, by decide⟩
    (prefixPartial 13 304325) = some ⟨13, 2, 0, 582471, 304325, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_304325_582471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304325 ⟨582471, by decide⟩ :=
  accepted_of_selected 13 304325 ⟨582471, by decide⟩ ⟨13, 2, 0, 582471, 304325, 2129, 16384⟩
    (by decide) selected_cut_22970

theorem selected_cut_22971 : selected 8 ⟨582490, by decide⟩
    (prefixPartial 13 304326) = some ⟨13, 2, 0, 582490, 304326, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_304326_582490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304326 ⟨582490, by decide⟩ :=
  accepted_of_selected 13 304326 ⟨582490, by decide⟩ ⟨13, 2, 0, 582490, 304326, 1597, 16384⟩
    (by decide) selected_cut_22971

theorem selected_cut_22972 : selected 8 ⟨582494, by decide⟩
    (prefixPartial 13 304327) = some ⟨13, 2, 0, 582494, 304327, 873, 16384⟩ := by
  decide +kernel

theorem context_13_304327_582494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304327 ⟨582494, by decide⟩ :=
  accepted_of_selected 13 304327 ⟨582494, by decide⟩ ⟨13, 2, 0, 582494, 304327, 873, 16384⟩
    (by decide) selected_cut_22972

theorem unmarked_context_12_76081_582495 : frontier 9 ⟨582495, by decide⟩
    (prefixCache 12 76081) (prefixPartial 12 76081) = false := by
  decide +kernel

theorem node_context_12_76081_582495 : EJMOriginalGlobalDAGData.nodes 9 ⟨582495, by decide⟩ =
    .split (coordinate 12) (![⟨582446, by decide⟩,⟨582471, by decide⟩,⟨582490, by decide⟩,⟨582494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76081_582495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76081 ⟨582495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76081
    ⟨582495, by decide⟩ (by decide) (![⟨582446, by decide⟩,⟨582471, by decide⟩,⟨582490, by decide⟩,⟨582494, by decide⟩]) unmarked_context_12_76081_582495 node_context_12_76081_582495
  intro a
  fin_cases a
  · exact context_13_304324_582446
  · exact context_13_304325_582471
  · exact context_13_304326_582490
  · exact context_13_304327_582494

theorem selected_cut_22973 : selected 8 ⟨582510, by decide⟩
    (prefixPartial 13 304328) = some ⟨13, 2, 0, 582510, 304328, 729, 16384⟩ := by
  decide +kernel

theorem context_13_304328_582510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304328 ⟨582510, by decide⟩ :=
  accepted_of_selected 13 304328 ⟨582510, by decide⟩ ⟨13, 2, 0, 582510, 304328, 729, 16384⟩
    (by decide) selected_cut_22973

theorem selected_cut_22974 : selected 8 ⟨582538, by decide⟩
    (prefixPartial 13 304329) = some ⟨13, 2, 0, 582538, 304329, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_304329_582538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304329 ⟨582538, by decide⟩ :=
  accepted_of_selected 13 304329 ⟨582538, by decide⟩ ⟨13, 2, 0, 582538, 304329, 2305, 16384⟩
    (by decide) selected_cut_22974

theorem selected_cut_22975 : selected 8 ⟨582557, by decide⟩
    (prefixPartial 13 304330) = some ⟨13, 2, 0, 582557, 304330, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_304330_582557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304330 ⟨582557, by decide⟩ :=
  accepted_of_selected 13 304330 ⟨582557, by decide⟩ ⟨13, 2, 0, 582557, 304330, 1893, 16384⟩
    (by decide) selected_cut_22975

theorem selected_cut_22976 : selected 8 ⟨582565, by decide⟩
    (prefixPartial 13 304331) = some ⟨13, 2, 0, 582565, 304331, 905, 16384⟩ := by
  decide +kernel

theorem context_13_304331_582565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304331 ⟨582565, by decide⟩ :=
  accepted_of_selected 13 304331 ⟨582565, by decide⟩ ⟨13, 2, 0, 582565, 304331, 905, 16384⟩
    (by decide) selected_cut_22976

theorem unmarked_context_12_76082_582566 : frontier 9 ⟨582566, by decide⟩
    (prefixCache 12 76082) (prefixPartial 12 76082) = false := by
  decide +kernel

theorem node_context_12_76082_582566 : EJMOriginalGlobalDAGData.nodes 9 ⟨582566, by decide⟩ =
    .split (coordinate 12) (![⟨582510, by decide⟩,⟨582538, by decide⟩,⟨582557, by decide⟩,⟨582565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76082_582566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76082 ⟨582566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76082
    ⟨582566, by decide⟩ (by decide) (![⟨582510, by decide⟩,⟨582538, by decide⟩,⟨582557, by decide⟩,⟨582565, by decide⟩]) unmarked_context_12_76082_582566 node_context_12_76082_582566
  intro a
  fin_cases a
  · exact context_13_304328_582510
  · exact context_13_304329_582538
  · exact context_13_304330_582557
  · exact context_13_304331_582565

theorem selected_cut_22977 : selected 8 ⟨582577, by decide⟩
    (prefixPartial 13 304332) = some ⟨13, 2, 0, 582577, 304332, 789, 16384⟩ := by
  decide +kernel

theorem context_13_304332_582577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304332 ⟨582577, by decide⟩ :=
  accepted_of_selected 13 304332 ⟨582577, by decide⟩ ⟨13, 2, 0, 582577, 304332, 789, 16384⟩
    (by decide) selected_cut_22977

theorem selected_cut_22978 : selected 8 ⟨582606, by decide⟩
    (prefixPartial 13 304333) = some ⟨13, 2, 0, 582606, 304333, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_304333_582606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304333 ⟨582606, by decide⟩ :=
  accepted_of_selected 13 304333 ⟨582606, by decide⟩ ⟨13, 2, 0, 582606, 304333, 2429, 16384⟩
    (by decide) selected_cut_22978

theorem selected_cut_22979 : selected 8 ⟨582626, by decide⟩
    (prefixPartial 13 304334) = some ⟨13, 2, 0, 582626, 304334, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_304334_582626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304334 ⟨582626, by decide⟩ :=
  accepted_of_selected 13 304334 ⟨582626, by decide⟩ ⟨13, 2, 0, 582626, 304334, 1729, 16384⟩
    (by decide) selected_cut_22979

theorem selected_cut_22980 : selected 8 ⟨582633, by decide⟩
    (prefixPartial 13 304335) = some ⟨13, 2, 0, 582633, 304335, 789, 16384⟩ := by
  decide +kernel

theorem context_13_304335_582633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304335 ⟨582633, by decide⟩ :=
  accepted_of_selected 13 304335 ⟨582633, by decide⟩ ⟨13, 2, 0, 582633, 304335, 789, 16384⟩
    (by decide) selected_cut_22980

theorem unmarked_context_12_76083_582634 : frontier 9 ⟨582634, by decide⟩
    (prefixCache 12 76083) (prefixPartial 12 76083) = false := by
  decide +kernel

theorem node_context_12_76083_582634 : EJMOriginalGlobalDAGData.nodes 9 ⟨582634, by decide⟩ =
    .split (coordinate 12) (![⟨582577, by decide⟩,⟨582606, by decide⟩,⟨582626, by decide⟩,⟨582633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76083_582634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76083 ⟨582634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76083
    ⟨582634, by decide⟩ (by decide) (![⟨582577, by decide⟩,⟨582606, by decide⟩,⟨582626, by decide⟩,⟨582633, by decide⟩]) unmarked_context_12_76083_582634 node_context_12_76083_582634
  intro a
  fin_cases a
  · exact context_13_304332_582577
  · exact context_13_304333_582606
  · exact context_13_304334_582626
  · exact context_13_304335_582633

theorem unmarked_context_11_19020_582635 : frontier 10 ⟨582635, by decide⟩
    (prefixCache 11 19020) (prefixPartial 11 19020) = false := by
  decide +kernel

theorem node_context_11_19020_582635 : EJMOriginalGlobalDAGData.nodes 10 ⟨582635, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨582495, by decide⟩,⟨582566, by decide⟩,⟨582634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19020_582635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19020 ⟨582635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19020
    ⟨582635, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨582495, by decide⟩,⟨582566, by decide⟩,⟨582634, by decide⟩]) unmarked_context_11_19020_582635 node_context_11_19020_582635
  intro a
  fin_cases a
  · exact context_12_76080_445562
  · exact context_12_76081_582495
  · exact context_12_76082_582566
  · exact context_12_76083_582634

theorem selected_cut_22981 : selected 8 ⟨582650, by decide⟩
    (prefixPartial 13 304336) = some ⟨13, 2, 0, 582650, 304336, 817, 16384⟩ := by
  decide +kernel

theorem context_13_304336_582650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304336 ⟨582650, by decide⟩ :=
  accepted_of_selected 13 304336 ⟨582650, by decide⟩ ⟨13, 2, 0, 582650, 304336, 817, 16384⟩
    (by decide) selected_cut_22981

theorem selected_cut_22982 : selected 8 ⟨582676, by decide⟩
    (prefixPartial 13 304337) = some ⟨13, 2, 0, 582676, 304337, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_304337_582676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304337 ⟨582676, by decide⟩ :=
  accepted_of_selected 13 304337 ⟨582676, by decide⟩ ⟨13, 2, 0, 582676, 304337, 2637, 16384⟩
    (by decide) selected_cut_22982

theorem selected_cut_22983 : selected 8 ⟨582696, by decide⟩
    (prefixPartial 13 304338) = some ⟨13, 2, 0, 582696, 304338, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_304338_582696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304338 ⟨582696, by decide⟩ :=
  accepted_of_selected 13 304338 ⟨582696, by decide⟩ ⟨13, 2, 0, 582696, 304338, 1973, 16384⟩
    (by decide) selected_cut_22983

theorem selected_cut_22984 : selected 8 ⟨582705, by decide⟩
    (prefixPartial 13 304339) = some ⟨13, 2, 0, 582705, 304339, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_304339_582705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304339 ⟨582705, by decide⟩ :=
  accepted_of_selected 13 304339 ⟨582705, by decide⟩ ⟨13, 2, 0, 582705, 304339, 1085, 16384⟩
    (by decide) selected_cut_22984

theorem unmarked_context_12_76084_582706 : frontier 9 ⟨582706, by decide⟩
    (prefixCache 12 76084) (prefixPartial 12 76084) = false := by
  decide +kernel

theorem node_context_12_76084_582706 : EJMOriginalGlobalDAGData.nodes 9 ⟨582706, by decide⟩ =
    .split (coordinate 12) (![⟨582650, by decide⟩,⟨582676, by decide⟩,⟨582696, by decide⟩,⟨582705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76084_582706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76084 ⟨582706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76084
    ⟨582706, by decide⟩ (by decide) (![⟨582650, by decide⟩,⟨582676, by decide⟩,⟨582696, by decide⟩,⟨582705, by decide⟩]) unmarked_context_12_76084_582706 node_context_12_76084_582706
  intro a
  fin_cases a
  · exact context_13_304336_582650
  · exact context_13_304337_582676
  · exact context_13_304338_582696
  · exact context_13_304339_582705

theorem selected_cut_22985 : selected 8 ⟨582716, by decide⟩
    (prefixPartial 13 304340) = some ⟨13, 2, 0, 582716, 304340, 781, 16384⟩ := by
  decide +kernel

theorem context_13_304340_582716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304340 ⟨582716, by decide⟩ :=
  accepted_of_selected 13 304340 ⟨582716, by decide⟩ ⟨13, 2, 0, 582716, 304340, 781, 16384⟩
    (by decide) selected_cut_22985

theorem selected_cut_22986 : selected 8 ⟨582747, by decide⟩
    (prefixPartial 13 304341) = some ⟨13, 2, 0, 582747, 304341, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_304341_582747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304341 ⟨582747, by decide⟩ :=
  accepted_of_selected 13 304341 ⟨582747, by decide⟩ ⟨13, 2, 0, 582747, 304341, 3185, 16384⟩
    (by decide) selected_cut_22986

theorem selected_cut_22987 : selected 8 ⟨582772, by decide⟩
    (prefixPartial 13 304342) = some ⟨13, 2, 0, 582772, 304342, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_304342_582772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304342 ⟨582772, by decide⟩ :=
  accepted_of_selected 13 304342 ⟨582772, by decide⟩ ⟨13, 2, 0, 582772, 304342, 2305, 16384⟩
    (by decide) selected_cut_22987

theorem selected_cut_22988 : selected 8 ⟨582782, by decide⟩
    (prefixPartial 13 304343) = some ⟨13, 2, 0, 582782, 304343, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_304343_582782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304343 ⟨582782, by decide⟩ :=
  accepted_of_selected 13 304343 ⟨582782, by decide⟩ ⟨13, 2, 0, 582782, 304343, 1241, 16384⟩
    (by decide) selected_cut_22988

theorem unmarked_context_12_76085_582783 : frontier 9 ⟨582783, by decide⟩
    (prefixCache 12 76085) (prefixPartial 12 76085) = false := by
  decide +kernel

theorem node_context_12_76085_582783 : EJMOriginalGlobalDAGData.nodes 9 ⟨582783, by decide⟩ =
    .split (coordinate 12) (![⟨582716, by decide⟩,⟨582747, by decide⟩,⟨582772, by decide⟩,⟨582782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76085_582783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76085 ⟨582783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76085
    ⟨582783, by decide⟩ (by decide) (![⟨582716, by decide⟩,⟨582747, by decide⟩,⟨582772, by decide⟩,⟨582782, by decide⟩]) unmarked_context_12_76085_582783 node_context_12_76085_582783
  intro a
  fin_cases a
  · exact context_13_304340_582716
  · exact context_13_304341_582747
  · exact context_13_304342_582772
  · exact context_13_304343_582782

theorem selected_cut_22989 : selected 8 ⟨582792, by decide⟩
    (prefixPartial 13 304344) = some ⟨13, 2, 0, 582792, 304344, 501, 16384⟩ := by
  decide +kernel

theorem context_13_304344_582792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304344 ⟨582792, by decide⟩ :=
  accepted_of_selected 13 304344 ⟨582792, by decide⟩ ⟨13, 2, 0, 582792, 304344, 501, 16384⟩
    (by decide) selected_cut_22989

theorem selected_cut_22990 : selected 8 ⟨582815, by decide⟩
    (prefixPartial 13 304345) = some ⟨13, 2, 0, 582815, 304345, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_304345_582815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304345 ⟨582815, by decide⟩ :=
  accepted_of_selected 13 304345 ⟨582815, by decide⟩ ⟨13, 2, 0, 582815, 304345, 2145, 16384⟩
    (by decide) selected_cut_22990

theorem selected_cut_22991 : selected 8 ⟨582833, by decide⟩
    (prefixPartial 13 304346) = some ⟨13, 2, 0, 582833, 304346, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_304346_582833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304346 ⟨582833, by decide⟩ :=
  accepted_of_selected 13 304346 ⟨582833, by decide⟩ ⟨13, 2, 0, 582833, 304346, 1617, 16384⟩
    (by decide) selected_cut_22991

theorem selected_cut_22992 : selected 8 ⟨582841, by decide⟩
    (prefixPartial 13 304347) = some ⟨13, 2, 0, 582841, 304347, 933, 16384⟩ := by
  decide +kernel

theorem context_13_304347_582841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304347 ⟨582841, by decide⟩ :=
  accepted_of_selected 13 304347 ⟨582841, by decide⟩ ⟨13, 2, 0, 582841, 304347, 933, 16384⟩
    (by decide) selected_cut_22992

theorem unmarked_context_12_76086_582842 : frontier 9 ⟨582842, by decide⟩
    (prefixCache 12 76086) (prefixPartial 12 76086) = false := by
  decide +kernel

theorem node_context_12_76086_582842 : EJMOriginalGlobalDAGData.nodes 9 ⟨582842, by decide⟩ =
    .split (coordinate 12) (![⟨582792, by decide⟩,⟨582815, by decide⟩,⟨582833, by decide⟩,⟨582841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76086_582842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76086 ⟨582842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76086
    ⟨582842, by decide⟩ (by decide) (![⟨582792, by decide⟩,⟨582815, by decide⟩,⟨582833, by decide⟩,⟨582841, by decide⟩]) unmarked_context_12_76086_582842 node_context_12_76086_582842
  intro a
  fin_cases a
  · exact context_13_304344_582792
  · exact context_13_304345_582815
  · exact context_13_304346_582833
  · exact context_13_304347_582841

theorem selected_cut_22993 : selected 8 ⟨582851, by decide⟩
    (prefixPartial 13 304348) = some ⟨13, 2, 0, 582851, 304348, 441, 16384⟩ := by
  decide +kernel

theorem context_13_304348_582851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304348 ⟨582851, by decide⟩ :=
  accepted_of_selected 13 304348 ⟨582851, by decide⟩ ⟨13, 2, 0, 582851, 304348, 441, 16384⟩
    (by decide) selected_cut_22993

theorem selected_cut_22994 : selected 8 ⟨582880, by decide⟩
    (prefixPartial 13 304349) = some ⟨13, 2, 0, 582880, 304349, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_304349_582880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304349 ⟨582880, by decide⟩ :=
  accepted_of_selected 13 304349 ⟨582880, by decide⟩ ⟨13, 2, 0, 582880, 304349, 2297, 16384⟩
    (by decide) selected_cut_22994

theorem selected_cut_22995 : selected 8 ⟨582899, by decide⟩
    (prefixPartial 13 304350) = some ⟨13, 2, 0, 582899, 304350, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_304350_582899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304350 ⟨582899, by decide⟩ :=
  accepted_of_selected 13 304350 ⟨582899, by decide⟩ ⟨13, 2, 0, 582899, 304350, 1621, 16384⟩
    (by decide) selected_cut_22995

theorem selected_cut_22996 : selected 8 ⟨582904, by decide⟩
    (prefixPartial 13 304351) = some ⟨13, 2, 0, 582904, 304351, 733, 16384⟩ := by
  decide +kernel

theorem context_13_304351_582904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304351 ⟨582904, by decide⟩ :=
  accepted_of_selected 13 304351 ⟨582904, by decide⟩ ⟨13, 2, 0, 582904, 304351, 733, 16384⟩
    (by decide) selected_cut_22996

theorem unmarked_context_12_76087_582905 : frontier 9 ⟨582905, by decide⟩
    (prefixCache 12 76087) (prefixPartial 12 76087) = false := by
  decide +kernel

theorem node_context_12_76087_582905 : EJMOriginalGlobalDAGData.nodes 9 ⟨582905, by decide⟩ =
    .split (coordinate 12) (![⟨582851, by decide⟩,⟨582880, by decide⟩,⟨582899, by decide⟩,⟨582904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76087_582905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76087 ⟨582905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76087
    ⟨582905, by decide⟩ (by decide) (![⟨582851, by decide⟩,⟨582880, by decide⟩,⟨582899, by decide⟩,⟨582904, by decide⟩]) unmarked_context_12_76087_582905 node_context_12_76087_582905
  intro a
  fin_cases a
  · exact context_13_304348_582851
  · exact context_13_304349_582880
  · exact context_13_304350_582899
  · exact context_13_304351_582904

theorem unmarked_context_11_19021_582906 : frontier 10 ⟨582906, by decide⟩
    (prefixCache 11 19021) (prefixPartial 11 19021) = false := by
  decide +kernel

theorem node_context_11_19021_582906 : EJMOriginalGlobalDAGData.nodes 10 ⟨582906, by decide⟩ =
    .split (coordinate 11) (![⟨582706, by decide⟩,⟨582783, by decide⟩,⟨582842, by decide⟩,⟨582905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19021_582906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19021 ⟨582906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19021
    ⟨582906, by decide⟩ (by decide) (![⟨582706, by decide⟩,⟨582783, by decide⟩,⟨582842, by decide⟩,⟨582905, by decide⟩]) unmarked_context_11_19021_582906 node_context_11_19021_582906
  intro a
  fin_cases a
  · exact context_12_76084_582706
  · exact context_12_76085_582783
  · exact context_12_76086_582842
  · exact context_12_76087_582905

theorem selected_cut_22997 : selected 8 ⟨582916, by decide⟩
    (prefixPartial 13 304352) = some ⟨13, 2, 0, 582916, 304352, 509, 16384⟩ := by
  decide +kernel

theorem context_13_304352_582916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304352 ⟨582916, by decide⟩ :=
  accepted_of_selected 13 304352 ⟨582916, by decide⟩ ⟨13, 2, 0, 582916, 304352, 509, 16384⟩
    (by decide) selected_cut_22997

theorem selected_cut_22998 : selected 8 ⟨582945, by decide⟩
    (prefixPartial 13 304353) = some ⟨13, 2, 0, 582945, 304353, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_304353_582945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304353 ⟨582945, by decide⟩ :=
  accepted_of_selected 13 304353 ⟨582945, by decide⟩ ⟨13, 2, 0, 582945, 304353, 2693, 16384⟩
    (by decide) selected_cut_22998

theorem selected_cut_22999 : selected 8 ⟨582962, by decide⟩
    (prefixPartial 13 304354) = some ⟨13, 2, 0, 582962, 304354, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_304354_582962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304354 ⟨582962, by decide⟩ :=
  accepted_of_selected 13 304354 ⟨582962, by decide⟩ ⟨13, 2, 0, 582962, 304354, 1961, 16384⟩
    (by decide) selected_cut_22999

theorem selected_cut_23000 : selected 8 ⟨582969, by decide⟩
    (prefixPartial 13 304355) = some ⟨13, 2, 0, 582969, 304355, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_304355_582969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304355 ⟨582969, by decide⟩ :=
  accepted_of_selected 13 304355 ⟨582969, by decide⟩ ⟨13, 2, 0, 582969, 304355, 1073, 16384⟩
    (by decide) selected_cut_23000

theorem unmarked_context_12_76088_582970 : frontier 9 ⟨582970, by decide⟩
    (prefixCache 12 76088) (prefixPartial 12 76088) = false := by
  decide +kernel

theorem node_context_12_76088_582970 : EJMOriginalGlobalDAGData.nodes 9 ⟨582970, by decide⟩ =
    .split (coordinate 12) (![⟨582916, by decide⟩,⟨582945, by decide⟩,⟨582962, by decide⟩,⟨582969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76088_582970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76088 ⟨582970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76088
    ⟨582970, by decide⟩ (by decide) (![⟨582916, by decide⟩,⟨582945, by decide⟩,⟨582962, by decide⟩,⟨582969, by decide⟩]) unmarked_context_12_76088_582970 node_context_12_76088_582970
  intro a
  fin_cases a
  · exact context_13_304352_582916
  · exact context_13_304353_582945
  · exact context_13_304354_582962
  · exact context_13_304355_582969

theorem selected_cut_23001 : selected 8 ⟨582980, by decide⟩
    (prefixPartial 13 304356) = some ⟨13, 2, 0, 582980, 304356, 321, 16384⟩ := by
  decide +kernel

theorem context_13_304356_582980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304356 ⟨582980, by decide⟩ :=
  accepted_of_selected 13 304356 ⟨582980, by decide⟩ ⟨13, 2, 0, 582980, 304356, 321, 16384⟩
    (by decide) selected_cut_23001

theorem selected_cut_23002 : selected 8 ⟨583006, by decide⟩
    (prefixPartial 13 304357) = some ⟨13, 2, 0, 583006, 304357, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_304357_583006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304357 ⟨583006, by decide⟩ :=
  accepted_of_selected 13 304357 ⟨583006, by decide⟩ ⟨13, 2, 0, 583006, 304357, 1817, 16384⟩
    (by decide) selected_cut_23002

theorem selected_cut_23003 : selected 8 ⟨583025, by decide⟩
    (prefixPartial 13 304358) = some ⟨13, 2, 0, 583025, 304358, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_304358_583025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304358 ⟨583025, by decide⟩ :=
  accepted_of_selected 13 304358 ⟨583025, by decide⟩ ⟨13, 2, 0, 583025, 304358, 1545, 16384⟩
    (by decide) selected_cut_23003

theorem selected_cut_23004 : selected 8 ⟨583030, by decide⟩
    (prefixPartial 13 304359) = some ⟨13, 2, 0, 583030, 304359, 917, 16384⟩ := by
  decide +kernel

theorem context_13_304359_583030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304359 ⟨583030, by decide⟩ :=
  accepted_of_selected 13 304359 ⟨583030, by decide⟩ ⟨13, 2, 0, 583030, 304359, 917, 16384⟩
    (by decide) selected_cut_23004

theorem unmarked_context_12_76089_583031 : frontier 9 ⟨583031, by decide⟩
    (prefixCache 12 76089) (prefixPartial 12 76089) = false := by
  decide +kernel

theorem node_context_12_76089_583031 : EJMOriginalGlobalDAGData.nodes 9 ⟨583031, by decide⟩ =
    .split (coordinate 12) (![⟨582980, by decide⟩,⟨583006, by decide⟩,⟨583025, by decide⟩,⟨583030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76089_583031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76089 ⟨583031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76089
    ⟨583031, by decide⟩ (by decide) (![⟨582980, by decide⟩,⟨583006, by decide⟩,⟨583025, by decide⟩,⟨583030, by decide⟩]) unmarked_context_12_76089_583031 node_context_12_76089_583031
  intro a
  fin_cases a
  · exact context_13_304356_582980
  · exact context_13_304357_583006
  · exact context_13_304358_583025
  · exact context_13_304359_583030

theorem selected_cut_23005 : selected 8 ⟨583037, by decide⟩
    (prefixPartial 13 304360) = some ⟨13, 2, 0, 583037, 304360, 297, 16384⟩ := by
  decide +kernel

theorem context_13_304360_583037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304360 ⟨583037, by decide⟩ :=
  accepted_of_selected 13 304360 ⟨583037, by decide⟩ ⟨13, 2, 0, 583037, 304360, 297, 16384⟩
    (by decide) selected_cut_23005

theorem selected_cut_23006 : selected 8 ⟨583058, by decide⟩
    (prefixPartial 13 304361) = some ⟨13, 2, 0, 583058, 304361, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_304361_583058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304361 ⟨583058, by decide⟩ :=
  accepted_of_selected 13 304361 ⟨583058, by decide⟩ ⟨13, 2, 0, 583058, 304361, 1997, 16384⟩
    (by decide) selected_cut_23006

theorem selected_cut_23007 : selected 8 ⟨583078, by decide⟩
    (prefixPartial 13 304362) = some ⟨13, 2, 0, 583078, 304362, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_304362_583078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304362 ⟨583078, by decide⟩ :=
  accepted_of_selected 13 304362 ⟨583078, by decide⟩ ⟨13, 2, 0, 583078, 304362, 1581, 16384⟩
    (by decide) selected_cut_23007

theorem selected_cut_23008 : selected 8 ⟨583084, by decide⟩
    (prefixPartial 13 304363) = some ⟨13, 2, 0, 583084, 304363, 857, 16384⟩ := by
  decide +kernel

theorem context_13_304363_583084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304363 ⟨583084, by decide⟩ :=
  accepted_of_selected 13 304363 ⟨583084, by decide⟩ ⟨13, 2, 0, 583084, 304363, 857, 16384⟩
    (by decide) selected_cut_23008

theorem unmarked_context_12_76090_583085 : frontier 9 ⟨583085, by decide⟩
    (prefixCache 12 76090) (prefixPartial 12 76090) = false := by
  decide +kernel

theorem node_context_12_76090_583085 : EJMOriginalGlobalDAGData.nodes 9 ⟨583085, by decide⟩ =
    .split (coordinate 12) (![⟨583037, by decide⟩,⟨583058, by decide⟩,⟨583078, by decide⟩,⟨583084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76090_583085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76090 ⟨583085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76090
    ⟨583085, by decide⟩ (by decide) (![⟨583037, by decide⟩,⟨583058, by decide⟩,⟨583078, by decide⟩,⟨583084, by decide⟩]) unmarked_context_12_76090_583085 node_context_12_76090_583085
  intro a
  fin_cases a
  · exact context_13_304360_583037
  · exact context_13_304361_583058
  · exact context_13_304362_583078
  · exact context_13_304363_583084

theorem selected_cut_23009 : selected 8 ⟨583093, by decide⟩
    (prefixPartial 13 304364) = some ⟨13, 2, 0, 583093, 304364, 233, 16384⟩ := by
  decide +kernel

theorem context_13_304364_583093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304364 ⟨583093, by decide⟩ :=
  accepted_of_selected 13 304364 ⟨583093, by decide⟩ ⟨13, 2, 0, 583093, 304364, 233, 16384⟩
    (by decide) selected_cut_23009

theorem selected_cut_23010 : selected 8 ⟨583123, by decide⟩
    (prefixPartial 13 304365) = some ⟨13, 2, 0, 583123, 304365, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_304365_583123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304365 ⟨583123, by decide⟩ :=
  accepted_of_selected 13 304365 ⟨583123, by decide⟩ ⟨13, 2, 0, 583123, 304365, 2337, 16384⟩
    (by decide) selected_cut_23010

theorem selected_cut_23011 : selected 8 ⟨583144, by decide⟩
    (prefixPartial 13 304366) = some ⟨13, 2, 0, 583144, 304366, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_304366_583144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304366 ⟨583144, by decide⟩ :=
  accepted_of_selected 13 304366 ⟨583144, by decide⟩ ⟨13, 2, 0, 583144, 304366, 1581, 16384⟩
    (by decide) selected_cut_23011

theorem selected_cut_23012 : selected 8 ⟨583150, by decide⟩
    (prefixPartial 13 304367) = some ⟨13, 2, 0, 583150, 304367, 733, 16384⟩ := by
  decide +kernel

theorem context_13_304367_583150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304367 ⟨583150, by decide⟩ :=
  accepted_of_selected 13 304367 ⟨583150, by decide⟩ ⟨13, 2, 0, 583150, 304367, 733, 16384⟩
    (by decide) selected_cut_23012

theorem unmarked_context_12_76091_583151 : frontier 9 ⟨583151, by decide⟩
    (prefixCache 12 76091) (prefixPartial 12 76091) = false := by
  decide +kernel

theorem node_context_12_76091_583151 : EJMOriginalGlobalDAGData.nodes 9 ⟨583151, by decide⟩ =
    .split (coordinate 12) (![⟨583093, by decide⟩,⟨583123, by decide⟩,⟨583144, by decide⟩,⟨583150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76091_583151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76091 ⟨583151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76091
    ⟨583151, by decide⟩ (by decide) (![⟨583093, by decide⟩,⟨583123, by decide⟩,⟨583144, by decide⟩,⟨583150, by decide⟩]) unmarked_context_12_76091_583151 node_context_12_76091_583151
  intro a
  fin_cases a
  · exact context_13_304364_583093
  · exact context_13_304365_583123
  · exact context_13_304366_583144
  · exact context_13_304367_583150

theorem unmarked_context_11_19022_583152 : frontier 10 ⟨583152, by decide⟩
    (prefixCache 11 19022) (prefixPartial 11 19022) = false := by
  decide +kernel

theorem node_context_11_19022_583152 : EJMOriginalGlobalDAGData.nodes 10 ⟨583152, by decide⟩ =
    .split (coordinate 11) (![⟨582970, by decide⟩,⟨583031, by decide⟩,⟨583085, by decide⟩,⟨583151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19022_583152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19022 ⟨583152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19022
    ⟨583152, by decide⟩ (by decide) (![⟨582970, by decide⟩,⟨583031, by decide⟩,⟨583085, by decide⟩,⟨583151, by decide⟩]) unmarked_context_11_19022_583152 node_context_11_19022_583152
  intro a
  fin_cases a
  · exact context_12_76088_582970
  · exact context_12_76089_583031
  · exact context_12_76090_583085
  · exact context_12_76091_583151

theorem selected_cut_23013 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76092) = some ⟨12, 1, 0, 445562, 76092, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76092_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76092 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76092 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76092, 1, 65536⟩
    (by decide) selected_cut_23013

theorem selected_cut_23014 : selected 8 ⟨583156, by decide⟩
    (prefixPartial 13 304372) = some ⟨13, 2, 0, 583156, 304372, 133, 16384⟩ := by
  decide +kernel

theorem context_13_304372_583156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304372 ⟨583156, by decide⟩ :=
  accepted_of_selected 13 304372 ⟨583156, by decide⟩ ⟨13, 2, 0, 583156, 304372, 133, 16384⟩
    (by decide) selected_cut_23014

theorem selected_cut_23015 : selected 8 ⟨583179, by decide⟩
    (prefixPartial 13 304373) = some ⟨13, 2, 0, 583179, 304373, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_304373_583179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304373 ⟨583179, by decide⟩ :=
  accepted_of_selected 13 304373 ⟨583179, by decide⟩ ⟨13, 2, 0, 583179, 304373, 2177, 16384⟩
    (by decide) selected_cut_23015

theorem selected_cut_23016 : selected 8 ⟨583198, by decide⟩
    (prefixPartial 13 304374) = some ⟨13, 2, 0, 583198, 304374, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_304374_583198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304374 ⟨583198, by decide⟩ :=
  accepted_of_selected 13 304374 ⟨583198, by decide⟩ ⟨13, 2, 0, 583198, 304374, 1681, 16384⟩
    (by decide) selected_cut_23016

theorem selected_cut_23017 : selected 8 ⟨583205, by decide⟩
    (prefixPartial 13 304375) = some ⟨13, 2, 0, 583205, 304375, 853, 16384⟩ := by
  decide +kernel

theorem context_13_304375_583205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304375 ⟨583205, by decide⟩ :=
  accepted_of_selected 13 304375 ⟨583205, by decide⟩ ⟨13, 2, 0, 583205, 304375, 853, 16384⟩
    (by decide) selected_cut_23017

theorem unmarked_context_12_76093_583206 : frontier 9 ⟨583206, by decide⟩
    (prefixCache 12 76093) (prefixPartial 12 76093) = false := by
  decide +kernel

theorem node_context_12_76093_583206 : EJMOriginalGlobalDAGData.nodes 9 ⟨583206, by decide⟩ =
    .split (coordinate 12) (![⟨583156, by decide⟩,⟨583179, by decide⟩,⟨583198, by decide⟩,⟨583205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76093_583206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76093 ⟨583206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76093
    ⟨583206, by decide⟩ (by decide) (![⟨583156, by decide⟩,⟨583179, by decide⟩,⟨583198, by decide⟩,⟨583205, by decide⟩]) unmarked_context_12_76093_583206 node_context_12_76093_583206
  intro a
  fin_cases a
  · exact context_13_304372_583156
  · exact context_13_304373_583179
  · exact context_13_304374_583198
  · exact context_13_304375_583205

theorem selected_cut_23018 : selected 8 ⟨583211, by decide⟩
    (prefixPartial 13 304376) = some ⟨13, 2, 0, 583211, 304376, 141, 16384⟩ := by
  decide +kernel

theorem context_13_304376_583211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304376 ⟨583211, by decide⟩ :=
  accepted_of_selected 13 304376 ⟨583211, by decide⟩ ⟨13, 2, 0, 583211, 304376, 141, 16384⟩
    (by decide) selected_cut_23018

theorem selected_cut_23019 : selected 8 ⟨583240, by decide⟩
    (prefixPartial 13 304377) = some ⟨13, 2, 0, 583240, 304377, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_304377_583240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304377 ⟨583240, by decide⟩ :=
  accepted_of_selected 13 304377 ⟨583240, by decide⟩ ⟨13, 2, 0, 583240, 304377, 2429, 16384⟩
    (by decide) selected_cut_23019

theorem selected_cut_23020 : selected 8 ⟨583260, by decide⟩
    (prefixPartial 13 304378) = some ⟨13, 2, 0, 583260, 304378, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_304378_583260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304378 ⟨583260, by decide⟩ :=
  accepted_of_selected 13 304378 ⟨583260, by decide⟩ ⟨13, 2, 0, 583260, 304378, 1861, 16384⟩
    (by decide) selected_cut_23020

theorem selected_cut_23021 : selected 8 ⟨583266, by decide⟩
    (prefixPartial 13 304379) = some ⟨13, 2, 0, 583266, 304379, 957, 16384⟩ := by
  decide +kernel

theorem context_13_304379_583266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304379 ⟨583266, by decide⟩ :=
  accepted_of_selected 13 304379 ⟨583266, by decide⟩ ⟨13, 2, 0, 583266, 304379, 957, 16384⟩
    (by decide) selected_cut_23021

theorem unmarked_context_12_76094_583267 : frontier 9 ⟨583267, by decide⟩
    (prefixCache 12 76094) (prefixPartial 12 76094) = false := by
  decide +kernel

theorem node_context_12_76094_583267 : EJMOriginalGlobalDAGData.nodes 9 ⟨583267, by decide⟩ =
    .split (coordinate 12) (![⟨583211, by decide⟩,⟨583240, by decide⟩,⟨583260, by decide⟩,⟨583266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76094_583267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76094 ⟨583267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76094
    ⟨583267, by decide⟩ (by decide) (![⟨583211, by decide⟩,⟨583240, by decide⟩,⟨583260, by decide⟩,⟨583266, by decide⟩]) unmarked_context_12_76094_583267 node_context_12_76094_583267
  intro a
  fin_cases a
  · exact context_13_304376_583211
  · exact context_13_304377_583240
  · exact context_13_304378_583260
  · exact context_13_304379_583266

theorem selected_cut_23022 : selected 8 ⟨583271, by decide⟩
    (prefixPartial 13 304380) = some ⟨13, 2, 0, 583271, 304380, 77, 16384⟩ := by
  decide +kernel

theorem context_13_304380_583271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304380 ⟨583271, by decide⟩ :=
  accepted_of_selected 13 304380 ⟨583271, by decide⟩ ⟨13, 2, 0, 583271, 304380, 77, 16384⟩
    (by decide) selected_cut_23022

theorem selected_cut_23023 : selected 8 ⟨583304, by decide⟩
    (prefixPartial 13 304381) = some ⟨13, 2, 0, 583304, 304381, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_304381_583304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304381 ⟨583304, by decide⟩ :=
  accepted_of_selected 13 304381 ⟨583304, by decide⟩ ⟨13, 2, 0, 583304, 304381, 2553, 16384⟩
    (by decide) selected_cut_23023

theorem selected_cut_23024 : selected 8 ⟨583322, by decide⟩
    (prefixPartial 13 304382) = some ⟨13, 2, 0, 583322, 304382, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_304382_583322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304382 ⟨583322, by decide⟩ :=
  accepted_of_selected 13 304382 ⟨583322, by decide⟩ ⟨13, 2, 0, 583322, 304382, 1725, 16384⟩
    (by decide) selected_cut_23024

theorem selected_cut_23025 : selected 8 ⟨583330, by decide⟩
    (prefixPartial 13 304383) = some ⟨13, 2, 0, 583330, 304383, 765, 16384⟩ := by
  decide +kernel

theorem context_13_304383_583330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304383 ⟨583330, by decide⟩ :=
  accepted_of_selected 13 304383 ⟨583330, by decide⟩ ⟨13, 2, 0, 583330, 304383, 765, 16384⟩
    (by decide) selected_cut_23025

theorem unmarked_context_12_76095_583331 : frontier 9 ⟨583331, by decide⟩
    (prefixCache 12 76095) (prefixPartial 12 76095) = false := by
  decide +kernel

theorem node_context_12_76095_583331 : EJMOriginalGlobalDAGData.nodes 9 ⟨583331, by decide⟩ =
    .split (coordinate 12) (![⟨583271, by decide⟩,⟨583304, by decide⟩,⟨583322, by decide⟩,⟨583330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76095_583331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76095 ⟨583331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76095
    ⟨583331, by decide⟩ (by decide) (![⟨583271, by decide⟩,⟨583304, by decide⟩,⟨583322, by decide⟩,⟨583330, by decide⟩]) unmarked_context_12_76095_583331 node_context_12_76095_583331
  intro a
  fin_cases a
  · exact context_13_304380_583271
  · exact context_13_304381_583304
  · exact context_13_304382_583322
  · exact context_13_304383_583330

theorem unmarked_context_11_19023_583332 : frontier 10 ⟨583332, by decide⟩
    (prefixCache 11 19023) (prefixPartial 11 19023) = false := by
  decide +kernel

theorem node_context_11_19023_583332 : EJMOriginalGlobalDAGData.nodes 10 ⟨583332, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨583206, by decide⟩,⟨583267, by decide⟩,⟨583331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19023_583332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19023 ⟨583332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19023
    ⟨583332, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨583206, by decide⟩,⟨583267, by decide⟩,⟨583331, by decide⟩]) unmarked_context_11_19023_583332 node_context_11_19023_583332
  intro a
  fin_cases a
  · exact context_12_76092_445562
  · exact context_12_76093_583206
  · exact context_12_76094_583267
  · exact context_12_76095_583331

theorem unmarked_context_10_4755_583333 : frontier 11 ⟨583333, by decide⟩
    (prefixCache 10 4755) (prefixPartial 10 4755) = false := by
  decide +kernel

theorem node_context_10_4755_583333 : EJMOriginalGlobalDAGData.nodes 11 ⟨583333, by decide⟩ =
    .split (coordinate 10) (![⟨582635, by decide⟩,⟨582906, by decide⟩,⟨583152, by decide⟩,⟨583332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4755_583333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4755 ⟨583333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4755
    ⟨583333, by decide⟩ (by decide) (![⟨582635, by decide⟩,⟨582906, by decide⟩,⟨583152, by decide⟩,⟨583332, by decide⟩]) unmarked_context_10_4755_583333 node_context_10_4755_583333
  intro a
  fin_cases a
  · exact context_11_19020_582635
  · exact context_11_19021_582906
  · exact context_11_19022_583152
  · exact context_11_19023_583332

theorem unmarked_context_9_1188_583334 : frontier 12 ⟨583334, by decide⟩
    (prefixCache 9 1188) (prefixPartial 9 1188) = false := by
  decide +kernel

theorem node_context_9_1188_583334 : EJMOriginalGlobalDAGData.nodes 12 ⟨583334, by decide⟩ =
    .split (coordinate 9) (![⟨580726, by decide⟩,⟨581575, by decide⟩,⟨582438, by decide⟩,⟨583333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1188_583334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1188 ⟨583334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1188
    ⟨583334, by decide⟩ (by decide) (![⟨580726, by decide⟩,⟨581575, by decide⟩,⟨582438, by decide⟩,⟨583333, by decide⟩]) unmarked_context_9_1188_583334 node_context_9_1188_583334
  intro a
  fin_cases a
  · exact context_10_4752_580726
  · exact context_10_4753_581575
  · exact context_10_4754_582438
  · exact context_10_4755_583333

theorem selected_cut_23026 : selected 9 ⟨583380, by decide⟩
    (prefixPartial 12 76096) = some ⟨12, 2, 0, 583380, 76096, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_76096_583380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76096 ⟨583380, by decide⟩ :=
  accepted_of_selected 12 76096 ⟨583380, by decide⟩ ⟨12, 2, 0, 583380, 76096, 3437, 65536⟩
    (by decide) selected_cut_23026

theorem selected_cut_23027 : selected 9 ⟨583419, by decide⟩
    (prefixPartial 12 76097) = some ⟨12, 2, 0, 583419, 76097, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_76097_583419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76097 ⟨583419, by decide⟩ :=
  accepted_of_selected 12 76097 ⟨583419, by decide⟩ ⟨12, 2, 0, 583419, 76097, 3125, 65536⟩
    (by decide) selected_cut_23027

theorem selected_cut_23028 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304392) = some ⟨13, 1, 0, 3444, 304392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304392, 1, 16384⟩
    (by decide) selected_cut_23028

theorem selected_cut_23029 : selected 8 ⟨583443, by decide⟩
    (prefixPartial 13 304393) = some ⟨13, 2, 0, 583443, 304393, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_304393_583443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304393 ⟨583443, by decide⟩ :=
  accepted_of_selected 13 304393 ⟨583443, by decide⟩ ⟨13, 2, 0, 583443, 304393, 1837, 16384⟩
    (by decide) selected_cut_23029

theorem selected_cut_23030 : selected 8 ⟨583462, by decide⟩
    (prefixPartial 13 304394) = some ⟨13, 2, 0, 583462, 304394, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_304394_583462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304394 ⟨583462, by decide⟩ :=
  accepted_of_selected 13 304394 ⟨583462, by decide⟩ ⟨13, 2, 0, 583462, 304394, 1633, 16384⟩
    (by decide) selected_cut_23030

theorem selected_cut_23031 : selected 8 ⟨583468, by decide⟩
    (prefixPartial 13 304395) = some ⟨13, 2, 0, 583468, 304395, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_304395_583468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304395 ⟨583468, by decide⟩ :=
  accepted_of_selected 13 304395 ⟨583468, by decide⟩ ⟨13, 2, 0, 583468, 304395, 1017, 16384⟩
    (by decide) selected_cut_23031

theorem unmarked_context_12_76098_583469 : frontier 9 ⟨583469, by decide⟩
    (prefixCache 12 76098) (prefixPartial 12 76098) = false := by
  decide +kernel

theorem node_context_12_76098_583469 : EJMOriginalGlobalDAGData.nodes 9 ⟨583469, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨583443, by decide⟩,⟨583462, by decide⟩,⟨583468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76098_583469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76098 ⟨583469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76098
    ⟨583469, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨583443, by decide⟩,⟨583462, by decide⟩,⟨583468, by decide⟩]) unmarked_context_12_76098_583469 node_context_12_76098_583469
  intro a
  fin_cases a
  · exact context_13_304392_3444
  · exact context_13_304393_583443
  · exact context_13_304394_583462
  · exact context_13_304395_583468

theorem selected_cut_23032 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304396) = some ⟨13, 1, 0, 3444, 304396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304396, 1, 16384⟩
    (by decide) selected_cut_23032

theorem selected_cut_23033 : selected 8 ⟨583491, by decide⟩
    (prefixPartial 13 304397) = some ⟨13, 2, 0, 583491, 304397, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_304397_583491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304397 ⟨583491, by decide⟩ :=
  accepted_of_selected 13 304397 ⟨583491, by decide⟩ ⟨13, 2, 0, 583491, 304397, 1689, 16384⟩
    (by decide) selected_cut_23033

theorem selected_cut_23034 : selected 8 ⟨583512, by decide⟩
    (prefixPartial 13 304398) = some ⟨13, 2, 0, 583512, 304398, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_304398_583512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304398 ⟨583512, by decide⟩ :=
  accepted_of_selected 13 304398 ⟨583512, by decide⟩ ⟨13, 2, 0, 583512, 304398, 1625, 16384⟩
    (by decide) selected_cut_23034

theorem selected_cut_23035 : selected 8 ⟨583518, by decide⟩
    (prefixPartial 13 304399) = some ⟨13, 2, 0, 583518, 304399, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_304399_583518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304399 ⟨583518, by decide⟩ :=
  accepted_of_selected 13 304399 ⟨583518, by decide⟩ ⟨13, 2, 0, 583518, 304399, 1009, 16384⟩
    (by decide) selected_cut_23035

theorem unmarked_context_12_76099_583519 : frontier 9 ⟨583519, by decide⟩
    (prefixCache 12 76099) (prefixPartial 12 76099) = false := by
  decide +kernel

theorem node_context_12_76099_583519 : EJMOriginalGlobalDAGData.nodes 9 ⟨583519, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨583491, by decide⟩,⟨583512, by decide⟩,⟨583518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76099_583519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76099 ⟨583519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76099
    ⟨583519, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨583491, by decide⟩,⟨583512, by decide⟩,⟨583518, by decide⟩]) unmarked_context_12_76099_583519 node_context_12_76099_583519
  intro a
  fin_cases a
  · exact context_13_304396_3444
  · exact context_13_304397_583491
  · exact context_13_304398_583512
  · exact context_13_304399_583518

theorem unmarked_context_11_19024_583520 : frontier 10 ⟨583520, by decide⟩
    (prefixCache 11 19024) (prefixPartial 11 19024) = false := by
  decide +kernel

theorem node_context_11_19024_583520 : EJMOriginalGlobalDAGData.nodes 10 ⟨583520, by decide⟩ =
    .split (coordinate 11) (![⟨583380, by decide⟩,⟨583419, by decide⟩,⟨583469, by decide⟩,⟨583519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19024_583520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19024 ⟨583520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19024
    ⟨583520, by decide⟩ (by decide) (![⟨583380, by decide⟩,⟨583419, by decide⟩,⟨583469, by decide⟩,⟨583519, by decide⟩]) unmarked_context_11_19024_583520 node_context_11_19024_583520
  intro a
  fin_cases a
  · exact context_12_76096_583380
  · exact context_12_76097_583419
  · exact context_12_76098_583469
  · exact context_12_76099_583519

theorem selected_cut_23036 : selected 9 ⟨583557, by decide⟩
    (prefixPartial 12 76100) = some ⟨12, 2, 0, 583557, 76100, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_76100_583557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76100 ⟨583557, by decide⟩ :=
  accepted_of_selected 12 76100 ⟨583557, by decide⟩ ⟨12, 2, 0, 583557, 76100, 2789, 65536⟩
    (by decide) selected_cut_23036

theorem selected_cut_23037 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 76101) = some ⟨12, 1, 0, 441672, 76101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76101_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76101 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 76101 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 76101, 1, 65536⟩
    (by decide) selected_cut_23037

theorem selected_cut_23038 : selected 9 ⟨583603, by decide⟩
    (prefixPartial 12 76102) = some ⟨12, 2, 0, 583603, 76102, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_76102_583603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76102 ⟨583603, by decide⟩ :=
  accepted_of_selected 12 76102 ⟨583603, by decide⟩ ⟨12, 2, 0, 583603, 76102, 3541, 65536⟩
    (by decide) selected_cut_23038

theorem selected_cut_23039 : selected 9 ⟨583651, by decide⟩
    (prefixPartial 12 76103) = some ⟨12, 2, 0, 583651, 76103, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_76103_583651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76103 ⟨583651, by decide⟩ :=
  accepted_of_selected 12 76103 ⟨583651, by decide⟩ ⟨12, 2, 0, 583651, 76103, 3565, 65536⟩
    (by decide) selected_cut_23039

theorem unmarked_context_11_19025_583652 : frontier 10 ⟨583652, by decide⟩
    (prefixCache 11 19025) (prefixPartial 11 19025) = false := by
  decide +kernel

theorem node_context_11_19025_583652 : EJMOriginalGlobalDAGData.nodes 10 ⟨583652, by decide⟩ =
    .split (coordinate 11) (![⟨583557, by decide⟩,⟨441672, by decide⟩,⟨583603, by decide⟩,⟨583651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19025_583652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19025 ⟨583652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19025
    ⟨583652, by decide⟩ (by decide) (![⟨583557, by decide⟩,⟨441672, by decide⟩,⟨583603, by decide⟩,⟨583651, by decide⟩]) unmarked_context_11_19025_583652 node_context_11_19025_583652
  intro a
  fin_cases a
  · exact context_12_76100_583557
  · exact context_12_76101_441672
  · exact context_12_76102_583603
  · exact context_12_76103_583651

theorem selected_cut_23040 : selected 9 ⟨583695, by decide⟩
    (prefixPartial 12 76104) = some ⟨12, 2, 0, 583695, 76104, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_76104_583695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76104 ⟨583695, by decide⟩ :=
  accepted_of_selected 12 76104 ⟨583695, by decide⟩ ⟨12, 2, 0, 583695, 76104, 3309, 65536⟩
    (by decide) selected_cut_23040

theorem selected_cut_23041 : selected 9 ⟨583731, by decide⟩
    (prefixPartial 12 76105) = some ⟨12, 2, 0, 583731, 76105, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_76105_583731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76105 ⟨583731, by decide⟩ :=
  accepted_of_selected 12 76105 ⟨583731, by decide⟩ ⟨12, 2, 0, 583731, 76105, 3057, 65536⟩
    (by decide) selected_cut_23041

theorem selected_cut_23042 : selected 9 ⟨583781, by decide⟩
    (prefixPartial 12 76106) = some ⟨12, 2, 0, 583781, 76106, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_76106_583781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76106 ⟨583781, by decide⟩ :=
  accepted_of_selected 12 76106 ⟨583781, by decide⟩ ⟨12, 2, 0, 583781, 76106, 3805, 65536⟩
    (by decide) selected_cut_23042

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
