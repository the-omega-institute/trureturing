/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover251
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_24195 : selected 9 ⟨612131, by decide⟩
    (prefixPartial 12 76965) = some ⟨12, 2, 0, 612131, 76965, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_76965_612131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76965 ⟨612131, by decide⟩ :=
  accepted_of_selected 12 76965 ⟨612131, by decide⟩ ⟨12, 2, 0, 612131, 76965, 1813, 65536⟩
    (by decide) selected_cut_24195

theorem selected_cut_24196 : selected 9 ⟨612147, by decide⟩
    (prefixPartial 12 76966) = some ⟨12, 2, 0, 612147, 76966, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_76966_612147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76966 ⟨612147, by decide⟩ :=
  accepted_of_selected 12 76966 ⟨612147, by decide⟩ ⟨12, 2, 0, 612147, 76966, 1733, 65536⟩
    (by decide) selected_cut_24196

theorem selected_cut_24197 : selected 9 ⟨612183, by decide⟩
    (prefixPartial 12 76967) = some ⟨12, 2, 0, 612183, 76967, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_76967_612183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76967 ⟨612183, by decide⟩ :=
  accepted_of_selected 12 76967 ⟨612183, by decide⟩ ⟨12, 2, 0, 612183, 76967, 1877, 65536⟩
    (by decide) selected_cut_24197

theorem unmarked_context_11_19241_612184 : frontier 10 ⟨612184, by decide⟩
    (prefixCache 11 19241) (prefixPartial 11 19241) = false := by
  decide +kernel

theorem node_context_11_19241_612184 : EJMOriginalGlobalDAGData.nodes 10 ⟨612184, by decide⟩ =
    .split (coordinate 11) (![⟨612109, by decide⟩,⟨612131, by decide⟩,⟨612147, by decide⟩,⟨612183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19241_612184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19241 ⟨612184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19241
    ⟨612184, by decide⟩ (by decide) (![⟨612109, by decide⟩,⟨612131, by decide⟩,⟨612147, by decide⟩,⟨612183, by decide⟩]) unmarked_context_11_19241_612184 node_context_11_19241_612184
  intro a
  fin_cases a
  · exact context_12_76964_612109
  · exact context_12_76965_612131
  · exact context_12_76966_612147
  · exact context_12_76967_612183

theorem selected_cut_24198 : selected 9 ⟨612202, by decide⟩
    (prefixPartial 12 76968) = some ⟨12, 2, 0, 612202, 76968, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_76968_612202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76968 ⟨612202, by decide⟩ :=
  accepted_of_selected 12 76968 ⟨612202, by decide⟩ ⟨12, 2, 0, 612202, 76968, 1597, 65536⟩
    (by decide) selected_cut_24198

theorem selected_cut_24199 : selected 9 ⟨612228, by decide⟩
    (prefixPartial 12 76969) = some ⟨12, 2, 0, 612228, 76969, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_76969_612228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76969 ⟨612228, by decide⟩ :=
  accepted_of_selected 12 76969 ⟨612228, by decide⟩ ⟨12, 2, 0, 612228, 76969, 1829, 65536⟩
    (by decide) selected_cut_24199

theorem selected_cut_24200 : selected 9 ⟨612247, by decide⟩
    (prefixPartial 12 76970) = some ⟨12, 2, 0, 612247, 76970, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_76970_612247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76970 ⟨612247, by decide⟩ :=
  accepted_of_selected 12 76970 ⟨612247, by decide⟩ ⟨12, 2, 0, 612247, 76970, 1593, 65536⟩
    (by decide) selected_cut_24200

theorem selected_cut_24201 : selected 9 ⟨612272, by decide⟩
    (prefixPartial 12 76971) = some ⟨12, 2, 0, 612272, 76971, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_76971_612272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76971 ⟨612272, by decide⟩ :=
  accepted_of_selected 12 76971 ⟨612272, by decide⟩ ⟨12, 2, 0, 612272, 76971, 1709, 65536⟩
    (by decide) selected_cut_24201

theorem unmarked_context_11_19242_612273 : frontier 10 ⟨612273, by decide⟩
    (prefixCache 11 19242) (prefixPartial 11 19242) = false := by
  decide +kernel

theorem node_context_11_19242_612273 : EJMOriginalGlobalDAGData.nodes 10 ⟨612273, by decide⟩ =
    .split (coordinate 11) (![⟨612202, by decide⟩,⟨612228, by decide⟩,⟨612247, by decide⟩,⟨612272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19242_612273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19242 ⟨612273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19242
    ⟨612273, by decide⟩ (by decide) (![⟨612202, by decide⟩,⟨612228, by decide⟩,⟨612247, by decide⟩,⟨612272, by decide⟩]) unmarked_context_11_19242_612273 node_context_11_19242_612273
  intro a
  fin_cases a
  · exact context_12_76968_612202
  · exact context_12_76969_612228
  · exact context_12_76970_612247
  · exact context_12_76971_612272

theorem selected_cut_24202 : selected 9 ⟨612290, by decide⟩
    (prefixPartial 12 76972) = some ⟨12, 2, 0, 612290, 76972, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_76972_612290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76972 ⟨612290, by decide⟩ :=
  accepted_of_selected 12 76972 ⟨612290, by decide⟩ ⟨12, 2, 0, 612290, 76972, 1273, 65536⟩
    (by decide) selected_cut_24202

theorem selected_cut_24203 : selected 9 ⟨612308, by decide⟩
    (prefixPartial 12 76973) = some ⟨12, 2, 0, 612308, 76973, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_76973_612308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76973 ⟨612308, by decide⟩ :=
  accepted_of_selected 12 76973 ⟨612308, by decide⟩ ⟨12, 2, 0, 612308, 76973, 1473, 65536⟩
    (by decide) selected_cut_24203

theorem selected_cut_24204 : selected 9 ⟨612326, by decide⟩
    (prefixPartial 12 76974) = some ⟨12, 2, 0, 612326, 76974, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_76974_612326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76974 ⟨612326, by decide⟩ :=
  accepted_of_selected 12 76974 ⟨612326, by decide⟩ ⟨12, 2, 0, 612326, 76974, 1385, 65536⟩
    (by decide) selected_cut_24204

theorem selected_cut_24205 : selected 9 ⟨612336, by decide⟩
    (prefixPartial 12 76975) = some ⟨12, 2, 0, 612336, 76975, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_76975_612336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76975 ⟨612336, by decide⟩ :=
  accepted_of_selected 12 76975 ⟨612336, by decide⟩ ⟨12, 2, 0, 612336, 76975, 1409, 65536⟩
    (by decide) selected_cut_24205

theorem unmarked_context_11_19243_612337 : frontier 10 ⟨612337, by decide⟩
    (prefixCache 11 19243) (prefixPartial 11 19243) = false := by
  decide +kernel

theorem node_context_11_19243_612337 : EJMOriginalGlobalDAGData.nodes 10 ⟨612337, by decide⟩ =
    .split (coordinate 11) (![⟨612290, by decide⟩,⟨612308, by decide⟩,⟨612326, by decide⟩,⟨612336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19243_612337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19243 ⟨612337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19243
    ⟨612337, by decide⟩ (by decide) (![⟨612290, by decide⟩,⟨612308, by decide⟩,⟨612326, by decide⟩,⟨612336, by decide⟩]) unmarked_context_11_19243_612337 node_context_11_19243_612337
  intro a
  fin_cases a
  · exact context_12_76972_612290
  · exact context_12_76973_612308
  · exact context_12_76974_612326
  · exact context_12_76975_612336

theorem unmarked_context_10_4810_612338 : frontier 11 ⟨612338, by decide⟩
    (prefixCache 10 4810) (prefixPartial 10 4810) = false := by
  decide +kernel

theorem node_context_10_4810_612338 : EJMOriginalGlobalDAGData.nodes 11 ⟨612338, by decide⟩ =
    .split (coordinate 10) (![⟨612090, by decide⟩,⟨612184, by decide⟩,⟨612273, by decide⟩,⟨612337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4810_612338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4810 ⟨612338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4810
    ⟨612338, by decide⟩ (by decide) (![⟨612090, by decide⟩,⟨612184, by decide⟩,⟨612273, by decide⟩,⟨612337, by decide⟩]) unmarked_context_10_4810_612338 node_context_10_4810_612338
  intro a
  fin_cases a
  · exact context_11_19240_612090
  · exact context_11_19241_612184
  · exact context_11_19242_612273
  · exact context_11_19243_612337

theorem selected_cut_24206 : selected 10 ⟨612385, by decide⟩
    (prefixPartial 11 19244) = some ⟨11, 2, 0, 612385, 19244, 4069, 262144⟩ := by
  decide +kernel

theorem context_11_19244_612385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19244 ⟨612385, by decide⟩ :=
  accepted_of_selected 11 19244 ⟨612385, by decide⟩ ⟨11, 2, 0, 612385, 19244, 4069, 262144⟩
    (by decide) selected_cut_24206

theorem selected_cut_24207 : selected 9 ⟨612399, by decide⟩
    (prefixPartial 12 76980) = some ⟨12, 2, 0, 612399, 76980, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_76980_612399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76980 ⟨612399, by decide⟩ :=
  accepted_of_selected 12 76980 ⟨612399, by decide⟩ ⟨12, 2, 0, 612399, 76980, 1309, 65536⟩
    (by decide) selected_cut_24207

theorem selected_cut_24208 : selected 9 ⟨612412, by decide⟩
    (prefixPartial 12 76981) = some ⟨12, 2, 0, 612412, 76981, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_76981_612412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76981 ⟨612412, by decide⟩ :=
  accepted_of_selected 12 76981 ⟨612412, by decide⟩ ⟨12, 2, 0, 612412, 76981, 1437, 65536⟩
    (by decide) selected_cut_24208

theorem selected_cut_24209 : selected 9 ⟨612425, by decide⟩
    (prefixPartial 12 76982) = some ⟨12, 2, 0, 612425, 76982, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_76982_612425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76982 ⟨612425, by decide⟩ :=
  accepted_of_selected 12 76982 ⟨612425, by decide⟩ ⟨12, 2, 0, 612425, 76982, 1313, 65536⟩
    (by decide) selected_cut_24209

theorem selected_cut_24210 : selected 9 ⟨612449, by decide⟩
    (prefixPartial 12 76983) = some ⟨12, 2, 0, 612449, 76983, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_76983_612449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76983 ⟨612449, by decide⟩ :=
  accepted_of_selected 12 76983 ⟨612449, by decide⟩ ⟨12, 2, 0, 612449, 76983, 1377, 65536⟩
    (by decide) selected_cut_24210

theorem unmarked_context_11_19245_612450 : frontier 10 ⟨612450, by decide⟩
    (prefixCache 11 19245) (prefixPartial 11 19245) = false := by
  decide +kernel

theorem node_context_11_19245_612450 : EJMOriginalGlobalDAGData.nodes 10 ⟨612450, by decide⟩ =
    .split (coordinate 11) (![⟨612399, by decide⟩,⟨612412, by decide⟩,⟨612425, by decide⟩,⟨612449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19245_612450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19245 ⟨612450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19245
    ⟨612450, by decide⟩ (by decide) (![⟨612399, by decide⟩,⟨612412, by decide⟩,⟨612425, by decide⟩,⟨612449, by decide⟩]) unmarked_context_11_19245_612450 node_context_11_19245_612450
  intro a
  fin_cases a
  · exact context_12_76980_612399
  · exact context_12_76981_612412
  · exact context_12_76982_612425
  · exact context_12_76983_612449

theorem selected_cut_24211 : selected 9 ⟨612469, by decide⟩
    (prefixPartial 12 76984) = some ⟨12, 2, 0, 612469, 76984, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_76984_612469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76984 ⟨612469, by decide⟩ :=
  accepted_of_selected 12 76984 ⟨612469, by decide⟩ ⟨12, 2, 0, 612469, 76984, 1213, 65536⟩
    (by decide) selected_cut_24211

theorem selected_cut_24212 : selected 9 ⟨612488, by decide⟩
    (prefixPartial 12 76985) = some ⟨12, 2, 0, 612488, 76985, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_76985_612488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76985 ⟨612488, by decide⟩ :=
  accepted_of_selected 12 76985 ⟨612488, by decide⟩ ⟨12, 2, 0, 612488, 76985, 1397, 65536⟩
    (by decide) selected_cut_24212

theorem selected_cut_24213 : selected 9 ⟨612500, by decide⟩
    (prefixPartial 12 76986) = some ⟨12, 2, 0, 612500, 76986, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_76986_612500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76986 ⟨612500, by decide⟩ :=
  accepted_of_selected 12 76986 ⟨612500, by decide⟩ ⟨12, 2, 0, 612500, 76986, 1161, 65536⟩
    (by decide) selected_cut_24213

theorem selected_cut_24214 : selected 9 ⟨612522, by decide⟩
    (prefixPartial 12 76987) = some ⟨12, 2, 0, 612522, 76987, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_76987_612522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76987 ⟨612522, by decide⟩ :=
  accepted_of_selected 12 76987 ⟨612522, by decide⟩ ⟨12, 2, 0, 612522, 76987, 1217, 65536⟩
    (by decide) selected_cut_24214

theorem unmarked_context_11_19246_612523 : frontier 10 ⟨612523, by decide⟩
    (prefixCache 11 19246) (prefixPartial 11 19246) = false := by
  decide +kernel

theorem node_context_11_19246_612523 : EJMOriginalGlobalDAGData.nodes 10 ⟨612523, by decide⟩ =
    .split (coordinate 11) (![⟨612469, by decide⟩,⟨612488, by decide⟩,⟨612500, by decide⟩,⟨612522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19246_612523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19246 ⟨612523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19246
    ⟨612523, by decide⟩ (by decide) (![⟨612469, by decide⟩,⟨612488, by decide⟩,⟨612500, by decide⟩,⟨612522, by decide⟩]) unmarked_context_11_19246_612523 node_context_11_19246_612523
  intro a
  fin_cases a
  · exact context_12_76984_612469
  · exact context_12_76985_612488
  · exact context_12_76986_612500
  · exact context_12_76987_612522

theorem selected_cut_24215 : selected 10 ⟨612615, by decide⟩
    (prefixPartial 11 19247) = some ⟨11, 2, 0, 612615, 19247, 3757, 262144⟩ := by
  decide +kernel

theorem context_11_19247_612615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19247 ⟨612615, by decide⟩ :=
  accepted_of_selected 11 19247 ⟨612615, by decide⟩ ⟨11, 2, 0, 612615, 19247, 3757, 262144⟩
    (by decide) selected_cut_24215

theorem unmarked_context_10_4811_612616 : frontier 11 ⟨612616, by decide⟩
    (prefixCache 10 4811) (prefixPartial 10 4811) = false := by
  decide +kernel

theorem node_context_10_4811_612616 : EJMOriginalGlobalDAGData.nodes 11 ⟨612616, by decide⟩ =
    .split (coordinate 10) (![⟨612385, by decide⟩,⟨612450, by decide⟩,⟨612523, by decide⟩,⟨612615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4811_612616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4811 ⟨612616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4811
    ⟨612616, by decide⟩ (by decide) (![⟨612385, by decide⟩,⟨612450, by decide⟩,⟨612523, by decide⟩,⟨612615, by decide⟩]) unmarked_context_10_4811_612616 node_context_10_4811_612616
  intro a
  fin_cases a
  · exact context_11_19244_612385
  · exact context_11_19245_612450
  · exact context_11_19246_612523
  · exact context_11_19247_612615

theorem unmarked_context_9_1202_612617 : frontier 12 ⟨612617, by decide⟩
    (prefixCache 9 1202) (prefixPartial 9 1202) = false := by
  decide +kernel

theorem node_context_9_1202_612617 : EJMOriginalGlobalDAGData.nodes 12 ⟨612617, by decide⟩ =
    .split (coordinate 9) (![⟨611431, by decide⟩,⟨612029, by decide⟩,⟨612338, by decide⟩,⟨612616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1202_612617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1202 ⟨612617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1202
    ⟨612617, by decide⟩ (by decide) (![⟨611431, by decide⟩,⟨612029, by decide⟩,⟨612338, by decide⟩,⟨612616, by decide⟩]) unmarked_context_9_1202_612617 node_context_9_1202_612617
  intro a
  fin_cases a
  · exact context_10_4808_611431
  · exact context_10_4809_612029
  · exact context_10_4810_612338
  · exact context_10_4811_612616

theorem selected_cut_24216 : selected 10 ⟨612646, by decide⟩
    (prefixPartial 11 19248) = some ⟨11, 2, 0, 612646, 19248, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_19248_612646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19248 ⟨612646, by decide⟩ :=
  accepted_of_selected 11 19248 ⟨612646, by decide⟩ ⟨11, 2, 0, 612646, 19248, 2385, 262144⟩
    (by decide) selected_cut_24216

theorem selected_cut_24217 : selected 10 ⟨612679, by decide⟩
    (prefixPartial 11 19249) = some ⟨11, 2, 0, 612679, 19249, 2769, 262144⟩ := by
  decide +kernel

theorem context_11_19249_612679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19249 ⟨612679, by decide⟩ :=
  accepted_of_selected 11 19249 ⟨612679, by decide⟩ ⟨11, 2, 0, 612679, 19249, 2769, 262144⟩
    (by decide) selected_cut_24217

theorem selected_cut_24218 : selected 10 ⟨612713, by decide⟩
    (prefixPartial 11 19250) = some ⟨11, 2, 0, 612713, 19250, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_19250_612713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19250 ⟨612713, by decide⟩ :=
  accepted_of_selected 11 19250 ⟨612713, by decide⟩ ⟨11, 2, 0, 612713, 19250, 2809, 262144⟩
    (by decide) selected_cut_24218

theorem selected_cut_24219 : selected 10 ⟨612750, by decide⟩
    (prefixPartial 11 19251) = some ⟨11, 2, 0, 612750, 19251, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_19251_612750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19251 ⟨612750, by decide⟩ :=
  accepted_of_selected 11 19251 ⟨612750, by decide⟩ ⟨11, 2, 0, 612750, 19251, 2401, 262144⟩
    (by decide) selected_cut_24219

theorem unmarked_context_10_4812_612751 : frontier 11 ⟨612751, by decide⟩
    (prefixCache 10 4812) (prefixPartial 10 4812) = false := by
  decide +kernel

theorem node_context_10_4812_612751 : EJMOriginalGlobalDAGData.nodes 11 ⟨612751, by decide⟩ =
    .split (coordinate 10) (![⟨612646, by decide⟩,⟨612679, by decide⟩,⟨612713, by decide⟩,⟨612750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4812_612751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4812 ⟨612751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4812
    ⟨612751, by decide⟩ (by decide) (![⟨612646, by decide⟩,⟨612679, by decide⟩,⟨612713, by decide⟩,⟨612750, by decide⟩]) unmarked_context_10_4812_612751 node_context_10_4812_612751
  intro a
  fin_cases a
  · exact context_11_19248_612646
  · exact context_11_19249_612679
  · exact context_11_19250_612713
  · exact context_11_19251_612750

theorem selected_cut_24220 : selected 10 ⟨612770, by decide⟩
    (prefixPartial 11 19252) = some ⟨11, 2, 0, 612770, 19252, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_19252_612770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19252 ⟨612770, by decide⟩ :=
  accepted_of_selected 11 19252 ⟨612770, by decide⟩ ⟨11, 2, 0, 612770, 19252, 1993, 262144⟩
    (by decide) selected_cut_24220

theorem selected_cut_24221 : selected 10 ⟨612801, by decide⟩
    (prefixPartial 11 19253) = some ⟨11, 2, 0, 612801, 19253, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_19253_612801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19253 ⟨612801, by decide⟩ :=
  accepted_of_selected 11 19253 ⟨612801, by decide⟩ ⟨11, 2, 0, 612801, 19253, 2329, 262144⟩
    (by decide) selected_cut_24221

theorem selected_cut_24222 : selected 10 ⟨612825, by decide⟩
    (prefixPartial 11 19254) = some ⟨11, 2, 0, 612825, 19254, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_19254_612825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19254 ⟨612825, by decide⟩ :=
  accepted_of_selected 11 19254 ⟨612825, by decide⟩ ⟨11, 2, 0, 612825, 19254, 2113, 262144⟩
    (by decide) selected_cut_24222

theorem selected_cut_24223 : selected 10 ⟨612847, by decide⟩
    (prefixPartial 11 19255) = some ⟨11, 2, 0, 612847, 19255, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_19255_612847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19255 ⟨612847, by decide⟩ :=
  accepted_of_selected 11 19255 ⟨612847, by decide⟩ ⟨11, 2, 0, 612847, 19255, 1773, 262144⟩
    (by decide) selected_cut_24223

theorem unmarked_context_10_4813_612848 : frontier 11 ⟨612848, by decide⟩
    (prefixCache 10 4813) (prefixPartial 10 4813) = false := by
  decide +kernel

theorem node_context_10_4813_612848 : EJMOriginalGlobalDAGData.nodes 11 ⟨612848, by decide⟩ =
    .split (coordinate 10) (![⟨612770, by decide⟩,⟨612801, by decide⟩,⟨612825, by decide⟩,⟨612847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4813_612848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4813 ⟨612848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4813
    ⟨612848, by decide⟩ (by decide) (![⟨612770, by decide⟩,⟨612801, by decide⟩,⟨612825, by decide⟩,⟨612847, by decide⟩]) unmarked_context_10_4813_612848 node_context_10_4813_612848
  intro a
  fin_cases a
  · exact context_11_19252_612770
  · exact context_11_19253_612801
  · exact context_11_19254_612825
  · exact context_11_19255_612847

theorem selected_cut_24224 : selected 10 ⟨612864, by decide⟩
    (prefixPartial 11 19256) = some ⟨11, 2, 0, 612864, 19256, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_19256_612864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19256 ⟨612864, by decide⟩ :=
  accepted_of_selected 11 19256 ⟨612864, by decide⟩ ⟨11, 2, 0, 612864, 19256, 1105, 262144⟩
    (by decide) selected_cut_24224

theorem selected_cut_24225 : selected 10 ⟨612883, by decide⟩
    (prefixPartial 11 19257) = some ⟨11, 2, 0, 612883, 19257, 1325, 262144⟩ := by
  decide +kernel

theorem context_11_19257_612883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19257 ⟨612883, by decide⟩ :=
  accepted_of_selected 11 19257 ⟨612883, by decide⟩ ⟨11, 2, 0, 612883, 19257, 1325, 262144⟩
    (by decide) selected_cut_24225

theorem selected_cut_24226 : selected 10 ⟨612899, by decide⟩
    (prefixPartial 11 19258) = some ⟨11, 2, 0, 612899, 19258, 1029, 262144⟩ := by
  decide +kernel

theorem context_11_19258_612899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19258 ⟨612899, by decide⟩ :=
  accepted_of_selected 11 19258 ⟨612899, by decide⟩ ⟨11, 2, 0, 612899, 19258, 1029, 262144⟩
    (by decide) selected_cut_24226

theorem selected_cut_24227 : selected 10 ⟨612915, by decide⟩
    (prefixPartial 11 19259) = some ⟨11, 2, 0, 612915, 19259, 777, 262144⟩ := by
  decide +kernel

theorem context_11_19259_612915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19259 ⟨612915, by decide⟩ :=
  accepted_of_selected 11 19259 ⟨612915, by decide⟩ ⟨11, 2, 0, 612915, 19259, 777, 262144⟩
    (by decide) selected_cut_24227

theorem unmarked_context_10_4814_612916 : frontier 11 ⟨612916, by decide⟩
    (prefixCache 10 4814) (prefixPartial 10 4814) = false := by
  decide +kernel

theorem node_context_10_4814_612916 : EJMOriginalGlobalDAGData.nodes 11 ⟨612916, by decide⟩ =
    .split (coordinate 10) (![⟨612864, by decide⟩,⟨612883, by decide⟩,⟨612899, by decide⟩,⟨612915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4814_612916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4814 ⟨612916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4814
    ⟨612916, by decide⟩ (by decide) (![⟨612864, by decide⟩,⟨612883, by decide⟩,⟨612899, by decide⟩,⟨612915, by decide⟩]) unmarked_context_10_4814_612916 node_context_10_4814_612916
  intro a
  fin_cases a
  · exact context_11_19256_612864
  · exact context_11_19257_612883
  · exact context_11_19258_612899
  · exact context_11_19259_612915

theorem selected_cut_24228 : selected 11 ⟨612962, by decide⟩
    (prefixPartial 10 4815) = some ⟨10, 2, 0, 612962, 4815, 933, 1048576⟩ := by
  decide +kernel

theorem context_10_4815_612962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4815 ⟨612962, by decide⟩ :=
  accepted_of_selected 10 4815 ⟨612962, by decide⟩ ⟨10, 2, 0, 612962, 4815, 933, 1048576⟩
    (by decide) selected_cut_24228

theorem unmarked_context_9_1203_612963 : frontier 12 ⟨612963, by decide⟩
    (prefixCache 9 1203) (prefixPartial 9 1203) = false := by
  decide +kernel

theorem node_context_9_1203_612963 : EJMOriginalGlobalDAGData.nodes 12 ⟨612963, by decide⟩ =
    .split (coordinate 9) (![⟨612751, by decide⟩,⟨612848, by decide⟩,⟨612916, by decide⟩,⟨612962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1203_612963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1203 ⟨612963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1203
    ⟨612963, by decide⟩ (by decide) (![⟨612751, by decide⟩,⟨612848, by decide⟩,⟨612916, by decide⟩,⟨612962, by decide⟩]) unmarked_context_9_1203_612963 node_context_9_1203_612963
  intro a
  fin_cases a
  · exact context_10_4812_612751
  · exact context_10_4813_612848
  · exact context_10_4814_612916
  · exact context_10_4815_612962

theorem unmarked_context_8_300_612964 : frontier 13 ⟨612964, by decide⟩
    (prefixCache 8 300) (prefixPartial 8 300) = false := by
  decide +kernel

theorem node_context_8_300_612964 : EJMOriginalGlobalDAGData.nodes 13 ⟨612964, by decide⟩ =
    .split (coordinate 8) (![⟨607722, by decide⟩,⟨610940, by decide⟩,⟨612617, by decide⟩,⟨612963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_300_612964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 300 ⟨612964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 300
    ⟨612964, by decide⟩ (by decide) (![⟨607722, by decide⟩,⟨610940, by decide⟩,⟨612617, by decide⟩,⟨612963, by decide⟩]) unmarked_context_8_300_612964 node_context_8_300_612964
  intro a
  fin_cases a
  · exact context_9_1200_607722
  · exact context_9_1201_610940
  · exact context_9_1202_612617
  · exact context_9_1203_612963

theorem selected_cut_24229 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 19264) = some ⟨11, 1, 0, 434745, 19264, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19264_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19264 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 19264 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 19264, 1, 262144⟩
    (by decide) selected_cut_24229

theorem selected_cut_24230 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 77060) = some ⟨12, 1, 0, 448748, 77060, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77060_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77060 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 77060 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 77060, 1, 65536⟩
    (by decide) selected_cut_24230

theorem selected_cut_24231 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 77061) = some ⟨12, 1, 0, 34034, 77061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77061_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77061 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 77061 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 77061, 1, 65536⟩
    (by decide) selected_cut_24231

theorem selected_cut_24232 : selected 8 ⟨613028, by decide⟩
    (prefixPartial 13 308248) = some ⟨13, 2, 0, 613028, 308248, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_308248_613028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308248 ⟨613028, by decide⟩ :=
  accepted_of_selected 13 308248 ⟨613028, by decide⟩ ⟨13, 2, 0, 613028, 308248, 1913, 16384⟩
    (by decide) selected_cut_24232

theorem selected_cut_24233 : selected 8 ⟨613066, by decide⟩
    (prefixPartial 13 308249) = some ⟨13, 2, 0, 613066, 308249, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_308249_613066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308249 ⟨613066, by decide⟩ :=
  accepted_of_selected 13 308249 ⟨613066, by decide⟩ ⟨13, 2, 0, 613066, 308249, 2445, 16384⟩
    (by decide) selected_cut_24233

theorem selected_cut_24234 : selected 8 ⟨613099, by decide⟩
    (prefixPartial 13 308250) = some ⟨13, 2, 0, 613099, 308250, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_308250_613099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308250 ⟨613099, by decide⟩ :=
  accepted_of_selected 13 308250 ⟨613099, by decide⟩ ⟨13, 2, 0, 613099, 308250, 1893, 16384⟩
    (by decide) selected_cut_24234

theorem selected_cut_24235 : selected 8 ⟨613115, by decide⟩
    (prefixPartial 13 308251) = some ⟨13, 2, 0, 613115, 308251, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_308251_613115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308251 ⟨613115, by decide⟩ :=
  accepted_of_selected 13 308251 ⟨613115, by decide⟩ ⟨13, 2, 0, 613115, 308251, 1117, 16384⟩
    (by decide) selected_cut_24235

theorem unmarked_context_12_77062_613116 : frontier 9 ⟨613116, by decide⟩
    (prefixCache 12 77062) (prefixPartial 12 77062) = false := by
  decide +kernel

theorem node_context_12_77062_613116 : EJMOriginalGlobalDAGData.nodes 9 ⟨613116, by decide⟩ =
    .split (coordinate 12) (![⟨613028, by decide⟩,⟨613066, by decide⟩,⟨613099, by decide⟩,⟨613115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77062_613116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77062 ⟨613116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77062
    ⟨613116, by decide⟩ (by decide) (![⟨613028, by decide⟩,⟨613066, by decide⟩,⟨613099, by decide⟩,⟨613115, by decide⟩]) unmarked_context_12_77062_613116 node_context_12_77062_613116
  intro a
  fin_cases a
  · exact context_13_308248_613028
  · exact context_13_308249_613066
  · exact context_13_308250_613099
  · exact context_13_308251_613115

theorem selected_cut_24236 : selected 9 ⟨603785, by decide⟩
    (prefixPartial 12 77063) = some ⟨12, 1, 0, 603785, 77063, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77063_603785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77063 ⟨603785, by decide⟩ :=
  accepted_of_selected 12 77063 ⟨603785, by decide⟩ ⟨12, 1, 0, 603785, 77063, 1, 65536⟩
    (by decide) selected_cut_24236

theorem unmarked_context_11_19265_613117 : frontier 10 ⟨613117, by decide⟩
    (prefixCache 11 19265) (prefixPartial 11 19265) = false := by
  decide +kernel

theorem node_context_11_19265_613117 : EJMOriginalGlobalDAGData.nodes 10 ⟨613117, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨613116, by decide⟩,⟨603785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19265_613117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19265 ⟨613117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19265
    ⟨613117, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨613116, by decide⟩,⟨603785, by decide⟩]) unmarked_context_11_19265_613117 node_context_11_19265_613117
  intro a
  fin_cases a
  · exact context_12_77060_448748
  · exact context_12_77061_34034
  · exact context_12_77062_613116
  · exact context_12_77063_603785

theorem selected_cut_24237 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 77064) = some ⟨12, 1, 0, 448748, 77064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77064_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77064 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 77064 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 77064, 1, 65536⟩
    (by decide) selected_cut_24237

theorem selected_cut_24238 : selected 8 ⟨613185, by decide⟩
    (prefixPartial 13 308260) = some ⟨13, 2, 0, 613185, 308260, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_308260_613185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308260 ⟨613185, by decide⟩ :=
  accepted_of_selected 13 308260 ⟨613185, by decide⟩ ⟨13, 2, 0, 613185, 308260, 2593, 16384⟩
    (by decide) selected_cut_24238

theorem selected_cut_24239 : selected 8 ⟨613236, by decide⟩
    (prefixPartial 13 308261) = some ⟨13, 2, 0, 613236, 308261, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_308261_613236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308261 ⟨613236, by decide⟩ :=
  accepted_of_selected 13 308261 ⟨613236, by decide⟩ ⟨13, 2, 0, 613236, 308261, 2557, 16384⟩
    (by decide) selected_cut_24239

theorem selected_cut_24240 : selected 8 ⟨613299, by decide⟩
    (prefixPartial 13 308262) = some ⟨13, 2, 0, 613299, 308262, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_308262_613299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308262 ⟨613299, by decide⟩ :=
  accepted_of_selected 13 308262 ⟨613299, by decide⟩ ⟨13, 2, 0, 613299, 308262, 2449, 16384⟩
    (by decide) selected_cut_24240

theorem selected_cut_24241 : selected 8 ⟨613322, by decide⟩
    (prefixPartial 13 308263) = some ⟨13, 2, 0, 613322, 308263, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_308263_613322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308263 ⟨613322, by decide⟩ :=
  accepted_of_selected 13 308263 ⟨613322, by decide⟩ ⟨13, 2, 0, 613322, 308263, 1169, 16384⟩
    (by decide) selected_cut_24241

theorem unmarked_context_12_77065_613323 : frontier 9 ⟨613323, by decide⟩
    (prefixCache 12 77065) (prefixPartial 12 77065) = false := by
  decide +kernel

theorem node_context_12_77065_613323 : EJMOriginalGlobalDAGData.nodes 9 ⟨613323, by decide⟩ =
    .split (coordinate 12) (![⟨613185, by decide⟩,⟨613236, by decide⟩,⟨613299, by decide⟩,⟨613322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77065_613323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77065 ⟨613323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77065
    ⟨613323, by decide⟩ (by decide) (![⟨613185, by decide⟩,⟨613236, by decide⟩,⟨613299, by decide⟩,⟨613322, by decide⟩]) unmarked_context_12_77065_613323 node_context_12_77065_613323
  intro a
  fin_cases a
  · exact context_13_308260_613185
  · exact context_13_308261_613236
  · exact context_13_308262_613299
  · exact context_13_308263_613322

theorem selected_cut_24242 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 77066) = some ⟨12, 1, 0, 524302, 77066, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77066_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77066 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 77066 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 77066, 1, 65536⟩
    (by decide) selected_cut_24242

theorem selected_cut_24243 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 77067) = some ⟨12, 1, 0, 604131, 77067, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77067_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77067 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 77067 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 77067, 1, 65536⟩
    (by decide) selected_cut_24243

theorem unmarked_context_11_19266_613324 : frontier 10 ⟨613324, by decide⟩
    (prefixCache 11 19266) (prefixPartial 11 19266) = false := by
  decide +kernel

theorem node_context_11_19266_613324 : EJMOriginalGlobalDAGData.nodes 10 ⟨613324, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨613323, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19266_613324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19266 ⟨613324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19266
    ⟨613324, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨613323, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_19266_613324 node_context_11_19266_613324
  intro a
  fin_cases a
  · exact context_12_77064_448748
  · exact context_12_77065_613323
  · exact context_12_77066_524302
  · exact context_12_77067_604131

theorem selected_cut_24244 : selected 10 ⟨604133, by decide⟩
    (prefixPartial 11 19267) = some ⟨11, 2, 0, 604133, 19267, 5, 262144⟩ := by
  decide +kernel

theorem context_11_19267_604133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19267 ⟨604133, by decide⟩ :=
  accepted_of_selected 11 19267 ⟨604133, by decide⟩ ⟨11, 2, 0, 604133, 19267, 5, 262144⟩
    (by decide) selected_cut_24244

theorem unmarked_context_10_4816_613325 : frontier 11 ⟨613325, by decide⟩
    (prefixCache 10 4816) (prefixPartial 10 4816) = false := by
  decide +kernel

theorem node_context_10_4816_613325 : EJMOriginalGlobalDAGData.nodes 11 ⟨613325, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨613117, by decide⟩,⟨613324, by decide⟩,⟨604133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4816_613325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4816 ⟨613325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4816
    ⟨613325, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨613117, by decide⟩,⟨613324, by decide⟩,⟨604133, by decide⟩]) unmarked_context_10_4816_613325 node_context_10_4816_613325
  intro a
  fin_cases a
  · exact context_11_19264_434745
  · exact context_11_19265_613117
  · exact context_11_19266_613324
  · exact context_11_19267_604133

theorem selected_cut_24245 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 77072) = some ⟨12, 1, 0, 435160, 77072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77072_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77072 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 77072 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 77072, 1, 65536⟩
    (by decide) selected_cut_24245

theorem selected_cut_24246 : selected 8 ⟨613363, by decide⟩
    (prefixPartial 13 308292) = some ⟨13, 2, 0, 613363, 308292, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_308292_613363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308292 ⟨613363, by decide⟩ :=
  accepted_of_selected 13 308292 ⟨613363, by decide⟩ ⟨13, 2, 0, 613363, 308292, 1809, 16384⟩
    (by decide) selected_cut_24246

theorem selected_cut_24247 : selected 8 ⟨613396, by decide⟩
    (prefixPartial 13 308293) = some ⟨13, 2, 0, 613396, 308293, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_308293_613396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308293 ⟨613396, by decide⟩ :=
  accepted_of_selected 13 308293 ⟨613396, by decide⟩ ⟨13, 2, 0, 613396, 308293, 2021, 16384⟩
    (by decide) selected_cut_24247

theorem selected_cut_24248 : selected 8 ⟨613422, by decide⟩
    (prefixPartial 13 308294) = some ⟨13, 2, 0, 613422, 308294, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_308294_613422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308294 ⟨613422, by decide⟩ :=
  accepted_of_selected 13 308294 ⟨613422, by decide⟩ ⟨13, 2, 0, 613422, 308294, 1629, 16384⟩
    (by decide) selected_cut_24248

theorem selected_cut_24249 : selected 8 ⟨613435, by decide⟩
    (prefixPartial 13 308295) = some ⟨13, 2, 0, 613435, 308295, 845, 16384⟩ := by
  decide +kernel

theorem context_13_308295_613435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308295 ⟨613435, by decide⟩ :=
  accepted_of_selected 13 308295 ⟨613435, by decide⟩ ⟨13, 2, 0, 613435, 308295, 845, 16384⟩
    (by decide) selected_cut_24249

theorem unmarked_context_12_77073_613436 : frontier 9 ⟨613436, by decide⟩
    (prefixCache 12 77073) (prefixPartial 12 77073) = false := by
  decide +kernel

theorem node_context_12_77073_613436 : EJMOriginalGlobalDAGData.nodes 9 ⟨613436, by decide⟩ =
    .split (coordinate 12) (![⟨613363, by decide⟩,⟨613396, by decide⟩,⟨613422, by decide⟩,⟨613435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77073_613436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77073 ⟨613436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77073
    ⟨613436, by decide⟩ (by decide) (![⟨613363, by decide⟩,⟨613396, by decide⟩,⟨613422, by decide⟩,⟨613435, by decide⟩]) unmarked_context_12_77073_613436 node_context_12_77073_613436
  intro a
  fin_cases a
  · exact context_13_308292_613363
  · exact context_13_308293_613396
  · exact context_13_308294_613422
  · exact context_13_308295_613435

theorem selected_cut_24250 : selected 8 ⟨613475, by decide⟩
    (prefixPartial 13 308296) = some ⟨13, 2, 0, 613475, 308296, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_308296_613475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308296 ⟨613475, by decide⟩ :=
  accepted_of_selected 13 308296 ⟨613475, by decide⟩ ⟨13, 2, 0, 613475, 308296, 1789, 16384⟩
    (by decide) selected_cut_24250

theorem selected_cut_24251 : selected 8 ⟨613512, by decide⟩
    (prefixPartial 13 308297) = some ⟨13, 2, 0, 613512, 308297, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_308297_613512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308297 ⟨613512, by decide⟩ :=
  accepted_of_selected 13 308297 ⟨613512, by decide⟩ ⟨13, 2, 0, 613512, 308297, 2201, 16384⟩
    (by decide) selected_cut_24251

theorem selected_cut_24252 : selected 8 ⟨613535, by decide⟩
    (prefixPartial 13 308298) = some ⟨13, 2, 0, 613535, 308298, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_308298_613535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308298 ⟨613535, by decide⟩ :=
  accepted_of_selected 13 308298 ⟨613535, by decide⟩ ⟨13, 2, 0, 613535, 308298, 1509, 16384⟩
    (by decide) selected_cut_24252

theorem selected_cut_24253 : selected 8 ⟨613546, by decide⟩
    (prefixPartial 13 308299) = some ⟨13, 2, 0, 613546, 308299, 905, 16384⟩ := by
  decide +kernel

theorem context_13_308299_613546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308299 ⟨613546, by decide⟩ :=
  accepted_of_selected 13 308299 ⟨613546, by decide⟩ ⟨13, 2, 0, 613546, 308299, 905, 16384⟩
    (by decide) selected_cut_24253

theorem unmarked_context_12_77074_613547 : frontier 9 ⟨613547, by decide⟩
    (prefixCache 12 77074) (prefixPartial 12 77074) = false := by
  decide +kernel

theorem node_context_12_77074_613547 : EJMOriginalGlobalDAGData.nodes 9 ⟨613547, by decide⟩ =
    .split (coordinate 12) (![⟨613475, by decide⟩,⟨613512, by decide⟩,⟨613535, by decide⟩,⟨613546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77074_613547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77074 ⟨613547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77074
    ⟨613547, by decide⟩ (by decide) (![⟨613475, by decide⟩,⟨613512, by decide⟩,⟨613535, by decide⟩,⟨613546, by decide⟩]) unmarked_context_12_77074_613547 node_context_12_77074_613547
  intro a
  fin_cases a
  · exact context_13_308296_613475
  · exact context_13_308297_613512
  · exact context_13_308298_613535
  · exact context_13_308299_613546

theorem selected_cut_24254 : selected 8 ⟨613587, by decide⟩
    (prefixPartial 13 308300) = some ⟨13, 2, 0, 613587, 308300, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_308300_613587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308300 ⟨613587, by decide⟩ :=
  accepted_of_selected 13 308300 ⟨613587, by decide⟩ ⟨13, 2, 0, 613587, 308300, 1965, 16384⟩
    (by decide) selected_cut_24254

theorem selected_cut_24255 : selected 8 ⟨613623, by decide⟩
    (prefixPartial 13 308301) = some ⟨13, 2, 0, 613623, 308301, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_308301_613623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308301 ⟨613623, by decide⟩ :=
  accepted_of_selected 13 308301 ⟨613623, by decide⟩ ⟨13, 2, 0, 613623, 308301, 2381, 16384⟩
    (by decide) selected_cut_24255

theorem selected_cut_24256 : selected 8 ⟨613649, by decide⟩
    (prefixPartial 13 308302) = some ⟨13, 2, 0, 613649, 308302, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_308302_613649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308302 ⟨613649, by decide⟩ :=
  accepted_of_selected 13 308302 ⟨613649, by decide⟩ ⟨13, 2, 0, 613649, 308302, 1781, 16384⟩
    (by decide) selected_cut_24256

theorem selected_cut_24257 : selected 8 ⟨613669, by decide⟩
    (prefixPartial 13 308303) = some ⟨13, 2, 0, 613669, 308303, 945, 16384⟩ := by
  decide +kernel

theorem context_13_308303_613669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308303 ⟨613669, by decide⟩ :=
  accepted_of_selected 13 308303 ⟨613669, by decide⟩ ⟨13, 2, 0, 613669, 308303, 945, 16384⟩
    (by decide) selected_cut_24257

theorem unmarked_context_12_77075_613670 : frontier 9 ⟨613670, by decide⟩
    (prefixCache 12 77075) (prefixPartial 12 77075) = false := by
  decide +kernel

theorem node_context_12_77075_613670 : EJMOriginalGlobalDAGData.nodes 9 ⟨613670, by decide⟩ =
    .split (coordinate 12) (![⟨613587, by decide⟩,⟨613623, by decide⟩,⟨613649, by decide⟩,⟨613669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77075_613670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77075 ⟨613670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77075
    ⟨613670, by decide⟩ (by decide) (![⟨613587, by decide⟩,⟨613623, by decide⟩,⟨613649, by decide⟩,⟨613669, by decide⟩]) unmarked_context_12_77075_613670 node_context_12_77075_613670
  intro a
  fin_cases a
  · exact context_13_308300_613587
  · exact context_13_308301_613623
  · exact context_13_308302_613649
  · exact context_13_308303_613669

theorem unmarked_context_11_19268_613671 : frontier 10 ⟨613671, by decide⟩
    (prefixCache 11 19268) (prefixPartial 11 19268) = false := by
  decide +kernel

theorem node_context_11_19268_613671 : EJMOriginalGlobalDAGData.nodes 10 ⟨613671, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨613436, by decide⟩,⟨613547, by decide⟩,⟨613670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19268_613671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19268 ⟨613671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19268
    ⟨613671, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨613436, by decide⟩,⟨613547, by decide⟩,⟨613670, by decide⟩]) unmarked_context_11_19268_613671 node_context_11_19268_613671
  intro a
  fin_cases a
  · exact context_12_77072_435160
  · exact context_12_77073_613436
  · exact context_12_77074_613547
  · exact context_12_77075_613670

theorem selected_cut_24258 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 77076) = some ⟨12, 1, 0, 435160, 77076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77076_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77076 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 77076 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 77076, 1, 65536⟩
    (by decide) selected_cut_24258

theorem selected_cut_24259 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 77077) = some ⟨12, 1, 0, 439069, 77077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77077_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77077 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 77077 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 77077, 1, 65536⟩
    (by decide) selected_cut_24259

theorem selected_cut_24260 : selected 8 ⟨613702, by decide⟩
    (prefixPartial 13 308312) = some ⟨13, 2, 0, 613702, 308312, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_308312_613702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308312 ⟨613702, by decide⟩ :=
  accepted_of_selected 13 308312 ⟨613702, by decide⟩ ⟨13, 2, 0, 613702, 308312, 1565, 16384⟩
    (by decide) selected_cut_24260

theorem selected_cut_24261 : selected 8 ⟨613735, by decide⟩
    (prefixPartial 13 308313) = some ⟨13, 2, 0, 613735, 308313, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_308313_613735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308313 ⟨613735, by decide⟩ :=
  accepted_of_selected 13 308313 ⟨613735, by decide⟩ ⟨13, 2, 0, 613735, 308313, 2301, 16384⟩
    (by decide) selected_cut_24261

theorem selected_cut_24262 : selected 8 ⟨613755, by decide⟩
    (prefixPartial 13 308314) = some ⟨13, 2, 0, 613755, 308314, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_308314_613755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308314 ⟨613755, by decide⟩ :=
  accepted_of_selected 13 308314 ⟨613755, by decide⟩ ⟨13, 2, 0, 613755, 308314, 1393, 16384⟩
    (by decide) selected_cut_24262

theorem selected_cut_24263 : selected 8 ⟨613764, by decide⟩
    (prefixPartial 13 308315) = some ⟨13, 2, 0, 613764, 308315, 865, 16384⟩ := by
  decide +kernel

theorem context_13_308315_613764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308315 ⟨613764, by decide⟩ :=
  accepted_of_selected 13 308315 ⟨613764, by decide⟩ ⟨13, 2, 0, 613764, 308315, 865, 16384⟩
    (by decide) selected_cut_24263

theorem unmarked_context_12_77078_613765 : frontier 9 ⟨613765, by decide⟩
    (prefixCache 12 77078) (prefixPartial 12 77078) = false := by
  decide +kernel

theorem node_context_12_77078_613765 : EJMOriginalGlobalDAGData.nodes 9 ⟨613765, by decide⟩ =
    .split (coordinate 12) (![⟨613702, by decide⟩,⟨613735, by decide⟩,⟨613755, by decide⟩,⟨613764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77078_613765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77078 ⟨613765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77078
    ⟨613765, by decide⟩ (by decide) (![⟨613702, by decide⟩,⟨613735, by decide⟩,⟨613755, by decide⟩,⟨613764, by decide⟩]) unmarked_context_12_77078_613765 node_context_12_77078_613765
  intro a
  fin_cases a
  · exact context_13_308312_613702
  · exact context_13_308313_613735
  · exact context_13_308314_613755
  · exact context_13_308315_613764

theorem selected_cut_24264 : selected 8 ⟨613796, by decide⟩
    (prefixPartial 13 308316) = some ⟨13, 2, 0, 613796, 308316, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_308316_613796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308316 ⟨613796, by decide⟩ :=
  accepted_of_selected 13 308316 ⟨613796, by decide⟩ ⟨13, 2, 0, 613796, 308316, 1729, 16384⟩
    (by decide) selected_cut_24264

theorem selected_cut_24265 : selected 8 ⟨613826, by decide⟩
    (prefixPartial 13 308317) = some ⟨13, 2, 0, 613826, 308317, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_308317_613826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308317 ⟨613826, by decide⟩ :=
  accepted_of_selected 13 308317 ⟨613826, by decide⟩ ⟨13, 2, 0, 613826, 308317, 2409, 16384⟩
    (by decide) selected_cut_24265

theorem selected_cut_24266 : selected 8 ⟨613847, by decide⟩
    (prefixPartial 13 308318) = some ⟨13, 2, 0, 613847, 308318, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_308318_613847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308318 ⟨613847, by decide⟩ :=
  accepted_of_selected 13 308318 ⟨613847, by decide⟩ ⟨13, 2, 0, 613847, 308318, 1765, 16384⟩
    (by decide) selected_cut_24266

theorem selected_cut_24267 : selected 8 ⟨613855, by decide⟩
    (prefixPartial 13 308319) = some ⟨13, 2, 0, 613855, 308319, 889, 16384⟩ := by
  decide +kernel

theorem context_13_308319_613855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308319 ⟨613855, by decide⟩ :=
  accepted_of_selected 13 308319 ⟨613855, by decide⟩ ⟨13, 2, 0, 613855, 308319, 889, 16384⟩
    (by decide) selected_cut_24267

theorem unmarked_context_12_77079_613856 : frontier 9 ⟨613856, by decide⟩
    (prefixCache 12 77079) (prefixPartial 12 77079) = false := by
  decide +kernel

theorem node_context_12_77079_613856 : EJMOriginalGlobalDAGData.nodes 9 ⟨613856, by decide⟩ =
    .split (coordinate 12) (![⟨613796, by decide⟩,⟨613826, by decide⟩,⟨613847, by decide⟩,⟨613855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77079_613856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77079 ⟨613856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77079
    ⟨613856, by decide⟩ (by decide) (![⟨613796, by decide⟩,⟨613826, by decide⟩,⟨613847, by decide⟩,⟨613855, by decide⟩]) unmarked_context_12_77079_613856 node_context_12_77079_613856
  intro a
  fin_cases a
  · exact context_13_308316_613796
  · exact context_13_308317_613826
  · exact context_13_308318_613847
  · exact context_13_308319_613855

theorem unmarked_context_11_19269_613857 : frontier 10 ⟨613857, by decide⟩
    (prefixCache 11 19269) (prefixPartial 11 19269) = false := by
  decide +kernel

theorem node_context_11_19269_613857 : EJMOriginalGlobalDAGData.nodes 10 ⟨613857, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨439069, by decide⟩,⟨613765, by decide⟩,⟨613856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19269_613857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19269 ⟨613857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19269
    ⟨613857, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨439069, by decide⟩,⟨613765, by decide⟩,⟨613856, by decide⟩]) unmarked_context_11_19269_613857 node_context_11_19269_613857
  intro a
  fin_cases a
  · exact context_12_77076_435160
  · exact context_12_77077_439069
  · exact context_12_77078_613765
  · exact context_12_77079_613856

theorem selected_cut_24268 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 77080) = some ⟨12, 1, 0, 449505, 77080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77080_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77080 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 77080 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 77080, 1, 65536⟩
    (by decide) selected_cut_24268

theorem selected_cut_24269 : selected 8 ⟨613890, by decide⟩
    (prefixPartial 13 308324) = some ⟨13, 2, 0, 613890, 308324, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_308324_613890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308324 ⟨613890, by decide⟩ :=
  accepted_of_selected 13 308324 ⟨613890, by decide⟩ ⟨13, 2, 0, 613890, 308324, 1617, 16384⟩
    (by decide) selected_cut_24269

theorem selected_cut_24270 : selected 8 ⟨613927, by decide⟩
    (prefixPartial 13 308325) = some ⟨13, 2, 0, 613927, 308325, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_308325_613927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308325 ⟨613927, by decide⟩ :=
  accepted_of_selected 13 308325 ⟨613927, by decide⟩ ⟨13, 2, 0, 613927, 308325, 2093, 16384⟩
    (by decide) selected_cut_24270

theorem selected_cut_24271 : selected 8 ⟨613951, by decide⟩
    (prefixPartial 13 308326) = some ⟨13, 2, 0, 613951, 308326, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_308326_613951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308326 ⟨613951, by decide⟩ :=
  accepted_of_selected 13 308326 ⟨613951, by decide⟩ ⟨13, 2, 0, 613951, 308326, 1853, 16384⟩
    (by decide) selected_cut_24271

theorem selected_cut_24272 : selected 8 ⟨613965, by decide⟩
    (prefixPartial 13 308327) = some ⟨13, 2, 0, 613965, 308327, 997, 16384⟩ := by
  decide +kernel

theorem context_13_308327_613965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308327 ⟨613965, by decide⟩ :=
  accepted_of_selected 13 308327 ⟨613965, by decide⟩ ⟨13, 2, 0, 613965, 308327, 997, 16384⟩
    (by decide) selected_cut_24272

theorem unmarked_context_12_77081_613966 : frontier 9 ⟨613966, by decide⟩
    (prefixCache 12 77081) (prefixPartial 12 77081) = false := by
  decide +kernel

theorem node_context_12_77081_613966 : EJMOriginalGlobalDAGData.nodes 9 ⟨613966, by decide⟩ =
    .split (coordinate 12) (![⟨613890, by decide⟩,⟨613927, by decide⟩,⟨613951, by decide⟩,⟨613965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77081_613966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77081 ⟨613966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77081
    ⟨613966, by decide⟩ (by decide) (![⟨613890, by decide⟩,⟨613927, by decide⟩,⟨613951, by decide⟩,⟨613965, by decide⟩]) unmarked_context_12_77081_613966 node_context_12_77081_613966
  intro a
  fin_cases a
  · exact context_13_308324_613890
  · exact context_13_308325_613927
  · exact context_13_308326_613951
  · exact context_13_308327_613965

theorem selected_cut_24273 : selected 8 ⟨613994, by decide⟩
    (prefixPartial 13 308328) = some ⟨13, 2, 0, 613994, 308328, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_308328_613994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308328 ⟨613994, by decide⟩ :=
  accepted_of_selected 13 308328 ⟨613994, by decide⟩ ⟨13, 2, 0, 613994, 308328, 1545, 16384⟩
    (by decide) selected_cut_24273

theorem selected_cut_24274 : selected 8 ⟨614026, by decide⟩
    (prefixPartial 13 308329) = some ⟨13, 2, 0, 614026, 308329, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_308329_614026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308329 ⟨614026, by decide⟩ :=
  accepted_of_selected 13 308329 ⟨614026, by decide⟩ ⟨13, 2, 0, 614026, 308329, 2241, 16384⟩
    (by decide) selected_cut_24274

theorem selected_cut_24275 : selected 8 ⟨614050, by decide⟩
    (prefixPartial 13 308330) = some ⟨13, 2, 0, 614050, 308330, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_308330_614050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308330 ⟨614050, by decide⟩ :=
  accepted_of_selected 13 308330 ⟨614050, by decide⟩ ⟨13, 2, 0, 614050, 308330, 1617, 16384⟩
    (by decide) selected_cut_24275

theorem selected_cut_24276 : selected 8 ⟨614068, by decide⟩
    (prefixPartial 13 308331) = some ⟨13, 2, 0, 614068, 308331, 993, 16384⟩ := by
  decide +kernel

theorem context_13_308331_614068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308331 ⟨614068, by decide⟩ :=
  accepted_of_selected 13 308331 ⟨614068, by decide⟩ ⟨13, 2, 0, 614068, 308331, 993, 16384⟩
    (by decide) selected_cut_24276

theorem unmarked_context_12_77082_614069 : frontier 9 ⟨614069, by decide⟩
    (prefixCache 12 77082) (prefixPartial 12 77082) = false := by
  decide +kernel

theorem node_context_12_77082_614069 : EJMOriginalGlobalDAGData.nodes 9 ⟨614069, by decide⟩ =
    .split (coordinate 12) (![⟨613994, by decide⟩,⟨614026, by decide⟩,⟨614050, by decide⟩,⟨614068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77082_614069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77082 ⟨614069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77082
    ⟨614069, by decide⟩ (by decide) (![⟨613994, by decide⟩,⟨614026, by decide⟩,⟨614050, by decide⟩,⟨614068, by decide⟩]) unmarked_context_12_77082_614069 node_context_12_77082_614069
  intro a
  fin_cases a
  · exact context_13_308328_613994
  · exact context_13_308329_614026
  · exact context_13_308330_614050
  · exact context_13_308331_614068

theorem selected_cut_24277 : selected 8 ⟨614106, by decide⟩
    (prefixPartial 13 308332) = some ⟨13, 2, 0, 614106, 308332, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_308332_614106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308332 ⟨614106, by decide⟩ :=
  accepted_of_selected 13 308332 ⟨614106, by decide⟩ ⟨13, 2, 0, 614106, 308332, 1661, 16384⟩
    (by decide) selected_cut_24277

theorem selected_cut_24278 : selected 8 ⟨614141, by decide⟩
    (prefixPartial 13 308333) = some ⟨13, 2, 0, 614141, 308333, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_308333_614141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308333 ⟨614141, by decide⟩ :=
  accepted_of_selected 13 308333 ⟨614141, by decide⟩ ⟨13, 2, 0, 614141, 308333, 2525, 16384⟩
    (by decide) selected_cut_24278

theorem selected_cut_24279 : selected 8 ⟨614171, by decide⟩
    (prefixPartial 13 308334) = some ⟨13, 2, 0, 614171, 308334, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_308334_614171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308334 ⟨614171, by decide⟩ :=
  accepted_of_selected 13 308334 ⟨614171, by decide⟩ ⟨13, 2, 0, 614171, 308334, 2017, 16384⟩
    (by decide) selected_cut_24279

theorem selected_cut_24280 : selected 8 ⟨614184, by decide⟩
    (prefixPartial 13 308335) = some ⟨13, 2, 0, 614184, 308335, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_308335_614184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308335 ⟨614184, by decide⟩ :=
  accepted_of_selected 13 308335 ⟨614184, by decide⟩ ⟨13, 2, 0, 614184, 308335, 1025, 16384⟩
    (by decide) selected_cut_24280

theorem unmarked_context_12_77083_614185 : frontier 9 ⟨614185, by decide⟩
    (prefixCache 12 77083) (prefixPartial 12 77083) = false := by
  decide +kernel

theorem node_context_12_77083_614185 : EJMOriginalGlobalDAGData.nodes 9 ⟨614185, by decide⟩ =
    .split (coordinate 12) (![⟨614106, by decide⟩,⟨614141, by decide⟩,⟨614171, by decide⟩,⟨614184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77083_614185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77083 ⟨614185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77083
    ⟨614185, by decide⟩ (by decide) (![⟨614106, by decide⟩,⟨614141, by decide⟩,⟨614171, by decide⟩,⟨614184, by decide⟩]) unmarked_context_12_77083_614185 node_context_12_77083_614185
  intro a
  fin_cases a
  · exact context_13_308332_614106
  · exact context_13_308333_614141
  · exact context_13_308334_614171
  · exact context_13_308335_614184

theorem unmarked_context_11_19270_614186 : frontier 10 ⟨614186, by decide⟩
    (prefixCache 11 19270) (prefixPartial 11 19270) = false := by
  decide +kernel

theorem node_context_11_19270_614186 : EJMOriginalGlobalDAGData.nodes 10 ⟨614186, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨613966, by decide⟩,⟨614069, by decide⟩,⟨614185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19270_614186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19270 ⟨614186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19270
    ⟨614186, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨613966, by decide⟩,⟨614069, by decide⟩,⟨614185, by decide⟩]) unmarked_context_11_19270_614186 node_context_11_19270_614186
  intro a
  fin_cases a
  · exact context_12_77080_449505
  · exact context_12_77081_613966
  · exact context_12_77082_614069
  · exact context_12_77083_614185

theorem selected_cut_24281 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 77084) = some ⟨12, 1, 0, 539296, 77084, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77084_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77084 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 77084 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 77084, 1, 65536⟩
    (by decide) selected_cut_24281

theorem selected_cut_24282 : selected 8 ⟨614213, by decide⟩
    (prefixPartial 13 308340) = some ⟨13, 2, 0, 614213, 308340, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_308340_614213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308340 ⟨614213, by decide⟩ :=
  accepted_of_selected 13 308340 ⟨614213, by decide⟩ ⟨13, 2, 0, 614213, 308340, 1285, 16384⟩
    (by decide) selected_cut_24282

theorem selected_cut_24283 : selected 8 ⟨614245, by decide⟩
    (prefixPartial 13 308341) = some ⟨13, 2, 0, 614245, 308341, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_308341_614245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308341 ⟨614245, by decide⟩ :=
  accepted_of_selected 13 308341 ⟨614245, by decide⟩ ⟨13, 2, 0, 614245, 308341, 2089, 16384⟩
    (by decide) selected_cut_24283

theorem selected_cut_24284 : selected 8 ⟨614264, by decide⟩
    (prefixPartial 13 308342) = some ⟨13, 2, 0, 614264, 308342, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_308342_614264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308342 ⟨614264, by decide⟩ :=
  accepted_of_selected 13 308342 ⟨614264, by decide⟩ ⟨13, 2, 0, 614264, 308342, 1657, 16384⟩
    (by decide) selected_cut_24284

theorem selected_cut_24285 : selected 8 ⟨614273, by decide⟩
    (prefixPartial 13 308343) = some ⟨13, 2, 0, 614273, 308343, 849, 16384⟩ := by
  decide +kernel

theorem context_13_308343_614273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308343 ⟨614273, by decide⟩ :=
  accepted_of_selected 13 308343 ⟨614273, by decide⟩ ⟨13, 2, 0, 614273, 308343, 849, 16384⟩
    (by decide) selected_cut_24285

theorem unmarked_context_12_77085_614274 : frontier 9 ⟨614274, by decide⟩
    (prefixCache 12 77085) (prefixPartial 12 77085) = false := by
  decide +kernel

theorem node_context_12_77085_614274 : EJMOriginalGlobalDAGData.nodes 9 ⟨614274, by decide⟩ =
    .split (coordinate 12) (![⟨614213, by decide⟩,⟨614245, by decide⟩,⟨614264, by decide⟩,⟨614273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77085_614274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77085 ⟨614274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77085
    ⟨614274, by decide⟩ (by decide) (![⟨614213, by decide⟩,⟨614245, by decide⟩,⟨614264, by decide⟩,⟨614273, by decide⟩]) unmarked_context_12_77085_614274 node_context_12_77085_614274
  intro a
  fin_cases a
  · exact context_13_308340_614213
  · exact context_13_308341_614245
  · exact context_13_308342_614264
  · exact context_13_308343_614273

theorem selected_cut_24286 : selected 8 ⟨614297, by decide⟩
    (prefixPartial 13 308344) = some ⟨13, 2, 0, 614297, 308344, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_308344_614297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308344 ⟨614297, by decide⟩ :=
  accepted_of_selected 13 308344 ⟨614297, by decide⟩ ⟨13, 2, 0, 614297, 308344, 1345, 16384⟩
    (by decide) selected_cut_24286

theorem selected_cut_24287 : selected 8 ⟨614326, by decide⟩
    (prefixPartial 13 308345) = some ⟨13, 2, 0, 614326, 308345, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_308345_614326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308345 ⟨614326, by decide⟩ :=
  accepted_of_selected 13 308345 ⟨614326, by decide⟩ ⟨13, 2, 0, 614326, 308345, 2309, 16384⟩
    (by decide) selected_cut_24287

theorem selected_cut_24288 : selected 8 ⟨614346, by decide⟩
    (prefixPartial 13 308346) = some ⟨13, 2, 0, 614346, 308346, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_308346_614346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308346 ⟨614346, by decide⟩ :=
  accepted_of_selected 13 308346 ⟨614346, by decide⟩ ⟨13, 2, 0, 614346, 308346, 1433, 16384⟩
    (by decide) selected_cut_24288

theorem selected_cut_24289 : selected 8 ⟨614354, by decide⟩
    (prefixPartial 13 308347) = some ⟨13, 2, 0, 614354, 308347, 889, 16384⟩ := by
  decide +kernel

theorem context_13_308347_614354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308347 ⟨614354, by decide⟩ :=
  accepted_of_selected 13 308347 ⟨614354, by decide⟩ ⟨13, 2, 0, 614354, 308347, 889, 16384⟩
    (by decide) selected_cut_24289

theorem unmarked_context_12_77086_614355 : frontier 9 ⟨614355, by decide⟩
    (prefixCache 12 77086) (prefixPartial 12 77086) = false := by
  decide +kernel

theorem node_context_12_77086_614355 : EJMOriginalGlobalDAGData.nodes 9 ⟨614355, by decide⟩ =
    .split (coordinate 12) (![⟨614297, by decide⟩,⟨614326, by decide⟩,⟨614346, by decide⟩,⟨614354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77086_614355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77086 ⟨614355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77086
    ⟨614355, by decide⟩ (by decide) (![⟨614297, by decide⟩,⟨614326, by decide⟩,⟨614346, by decide⟩,⟨614354, by decide⟩]) unmarked_context_12_77086_614355 node_context_12_77086_614355
  intro a
  fin_cases a
  · exact context_13_308344_614297
  · exact context_13_308345_614326
  · exact context_13_308346_614346
  · exact context_13_308347_614354

theorem selected_cut_24290 : selected 8 ⟨614377, by decide⟩
    (prefixPartial 13 308348) = some ⟨13, 2, 0, 614377, 308348, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_308348_614377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308348 ⟨614377, by decide⟩ :=
  accepted_of_selected 13 308348 ⟨614377, by decide⟩ ⟨13, 2, 0, 614377, 308348, 1317, 16384⟩
    (by decide) selected_cut_24290

theorem selected_cut_24291 : selected 8 ⟨614405, by decide⟩
    (prefixPartial 13 308349) = some ⟨13, 2, 0, 614405, 308349, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_308349_614405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308349 ⟨614405, by decide⟩ :=
  accepted_of_selected 13 308349 ⟨614405, by decide⟩ ⟨13, 2, 0, 614405, 308349, 2441, 16384⟩
    (by decide) selected_cut_24291

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
