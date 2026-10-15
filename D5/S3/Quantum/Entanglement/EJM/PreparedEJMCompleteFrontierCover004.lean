/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover003
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00387 : selected 8 ⟨18948, by decide⟩
    (prefixPartial 13 5307) = some ⟨13, 2, 0, 18948, 5307, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_5307_18948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5307 ⟨18948, by decide⟩ :=
  accepted_of_selected 13 5307 ⟨18948, by decide⟩ ⟨13, 2, 0, 18948, 5307, 1045, 16384⟩
    (by decide) selected_cut_00387

theorem unmarked_context_12_1326_18949 : frontier 9 ⟨18949, by decide⟩
    (prefixCache 12 1326) (prefixPartial 12 1326) = false := by
  decide +kernel

theorem node_context_12_1326_18949 : EJMOriginalGlobalDAGData.nodes 9 ⟨18949, by decide⟩ =
    .split (coordinate 12) (![⟨18801, by decide⟩,⟨18872, by decide⟩,⟨18915, by decide⟩,⟨18948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1326_18949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1326 ⟨18949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1326
    ⟨18949, by decide⟩ (by decide) (![⟨18801, by decide⟩,⟨18872, by decide⟩,⟨18915, by decide⟩,⟨18948, by decide⟩]) unmarked_context_12_1326_18949 node_context_12_1326_18949
  intro a
  fin_cases a
  · exact context_13_5304_18801
  · exact context_13_5305_18872
  · exact context_13_5306_18915
  · exact context_13_5307_18948

theorem selected_cut_00388 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 1327) = some ⟨12, 1, 0, 4596, 1327, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1327_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1327 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 1327 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 1327, 1, 65536⟩
    (by decide) selected_cut_00388

theorem unmarked_context_11_331_18950 : frontier 10 ⟨18950, by decide⟩
    (prefixCache 11 331) (prefixPartial 11 331) = false := by
  decide +kernel

theorem node_context_11_331_18950 : EJMOriginalGlobalDAGData.nodes 10 ⟨18950, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18949, by decide⟩,⟨4596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_331_18950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 331 ⟨18950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 331
    ⟨18950, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨18949, by decide⟩,⟨4596, by decide⟩]) unmarked_context_11_331_18950 node_context_11_331_18950
  intro a
  fin_cases a
  · exact context_12_1324_1738
  · exact context_12_1325_1738
  · exact context_12_1326_18949
  · exact context_12_1327_4596

theorem unmarked_context_10_82_18951 : frontier 11 ⟨18951, by decide⟩
    (prefixCache 10 82) (prefixPartial 10 82) = false := by
  decide +kernel

theorem node_context_10_82_18951 : EJMOriginalGlobalDAGData.nodes 11 ⟨18951, by decide⟩ =
    .split (coordinate 10) (![⟨18231, by decide⟩,⟨18522, by decide⟩,⟨18788, by decide⟩,⟨18950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_82_18951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 82 ⟨18951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 82
    ⟨18951, by decide⟩ (by decide) (![⟨18231, by decide⟩,⟨18522, by decide⟩,⟨18788, by decide⟩,⟨18950, by decide⟩]) unmarked_context_10_82_18951 node_context_10_82_18951
  intro a
  fin_cases a
  · exact context_11_328_18231
  · exact context_11_329_18522
  · exact context_11_330_18788
  · exact context_11_331_18950

theorem selected_cut_00389 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 83) = some ⟨10, 1, 0, 3440, 83, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_83_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 83 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 83 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 83, 1, 1048576⟩
    (by decide) selected_cut_00389

theorem unmarked_context_9_20_18952 : frontier 12 ⟨18952, by decide⟩
    (prefixCache 9 20) (prefixPartial 9 20) = false := by
  decide +kernel

theorem node_context_9_20_18952 : EJMOriginalGlobalDAGData.nodes 12 ⟨18952, by decide⟩ =
    .split (coordinate 9) (![⟨16782, by decide⟩,⟨17939, by decide⟩,⟨18951, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_20_18952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 20 ⟨18952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 20
    ⟨18952, by decide⟩ (by decide) (![⟨16782, by decide⟩,⟨17939, by decide⟩,⟨18951, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_20_18952 node_context_9_20_18952
  intro a
  fin_cases a
  · exact context_10_80_16782
  · exact context_10_81_17939
  · exact context_10_82_18951
  · exact context_10_83_3440

theorem selected_cut_00390 : selected 9 ⟨19027, by decide⟩
    (prefixPartial 12 1344) = some ⟨12, 2, 0, 19027, 1344, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_1344_19027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1344 ⟨19027, by decide⟩ :=
  accepted_of_selected 12 1344 ⟨19027, by decide⟩ ⟨12, 2, 0, 19027, 1344, 1897, 65536⟩
    (by decide) selected_cut_00390

theorem selected_cut_00391 : selected 9 ⟨19085, by decide⟩
    (prefixPartial 12 1345) = some ⟨12, 2, 0, 19085, 1345, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_1345_19085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1345 ⟨19085, by decide⟩ :=
  accepted_of_selected 12 1345 ⟨19085, by decide⟩ ⟨12, 2, 0, 19085, 1345, 2233, 65536⟩
    (by decide) selected_cut_00391

theorem selected_cut_00392 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5384) = some ⟨13, 1, 0, 3444, 5384, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5384_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5384 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5384 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5384, 1, 16384⟩
    (by decide) selected_cut_00392

theorem selected_cut_00393 : selected 8 ⟨19127, by decide⟩
    (prefixPartial 13 5385) = some ⟨13, 2, 0, 19127, 5385, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_5385_19127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5385 ⟨19127, by decide⟩ :=
  accepted_of_selected 13 5385 ⟨19127, by decide⟩ ⟨13, 2, 0, 19127, 5385, 1393, 16384⟩
    (by decide) selected_cut_00393

theorem selected_cut_00394 : selected 8 ⟨19158, by decide⟩
    (prefixPartial 13 5386) = some ⟨13, 2, 0, 19158, 5386, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_5386_19158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5386 ⟨19158, by decide⟩ :=
  accepted_of_selected 13 5386 ⟨19158, by decide⟩ ⟨13, 2, 0, 19158, 5386, 2241, 16384⟩
    (by decide) selected_cut_00394

theorem selected_cut_00395 : selected 8 ⟨19176, by decide⟩
    (prefixPartial 13 5387) = some ⟨13, 2, 0, 19176, 5387, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_5387_19176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5387 ⟨19176, by decide⟩ :=
  accepted_of_selected 13 5387 ⟨19176, by decide⟩ ⟨13, 2, 0, 19176, 5387, 1061, 16384⟩
    (by decide) selected_cut_00395

theorem unmarked_context_12_1346_19177 : frontier 9 ⟨19177, by decide⟩
    (prefixCache 12 1346) (prefixPartial 12 1346) = false := by
  decide +kernel

theorem node_context_12_1346_19177 : EJMOriginalGlobalDAGData.nodes 9 ⟨19177, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨19127, by decide⟩,⟨19158, by decide⟩,⟨19176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1346_19177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1346 ⟨19177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1346
    ⟨19177, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨19127, by decide⟩,⟨19158, by decide⟩,⟨19176, by decide⟩]) unmarked_context_12_1346_19177 node_context_12_1346_19177
  intro a
  fin_cases a
  · exact context_13_5384_3444
  · exact context_13_5385_19127
  · exact context_13_5386_19158
  · exact context_13_5387_19176

theorem selected_cut_00396 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1347) = some ⟨12, 1, 0, 893, 1347, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1347_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1347 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1347 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1347, 1, 65536⟩
    (by decide) selected_cut_00396

theorem unmarked_context_11_336_19178 : frontier 10 ⟨19178, by decide⟩
    (prefixCache 11 336) (prefixPartial 11 336) = false := by
  decide +kernel

theorem node_context_11_336_19178 : EJMOriginalGlobalDAGData.nodes 10 ⟨19178, by decide⟩ =
    .split (coordinate 11) (![⟨19027, by decide⟩,⟨19085, by decide⟩,⟨19177, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_336_19178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 336 ⟨19178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 336
    ⟨19178, by decide⟩ (by decide) (![⟨19027, by decide⟩,⟨19085, by decide⟩,⟨19177, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_336_19178 node_context_11_336_19178
  intro a
  fin_cases a
  · exact context_12_1344_19027
  · exact context_12_1345_19085
  · exact context_12_1346_19177
  · exact context_12_1347_893

theorem selected_cut_00397 : selected 9 ⟨19222, by decide⟩
    (prefixPartial 12 1348) = some ⟨12, 2, 0, 19222, 1348, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_1348_19222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1348 ⟨19222, by decide⟩ :=
  accepted_of_selected 12 1348 ⟨19222, by decide⟩ ⟨12, 2, 0, 19222, 1348, 1369, 65536⟩
    (by decide) selected_cut_00397

theorem selected_cut_00398 : selected 9 ⟨19296, by decide⟩
    (prefixPartial 12 1349) = some ⟨12, 2, 0, 19296, 1349, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_1349_19296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1349 ⟨19296, by decide⟩ :=
  accepted_of_selected 12 1349 ⟨19296, by decide⟩ ⟨12, 2, 0, 19296, 1349, 3057, 65536⟩
    (by decide) selected_cut_00398

theorem selected_cut_00399 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5400) = some ⟨13, 1, 0, 3444, 5400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5400, 1, 16384⟩
    (by decide) selected_cut_00399

theorem selected_cut_00400 : selected 8 ⟨19323, by decide⟩
    (prefixPartial 13 5401) = some ⟨13, 2, 0, 19323, 5401, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_5401_19323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5401 ⟨19323, by decide⟩ :=
  accepted_of_selected 13 5401 ⟨19323, by decide⟩ ⟨13, 2, 0, 19323, 5401, 1161, 16384⟩
    (by decide) selected_cut_00400

theorem selected_cut_00401 : selected 8 ⟨19368, by decide⟩
    (prefixPartial 13 5402) = some ⟨13, 2, 0, 19368, 5402, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_5402_19368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5402 ⟨19368, by decide⟩ :=
  accepted_of_selected 13 5402 ⟨19368, by decide⟩ ⟨13, 2, 0, 19368, 5402, 2049, 16384⟩
    (by decide) selected_cut_00401

theorem selected_cut_00402 : selected 8 ⟨19384, by decide⟩
    (prefixPartial 13 5403) = some ⟨13, 2, 0, 19384, 5403, 981, 16384⟩ := by
  decide +kernel

theorem context_13_5403_19384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5403 ⟨19384, by decide⟩ :=
  accepted_of_selected 13 5403 ⟨19384, by decide⟩ ⟨13, 2, 0, 19384, 5403, 981, 16384⟩
    (by decide) selected_cut_00402

theorem unmarked_context_12_1350_19385 : frontier 9 ⟨19385, by decide⟩
    (prefixCache 12 1350) (prefixPartial 12 1350) = false := by
  decide +kernel

theorem node_context_12_1350_19385 : EJMOriginalGlobalDAGData.nodes 9 ⟨19385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨19323, by decide⟩,⟨19368, by decide⟩,⟨19384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1350_19385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1350 ⟨19385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1350
    ⟨19385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨19323, by decide⟩,⟨19368, by decide⟩,⟨19384, by decide⟩]) unmarked_context_12_1350_19385 node_context_12_1350_19385
  intro a
  fin_cases a
  · exact context_13_5400_3444
  · exact context_13_5401_19323
  · exact context_13_5402_19368
  · exact context_13_5403_19384

theorem selected_cut_00403 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1351) = some ⟨12, 1, 0, 893, 1351, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1351_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1351 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1351 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1351, 1, 65536⟩
    (by decide) selected_cut_00403

theorem unmarked_context_11_337_19386 : frontier 10 ⟨19386, by decide⟩
    (prefixCache 11 337) (prefixPartial 11 337) = false := by
  decide +kernel

theorem node_context_11_337_19386 : EJMOriginalGlobalDAGData.nodes 10 ⟨19386, by decide⟩ =
    .split (coordinate 11) (![⟨19222, by decide⟩,⟨19296, by decide⟩,⟨19385, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_337_19386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 337 ⟨19386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 337
    ⟨19386, by decide⟩ (by decide) (![⟨19222, by decide⟩,⟨19296, by decide⟩,⟨19385, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_337_19386 node_context_11_337_19386
  intro a
  fin_cases a
  · exact context_12_1348_19222
  · exact context_12_1349_19296
  · exact context_12_1350_19385
  · exact context_12_1351_893

theorem selected_cut_00404 : selected 9 ⟨19466, by decide⟩
    (prefixPartial 12 1352) = some ⟨12, 2, 0, 19466, 1352, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_1352_19466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1352 ⟨19466, by decide⟩ :=
  accepted_of_selected 12 1352 ⟨19466, by decide⟩ ⟨12, 2, 0, 19466, 1352, 3341, 65536⟩
    (by decide) selected_cut_00404

theorem selected_cut_00405 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5412) = some ⟨13, 1, 0, 3444, 5412, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5412_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5412 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5412 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5412, 1, 16384⟩
    (by decide) selected_cut_00405

theorem selected_cut_00406 : selected 8 ⟨19509, by decide⟩
    (prefixPartial 13 5413) = some ⟨13, 2, 0, 19509, 5413, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_5413_19509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5413 ⟨19509, by decide⟩ :=
  accepted_of_selected 13 5413 ⟨19509, by decide⟩ ⟨13, 2, 0, 19509, 5413, 1469, 16384⟩
    (by decide) selected_cut_00406

theorem selected_cut_00407 : selected 8 ⟨19538, by decide⟩
    (prefixPartial 13 5414) = some ⟨13, 2, 0, 19538, 5414, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_5414_19538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5414 ⟨19538, by decide⟩ :=
  accepted_of_selected 13 5414 ⟨19538, by decide⟩ ⟨13, 2, 0, 19538, 5414, 2185, 16384⟩
    (by decide) selected_cut_00407

theorem selected_cut_00408 : selected 8 ⟨19558, by decide⟩
    (prefixPartial 13 5415) = some ⟨13, 2, 0, 19558, 5415, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_5415_19558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5415 ⟨19558, by decide⟩ :=
  accepted_of_selected 13 5415 ⟨19558, by decide⟩ ⟨13, 2, 0, 19558, 5415, 1065, 16384⟩
    (by decide) selected_cut_00408

theorem unmarked_context_12_1353_19559 : frontier 9 ⟨19559, by decide⟩
    (prefixCache 12 1353) (prefixPartial 12 1353) = false := by
  decide +kernel

theorem node_context_12_1353_19559 : EJMOriginalGlobalDAGData.nodes 9 ⟨19559, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨19509, by decide⟩,⟨19538, by decide⟩,⟨19558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1353_19559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1353 ⟨19559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1353
    ⟨19559, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨19509, by decide⟩,⟨19538, by decide⟩,⟨19558, by decide⟩]) unmarked_context_12_1353_19559 node_context_12_1353_19559
  intro a
  fin_cases a
  · exact context_13_5412_3444
  · exact context_13_5413_19509
  · exact context_13_5414_19538
  · exact context_13_5415_19558

theorem selected_cut_00409 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5416) = some ⟨13, 1, 0, 3444, 5416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5416, 1, 16384⟩
    (by decide) selected_cut_00409

theorem selected_cut_00410 : selected 8 ⟨19591, by decide⟩
    (prefixPartial 13 5417) = some ⟨13, 2, 0, 19591, 5417, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_5417_19591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5417 ⟨19591, by decide⟩ :=
  accepted_of_selected 13 5417 ⟨19591, by decide⟩ ⟨13, 2, 0, 19591, 5417, 1373, 16384⟩
    (by decide) selected_cut_00410

theorem selected_cut_00411 : selected 8 ⟨19628, by decide⟩
    (prefixPartial 13 5418) = some ⟨13, 2, 0, 19628, 5418, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_5418_19628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5418 ⟨19628, by decide⟩ :=
  accepted_of_selected 13 5418 ⟨19628, by decide⟩ ⟨13, 2, 0, 19628, 5418, 2309, 16384⟩
    (by decide) selected_cut_00411

theorem selected_cut_00412 : selected 8 ⟨19645, by decide⟩
    (prefixPartial 13 5419) = some ⟨13, 2, 0, 19645, 5419, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_5419_19645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5419 ⟨19645, by decide⟩ :=
  accepted_of_selected 13 5419 ⟨19645, by decide⟩ ⟨13, 2, 0, 19645, 5419, 1093, 16384⟩
    (by decide) selected_cut_00412

theorem unmarked_context_12_1354_19646 : frontier 9 ⟨19646, by decide⟩
    (prefixCache 12 1354) (prefixPartial 12 1354) = false := by
  decide +kernel

theorem node_context_12_1354_19646 : EJMOriginalGlobalDAGData.nodes 9 ⟨19646, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨19591, by decide⟩,⟨19628, by decide⟩,⟨19645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1354_19646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1354 ⟨19646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1354
    ⟨19646, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨19591, by decide⟩,⟨19628, by decide⟩,⟨19645, by decide⟩]) unmarked_context_12_1354_19646 node_context_12_1354_19646
  intro a
  fin_cases a
  · exact context_13_5416_3444
  · exact context_13_5417_19591
  · exact context_13_5418_19628
  · exact context_13_5419_19645

theorem selected_cut_00413 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5420) = some ⟨13, 1, 0, 3444, 5420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5420, 1, 16384⟩
    (by decide) selected_cut_00413

theorem selected_cut_00414 : selected 8 ⟨19685, by decide⟩
    (prefixPartial 13 5421) = some ⟨13, 2, 0, 19685, 5421, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_5421_19685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5421 ⟨19685, by decide⟩ :=
  accepted_of_selected 13 5421 ⟨19685, by decide⟩ ⟨13, 2, 0, 19685, 5421, 1461, 16384⟩
    (by decide) selected_cut_00414

theorem selected_cut_00415 : selected 8 ⟨19727, by decide⟩
    (prefixPartial 13 5422) = some ⟨13, 2, 0, 19727, 5422, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_5422_19727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5422 ⟨19727, by decide⟩ :=
  accepted_of_selected 13 5422 ⟨19727, by decide⟩ ⟨13, 2, 0, 19727, 5422, 2521, 16384⟩
    (by decide) selected_cut_00415

theorem selected_cut_00416 : selected 8 ⟨19743, by decide⟩
    (prefixPartial 13 5423) = some ⟨13, 2, 0, 19743, 5423, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_5423_19743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5423 ⟨19743, by decide⟩ :=
  accepted_of_selected 13 5423 ⟨19743, by decide⟩ ⟨13, 2, 0, 19743, 5423, 1245, 16384⟩
    (by decide) selected_cut_00416

theorem unmarked_context_12_1355_19744 : frontier 9 ⟨19744, by decide⟩
    (prefixCache 12 1355) (prefixPartial 12 1355) = false := by
  decide +kernel

theorem node_context_12_1355_19744 : EJMOriginalGlobalDAGData.nodes 9 ⟨19744, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨19685, by decide⟩,⟨19727, by decide⟩,⟨19743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1355_19744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1355 ⟨19744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1355
    ⟨19744, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨19685, by decide⟩,⟨19727, by decide⟩,⟨19743, by decide⟩]) unmarked_context_12_1355_19744 node_context_12_1355_19744
  intro a
  fin_cases a
  · exact context_13_5420_3444
  · exact context_13_5421_19685
  · exact context_13_5422_19727
  · exact context_13_5423_19743

theorem unmarked_context_11_338_19745 : frontier 10 ⟨19745, by decide⟩
    (prefixCache 11 338) (prefixPartial 11 338) = false := by
  decide +kernel

theorem node_context_11_338_19745 : EJMOriginalGlobalDAGData.nodes 10 ⟨19745, by decide⟩ =
    .split (coordinate 11) (![⟨19466, by decide⟩,⟨19559, by decide⟩,⟨19646, by decide⟩,⟨19744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_338_19745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 338 ⟨19745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 338
    ⟨19745, by decide⟩ (by decide) (![⟨19466, by decide⟩,⟨19559, by decide⟩,⟨19646, by decide⟩,⟨19744, by decide⟩]) unmarked_context_11_338_19745 node_context_11_338_19745
  intro a
  fin_cases a
  · exact context_12_1352_19466
  · exact context_12_1353_19559
  · exact context_12_1354_19646
  · exact context_12_1355_19744

theorem selected_cut_00417 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 339) = some ⟨11, 1, 0, 1736, 339, 1, 262144⟩ := by
  decide +kernel

theorem context_11_339_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 339 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 339 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 339, 1, 262144⟩
    (by decide) selected_cut_00417

theorem unmarked_context_10_84_19746 : frontier 11 ⟨19746, by decide⟩
    (prefixCache 10 84) (prefixPartial 10 84) = false := by
  decide +kernel

theorem node_context_10_84_19746 : EJMOriginalGlobalDAGData.nodes 11 ⟨19746, by decide⟩ =
    .split (coordinate 10) (![⟨19178, by decide⟩,⟨19386, by decide⟩,⟨19745, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_84_19746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 84 ⟨19746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 84
    ⟨19746, by decide⟩ (by decide) (![⟨19178, by decide⟩,⟨19386, by decide⟩,⟨19745, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_84_19746 node_context_10_84_19746
  intro a
  fin_cases a
  · exact context_11_336_19178
  · exact context_11_337_19386
  · exact context_11_338_19745
  · exact context_11_339_1736

theorem selected_cut_00418 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1360) = some ⟨12, 1, 0, 1738, 1360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1360_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1360 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1360 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1360, 1, 65536⟩
    (by decide) selected_cut_00418

theorem selected_cut_00419 : selected 9 ⟨19788, by decide⟩
    (prefixPartial 12 1361) = some ⟨12, 2, 0, 19788, 1361, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_1361_19788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1361 ⟨19788, by decide⟩ :=
  accepted_of_selected 12 1361 ⟨19788, by decide⟩ ⟨12, 2, 0, 19788, 1361, 1297, 65536⟩
    (by decide) selected_cut_00419

theorem selected_cut_00420 : selected 9 ⟨19856, by decide⟩
    (prefixPartial 12 1362) = some ⟨12, 2, 0, 19856, 1362, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_1362_19856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1362 ⟨19856, by decide⟩ :=
  accepted_of_selected 12 1362 ⟨19856, by decide⟩ ⟨12, 2, 0, 19856, 1362, 3617, 65536⟩
    (by decide) selected_cut_00420

theorem selected_cut_00421 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1363) = some ⟨12, 1, 0, 893, 1363, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1363_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1363 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1363 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1363, 1, 65536⟩
    (by decide) selected_cut_00421

theorem unmarked_context_11_340_19857 : frontier 10 ⟨19857, by decide⟩
    (prefixCache 11 340) (prefixPartial 11 340) = false := by
  decide +kernel

theorem node_context_11_340_19857 : EJMOriginalGlobalDAGData.nodes 10 ⟨19857, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨19788, by decide⟩,⟨19856, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_340_19857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 340 ⟨19857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 340
    ⟨19857, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨19788, by decide⟩,⟨19856, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_340_19857 node_context_11_340_19857
  intro a
  fin_cases a
  · exact context_12_1360_1738
  · exact context_12_1361_19788
  · exact context_12_1362_19856
  · exact context_12_1363_893

theorem selected_cut_00422 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1364) = some ⟨12, 1, 0, 1738, 1364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1364_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1364 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1364 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1364, 1, 65536⟩
    (by decide) selected_cut_00422

theorem selected_cut_00423 : selected 9 ⟨19994, by decide⟩
    (prefixPartial 12 1365) = some ⟨12, 2, 0, 19994, 1365, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_1365_19994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1365 ⟨19994, by decide⟩ :=
  accepted_of_selected 12 1365 ⟨19994, by decide⟩ ⟨12, 2, 0, 19994, 1365, 1041, 65536⟩
    (by decide) selected_cut_00423

theorem selected_cut_00424 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5464) = some ⟨13, 1, 0, 3444, 5464, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5464_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5464 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5464 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5464, 1, 16384⟩
    (by decide) selected_cut_00424

theorem selected_cut_00425 : selected 8 ⟨20025, by decide⟩
    (prefixPartial 13 5465) = some ⟨13, 2, 0, 20025, 5465, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_5465_20025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5465 ⟨20025, by decide⟩ :=
  accepted_of_selected 13 5465 ⟨20025, by decide⟩ ⟨13, 2, 0, 20025, 5465, 1449, 16384⟩
    (by decide) selected_cut_00425

theorem selected_cut_00426 : selected 8 ⟨20086, by decide⟩
    (prefixPartial 13 5466) = some ⟨13, 2, 0, 20086, 5466, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_5466_20086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5466 ⟨20086, by decide⟩ :=
  accepted_of_selected 13 5466 ⟨20086, by decide⟩ ⟨13, 2, 0, 20086, 5466, 2993, 16384⟩
    (by decide) selected_cut_00426

theorem selected_cut_00427 : selected 8 ⟨20105, by decide⟩
    (prefixPartial 13 5467) = some ⟨13, 2, 0, 20105, 5467, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_5467_20105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5467 ⟨20105, by decide⟩ :=
  accepted_of_selected 13 5467 ⟨20105, by decide⟩ ⟨13, 2, 0, 20105, 5467, 1373, 16384⟩
    (by decide) selected_cut_00427

theorem unmarked_context_12_1366_20106 : frontier 9 ⟨20106, by decide⟩
    (prefixCache 12 1366) (prefixPartial 12 1366) = false := by
  decide +kernel

theorem node_context_12_1366_20106 : EJMOriginalGlobalDAGData.nodes 9 ⟨20106, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨20025, by decide⟩,⟨20086, by decide⟩,⟨20105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1366_20106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1366 ⟨20106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1366
    ⟨20106, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨20025, by decide⟩,⟨20086, by decide⟩,⟨20105, by decide⟩]) unmarked_context_12_1366_20106 node_context_12_1366_20106
  intro a
  fin_cases a
  · exact context_13_5464_3444
  · exact context_13_5465_20025
  · exact context_13_5466_20086
  · exact context_13_5467_20105

theorem selected_cut_00428 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 1367) = some ⟨12, 1, 0, 893, 1367, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1367_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1367 ⟨893, by decide⟩ :=
  accepted_of_selected 12 1367 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 1367, 1, 65536⟩
    (by decide) selected_cut_00428

theorem unmarked_context_11_341_20107 : frontier 10 ⟨20107, by decide⟩
    (prefixCache 11 341) (prefixPartial 11 341) = false := by
  decide +kernel

theorem node_context_11_341_20107 : EJMOriginalGlobalDAGData.nodes 10 ⟨20107, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨19994, by decide⟩,⟨20106, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_341_20107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 341 ⟨20107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 341
    ⟨20107, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨19994, by decide⟩,⟨20106, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_341_20107 node_context_11_341_20107
  intro a
  fin_cases a
  · exact context_12_1364_1738
  · exact context_12_1365_19994
  · exact context_12_1366_20106
  · exact context_12_1367_893

theorem selected_cut_00429 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1368) = some ⟨12, 1, 0, 1738, 1368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1368_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1368 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1368 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1368, 1, 65536⟩
    (by decide) selected_cut_00429

theorem selected_cut_00430 : selected 9 ⟨20170, by decide⟩
    (prefixPartial 12 1369) = some ⟨12, 2, 0, 20170, 1369, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_1369_20170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1369 ⟨20170, by decide⟩ :=
  accepted_of_selected 12 1369 ⟨20170, by decide⟩ ⟨12, 2, 0, 20170, 1369, 2961, 65536⟩
    (by decide) selected_cut_00430

theorem selected_cut_00431 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5480) = some ⟨13, 1, 0, 3444, 5480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5480, 1, 16384⟩
    (by decide) selected_cut_00431

theorem selected_cut_00432 : selected 8 ⟨20193, by decide⟩
    (prefixPartial 13 5481) = some ⟨13, 2, 0, 20193, 5481, 669, 16384⟩ := by
  decide +kernel

theorem context_13_5481_20193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5481 ⟨20193, by decide⟩ :=
  accepted_of_selected 13 5481 ⟨20193, by decide⟩ ⟨13, 2, 0, 20193, 5481, 669, 16384⟩
    (by decide) selected_cut_00432

theorem selected_cut_00433 : selected 8 ⟨20223, by decide⟩
    (prefixPartial 13 5482) = some ⟨13, 2, 0, 20223, 5482, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_5482_20223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5482 ⟨20223, by decide⟩ :=
  accepted_of_selected 13 5482 ⟨20223, by decide⟩ ⟨13, 2, 0, 20223, 5482, 2485, 16384⟩
    (by decide) selected_cut_00433

theorem selected_cut_00434 : selected 8 ⟨20242, by decide⟩
    (prefixPartial 13 5483) = some ⟨13, 2, 0, 20242, 5483, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_5483_20242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5483 ⟨20242, by decide⟩ :=
  accepted_of_selected 13 5483 ⟨20242, by decide⟩ ⟨13, 2, 0, 20242, 5483, 1173, 16384⟩
    (by decide) selected_cut_00434

theorem unmarked_context_12_1370_20243 : frontier 9 ⟨20243, by decide⟩
    (prefixCache 12 1370) (prefixPartial 12 1370) = false := by
  decide +kernel

theorem node_context_12_1370_20243 : EJMOriginalGlobalDAGData.nodes 9 ⟨20243, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨20193, by decide⟩,⟨20223, by decide⟩,⟨20242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1370_20243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1370 ⟨20243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1370
    ⟨20243, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨20193, by decide⟩,⟨20223, by decide⟩,⟨20242, by decide⟩]) unmarked_context_12_1370_20243 node_context_12_1370_20243
  intro a
  fin_cases a
  · exact context_13_5480_3444
  · exact context_13_5481_20193
  · exact context_13_5482_20223
  · exact context_13_5483_20242

theorem selected_cut_00435 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5484) = some ⟨13, 1, 0, 3444, 5484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5484, 1, 16384⟩
    (by decide) selected_cut_00435

theorem selected_cut_00436 : selected 8 ⟨20264, by decide⟩
    (prefixPartial 13 5485) = some ⟨13, 2, 0, 20264, 5485, 713, 16384⟩ := by
  decide +kernel

theorem context_13_5485_20264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5485 ⟨20264, by decide⟩ :=
  accepted_of_selected 13 5485 ⟨20264, by decide⟩ ⟨13, 2, 0, 20264, 5485, 713, 16384⟩
    (by decide) selected_cut_00436

theorem selected_cut_00437 : selected 8 ⟨20301, by decide⟩
    (prefixPartial 13 5486) = some ⟨13, 2, 0, 20301, 5486, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_5486_20301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5486 ⟨20301, by decide⟩ :=
  accepted_of_selected 13 5486 ⟨20301, by decide⟩ ⟨13, 2, 0, 20301, 5486, 2633, 16384⟩
    (by decide) selected_cut_00437

theorem selected_cut_00438 : selected 8 ⟨20320, by decide⟩
    (prefixPartial 13 5487) = some ⟨13, 2, 0, 20320, 5487, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_5487_20320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5487 ⟨20320, by decide⟩ :=
  accepted_of_selected 13 5487 ⟨20320, by decide⟩ ⟨13, 2, 0, 20320, 5487, 1349, 16384⟩
    (by decide) selected_cut_00438

theorem unmarked_context_12_1371_20321 : frontier 9 ⟨20321, by decide⟩
    (prefixCache 12 1371) (prefixPartial 12 1371) = false := by
  decide +kernel

theorem node_context_12_1371_20321 : EJMOriginalGlobalDAGData.nodes 9 ⟨20321, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨20264, by decide⟩,⟨20301, by decide⟩,⟨20320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1371_20321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1371 ⟨20321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1371
    ⟨20321, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨20264, by decide⟩,⟨20301, by decide⟩,⟨20320, by decide⟩]) unmarked_context_12_1371_20321 node_context_12_1371_20321
  intro a
  fin_cases a
  · exact context_13_5484_3444
  · exact context_13_5485_20264
  · exact context_13_5486_20301
  · exact context_13_5487_20320

theorem unmarked_context_11_342_20322 : frontier 10 ⟨20322, by decide⟩
    (prefixCache 11 342) (prefixPartial 11 342) = false := by
  decide +kernel

theorem node_context_11_342_20322 : EJMOriginalGlobalDAGData.nodes 10 ⟨20322, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨20170, by decide⟩,⟨20243, by decide⟩,⟨20321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_342_20322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 342 ⟨20322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 342
    ⟨20322, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨20170, by decide⟩,⟨20243, by decide⟩,⟨20321, by decide⟩]) unmarked_context_11_342_20322 node_context_11_342_20322
  intro a
  fin_cases a
  · exact context_12_1368_1738
  · exact context_12_1369_20170
  · exact context_12_1370_20243
  · exact context_12_1371_20321

theorem selected_cut_00439 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 343) = some ⟨11, 1, 0, 1736, 343, 1, 262144⟩ := by
  decide +kernel

theorem context_11_343_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 343 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 343 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 343, 1, 262144⟩
    (by decide) selected_cut_00439

theorem unmarked_context_10_85_20323 : frontier 11 ⟨20323, by decide⟩
    (prefixCache 10 85) (prefixPartial 10 85) = false := by
  decide +kernel

theorem node_context_10_85_20323 : EJMOriginalGlobalDAGData.nodes 11 ⟨20323, by decide⟩ =
    .split (coordinate 10) (![⟨19857, by decide⟩,⟨20107, by decide⟩,⟨20322, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_85_20323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 85 ⟨20323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 85
    ⟨20323, by decide⟩ (by decide) (![⟨19857, by decide⟩,⟨20107, by decide⟩,⟨20322, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_85_20323 node_context_10_85_20323
  intro a
  fin_cases a
  · exact context_11_340_19857
  · exact context_11_341_20107
  · exact context_11_342_20322
  · exact context_11_343_1736

theorem selected_cut_00440 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1376) = some ⟨12, 1, 0, 1738, 1376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1376_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1376 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1376 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1376, 1, 65536⟩
    (by decide) selected_cut_00440

theorem selected_cut_00441 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1377) = some ⟨12, 1, 0, 1738, 1377, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1377_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1377 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1377 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1377, 1, 65536⟩
    (by decide) selected_cut_00441

theorem selected_cut_00442 : selected 9 ⟨20405, by decide⟩
    (prefixPartial 12 1378) = some ⟨12, 2, 0, 20405, 1378, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_1378_20405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1378 ⟨20405, by decide⟩ :=
  accepted_of_selected 12 1378 ⟨20405, by decide⟩ ⟨12, 2, 0, 20405, 1378, 2821, 65536⟩
    (by decide) selected_cut_00442

theorem selected_cut_00443 : selected 9 ⟨20476, by decide⟩
    (prefixPartial 12 1379) = some ⟨12, 2, 0, 20476, 1379, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_1379_20476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1379 ⟨20476, by decide⟩ :=
  accepted_of_selected 12 1379 ⟨20476, by decide⟩ ⟨12, 2, 0, 20476, 1379, 2577, 65536⟩
    (by decide) selected_cut_00443

theorem unmarked_context_11_344_20477 : frontier 10 ⟨20477, by decide⟩
    (prefixCache 11 344) (prefixPartial 11 344) = false := by
  decide +kernel

theorem node_context_11_344_20477 : EJMOriginalGlobalDAGData.nodes 10 ⟨20477, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨20405, by decide⟩,⟨20476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_344_20477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 344 ⟨20477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 344
    ⟨20477, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨20405, by decide⟩,⟨20476, by decide⟩]) unmarked_context_11_344_20477 node_context_11_344_20477
  intro a
  fin_cases a
  · exact context_12_1376_1738
  · exact context_12_1377_1738
  · exact context_12_1378_20405
  · exact context_12_1379_20476

theorem selected_cut_00444 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1380) = some ⟨12, 1, 0, 1738, 1380, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1380_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1380 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1380 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1380, 1, 65536⟩
    (by decide) selected_cut_00444

theorem selected_cut_00445 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1381) = some ⟨12, 1, 0, 1738, 1381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1381_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1381 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1381 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1381, 1, 65536⟩
    (by decide) selected_cut_00445

theorem selected_cut_00446 : selected 9 ⟨20555, by decide⟩
    (prefixPartial 12 1382) = some ⟨12, 2, 0, 20555, 1382, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_1382_20555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1382 ⟨20555, by decide⟩ :=
  accepted_of_selected 12 1382 ⟨20555, by decide⟩ ⟨12, 2, 0, 20555, 1382, 2969, 65536⟩
    (by decide) selected_cut_00446

theorem selected_cut_00447 : selected 9 ⟨20630, by decide⟩
    (prefixPartial 12 1383) = some ⟨12, 2, 0, 20630, 1383, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_1383_20630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1383 ⟨20630, by decide⟩ :=
  accepted_of_selected 12 1383 ⟨20630, by decide⟩ ⟨12, 2, 0, 20630, 1383, 2633, 65536⟩
    (by decide) selected_cut_00447

theorem unmarked_context_11_345_20631 : frontier 10 ⟨20631, by decide⟩
    (prefixCache 11 345) (prefixPartial 11 345) = false := by
  decide +kernel

theorem node_context_11_345_20631 : EJMOriginalGlobalDAGData.nodes 10 ⟨20631, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨20555, by decide⟩,⟨20630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_345_20631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 345 ⟨20631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 345
    ⟨20631, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨20555, by decide⟩,⟨20630, by decide⟩]) unmarked_context_11_345_20631 node_context_11_345_20631
  intro a
  fin_cases a
  · exact context_12_1380_1738
  · exact context_12_1381_1738
  · exact context_12_1382_20555
  · exact context_12_1383_20630

theorem selected_cut_00448 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1384) = some ⟨12, 1, 0, 1738, 1384, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1384_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1384 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1384 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1384, 1, 65536⟩
    (by decide) selected_cut_00448

theorem selected_cut_00449 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1385) = some ⟨12, 1, 0, 1738, 1385, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1385_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1385 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1385 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1385, 1, 65536⟩
    (by decide) selected_cut_00449

theorem selected_cut_00450 : selected 9 ⟨20701, by decide⟩
    (prefixPartial 12 1386) = some ⟨12, 2, 0, 20701, 1386, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_1386_20701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1386 ⟨20701, by decide⟩ :=
  accepted_of_selected 12 1386 ⟨20701, by decide⟩ ⟨12, 2, 0, 20701, 1386, 2933, 65536⟩
    (by decide) selected_cut_00450

theorem selected_cut_00451 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 5548) = some ⟨13, 1, 0, 3444, 5548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_5548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 5548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 5548, 1, 16384⟩
    (by decide) selected_cut_00451

theorem selected_cut_00452 : selected 8 ⟨20713, by decide⟩
    (prefixPartial 13 5549) = some ⟨13, 2, 0, 20713, 5549, 249, 16384⟩ := by
  decide +kernel

theorem context_13_5549_20713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5549 ⟨20713, by decide⟩ :=
  accepted_of_selected 13 5549 ⟨20713, by decide⟩ ⟨13, 2, 0, 20713, 5549, 249, 16384⟩
    (by decide) selected_cut_00452

theorem selected_cut_00453 : selected 8 ⟨20749, by decide⟩
    (prefixPartial 13 5550) = some ⟨13, 2, 0, 20749, 5550, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_5550_20749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5550 ⟨20749, by decide⟩ :=
  accepted_of_selected 13 5550 ⟨20749, by decide⟩ ⟨13, 2, 0, 20749, 5550, 2661, 16384⟩
    (by decide) selected_cut_00453

theorem selected_cut_00454 : selected 8 ⟨20762, by decide⟩
    (prefixPartial 13 5551) = some ⟨13, 2, 0, 20762, 5551, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_5551_20762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5551 ⟨20762, by decide⟩ :=
  accepted_of_selected 13 5551 ⟨20762, by decide⟩ ⟨13, 2, 0, 20762, 5551, 1365, 16384⟩
    (by decide) selected_cut_00454

theorem unmarked_context_12_1387_20763 : frontier 9 ⟨20763, by decide⟩
    (prefixCache 12 1387) (prefixPartial 12 1387) = false := by
  decide +kernel

theorem node_context_12_1387_20763 : EJMOriginalGlobalDAGData.nodes 9 ⟨20763, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨20713, by decide⟩,⟨20749, by decide⟩,⟨20762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1387_20763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1387 ⟨20763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1387
    ⟨20763, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨20713, by decide⟩,⟨20749, by decide⟩,⟨20762, by decide⟩]) unmarked_context_12_1387_20763 node_context_12_1387_20763
  intro a
  fin_cases a
  · exact context_13_5548_3444
  · exact context_13_5549_20713
  · exact context_13_5550_20749
  · exact context_13_5551_20762

theorem unmarked_context_11_346_20764 : frontier 10 ⟨20764, by decide⟩
    (prefixCache 11 346) (prefixPartial 11 346) = false := by
  decide +kernel

theorem node_context_11_346_20764 : EJMOriginalGlobalDAGData.nodes 10 ⟨20764, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨20701, by decide⟩,⟨20763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_346_20764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 346 ⟨20764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 346
    ⟨20764, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨20701, by decide⟩,⟨20763, by decide⟩]) unmarked_context_11_346_20764 node_context_11_346_20764
  intro a
  fin_cases a
  · exact context_12_1384_1738
  · exact context_12_1385_1738
  · exact context_12_1386_20701
  · exact context_12_1387_20763

theorem selected_cut_00455 : selected 10 ⟨20844, by decide⟩
    (prefixPartial 11 347) = some ⟨11, 2, 0, 20844, 347, 3361, 262144⟩ := by
  decide +kernel

theorem context_11_347_20844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 347 ⟨20844, by decide⟩ :=
  accepted_of_selected 11 347 ⟨20844, by decide⟩ ⟨11, 2, 0, 20844, 347, 3361, 262144⟩
    (by decide) selected_cut_00455

theorem unmarked_context_10_86_20845 : frontier 11 ⟨20845, by decide⟩
    (prefixCache 10 86) (prefixPartial 10 86) = false := by
  decide +kernel

theorem node_context_10_86_20845 : EJMOriginalGlobalDAGData.nodes 11 ⟨20845, by decide⟩ =
    .split (coordinate 10) (![⟨20477, by decide⟩,⟨20631, by decide⟩,⟨20764, by decide⟩,⟨20844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_86_20845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 86 ⟨20845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 86
    ⟨20845, by decide⟩ (by decide) (![⟨20477, by decide⟩,⟨20631, by decide⟩,⟨20764, by decide⟩,⟨20844, by decide⟩]) unmarked_context_10_86_20845 node_context_10_86_20845
  intro a
  fin_cases a
  · exact context_11_344_20477
  · exact context_11_345_20631
  · exact context_11_346_20764
  · exact context_11_347_20844

theorem selected_cut_00456 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 87) = some ⟨10, 1, 0, 3440, 87, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_87_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 87 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 87 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 87, 1, 1048576⟩
    (by decide) selected_cut_00456

theorem unmarked_context_9_21_20846 : frontier 12 ⟨20846, by decide⟩
    (prefixCache 9 21) (prefixPartial 9 21) = false := by
  decide +kernel

theorem node_context_9_21_20846 : EJMOriginalGlobalDAGData.nodes 12 ⟨20846, by decide⟩ =
    .split (coordinate 9) (![⟨19746, by decide⟩,⟨20323, by decide⟩,⟨20845, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_21_20846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 21 ⟨20846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 21
    ⟨20846, by decide⟩ (by decide) (![⟨19746, by decide⟩,⟨20323, by decide⟩,⟨20845, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_21_20846 node_context_9_21_20846
  intro a
  fin_cases a
  · exact context_10_84_19746
  · exact context_10_85_20323
  · exact context_10_86_20845
  · exact context_10_87_3440

theorem selected_cut_00457 : selected 9 ⟨20894, by decide⟩
    (prefixPartial 12 1408) = some ⟨12, 2, 0, 20894, 1408, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_1408_20894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1408 ⟨20894, by decide⟩ :=
  accepted_of_selected 12 1408 ⟨20894, by decide⟩ ⟨12, 2, 0, 20894, 1408, 2177, 65536⟩
    (by decide) selected_cut_00457

theorem selected_cut_00458 : selected 9 ⟨20942, by decide⟩
    (prefixPartial 12 1409) = some ⟨12, 2, 0, 20942, 1409, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_1409_20942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1409 ⟨20942, by decide⟩ :=
  accepted_of_selected 12 1409 ⟨20942, by decide⟩ ⟨12, 2, 0, 20942, 1409, 3077, 65536⟩
    (by decide) selected_cut_00458

theorem selected_cut_00459 : selected 9 ⟨20980, by decide⟩
    (prefixPartial 12 1410) = some ⟨12, 2, 0, 20980, 1410, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_1410_20980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1410 ⟨20980, by decide⟩ :=
  accepted_of_selected 12 1410 ⟨20980, by decide⟩ ⟨12, 2, 0, 20980, 1410, 3257, 65536⟩
    (by decide) selected_cut_00459

theorem selected_cut_00460 : selected 9 ⟨21026, by decide⟩
    (prefixPartial 12 1411) = some ⟨12, 2, 0, 21026, 1411, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_1411_21026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1411 ⟨21026, by decide⟩ :=
  accepted_of_selected 12 1411 ⟨21026, by decide⟩ ⟨12, 2, 0, 21026, 1411, 3337, 65536⟩
    (by decide) selected_cut_00460

theorem unmarked_context_11_352_21027 : frontier 10 ⟨21027, by decide⟩
    (prefixCache 11 352) (prefixPartial 11 352) = false := by
  decide +kernel

theorem node_context_11_352_21027 : EJMOriginalGlobalDAGData.nodes 10 ⟨21027, by decide⟩ =
    .split (coordinate 11) (![⟨20894, by decide⟩,⟨20942, by decide⟩,⟨20980, by decide⟩,⟨21026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_352_21027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 352 ⟨21027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 352
    ⟨21027, by decide⟩ (by decide) (![⟨20894, by decide⟩,⟨20942, by decide⟩,⟨20980, by decide⟩,⟨21026, by decide⟩]) unmarked_context_11_352_21027 node_context_11_352_21027
  intro a
  fin_cases a
  · exact context_12_1408_20894
  · exact context_12_1409_20942
  · exact context_12_1410_20980
  · exact context_12_1411_21026

theorem selected_cut_00461 : selected 9 ⟨21088, by decide⟩
    (prefixPartial 12 1412) = some ⟨12, 2, 0, 21088, 1412, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_1412_21088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1412 ⟨21088, by decide⟩ :=
  accepted_of_selected 12 1412 ⟨21088, by decide⟩ ⟨12, 2, 0, 21088, 1412, 1657, 65536⟩
    (by decide) selected_cut_00461

theorem selected_cut_00462 : selected 9 ⟨21192, by decide⟩
    (prefixPartial 12 1413) = some ⟨12, 2, 0, 21192, 1413, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_1413_21192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1413 ⟨21192, by decide⟩ :=
  accepted_of_selected 12 1413 ⟨21192, by decide⟩ ⟨12, 2, 0, 21192, 1413, 3485, 65536⟩
    (by decide) selected_cut_00462

theorem selected_cut_00463 : selected 9 ⟨21264, by decide⟩
    (prefixPartial 12 1414) = some ⟨12, 2, 0, 21264, 1414, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_1414_21264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1414 ⟨21264, by decide⟩ :=
  accepted_of_selected 12 1414 ⟨21264, by decide⟩ ⟨12, 2, 0, 21264, 1414, 2861, 65536⟩
    (by decide) selected_cut_00463

theorem selected_cut_00464 : selected 9 ⟨21324, by decide⟩
    (prefixPartial 12 1415) = some ⟨12, 2, 0, 21324, 1415, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_1415_21324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1415 ⟨21324, by decide⟩ :=
  accepted_of_selected 12 1415 ⟨21324, by decide⟩ ⟨12, 2, 0, 21324, 1415, 2893, 65536⟩
    (by decide) selected_cut_00464

theorem unmarked_context_11_353_21325 : frontier 10 ⟨21325, by decide⟩
    (prefixCache 11 353) (prefixPartial 11 353) = false := by
  decide +kernel

theorem node_context_11_353_21325 : EJMOriginalGlobalDAGData.nodes 10 ⟨21325, by decide⟩ =
    .split (coordinate 11) (![⟨21088, by decide⟩,⟨21192, by decide⟩,⟨21264, by decide⟩,⟨21324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_353_21325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 353 ⟨21325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 353
    ⟨21325, by decide⟩ (by decide) (![⟨21088, by decide⟩,⟨21192, by decide⟩,⟨21264, by decide⟩,⟨21324, by decide⟩]) unmarked_context_11_353_21325 node_context_11_353_21325
  intro a
  fin_cases a
  · exact context_12_1412_21088
  · exact context_12_1413_21192
  · exact context_12_1414_21264
  · exact context_12_1415_21324

theorem selected_cut_00465 : selected 9 ⟨21407, by decide⟩
    (prefixPartial 12 1416) = some ⟨12, 2, 0, 21407, 1416, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_1416_21407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1416 ⟨21407, by decide⟩ :=
  accepted_of_selected 12 1416 ⟨21407, by decide⟩ ⟨12, 2, 0, 21407, 1416, 1785, 65536⟩
    (by decide) selected_cut_00465

theorem selected_cut_00466 : selected 9 ⟨21485, by decide⟩
    (prefixPartial 12 1417) = some ⟨12, 2, 0, 21485, 1417, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_1417_21485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1417 ⟨21485, by decide⟩ :=
  accepted_of_selected 12 1417 ⟨21485, by decide⟩ ⟨12, 2, 0, 21485, 1417, 2677, 65536⟩
    (by decide) selected_cut_00466

theorem selected_cut_00467 : selected 9 ⟨21544, by decide⟩
    (prefixPartial 12 1418) = some ⟨12, 2, 0, 21544, 1418, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_1418_21544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1418 ⟨21544, by decide⟩ :=
  accepted_of_selected 12 1418 ⟨21544, by decide⟩ ⟨12, 2, 0, 21544, 1418, 2629, 65536⟩
    (by decide) selected_cut_00467

theorem selected_cut_00468 : selected 9 ⟨21618, by decide⟩
    (prefixPartial 12 1419) = some ⟨12, 2, 0, 21618, 1419, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_1419_21618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1419 ⟨21618, by decide⟩ :=
  accepted_of_selected 12 1419 ⟨21618, by decide⟩ ⟨12, 2, 0, 21618, 1419, 2889, 65536⟩
    (by decide) selected_cut_00468

theorem unmarked_context_11_354_21619 : frontier 10 ⟨21619, by decide⟩
    (prefixCache 11 354) (prefixPartial 11 354) = false := by
  decide +kernel

theorem node_context_11_354_21619 : EJMOriginalGlobalDAGData.nodes 10 ⟨21619, by decide⟩ =
    .split (coordinate 11) (![⟨21407, by decide⟩,⟨21485, by decide⟩,⟨21544, by decide⟩,⟨21618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_354_21619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 354 ⟨21619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 354
    ⟨21619, by decide⟩ (by decide) (![⟨21407, by decide⟩,⟨21485, by decide⟩,⟨21544, by decide⟩,⟨21618, by decide⟩]) unmarked_context_11_354_21619 node_context_11_354_21619
  intro a
  fin_cases a
  · exact context_12_1416_21407
  · exact context_12_1417_21485
  · exact context_12_1418_21544
  · exact context_12_1419_21618

theorem selected_cut_00469 : selected 9 ⟨21684, by decide⟩
    (prefixPartial 12 1420) = some ⟨12, 2, 0, 21684, 1420, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_1420_21684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1420 ⟨21684, by decide⟩ :=
  accepted_of_selected 12 1420 ⟨21684, by decide⟩ ⟨12, 2, 0, 21684, 1420, 1433, 65536⟩
    (by decide) selected_cut_00469

theorem selected_cut_00470 : selected 9 ⟨21751, by decide⟩
    (prefixPartial 12 1421) = some ⟨12, 2, 0, 21751, 1421, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_1421_21751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1421 ⟨21751, by decide⟩ :=
  accepted_of_selected 12 1421 ⟨21751, by decide⟩ ⟨12, 2, 0, 21751, 1421, 2221, 65536⟩
    (by decide) selected_cut_00470

theorem selected_cut_00471 : selected 9 ⟨21833, by decide⟩
    (prefixPartial 12 1422) = some ⟨12, 2, 0, 21833, 1422, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_1422_21833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1422 ⟨21833, by decide⟩ :=
  accepted_of_selected 12 1422 ⟨21833, by decide⟩ ⟨12, 2, 0, 21833, 1422, 2393, 65536⟩
    (by decide) selected_cut_00471

theorem selected_cut_00472 : selected 9 ⟨21883, by decide⟩
    (prefixPartial 12 1423) = some ⟨12, 2, 0, 21883, 1423, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_1423_21883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1423 ⟨21883, by decide⟩ :=
  accepted_of_selected 12 1423 ⟨21883, by decide⟩ ⟨12, 2, 0, 21883, 1423, 2093, 65536⟩
    (by decide) selected_cut_00472

theorem unmarked_context_11_355_21884 : frontier 10 ⟨21884, by decide⟩
    (prefixCache 11 355) (prefixPartial 11 355) = false := by
  decide +kernel

theorem node_context_11_355_21884 : EJMOriginalGlobalDAGData.nodes 10 ⟨21884, by decide⟩ =
    .split (coordinate 11) (![⟨21684, by decide⟩,⟨21751, by decide⟩,⟨21833, by decide⟩,⟨21883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_355_21884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 355 ⟨21884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 355
    ⟨21884, by decide⟩ (by decide) (![⟨21684, by decide⟩,⟨21751, by decide⟩,⟨21833, by decide⟩,⟨21883, by decide⟩]) unmarked_context_11_355_21884 node_context_11_355_21884
  intro a
  fin_cases a
  · exact context_12_1420_21684
  · exact context_12_1421_21751
  · exact context_12_1422_21833
  · exact context_12_1423_21883

theorem unmarked_context_10_88_21885 : frontier 11 ⟨21885, by decide⟩
    (prefixCache 10 88) (prefixPartial 10 88) = false := by
  decide +kernel

theorem node_context_10_88_21885 : EJMOriginalGlobalDAGData.nodes 11 ⟨21885, by decide⟩ =
    .split (coordinate 10) (![⟨21027, by decide⟩,⟨21325, by decide⟩,⟨21619, by decide⟩,⟨21884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_88_21885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 88 ⟨21885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 88
    ⟨21885, by decide⟩ (by decide) (![⟨21027, by decide⟩,⟨21325, by decide⟩,⟨21619, by decide⟩,⟨21884, by decide⟩]) unmarked_context_10_88_21885 node_context_10_88_21885
  intro a
  fin_cases a
  · exact context_11_352_21027
  · exact context_11_353_21325
  · exact context_11_354_21619
  · exact context_11_355_21884

theorem selected_cut_00473 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1424) = some ⟨12, 1, 0, 1738, 1424, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1424_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1424 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1424 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1424, 1, 65536⟩
    (by decide) selected_cut_00473

theorem selected_cut_00474 : selected 9 ⟨21942, by decide⟩
    (prefixPartial 12 1425) = some ⟨12, 2, 0, 21942, 1425, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_1425_21942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1425 ⟨21942, by decide⟩ :=
  accepted_of_selected 12 1425 ⟨21942, by decide⟩ ⟨12, 2, 0, 21942, 1425, 1285, 65536⟩
    (by decide) selected_cut_00474

theorem selected_cut_00475 : selected 9 ⟨22011, by decide⟩
    (prefixPartial 12 1426) = some ⟨12, 2, 0, 22011, 1426, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_1426_22011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1426 ⟨22011, by decide⟩ :=
  accepted_of_selected 12 1426 ⟨22011, by decide⟩ ⟨12, 2, 0, 22011, 1426, 1873, 65536⟩
    (by decide) selected_cut_00475

theorem selected_cut_00476 : selected 9 ⟨22077, by decide⟩
    (prefixPartial 12 1427) = some ⟨12, 2, 0, 22077, 1427, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_1427_22077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1427 ⟨22077, by decide⟩ :=
  accepted_of_selected 12 1427 ⟨22077, by decide⟩ ⟨12, 2, 0, 22077, 1427, 1841, 65536⟩
    (by decide) selected_cut_00476

theorem unmarked_context_11_356_22078 : frontier 10 ⟨22078, by decide⟩
    (prefixCache 11 356) (prefixPartial 11 356) = false := by
  decide +kernel

theorem node_context_11_356_22078 : EJMOriginalGlobalDAGData.nodes 10 ⟨22078, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨21942, by decide⟩,⟨22011, by decide⟩,⟨22077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_356_22078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 356 ⟨22078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 356
    ⟨22078, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨21942, by decide⟩,⟨22011, by decide⟩,⟨22077, by decide⟩]) unmarked_context_11_356_22078 node_context_11_356_22078
  intro a
  fin_cases a
  · exact context_12_1424_1738
  · exact context_12_1425_21942
  · exact context_12_1426_22011
  · exact context_12_1427_22077

theorem selected_cut_00477 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 1428) = some ⟨12, 1, 0, 1738, 1428, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1428_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1428 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 1428 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 1428, 1, 65536⟩
    (by decide) selected_cut_00477

theorem selected_cut_00478 : selected 9 ⟨22218, by decide⟩
    (prefixPartial 12 1429) = some ⟨12, 2, 0, 22218, 1429, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_1429_22218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1429 ⟨22218, by decide⟩ :=
  accepted_of_selected 12 1429 ⟨22218, by decide⟩ ⟨12, 2, 0, 22218, 1429, 2409, 65536⟩
    (by decide) selected_cut_00478

theorem selected_cut_00479 : selected 9 ⟨22343, by decide⟩
    (prefixPartial 12 1430) = some ⟨12, 2, 0, 22343, 1430, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_1430_22343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1430 ⟨22343, by decide⟩ :=
  accepted_of_selected 12 1430 ⟨22343, by decide⟩ ⟨12, 2, 0, 22343, 1430, 2193, 65536⟩
    (by decide) selected_cut_00479

theorem selected_cut_00480 : selected 9 ⟨22468, by decide⟩
    (prefixPartial 12 1431) = some ⟨12, 2, 0, 22468, 1431, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_1431_22468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1431 ⟨22468, by decide⟩ :=
  accepted_of_selected 12 1431 ⟨22468, by decide⟩ ⟨12, 2, 0, 22468, 1431, 2065, 65536⟩
    (by decide) selected_cut_00480

theorem unmarked_context_11_357_22469 : frontier 10 ⟨22469, by decide⟩
    (prefixCache 11 357) (prefixPartial 11 357) = false := by
  decide +kernel

theorem node_context_11_357_22469 : EJMOriginalGlobalDAGData.nodes 10 ⟨22469, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨22218, by decide⟩,⟨22343, by decide⟩,⟨22468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_357_22469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 357 ⟨22469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 357
    ⟨22469, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨22218, by decide⟩,⟨22343, by decide⟩,⟨22468, by decide⟩]) unmarked_context_11_357_22469 node_context_11_357_22469
  intro a
  fin_cases a
  · exact context_12_1428_1738
  · exact context_12_1429_22218
  · exact context_12_1430_22343
  · exact context_12_1431_22468

theorem selected_cut_00481 : selected 10 ⟨22610, by decide⟩
    (prefixPartial 11 358) = some ⟨11, 2, 0, 22610, 358, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_358_22610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 358 ⟨22610, by decide⟩ :=
  accepted_of_selected 11 358 ⟨22610, by decide⟩ ⟨11, 2, 0, 22610, 358, 3653, 262144⟩
    (by decide) selected_cut_00481

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
