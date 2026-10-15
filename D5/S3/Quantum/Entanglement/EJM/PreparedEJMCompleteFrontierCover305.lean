/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover304
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29283 : selected 8 ⟨739954, by decide⟩
    (prefixPartial 13 373860) = some ⟨13, 2, 0, 739954, 373860, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_373860_739954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373860 ⟨739954, by decide⟩ :=
  accepted_of_selected 13 373860 ⟨739954, by decide⟩ ⟨13, 2, 0, 739954, 373860, 1361, 16384⟩
    (by decide) selected_cut_29283

theorem selected_cut_29284 : selected 8 ⟨739973, by decide⟩
    (prefixPartial 13 373861) = some ⟨13, 2, 0, 739973, 373861, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_373861_739973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373861 ⟨739973, by decide⟩ :=
  accepted_of_selected 13 373861 ⟨739973, by decide⟩ ⟨13, 2, 0, 739973, 373861, 1297, 16384⟩
    (by decide) selected_cut_29284

theorem selected_cut_29285 : selected 8 ⟨739996, by decide⟩
    (prefixPartial 13 373862) = some ⟨13, 2, 0, 739996, 373862, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_373862_739996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373862 ⟨739996, by decide⟩ :=
  accepted_of_selected 13 373862 ⟨739996, by decide⟩ ⟨13, 2, 0, 739996, 373862, 1605, 16384⟩
    (by decide) selected_cut_29285

theorem selected_cut_29286 : selected 8 ⟨740005, by decide⟩
    (prefixPartial 13 373863) = some ⟨13, 2, 0, 740005, 373863, 857, 16384⟩ := by
  decide +kernel

theorem context_13_373863_740005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373863 ⟨740005, by decide⟩ :=
  accepted_of_selected 13 373863 ⟨740005, by decide⟩ ⟨13, 2, 0, 740005, 373863, 857, 16384⟩
    (by decide) selected_cut_29286

theorem unmarked_context_12_93465_740006 : frontier 9 ⟨740006, by decide⟩
    (prefixCache 12 93465) (prefixPartial 12 93465) = false := by
  decide +kernel

theorem node_context_12_93465_740006 : EJMOriginalGlobalDAGData.nodes 9 ⟨740006, by decide⟩ =
    .split (coordinate 12) (![⟨739954, by decide⟩,⟨739973, by decide⟩,⟨739996, by decide⟩,⟨740005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93465_740006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93465 ⟨740006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93465
    ⟨740006, by decide⟩ (by decide) (![⟨739954, by decide⟩,⟨739973, by decide⟩,⟨739996, by decide⟩,⟨740005, by decide⟩]) unmarked_context_12_93465_740006 node_context_12_93465_740006
  intro a
  fin_cases a
  · exact context_13_373860_739954
  · exact context_13_373861_739973
  · exact context_13_373862_739996
  · exact context_13_373863_740005

theorem selected_cut_29287 : selected 8 ⟨740032, by decide⟩
    (prefixPartial 13 373864) = some ⟨13, 2, 0, 740032, 373864, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_373864_740032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373864 ⟨740032, by decide⟩ :=
  accepted_of_selected 13 373864 ⟨740032, by decide⟩ ⟨13, 2, 0, 740032, 373864, 1469, 16384⟩
    (by decide) selected_cut_29287

theorem selected_cut_29288 : selected 8 ⟨740054, by decide⟩
    (prefixPartial 13 373865) = some ⟨13, 2, 0, 740054, 373865, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_373865_740054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373865 ⟨740054, by decide⟩ :=
  accepted_of_selected 13 373865 ⟨740054, by decide⟩ ⟨13, 2, 0, 740054, 373865, 1605, 16384⟩
    (by decide) selected_cut_29288

theorem selected_cut_29289 : selected 8 ⟨740075, by decide⟩
    (prefixPartial 13 373866) = some ⟨13, 2, 0, 740075, 373866, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_373866_740075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373866 ⟨740075, by decide⟩ :=
  accepted_of_selected 13 373866 ⟨740075, by decide⟩ ⟨13, 2, 0, 740075, 373866, 1489, 16384⟩
    (by decide) selected_cut_29289

theorem selected_cut_29290 : selected 8 ⟨740083, by decide⟩
    (prefixPartial 13 373867) = some ⟨13, 2, 0, 740083, 373867, 889, 16384⟩ := by
  decide +kernel

theorem context_13_373867_740083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373867 ⟨740083, by decide⟩ :=
  accepted_of_selected 13 373867 ⟨740083, by decide⟩ ⟨13, 2, 0, 740083, 373867, 889, 16384⟩
    (by decide) selected_cut_29290

theorem unmarked_context_12_93466_740084 : frontier 9 ⟨740084, by decide⟩
    (prefixCache 12 93466) (prefixPartial 12 93466) = false := by
  decide +kernel

theorem node_context_12_93466_740084 : EJMOriginalGlobalDAGData.nodes 9 ⟨740084, by decide⟩ =
    .split (coordinate 12) (![⟨740032, by decide⟩,⟨740054, by decide⟩,⟨740075, by decide⟩,⟨740083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93466_740084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93466 ⟨740084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93466
    ⟨740084, by decide⟩ (by decide) (![⟨740032, by decide⟩,⟨740054, by decide⟩,⟨740075, by decide⟩,⟨740083, by decide⟩]) unmarked_context_12_93466_740084 node_context_12_93466_740084
  intro a
  fin_cases a
  · exact context_13_373864_740032
  · exact context_13_373865_740054
  · exact context_13_373866_740075
  · exact context_13_373867_740083

theorem selected_cut_29291 : selected 8 ⟨740112, by decide⟩
    (prefixPartial 13 373868) = some ⟨13, 2, 0, 740112, 373868, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_373868_740112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373868 ⟨740112, by decide⟩ :=
  accepted_of_selected 13 373868 ⟨740112, by decide⟩ ⟨13, 2, 0, 740112, 373868, 1553, 16384⟩
    (by decide) selected_cut_29291

theorem selected_cut_29292 : selected 8 ⟨740133, by decide⟩
    (prefixPartial 13 373869) = some ⟨13, 2, 0, 740133, 373869, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_373869_740133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373869 ⟨740133, by decide⟩ :=
  accepted_of_selected 13 373869 ⟨740133, by decide⟩ ⟨13, 2, 0, 740133, 373869, 1721, 16384⟩
    (by decide) selected_cut_29292

theorem selected_cut_29293 : selected 8 ⟨740155, by decide⟩
    (prefixPartial 13 373870) = some ⟨13, 2, 0, 740155, 373870, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_373870_740155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373870 ⟨740155, by decide⟩ :=
  accepted_of_selected 13 373870 ⟨740155, by decide⟩ ⟨13, 2, 0, 740155, 373870, 1737, 16384⟩
    (by decide) selected_cut_29293

theorem selected_cut_29294 : selected 8 ⟨740160, by decide⟩
    (prefixPartial 13 373871) = some ⟨13, 2, 0, 740160, 373871, 825, 16384⟩ := by
  decide +kernel

theorem context_13_373871_740160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373871 ⟨740160, by decide⟩ :=
  accepted_of_selected 13 373871 ⟨740160, by decide⟩ ⟨13, 2, 0, 740160, 373871, 825, 16384⟩
    (by decide) selected_cut_29294

theorem unmarked_context_12_93467_740161 : frontier 9 ⟨740161, by decide⟩
    (prefixCache 12 93467) (prefixPartial 12 93467) = false := by
  decide +kernel

theorem node_context_12_93467_740161 : EJMOriginalGlobalDAGData.nodes 9 ⟨740161, by decide⟩ =
    .split (coordinate 12) (![⟨740112, by decide⟩,⟨740133, by decide⟩,⟨740155, by decide⟩,⟨740160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93467_740161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93467 ⟨740161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93467
    ⟨740161, by decide⟩ (by decide) (![⟨740112, by decide⟩,⟨740133, by decide⟩,⟨740155, by decide⟩,⟨740160, by decide⟩]) unmarked_context_12_93467_740161 node_context_12_93467_740161
  intro a
  fin_cases a
  · exact context_13_373868_740112
  · exact context_13_373869_740133
  · exact context_13_373870_740155
  · exact context_13_373871_740160

theorem unmarked_context_11_23366_740162 : frontier 10 ⟨740162, by decide⟩
    (prefixCache 11 23366) (prefixPartial 11 23366) = false := by
  decide +kernel

theorem node_context_11_23366_740162 : EJMOriginalGlobalDAGData.nodes 10 ⟨740162, by decide⟩ =
    .split (coordinate 11) (![⟨739930, by decide⟩,⟨740006, by decide⟩,⟨740084, by decide⟩,⟨740161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23366_740162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23366 ⟨740162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23366
    ⟨740162, by decide⟩ (by decide) (![⟨739930, by decide⟩,⟨740006, by decide⟩,⟨740084, by decide⟩,⟨740161, by decide⟩]) unmarked_context_11_23366_740162 node_context_11_23366_740162
  intro a
  fin_cases a
  · exact context_12_93464_739930
  · exact context_12_93465_740006
  · exact context_12_93466_740084
  · exact context_12_93467_740161

theorem selected_cut_29295 : selected 8 ⟨740181, by decide⟩
    (prefixPartial 13 373872) = some ⟨13, 2, 0, 740181, 373872, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_373872_740181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373872 ⟨740181, by decide⟩ :=
  accepted_of_selected 13 373872 ⟨740181, by decide⟩ ⟨13, 2, 0, 740181, 373872, 1225, 16384⟩
    (by decide) selected_cut_29295

theorem selected_cut_29296 : selected 8 ⟨740204, by decide⟩
    (prefixPartial 13 373873) = some ⟨13, 2, 0, 740204, 373873, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_373873_740204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373873 ⟨740204, by decide⟩ :=
  accepted_of_selected 13 373873 ⟨740204, by decide⟩ ⟨13, 2, 0, 740204, 373873, 1577, 16384⟩
    (by decide) selected_cut_29296

theorem selected_cut_29297 : selected 8 ⟨740218, by decide⟩
    (prefixPartial 13 373874) = some ⟨13, 2, 0, 740218, 373874, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_373874_740218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373874 ⟨740218, by decide⟩ :=
  accepted_of_selected 13 373874 ⟨740218, by decide⟩ ⟨13, 2, 0, 740218, 373874, 1217, 16384⟩
    (by decide) selected_cut_29297

theorem selected_cut_29298 : selected 8 ⟨740227, by decide⟩
    (prefixPartial 13 373875) = some ⟨13, 2, 0, 740227, 373875, 777, 16384⟩ := by
  decide +kernel

theorem context_13_373875_740227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373875 ⟨740227, by decide⟩ :=
  accepted_of_selected 13 373875 ⟨740227, by decide⟩ ⟨13, 2, 0, 740227, 373875, 777, 16384⟩
    (by decide) selected_cut_29298

theorem unmarked_context_12_93468_740228 : frontier 9 ⟨740228, by decide⟩
    (prefixCache 12 93468) (prefixPartial 12 93468) = false := by
  decide +kernel

theorem node_context_12_93468_740228 : EJMOriginalGlobalDAGData.nodes 9 ⟨740228, by decide⟩ =
    .split (coordinate 12) (![⟨740181, by decide⟩,⟨740204, by decide⟩,⟨740218, by decide⟩,⟨740227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93468_740228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93468 ⟨740228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93468
    ⟨740228, by decide⟩ (by decide) (![⟨740181, by decide⟩,⟨740204, by decide⟩,⟨740218, by decide⟩,⟨740227, by decide⟩]) unmarked_context_12_93468_740228 node_context_12_93468_740228
  intro a
  fin_cases a
  · exact context_13_373872_740181
  · exact context_13_373873_740204
  · exact context_13_373874_740218
  · exact context_13_373875_740227

theorem selected_cut_29299 : selected 8 ⟨740251, by decide⟩
    (prefixPartial 13 373876) = some ⟨13, 2, 0, 740251, 373876, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_373876_740251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373876 ⟨740251, by decide⟩ :=
  accepted_of_selected 13 373876 ⟨740251, by decide⟩ ⟨13, 2, 0, 740251, 373876, 1193, 16384⟩
    (by decide) selected_cut_29299

theorem selected_cut_29300 : selected 8 ⟨740270, by decide⟩
    (prefixPartial 13 373877) = some ⟨13, 2, 0, 740270, 373877, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_373877_740270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373877 ⟨740270, by decide⟩ :=
  accepted_of_selected 13 373877 ⟨740270, by decide⟩ ⟨13, 2, 0, 740270, 373877, 1357, 16384⟩
    (by decide) selected_cut_29300

theorem selected_cut_29301 : selected 8 ⟨740292, by decide⟩
    (prefixPartial 13 373878) = some ⟨13, 2, 0, 740292, 373878, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_373878_740292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373878 ⟨740292, by decide⟩ :=
  accepted_of_selected 13 373878 ⟨740292, by decide⟩ ⟨13, 2, 0, 740292, 373878, 1373, 16384⟩
    (by decide) selected_cut_29301

theorem selected_cut_29302 : selected 8 ⟨740301, by decide⟩
    (prefixPartial 13 373879) = some ⟨13, 2, 0, 740301, 373879, 785, 16384⟩ := by
  decide +kernel

theorem context_13_373879_740301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373879 ⟨740301, by decide⟩ :=
  accepted_of_selected 13 373879 ⟨740301, by decide⟩ ⟨13, 2, 0, 740301, 373879, 785, 16384⟩
    (by decide) selected_cut_29302

theorem unmarked_context_12_93469_740302 : frontier 9 ⟨740302, by decide⟩
    (prefixCache 12 93469) (prefixPartial 12 93469) = false := by
  decide +kernel

theorem node_context_12_93469_740302 : EJMOriginalGlobalDAGData.nodes 9 ⟨740302, by decide⟩ =
    .split (coordinate 12) (![⟨740251, by decide⟩,⟨740270, by decide⟩,⟨740292, by decide⟩,⟨740301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93469_740302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93469 ⟨740302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93469
    ⟨740302, by decide⟩ (by decide) (![⟨740251, by decide⟩,⟨740270, by decide⟩,⟨740292, by decide⟩,⟨740301, by decide⟩]) unmarked_context_12_93469_740302 node_context_12_93469_740302
  intro a
  fin_cases a
  · exact context_13_373876_740251
  · exact context_13_373877_740270
  · exact context_13_373878_740292
  · exact context_13_373879_740301

theorem selected_cut_29303 : selected 8 ⟨740331, by decide⟩
    (prefixPartial 13 373880) = some ⟨13, 2, 0, 740331, 373880, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_373880_740331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373880 ⟨740331, by decide⟩ :=
  accepted_of_selected 13 373880 ⟨740331, by decide⟩ ⟨13, 2, 0, 740331, 373880, 1313, 16384⟩
    (by decide) selected_cut_29303

theorem selected_cut_29304 : selected 8 ⟨740354, by decide⟩
    (prefixPartial 13 373881) = some ⟨13, 2, 0, 740354, 373881, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_373881_740354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373881 ⟨740354, by decide⟩ :=
  accepted_of_selected 13 373881 ⟨740354, by decide⟩ ⟨13, 2, 0, 740354, 373881, 1677, 16384⟩
    (by decide) selected_cut_29304

theorem selected_cut_29305 : selected 8 ⟨740376, by decide⟩
    (prefixPartial 13 373882) = some ⟨13, 2, 0, 740376, 373882, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_373882_740376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373882 ⟨740376, by decide⟩ :=
  accepted_of_selected 13 373882 ⟨740376, by decide⟩ ⟨13, 2, 0, 740376, 373882, 1353, 16384⟩
    (by decide) selected_cut_29305

theorem selected_cut_29306 : selected 8 ⟨740385, by decide⟩
    (prefixPartial 13 373883) = some ⟨13, 2, 0, 740385, 373883, 941, 16384⟩ := by
  decide +kernel

theorem context_13_373883_740385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373883 ⟨740385, by decide⟩ :=
  accepted_of_selected 13 373883 ⟨740385, by decide⟩ ⟨13, 2, 0, 740385, 373883, 941, 16384⟩
    (by decide) selected_cut_29306

theorem unmarked_context_12_93470_740386 : frontier 9 ⟨740386, by decide⟩
    (prefixCache 12 93470) (prefixPartial 12 93470) = false := by
  decide +kernel

theorem node_context_12_93470_740386 : EJMOriginalGlobalDAGData.nodes 9 ⟨740386, by decide⟩ =
    .split (coordinate 12) (![⟨740331, by decide⟩,⟨740354, by decide⟩,⟨740376, by decide⟩,⟨740385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93470_740386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93470 ⟨740386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93470
    ⟨740386, by decide⟩ (by decide) (![⟨740331, by decide⟩,⟨740354, by decide⟩,⟨740376, by decide⟩,⟨740385, by decide⟩]) unmarked_context_12_93470_740386 node_context_12_93470_740386
  intro a
  fin_cases a
  · exact context_13_373880_740331
  · exact context_13_373881_740354
  · exact context_13_373882_740376
  · exact context_13_373883_740385

theorem selected_cut_29307 : selected 8 ⟨740413, by decide⟩
    (prefixPartial 13 373884) = some ⟨13, 2, 0, 740413, 373884, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_373884_740413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373884 ⟨740413, by decide⟩ :=
  accepted_of_selected 13 373884 ⟨740413, by decide⟩ ⟨13, 2, 0, 740413, 373884, 1437, 16384⟩
    (by decide) selected_cut_29307

theorem selected_cut_29308 : selected 8 ⟨740436, by decide⟩
    (prefixPartial 13 373885) = some ⟨13, 2, 0, 740436, 373885, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_373885_740436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373885 ⟨740436, by decide⟩ :=
  accepted_of_selected 13 373885 ⟨740436, by decide⟩ ⟨13, 2, 0, 740436, 373885, 1717, 16384⟩
    (by decide) selected_cut_29308

theorem selected_cut_29309 : selected 8 ⟨740459, by decide⟩
    (prefixPartial 13 373886) = some ⟨13, 2, 0, 740459, 373886, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_373886_740459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373886 ⟨740459, by decide⟩ :=
  accepted_of_selected 13 373886 ⟨740459, by decide⟩ ⟨13, 2, 0, 740459, 373886, 1493, 16384⟩
    (by decide) selected_cut_29309

theorem selected_cut_29310 : selected 8 ⟨740466, by decide⟩
    (prefixPartial 13 373887) = some ⟨13, 2, 0, 740466, 373887, 893, 16384⟩ := by
  decide +kernel

theorem context_13_373887_740466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373887 ⟨740466, by decide⟩ :=
  accepted_of_selected 13 373887 ⟨740466, by decide⟩ ⟨13, 2, 0, 740466, 373887, 893, 16384⟩
    (by decide) selected_cut_29310

theorem unmarked_context_12_93471_740467 : frontier 9 ⟨740467, by decide⟩
    (prefixCache 12 93471) (prefixPartial 12 93471) = false := by
  decide +kernel

theorem node_context_12_93471_740467 : EJMOriginalGlobalDAGData.nodes 9 ⟨740467, by decide⟩ =
    .split (coordinate 12) (![⟨740413, by decide⟩,⟨740436, by decide⟩,⟨740459, by decide⟩,⟨740466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93471_740467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93471 ⟨740467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93471
    ⟨740467, by decide⟩ (by decide) (![⟨740413, by decide⟩,⟨740436, by decide⟩,⟨740459, by decide⟩,⟨740466, by decide⟩]) unmarked_context_12_93471_740467 node_context_12_93471_740467
  intro a
  fin_cases a
  · exact context_13_373884_740413
  · exact context_13_373885_740436
  · exact context_13_373886_740459
  · exact context_13_373887_740466

theorem unmarked_context_11_23367_740468 : frontier 10 ⟨740468, by decide⟩
    (prefixCache 11 23367) (prefixPartial 11 23367) = false := by
  decide +kernel

theorem node_context_11_23367_740468 : EJMOriginalGlobalDAGData.nodes 10 ⟨740468, by decide⟩ =
    .split (coordinate 11) (![⟨740228, by decide⟩,⟨740302, by decide⟩,⟨740386, by decide⟩,⟨740467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23367_740468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23367 ⟨740468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23367
    ⟨740468, by decide⟩ (by decide) (![⟨740228, by decide⟩,⟨740302, by decide⟩,⟨740386, by decide⟩,⟨740467, by decide⟩]) unmarked_context_11_23367_740468 node_context_11_23367_740468
  intro a
  fin_cases a
  · exact context_12_93468_740228
  · exact context_12_93469_740302
  · exact context_12_93470_740386
  · exact context_12_93471_740467

theorem unmarked_context_10_5841_740469 : frontier 11 ⟨740469, by decide⟩
    (prefixCache 10 5841) (prefixPartial 10 5841) = false := by
  decide +kernel

theorem node_context_10_5841_740469 : EJMOriginalGlobalDAGData.nodes 11 ⟨740469, by decide⟩ =
    .split (coordinate 10) (![⟨739633, by decide⟩,⟨739864, by decide⟩,⟨740162, by decide⟩,⟨740468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5841_740469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5841 ⟨740469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5841
    ⟨740469, by decide⟩ (by decide) (![⟨739633, by decide⟩,⟨739864, by decide⟩,⟨740162, by decide⟩,⟨740468, by decide⟩]) unmarked_context_10_5841_740469 node_context_10_5841_740469
  intro a
  fin_cases a
  · exact context_11_23364_739633
  · exact context_11_23365_739864
  · exact context_11_23366_740162
  · exact context_11_23367_740468

theorem selected_cut_29311 : selected 8 ⟨740500, by decide⟩
    (prefixPartial 13 373888) = some ⟨13, 2, 0, 740500, 373888, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_373888_740500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373888 ⟨740500, by decide⟩ :=
  accepted_of_selected 13 373888 ⟨740500, by decide⟩ ⟨13, 2, 0, 740500, 373888, 1517, 16384⟩
    (by decide) selected_cut_29311

theorem selected_cut_29312 : selected 8 ⟨740527, by decide⟩
    (prefixPartial 13 373889) = some ⟨13, 2, 0, 740527, 373889, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_373889_740527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373889 ⟨740527, by decide⟩ :=
  accepted_of_selected 13 373889 ⟨740527, by decide⟩ ⟨13, 2, 0, 740527, 373889, 1677, 16384⟩
    (by decide) selected_cut_29312

theorem selected_cut_29313 : selected 8 ⟨740548, by decide⟩
    (prefixPartial 13 373890) = some ⟨13, 2, 0, 740548, 373890, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_373890_740548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373890 ⟨740548, by decide⟩ :=
  accepted_of_selected 13 373890 ⟨740548, by decide⟩ ⟨13, 2, 0, 740548, 373890, 1341, 16384⟩
    (by decide) selected_cut_29313

theorem selected_cut_29314 : selected 8 ⟨740557, by decide⟩
    (prefixPartial 13 373891) = some ⟨13, 2, 0, 740557, 373891, 889, 16384⟩ := by
  decide +kernel

theorem context_13_373891_740557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373891 ⟨740557, by decide⟩ :=
  accepted_of_selected 13 373891 ⟨740557, by decide⟩ ⟨13, 2, 0, 740557, 373891, 889, 16384⟩
    (by decide) selected_cut_29314

theorem unmarked_context_12_93472_740558 : frontier 9 ⟨740558, by decide⟩
    (prefixCache 12 93472) (prefixPartial 12 93472) = false := by
  decide +kernel

theorem node_context_12_93472_740558 : EJMOriginalGlobalDAGData.nodes 9 ⟨740558, by decide⟩ =
    .split (coordinate 12) (![⟨740500, by decide⟩,⟨740527, by decide⟩,⟨740548, by decide⟩,⟨740557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93472_740558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93472 ⟨740558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93472
    ⟨740558, by decide⟩ (by decide) (![⟨740500, by decide⟩,⟨740527, by decide⟩,⟨740548, by decide⟩,⟨740557, by decide⟩]) unmarked_context_12_93472_740558 node_context_12_93472_740558
  intro a
  fin_cases a
  · exact context_13_373888_740500
  · exact context_13_373889_740527
  · exact context_13_373890_740548
  · exact context_13_373891_740557

theorem selected_cut_29315 : selected 8 ⟨740582, by decide⟩
    (prefixPartial 13 373892) = some ⟨13, 2, 0, 740582, 373892, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_373892_740582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373892 ⟨740582, by decide⟩ :=
  accepted_of_selected 13 373892 ⟨740582, by decide⟩ ⟨13, 2, 0, 740582, 373892, 1397, 16384⟩
    (by decide) selected_cut_29315

theorem selected_cut_29316 : selected 8 ⟨740605, by decide⟩
    (prefixPartial 13 373893) = some ⟨13, 2, 0, 740605, 373893, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_373893_740605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373893 ⟨740605, by decide⟩ :=
  accepted_of_selected 13 373893 ⟨740605, by decide⟩ ⟨13, 2, 0, 740605, 373893, 1605, 16384⟩
    (by decide) selected_cut_29316

theorem selected_cut_29317 : selected 8 ⟨740625, by decide⟩
    (prefixPartial 13 373894) = some ⟨13, 2, 0, 740625, 373894, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_373894_740625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373894 ⟨740625, by decide⟩ :=
  accepted_of_selected 13 373894 ⟨740625, by decide⟩ ⟨13, 2, 0, 740625, 373894, 1529, 16384⟩
    (by decide) selected_cut_29317

theorem selected_cut_29318 : selected 8 ⟨740635, by decide⟩
    (prefixPartial 13 373895) = some ⟨13, 2, 0, 740635, 373895, 889, 16384⟩ := by
  decide +kernel

theorem context_13_373895_740635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373895 ⟨740635, by decide⟩ :=
  accepted_of_selected 13 373895 ⟨740635, by decide⟩ ⟨13, 2, 0, 740635, 373895, 889, 16384⟩
    (by decide) selected_cut_29318

theorem unmarked_context_12_93473_740636 : frontier 9 ⟨740636, by decide⟩
    (prefixCache 12 93473) (prefixPartial 12 93473) = false := by
  decide +kernel

theorem node_context_12_93473_740636 : EJMOriginalGlobalDAGData.nodes 9 ⟨740636, by decide⟩ =
    .split (coordinate 12) (![⟨740582, by decide⟩,⟨740605, by decide⟩,⟨740625, by decide⟩,⟨740635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93473_740636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93473 ⟨740636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93473
    ⟨740636, by decide⟩ (by decide) (![⟨740582, by decide⟩,⟨740605, by decide⟩,⟨740625, by decide⟩,⟨740635, by decide⟩]) unmarked_context_12_93473_740636 node_context_12_93473_740636
  intro a
  fin_cases a
  · exact context_13_373892_740582
  · exact context_13_373893_740605
  · exact context_13_373894_740625
  · exact context_13_373895_740635

theorem selected_cut_29319 : selected 8 ⟨740661, by decide⟩
    (prefixPartial 13 373896) = some ⟨13, 2, 0, 740661, 373896, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_373896_740661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373896 ⟨740661, by decide⟩ :=
  accepted_of_selected 13 373896 ⟨740661, by decide⟩ ⟨13, 2, 0, 740661, 373896, 1425, 16384⟩
    (by decide) selected_cut_29319

theorem selected_cut_29320 : selected 8 ⟨740698, by decide⟩
    (prefixPartial 13 373897) = some ⟨13, 2, 0, 740698, 373897, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_373897_740698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373897 ⟨740698, by decide⟩ :=
  accepted_of_selected 13 373897 ⟨740698, by decide⟩ ⟨13, 2, 0, 740698, 373897, 1997, 16384⟩
    (by decide) selected_cut_29320

theorem selected_cut_29321 : selected 8 ⟨740719, by decide⟩
    (prefixPartial 13 373898) = some ⟨13, 2, 0, 740719, 373898, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_373898_740719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373898 ⟨740719, by decide⟩ :=
  accepted_of_selected 13 373898 ⟨740719, by decide⟩ ⟨13, 2, 0, 740719, 373898, 1597, 16384⟩
    (by decide) selected_cut_29321

theorem selected_cut_29322 : selected 8 ⟨740728, by decide⟩
    (prefixPartial 13 373899) = some ⟨13, 2, 0, 740728, 373899, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_373899_740728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373899 ⟨740728, by decide⟩ :=
  accepted_of_selected 13 373899 ⟨740728, by decide⟩ ⟨13, 2, 0, 740728, 373899, 1021, 16384⟩
    (by decide) selected_cut_29322

theorem unmarked_context_12_93474_740729 : frontier 9 ⟨740729, by decide⟩
    (prefixCache 12 93474) (prefixPartial 12 93474) = false := by
  decide +kernel

theorem node_context_12_93474_740729 : EJMOriginalGlobalDAGData.nodes 9 ⟨740729, by decide⟩ =
    .split (coordinate 12) (![⟨740661, by decide⟩,⟨740698, by decide⟩,⟨740719, by decide⟩,⟨740728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93474_740729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93474 ⟨740729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93474
    ⟨740729, by decide⟩ (by decide) (![⟨740661, by decide⟩,⟨740698, by decide⟩,⟨740719, by decide⟩,⟨740728, by decide⟩]) unmarked_context_12_93474_740729 node_context_12_93474_740729
  intro a
  fin_cases a
  · exact context_13_373896_740661
  · exact context_13_373897_740698
  · exact context_13_373898_740719
  · exact context_13_373899_740728

theorem selected_cut_29323 : selected 8 ⟨740754, by decide⟩
    (prefixPartial 13 373900) = some ⟨13, 2, 0, 740754, 373900, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_373900_740754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373900 ⟨740754, by decide⟩ :=
  accepted_of_selected 13 373900 ⟨740754, by decide⟩ ⟨13, 2, 0, 740754, 373900, 1557, 16384⟩
    (by decide) selected_cut_29323

theorem selected_cut_29324 : selected 8 ⟨740791, by decide⟩
    (prefixPartial 13 373901) = some ⟨13, 2, 0, 740791, 373901, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_373901_740791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373901 ⟨740791, by decide⟩ :=
  accepted_of_selected 13 373901 ⟨740791, by decide⟩ ⟨13, 2, 0, 740791, 373901, 1981, 16384⟩
    (by decide) selected_cut_29324

theorem selected_cut_29325 : selected 8 ⟨740816, by decide⟩
    (prefixPartial 13 373902) = some ⟨13, 2, 0, 740816, 373902, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_373902_740816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373902 ⟨740816, by decide⟩ :=
  accepted_of_selected 13 373902 ⟨740816, by decide⟩ ⟨13, 2, 0, 740816, 373902, 1785, 16384⟩
    (by decide) selected_cut_29325

theorem selected_cut_29326 : selected 8 ⟨740834, by decide⟩
    (prefixPartial 13 373903) = some ⟨13, 2, 0, 740834, 373903, 993, 16384⟩ := by
  decide +kernel

theorem context_13_373903_740834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373903 ⟨740834, by decide⟩ :=
  accepted_of_selected 13 373903 ⟨740834, by decide⟩ ⟨13, 2, 0, 740834, 373903, 993, 16384⟩
    (by decide) selected_cut_29326

theorem unmarked_context_12_93475_740835 : frontier 9 ⟨740835, by decide⟩
    (prefixCache 12 93475) (prefixPartial 12 93475) = false := by
  decide +kernel

theorem node_context_12_93475_740835 : EJMOriginalGlobalDAGData.nodes 9 ⟨740835, by decide⟩ =
    .split (coordinate 12) (![⟨740754, by decide⟩,⟨740791, by decide⟩,⟨740816, by decide⟩,⟨740834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93475_740835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93475 ⟨740835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93475
    ⟨740835, by decide⟩ (by decide) (![⟨740754, by decide⟩,⟨740791, by decide⟩,⟨740816, by decide⟩,⟨740834, by decide⟩]) unmarked_context_12_93475_740835 node_context_12_93475_740835
  intro a
  fin_cases a
  · exact context_13_373900_740754
  · exact context_13_373901_740791
  · exact context_13_373902_740816
  · exact context_13_373903_740834

theorem unmarked_context_11_23368_740836 : frontier 10 ⟨740836, by decide⟩
    (prefixCache 11 23368) (prefixPartial 11 23368) = false := by
  decide +kernel

theorem node_context_11_23368_740836 : EJMOriginalGlobalDAGData.nodes 10 ⟨740836, by decide⟩ =
    .split (coordinate 11) (![⟨740558, by decide⟩,⟨740636, by decide⟩,⟨740729, by decide⟩,⟨740835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23368_740836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23368 ⟨740836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23368
    ⟨740836, by decide⟩ (by decide) (![⟨740558, by decide⟩,⟨740636, by decide⟩,⟨740729, by decide⟩,⟨740835, by decide⟩]) unmarked_context_11_23368_740836 node_context_11_23368_740836
  intro a
  fin_cases a
  · exact context_12_93472_740558
  · exact context_12_93473_740636
  · exact context_12_93474_740729
  · exact context_12_93475_740835

theorem selected_cut_29327 : selected 8 ⟨740855, by decide⟩
    (prefixPartial 13 373904) = some ⟨13, 2, 0, 740855, 373904, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_373904_740855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373904 ⟨740855, by decide⟩ :=
  accepted_of_selected 13 373904 ⟨740855, by decide⟩ ⟨13, 2, 0, 740855, 373904, 1161, 16384⟩
    (by decide) selected_cut_29327

theorem selected_cut_29328 : selected 8 ⟨740878, by decide⟩
    (prefixPartial 13 373905) = some ⟨13, 2, 0, 740878, 373905, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_373905_740878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373905 ⟨740878, by decide⟩ :=
  accepted_of_selected 13 373905 ⟨740878, by decide⟩ ⟨13, 2, 0, 740878, 373905, 1457, 16384⟩
    (by decide) selected_cut_29328

theorem selected_cut_29329 : selected 8 ⟨740900, by decide⟩
    (prefixPartial 13 373906) = some ⟨13, 2, 0, 740900, 373906, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_373906_740900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373906 ⟨740900, by decide⟩ :=
  accepted_of_selected 13 373906 ⟨740900, by decide⟩ ⟨13, 2, 0, 740900, 373906, 1245, 16384⟩
    (by decide) selected_cut_29329

theorem selected_cut_29330 : selected 8 ⟨740907, by decide⟩
    (prefixPartial 13 373907) = some ⟨13, 2, 0, 740907, 373907, 797, 16384⟩ := by
  decide +kernel

theorem context_13_373907_740907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373907 ⟨740907, by decide⟩ :=
  accepted_of_selected 13 373907 ⟨740907, by decide⟩ ⟨13, 2, 0, 740907, 373907, 797, 16384⟩
    (by decide) selected_cut_29330

theorem unmarked_context_12_93476_740908 : frontier 9 ⟨740908, by decide⟩
    (prefixCache 12 93476) (prefixPartial 12 93476) = false := by
  decide +kernel

theorem node_context_12_93476_740908 : EJMOriginalGlobalDAGData.nodes 9 ⟨740908, by decide⟩ =
    .split (coordinate 12) (![⟨740855, by decide⟩,⟨740878, by decide⟩,⟨740900, by decide⟩,⟨740907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93476_740908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93476 ⟨740908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93476
    ⟨740908, by decide⟩ (by decide) (![⟨740855, by decide⟩,⟨740878, by decide⟩,⟨740900, by decide⟩,⟨740907, by decide⟩]) unmarked_context_12_93476_740908 node_context_12_93476_740908
  intro a
  fin_cases a
  · exact context_13_373904_740855
  · exact context_13_373905_740878
  · exact context_13_373906_740900
  · exact context_13_373907_740907

theorem selected_cut_29331 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 93477) = some ⟨12, 1, 0, 719134, 93477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93477_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93477 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 93477 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 93477, 1, 65536⟩
    (by decide) selected_cut_29331

theorem selected_cut_29332 : selected 8 ⟨740929, by decide⟩
    (prefixPartial 13 373912) = some ⟨13, 2, 0, 740929, 373912, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_373912_740929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373912 ⟨740929, by decide⟩ :=
  accepted_of_selected 13 373912 ⟨740929, by decide⟩ ⟨13, 2, 0, 740929, 373912, 1169, 16384⟩
    (by decide) selected_cut_29332

theorem selected_cut_29333 : selected 8 ⟨740956, by decide⟩
    (prefixPartial 13 373913) = some ⟨13, 2, 0, 740956, 373913, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_373913_740956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373913 ⟨740956, by decide⟩ :=
  accepted_of_selected 13 373913 ⟨740956, by decide⟩ ⟨13, 2, 0, 740956, 373913, 1693, 16384⟩
    (by decide) selected_cut_29333

theorem selected_cut_29334 : selected 8 ⟨740976, by decide⟩
    (prefixPartial 13 373914) = some ⟨13, 2, 0, 740976, 373914, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_373914_740976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373914 ⟨740976, by decide⟩ :=
  accepted_of_selected 13 373914 ⟨740976, by decide⟩ ⟨13, 2, 0, 740976, 373914, 1353, 16384⟩
    (by decide) selected_cut_29334

theorem selected_cut_29335 : selected 8 ⟨740985, by decide⟩
    (prefixPartial 13 373915) = some ⟨13, 2, 0, 740985, 373915, 881, 16384⟩ := by
  decide +kernel

theorem context_13_373915_740985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373915 ⟨740985, by decide⟩ :=
  accepted_of_selected 13 373915 ⟨740985, by decide⟩ ⟨13, 2, 0, 740985, 373915, 881, 16384⟩
    (by decide) selected_cut_29335

theorem unmarked_context_12_93478_740986 : frontier 9 ⟨740986, by decide⟩
    (prefixCache 12 93478) (prefixPartial 12 93478) = false := by
  decide +kernel

theorem node_context_12_93478_740986 : EJMOriginalGlobalDAGData.nodes 9 ⟨740986, by decide⟩ =
    .split (coordinate 12) (![⟨740929, by decide⟩,⟨740956, by decide⟩,⟨740976, by decide⟩,⟨740985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93478_740986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93478 ⟨740986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93478
    ⟨740986, by decide⟩ (by decide) (![⟨740929, by decide⟩,⟨740956, by decide⟩,⟨740976, by decide⟩,⟨740985, by decide⟩]) unmarked_context_12_93478_740986 node_context_12_93478_740986
  intro a
  fin_cases a
  · exact context_13_373912_740929
  · exact context_13_373913_740956
  · exact context_13_373914_740976
  · exact context_13_373915_740985

theorem selected_cut_29336 : selected 8 ⟨741007, by decide⟩
    (prefixPartial 13 373916) = some ⟨13, 2, 0, 741007, 373916, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_373916_741007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373916 ⟨741007, by decide⟩ :=
  accepted_of_selected 13 373916 ⟨741007, by decide⟩ ⟨13, 2, 0, 741007, 373916, 1225, 16384⟩
    (by decide) selected_cut_29336

theorem selected_cut_29337 : selected 8 ⟨741033, by decide⟩
    (prefixPartial 13 373917) = some ⟨13, 2, 0, 741033, 373917, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_373917_741033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373917 ⟨741033, by decide⟩ :=
  accepted_of_selected 13 373917 ⟨741033, by decide⟩ ⟨13, 2, 0, 741033, 373917, 1641, 16384⟩
    (by decide) selected_cut_29337

theorem selected_cut_29338 : selected 8 ⟨741056, by decide⟩
    (prefixPartial 13 373918) = some ⟨13, 2, 0, 741056, 373918, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_373918_741056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373918 ⟨741056, by decide⟩ :=
  accepted_of_selected 13 373918 ⟨741056, by decide⟩ ⟨13, 2, 0, 741056, 373918, 1689, 16384⟩
    (by decide) selected_cut_29338

theorem selected_cut_29339 : selected 8 ⟨741061, by decide⟩
    (prefixPartial 13 373919) = some ⟨13, 2, 0, 741061, 373919, 857, 16384⟩ := by
  decide +kernel

theorem context_13_373919_741061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373919 ⟨741061, by decide⟩ :=
  accepted_of_selected 13 373919 ⟨741061, by decide⟩ ⟨13, 2, 0, 741061, 373919, 857, 16384⟩
    (by decide) selected_cut_29339

theorem unmarked_context_12_93479_741062 : frontier 9 ⟨741062, by decide⟩
    (prefixCache 12 93479) (prefixPartial 12 93479) = false := by
  decide +kernel

theorem node_context_12_93479_741062 : EJMOriginalGlobalDAGData.nodes 9 ⟨741062, by decide⟩ =
    .split (coordinate 12) (![⟨741007, by decide⟩,⟨741033, by decide⟩,⟨741056, by decide⟩,⟨741061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93479_741062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93479 ⟨741062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93479
    ⟨741062, by decide⟩ (by decide) (![⟨741007, by decide⟩,⟨741033, by decide⟩,⟨741056, by decide⟩,⟨741061, by decide⟩]) unmarked_context_12_93479_741062 node_context_12_93479_741062
  intro a
  fin_cases a
  · exact context_13_373916_741007
  · exact context_13_373917_741033
  · exact context_13_373918_741056
  · exact context_13_373919_741061

theorem unmarked_context_11_23369_741063 : frontier 10 ⟨741063, by decide⟩
    (prefixCache 11 23369) (prefixPartial 11 23369) = false := by
  decide +kernel

theorem node_context_11_23369_741063 : EJMOriginalGlobalDAGData.nodes 10 ⟨741063, by decide⟩ =
    .split (coordinate 11) (![⟨740908, by decide⟩,⟨719134, by decide⟩,⟨740986, by decide⟩,⟨741062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23369_741063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23369 ⟨741063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23369
    ⟨741063, by decide⟩ (by decide) (![⟨740908, by decide⟩,⟨719134, by decide⟩,⟨740986, by decide⟩,⟨741062, by decide⟩]) unmarked_context_11_23369_741063 node_context_11_23369_741063
  intro a
  fin_cases a
  · exact context_12_93476_740908
  · exact context_12_93477_719134
  · exact context_12_93478_740986
  · exact context_12_93479_741062

theorem selected_cut_29340 : selected 8 ⟨741080, by decide⟩
    (prefixPartial 13 373920) = some ⟨13, 2, 0, 741080, 373920, 973, 16384⟩ := by
  decide +kernel

theorem context_13_373920_741080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373920 ⟨741080, by decide⟩ :=
  accepted_of_selected 13 373920 ⟨741080, by decide⟩ ⟨13, 2, 0, 741080, 373920, 973, 16384⟩
    (by decide) selected_cut_29340

theorem selected_cut_29341 : selected 8 ⟨741104, by decide⟩
    (prefixPartial 13 373921) = some ⟨13, 2, 0, 741104, 373921, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_373921_741104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373921 ⟨741104, by decide⟩ :=
  accepted_of_selected 13 373921 ⟨741104, by decide⟩ ⟨13, 2, 0, 741104, 373921, 1653, 16384⟩
    (by decide) selected_cut_29341

theorem selected_cut_29342 : selected 8 ⟨741125, by decide⟩
    (prefixPartial 13 373922) = some ⟨13, 2, 0, 741125, 373922, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_373922_741125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373922 ⟨741125, by decide⟩ :=
  accepted_of_selected 13 373922 ⟨741125, by decide⟩ ⟨13, 2, 0, 741125, 373922, 1645, 16384⟩
    (by decide) selected_cut_29342

theorem selected_cut_29343 : selected 8 ⟨741134, by decide⟩
    (prefixPartial 13 373923) = some ⟨13, 2, 0, 741134, 373923, 929, 16384⟩ := by
  decide +kernel

theorem context_13_373923_741134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373923 ⟨741134, by decide⟩ :=
  accepted_of_selected 13 373923 ⟨741134, by decide⟩ ⟨13, 2, 0, 741134, 373923, 929, 16384⟩
    (by decide) selected_cut_29343

theorem unmarked_context_12_93480_741135 : frontier 9 ⟨741135, by decide⟩
    (prefixCache 12 93480) (prefixPartial 12 93480) = false := by
  decide +kernel

theorem node_context_12_93480_741135 : EJMOriginalGlobalDAGData.nodes 9 ⟨741135, by decide⟩ =
    .split (coordinate 12) (![⟨741080, by decide⟩,⟨741104, by decide⟩,⟨741125, by decide⟩,⟨741134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93480_741135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93480 ⟨741135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93480
    ⟨741135, by decide⟩ (by decide) (![⟨741080, by decide⟩,⟨741104, by decide⟩,⟨741125, by decide⟩,⟨741134, by decide⟩]) unmarked_context_12_93480_741135 node_context_12_93480_741135
  intro a
  fin_cases a
  · exact context_13_373920_741080
  · exact context_13_373921_741104
  · exact context_13_373922_741125
  · exact context_13_373923_741134

theorem selected_cut_29344 : selected 8 ⟨741157, by decide⟩
    (prefixPartial 13 373924) = some ⟨13, 2, 0, 741157, 373924, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_373924_741157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373924 ⟨741157, by decide⟩ :=
  accepted_of_selected 13 373924 ⟨741157, by decide⟩ ⟨13, 2, 0, 741157, 373924, 1057, 16384⟩
    (by decide) selected_cut_29344

theorem selected_cut_29345 : selected 8 ⟨741181, by decide⟩
    (prefixPartial 13 373925) = some ⟨13, 2, 0, 741181, 373925, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_373925_741181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373925 ⟨741181, by decide⟩ :=
  accepted_of_selected 13 373925 ⟨741181, by decide⟩ ⟨13, 2, 0, 741181, 373925, 1473, 16384⟩
    (by decide) selected_cut_29345

theorem selected_cut_29346 : selected 8 ⟨741200, by decide⟩
    (prefixPartial 13 373926) = some ⟨13, 2, 0, 741200, 373926, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_373926_741200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373926 ⟨741200, by decide⟩ :=
  accepted_of_selected 13 373926 ⟨741200, by decide⟩ ⟨13, 2, 0, 741200, 373926, 1761, 16384⟩
    (by decide) selected_cut_29346

theorem selected_cut_29347 : selected 8 ⟨741206, by decide⟩
    (prefixPartial 13 373927) = some ⟨13, 2, 0, 741206, 373927, 905, 16384⟩ := by
  decide +kernel

theorem context_13_373927_741206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373927 ⟨741206, by decide⟩ :=
  accepted_of_selected 13 373927 ⟨741206, by decide⟩ ⟨13, 2, 0, 741206, 373927, 905, 16384⟩
    (by decide) selected_cut_29347

theorem unmarked_context_12_93481_741207 : frontier 9 ⟨741207, by decide⟩
    (prefixCache 12 93481) (prefixPartial 12 93481) = false := by
  decide +kernel

theorem node_context_12_93481_741207 : EJMOriginalGlobalDAGData.nodes 9 ⟨741207, by decide⟩ =
    .split (coordinate 12) (![⟨741157, by decide⟩,⟨741181, by decide⟩,⟨741200, by decide⟩,⟨741206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93481_741207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93481 ⟨741207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93481
    ⟨741207, by decide⟩ (by decide) (![⟨741157, by decide⟩,⟨741181, by decide⟩,⟨741200, by decide⟩,⟨741206, by decide⟩]) unmarked_context_12_93481_741207 node_context_12_93481_741207
  intro a
  fin_cases a
  · exact context_13_373924_741157
  · exact context_13_373925_741181
  · exact context_13_373926_741200
  · exact context_13_373927_741206

theorem selected_cut_29348 : selected 8 ⟨741227, by decide⟩
    (prefixPartial 13 373928) = some ⟨13, 2, 0, 741227, 373928, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_373928_741227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373928 ⟨741227, by decide⟩ :=
  accepted_of_selected 13 373928 ⟨741227, by decide⟩ ⟨13, 2, 0, 741227, 373928, 1013, 16384⟩
    (by decide) selected_cut_29348

theorem selected_cut_29349 : selected 8 ⟨741253, by decide⟩
    (prefixPartial 13 373929) = some ⟨13, 2, 0, 741253, 373929, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_373929_741253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373929 ⟨741253, by decide⟩ :=
  accepted_of_selected 13 373929 ⟨741253, by decide⟩ ⟨13, 2, 0, 741253, 373929, 1797, 16384⟩
    (by decide) selected_cut_29349

theorem selected_cut_29350 : selected 8 ⟨741274, by decide⟩
    (prefixPartial 13 373930) = some ⟨13, 2, 0, 741274, 373930, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_373930_741274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373930 ⟨741274, by decide⟩ :=
  accepted_of_selected 13 373930 ⟨741274, by decide⟩ ⟨13, 2, 0, 741274, 373930, 1577, 16384⟩
    (by decide) selected_cut_29350

theorem selected_cut_29351 : selected 8 ⟨741283, by decide⟩
    (prefixPartial 13 373931) = some ⟨13, 2, 0, 741283, 373931, 957, 16384⟩ := by
  decide +kernel

theorem context_13_373931_741283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373931 ⟨741283, by decide⟩ :=
  accepted_of_selected 13 373931 ⟨741283, by decide⟩ ⟨13, 2, 0, 741283, 373931, 957, 16384⟩
    (by decide) selected_cut_29351

theorem unmarked_context_12_93482_741284 : frontier 9 ⟨741284, by decide⟩
    (prefixCache 12 93482) (prefixPartial 12 93482) = false := by
  decide +kernel

theorem node_context_12_93482_741284 : EJMOriginalGlobalDAGData.nodes 9 ⟨741284, by decide⟩ =
    .split (coordinate 12) (![⟨741227, by decide⟩,⟨741253, by decide⟩,⟨741274, by decide⟩,⟨741283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93482_741284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93482 ⟨741284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93482
    ⟨741284, by decide⟩ (by decide) (![⟨741227, by decide⟩,⟨741253, by decide⟩,⟨741274, by decide⟩,⟨741283, by decide⟩]) unmarked_context_12_93482_741284 node_context_12_93482_741284
  intro a
  fin_cases a
  · exact context_13_373928_741227
  · exact context_13_373929_741253
  · exact context_13_373930_741274
  · exact context_13_373931_741283

theorem selected_cut_29352 : selected 8 ⟨741299, by decide⟩
    (prefixPartial 13 373932) = some ⟨13, 2, 0, 741299, 373932, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_373932_741299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373932 ⟨741299, by decide⟩ :=
  accepted_of_selected 13 373932 ⟨741299, by decide⟩ ⟨13, 2, 0, 741299, 373932, 1005, 16384⟩
    (by decide) selected_cut_29352

theorem selected_cut_29353 : selected 8 ⟨741326, by decide⟩
    (prefixPartial 13 373933) = some ⟨13, 2, 0, 741326, 373933, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_373933_741326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373933 ⟨741326, by decide⟩ :=
  accepted_of_selected 13 373933 ⟨741326, by decide⟩ ⟨13, 2, 0, 741326, 373933, 1881, 16384⟩
    (by decide) selected_cut_29353

theorem selected_cut_29354 : selected 8 ⟨741350, by decide⟩
    (prefixPartial 13 373934) = some ⟨13, 2, 0, 741350, 373934, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_373934_741350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373934 ⟨741350, by decide⟩ :=
  accepted_of_selected 13 373934 ⟨741350, by decide⟩ ⟨13, 2, 0, 741350, 373934, 1957, 16384⟩
    (by decide) selected_cut_29354

theorem selected_cut_29355 : selected 8 ⟨741359, by decide⟩
    (prefixPartial 13 373935) = some ⟨13, 2, 0, 741359, 373935, 913, 16384⟩ := by
  decide +kernel

theorem context_13_373935_741359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373935 ⟨741359, by decide⟩ :=
  accepted_of_selected 13 373935 ⟨741359, by decide⟩ ⟨13, 2, 0, 741359, 373935, 913, 16384⟩
    (by decide) selected_cut_29355

theorem unmarked_context_12_93483_741360 : frontier 9 ⟨741360, by decide⟩
    (prefixCache 12 93483) (prefixPartial 12 93483) = false := by
  decide +kernel

theorem node_context_12_93483_741360 : EJMOriginalGlobalDAGData.nodes 9 ⟨741360, by decide⟩ =
    .split (coordinate 12) (![⟨741299, by decide⟩,⟨741326, by decide⟩,⟨741350, by decide⟩,⟨741359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93483_741360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93483 ⟨741360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93483
    ⟨741360, by decide⟩ (by decide) (![⟨741299, by decide⟩,⟨741326, by decide⟩,⟨741350, by decide⟩,⟨741359, by decide⟩]) unmarked_context_12_93483_741360 node_context_12_93483_741360
  intro a
  fin_cases a
  · exact context_13_373932_741299
  · exact context_13_373933_741326
  · exact context_13_373934_741350
  · exact context_13_373935_741359

theorem unmarked_context_11_23370_741361 : frontier 10 ⟨741361, by decide⟩
    (prefixCache 11 23370) (prefixPartial 11 23370) = false := by
  decide +kernel

theorem node_context_11_23370_741361 : EJMOriginalGlobalDAGData.nodes 10 ⟨741361, by decide⟩ =
    .split (coordinate 11) (![⟨741135, by decide⟩,⟨741207, by decide⟩,⟨741284, by decide⟩,⟨741360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23370_741361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23370 ⟨741361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23370
    ⟨741361, by decide⟩ (by decide) (![⟨741135, by decide⟩,⟨741207, by decide⟩,⟨741284, by decide⟩,⟨741360, by decide⟩]) unmarked_context_11_23370_741361 node_context_11_23370_741361
  intro a
  fin_cases a
  · exact context_12_93480_741135
  · exact context_12_93481_741207
  · exact context_12_93482_741284
  · exact context_12_93483_741360

theorem selected_cut_29356 : selected 8 ⟨741374, by decide⟩
    (prefixPartial 13 373936) = some ⟨13, 2, 0, 741374, 373936, 793, 16384⟩ := by
  decide +kernel

theorem context_13_373936_741374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373936 ⟨741374, by decide⟩ :=
  accepted_of_selected 13 373936 ⟨741374, by decide⟩ ⟨13, 2, 0, 741374, 373936, 793, 16384⟩
    (by decide) selected_cut_29356

theorem selected_cut_29357 : selected 8 ⟨741397, by decide⟩
    (prefixPartial 13 373937) = some ⟨13, 2, 0, 741397, 373937, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_373937_741397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373937 ⟨741397, by decide⟩ :=
  accepted_of_selected 13 373937 ⟨741397, by decide⟩ ⟨13, 2, 0, 741397, 373937, 1709, 16384⟩
    (by decide) selected_cut_29357

theorem selected_cut_29358 : selected 8 ⟨741414, by decide⟩
    (prefixPartial 13 373938) = some ⟨13, 2, 0, 741414, 373938, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_373938_741414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373938 ⟨741414, by decide⟩ :=
  accepted_of_selected 13 373938 ⟨741414, by decide⟩ ⟨13, 2, 0, 741414, 373938, 1249, 16384⟩
    (by decide) selected_cut_29358

theorem selected_cut_29359 : selected 8 ⟨741422, by decide⟩
    (prefixPartial 13 373939) = some ⟨13, 2, 0, 741422, 373939, 945, 16384⟩ := by
  decide +kernel

theorem context_13_373939_741422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373939 ⟨741422, by decide⟩ :=
  accepted_of_selected 13 373939 ⟨741422, by decide⟩ ⟨13, 2, 0, 741422, 373939, 945, 16384⟩
    (by decide) selected_cut_29359

theorem unmarked_context_12_93484_741423 : frontier 9 ⟨741423, by decide⟩
    (prefixCache 12 93484) (prefixPartial 12 93484) = false := by
  decide +kernel

theorem node_context_12_93484_741423 : EJMOriginalGlobalDAGData.nodes 9 ⟨741423, by decide⟩ =
    .split (coordinate 12) (![⟨741374, by decide⟩,⟨741397, by decide⟩,⟨741414, by decide⟩,⟨741422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93484_741423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93484 ⟨741423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93484
    ⟨741423, by decide⟩ (by decide) (![⟨741374, by decide⟩,⟨741397, by decide⟩,⟨741414, by decide⟩,⟨741422, by decide⟩]) unmarked_context_12_93484_741423 node_context_12_93484_741423
  intro a
  fin_cases a
  · exact context_13_373936_741374
  · exact context_13_373937_741397
  · exact context_13_373938_741414
  · exact context_13_373939_741422

theorem selected_cut_29360 : selected 8 ⟨741434, by decide⟩
    (prefixPartial 13 373940) = some ⟨13, 2, 0, 741434, 373940, 745, 16384⟩ := by
  decide +kernel

theorem context_13_373940_741434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373940 ⟨741434, by decide⟩ :=
  accepted_of_selected 13 373940 ⟨741434, by decide⟩ ⟨13, 2, 0, 741434, 373940, 745, 16384⟩
    (by decide) selected_cut_29360

theorem selected_cut_29361 : selected 8 ⟨741461, by decide⟩
    (prefixPartial 13 373941) = some ⟨13, 2, 0, 741461, 373941, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_373941_741461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373941 ⟨741461, by decide⟩ :=
  accepted_of_selected 13 373941 ⟨741461, by decide⟩ ⟨13, 2, 0, 741461, 373941, 1521, 16384⟩
    (by decide) selected_cut_29361

theorem selected_cut_29362 : selected 8 ⟨741481, by decide⟩
    (prefixPartial 13 373942) = some ⟨13, 2, 0, 741481, 373942, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_373942_741481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373942 ⟨741481, by decide⟩ :=
  accepted_of_selected 13 373942 ⟨741481, by decide⟩ ⟨13, 2, 0, 741481, 373942, 1425, 16384⟩
    (by decide) selected_cut_29362

theorem selected_cut_29363 : selected 8 ⟨741488, by decide⟩
    (prefixPartial 13 373943) = some ⟨13, 2, 0, 741488, 373943, 913, 16384⟩ := by
  decide +kernel

theorem context_13_373943_741488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373943 ⟨741488, by decide⟩ :=
  accepted_of_selected 13 373943 ⟨741488, by decide⟩ ⟨13, 2, 0, 741488, 373943, 913, 16384⟩
    (by decide) selected_cut_29363

theorem unmarked_context_12_93485_741489 : frontier 9 ⟨741489, by decide⟩
    (prefixCache 12 93485) (prefixPartial 12 93485) = false := by
  decide +kernel

theorem node_context_12_93485_741489 : EJMOriginalGlobalDAGData.nodes 9 ⟨741489, by decide⟩ =
    .split (coordinate 12) (![⟨741434, by decide⟩,⟨741461, by decide⟩,⟨741481, by decide⟩,⟨741488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93485_741489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93485 ⟨741489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93485
    ⟨741489, by decide⟩ (by decide) (![⟨741434, by decide⟩,⟨741461, by decide⟩,⟨741481, by decide⟩,⟨741488, by decide⟩]) unmarked_context_12_93485_741489 node_context_12_93485_741489
  intro a
  fin_cases a
  · exact context_13_373940_741434
  · exact context_13_373941_741461
  · exact context_13_373942_741481
  · exact context_13_373943_741488

theorem selected_cut_29364 : selected 8 ⟨741503, by decide⟩
    (prefixPartial 13 373944) = some ⟨13, 2, 0, 741503, 373944, 801, 16384⟩ := by
  decide +kernel

theorem context_13_373944_741503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373944 ⟨741503, by decide⟩ :=
  accepted_of_selected 13 373944 ⟨741503, by decide⟩ ⟨13, 2, 0, 741503, 373944, 801, 16384⟩
    (by decide) selected_cut_29364

theorem selected_cut_29365 : selected 8 ⟨741528, by decide⟩
    (prefixPartial 13 373945) = some ⟨13, 2, 0, 741528, 373945, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_373945_741528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373945 ⟨741528, by decide⟩ :=
  accepted_of_selected 13 373945 ⟨741528, by decide⟩ ⟨13, 2, 0, 741528, 373945, 1853, 16384⟩
    (by decide) selected_cut_29365

theorem selected_cut_29366 : selected 8 ⟨741547, by decide⟩
    (prefixPartial 13 373946) = some ⟨13, 2, 0, 741547, 373946, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_373946_741547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373946 ⟨741547, by decide⟩ :=
  accepted_of_selected 13 373946 ⟨741547, by decide⟩ ⟨13, 2, 0, 741547, 373946, 1349, 16384⟩
    (by decide) selected_cut_29366

theorem selected_cut_29367 : selected 8 ⟨741552, by decide⟩
    (prefixPartial 13 373947) = some ⟨13, 2, 0, 741552, 373947, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_373947_741552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373947 ⟨741552, by decide⟩ :=
  accepted_of_selected 13 373947 ⟨741552, by decide⟩ ⟨13, 2, 0, 741552, 373947, 1033, 16384⟩
    (by decide) selected_cut_29367

theorem unmarked_context_12_93486_741553 : frontier 9 ⟨741553, by decide⟩
    (prefixCache 12 93486) (prefixPartial 12 93486) = false := by
  decide +kernel

theorem node_context_12_93486_741553 : EJMOriginalGlobalDAGData.nodes 9 ⟨741553, by decide⟩ =
    .split (coordinate 12) (![⟨741503, by decide⟩,⟨741528, by decide⟩,⟨741547, by decide⟩,⟨741552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93486_741553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93486 ⟨741553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93486
    ⟨741553, by decide⟩ (by decide) (![⟨741503, by decide⟩,⟨741528, by decide⟩,⟨741547, by decide⟩,⟨741552, by decide⟩]) unmarked_context_12_93486_741553 node_context_12_93486_741553
  intro a
  fin_cases a
  · exact context_13_373944_741503
  · exact context_13_373945_741528
  · exact context_13_373946_741547
  · exact context_13_373947_741552

theorem selected_cut_29368 : selected 8 ⟨741567, by decide⟩
    (prefixPartial 13 373948) = some ⟨13, 2, 0, 741567, 373948, 741, 16384⟩ := by
  decide +kernel

theorem context_13_373948_741567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373948 ⟨741567, by decide⟩ :=
  accepted_of_selected 13 373948 ⟨741567, by decide⟩ ⟨13, 2, 0, 741567, 373948, 741, 16384⟩
    (by decide) selected_cut_29368

theorem selected_cut_29369 : selected 8 ⟨741590, by decide⟩
    (prefixPartial 13 373949) = some ⟨13, 2, 0, 741590, 373949, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_373949_741590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373949 ⟨741590, by decide⟩ :=
  accepted_of_selected 13 373949 ⟨741590, by decide⟩ ⟨13, 2, 0, 741590, 373949, 1845, 16384⟩
    (by decide) selected_cut_29369

theorem selected_cut_29370 : selected 8 ⟨741609, by decide⟩
    (prefixPartial 13 373950) = some ⟨13, 2, 0, 741609, 373950, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_373950_741609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373950 ⟨741609, by decide⟩ :=
  accepted_of_selected 13 373950 ⟨741609, by decide⟩ ⟨13, 2, 0, 741609, 373950, 1585, 16384⟩
    (by decide) selected_cut_29370

theorem selected_cut_29371 : selected 8 ⟨741614, by decide⟩
    (prefixPartial 13 373951) = some ⟨13, 2, 0, 741614, 373951, 981, 16384⟩ := by
  decide +kernel

theorem context_13_373951_741614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373951 ⟨741614, by decide⟩ :=
  accepted_of_selected 13 373951 ⟨741614, by decide⟩ ⟨13, 2, 0, 741614, 373951, 981, 16384⟩
    (by decide) selected_cut_29371

theorem unmarked_context_12_93487_741615 : frontier 9 ⟨741615, by decide⟩
    (prefixCache 12 93487) (prefixPartial 12 93487) = false := by
  decide +kernel

theorem node_context_12_93487_741615 : EJMOriginalGlobalDAGData.nodes 9 ⟨741615, by decide⟩ =
    .split (coordinate 12) (![⟨741567, by decide⟩,⟨741590, by decide⟩,⟨741609, by decide⟩,⟨741614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93487_741615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93487 ⟨741615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93487
    ⟨741615, by decide⟩ (by decide) (![⟨741567, by decide⟩,⟨741590, by decide⟩,⟨741609, by decide⟩,⟨741614, by decide⟩]) unmarked_context_12_93487_741615 node_context_12_93487_741615
  intro a
  fin_cases a
  · exact context_13_373948_741567
  · exact context_13_373949_741590
  · exact context_13_373950_741609
  · exact context_13_373951_741614

theorem unmarked_context_11_23371_741616 : frontier 10 ⟨741616, by decide⟩
    (prefixCache 11 23371) (prefixPartial 11 23371) = false := by
  decide +kernel

theorem node_context_11_23371_741616 : EJMOriginalGlobalDAGData.nodes 10 ⟨741616, by decide⟩ =
    .split (coordinate 11) (![⟨741423, by decide⟩,⟨741489, by decide⟩,⟨741553, by decide⟩,⟨741615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23371_741616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23371 ⟨741616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23371
    ⟨741616, by decide⟩ (by decide) (![⟨741423, by decide⟩,⟨741489, by decide⟩,⟨741553, by decide⟩,⟨741615, by decide⟩]) unmarked_context_11_23371_741616 node_context_11_23371_741616
  intro a
  fin_cases a
  · exact context_12_93484_741423
  · exact context_12_93485_741489
  · exact context_12_93486_741553
  · exact context_12_93487_741615

theorem unmarked_context_10_5842_741617 : frontier 11 ⟨741617, by decide⟩
    (prefixCache 10 5842) (prefixPartial 10 5842) = false := by
  decide +kernel

theorem node_context_10_5842_741617 : EJMOriginalGlobalDAGData.nodes 11 ⟨741617, by decide⟩ =
    .split (coordinate 10) (![⟨740836, by decide⟩,⟨741063, by decide⟩,⟨741361, by decide⟩,⟨741616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5842_741617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5842 ⟨741617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5842
    ⟨741617, by decide⟩ (by decide) (![⟨740836, by decide⟩,⟨741063, by decide⟩,⟨741361, by decide⟩,⟨741616, by decide⟩]) unmarked_context_10_5842_741617 node_context_10_5842_741617
  intro a
  fin_cases a
  · exact context_11_23368_740836
  · exact context_11_23369_741063
  · exact context_11_23370_741361
  · exact context_11_23371_741616

theorem selected_cut_29372 : selected 8 ⟨741631, by decide⟩
    (prefixPartial 13 373952) = some ⟨13, 2, 0, 741631, 373952, 741, 16384⟩ := by
  decide +kernel

theorem context_13_373952_741631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373952 ⟨741631, by decide⟩ :=
  accepted_of_selected 13 373952 ⟨741631, by decide⟩ ⟨13, 2, 0, 741631, 373952, 741, 16384⟩
    (by decide) selected_cut_29372

theorem selected_cut_29373 : selected 8 ⟨741656, by decide⟩
    (prefixPartial 13 373953) = some ⟨13, 2, 0, 741656, 373953, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_373953_741656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373953 ⟨741656, by decide⟩ :=
  accepted_of_selected 13 373953 ⟨741656, by decide⟩ ⟨13, 2, 0, 741656, 373953, 1977, 16384⟩
    (by decide) selected_cut_29373

theorem selected_cut_29374 : selected 8 ⟨741676, by decide⟩
    (prefixPartial 13 373954) = some ⟨13, 2, 0, 741676, 373954, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_373954_741676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373954 ⟨741676, by decide⟩ :=
  accepted_of_selected 13 373954 ⟨741676, by decide⟩ ⟨13, 2, 0, 741676, 373954, 1601, 16384⟩
    (by decide) selected_cut_29374

theorem selected_cut_29375 : selected 8 ⟨741684, by decide⟩
    (prefixPartial 13 373955) = some ⟨13, 2, 0, 741684, 373955, 761, 16384⟩ := by
  decide +kernel

theorem context_13_373955_741684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373955 ⟨741684, by decide⟩ :=
  accepted_of_selected 13 373955 ⟨741684, by decide⟩ ⟨13, 2, 0, 741684, 373955, 761, 16384⟩
    (by decide) selected_cut_29375

theorem unmarked_context_12_93488_741685 : frontier 9 ⟨741685, by decide⟩
    (prefixCache 12 93488) (prefixPartial 12 93488) = false := by
  decide +kernel

theorem node_context_12_93488_741685 : EJMOriginalGlobalDAGData.nodes 9 ⟨741685, by decide⟩ =
    .split (coordinate 12) (![⟨741631, by decide⟩,⟨741656, by decide⟩,⟨741676, by decide⟩,⟨741684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93488_741685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93488 ⟨741685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93488
    ⟨741685, by decide⟩ (by decide) (![⟨741631, by decide⟩,⟨741656, by decide⟩,⟨741676, by decide⟩,⟨741684, by decide⟩]) unmarked_context_12_93488_741685 node_context_12_93488_741685
  intro a
  fin_cases a
  · exact context_13_373952_741631
  · exact context_13_373953_741656
  · exact context_13_373954_741676
  · exact context_13_373955_741684

theorem selected_cut_29376 : selected 8 ⟨741696, by decide⟩
    (prefixPartial 13 373956) = some ⟨13, 2, 0, 741696, 373956, 657, 16384⟩ := by
  decide +kernel

theorem context_13_373956_741696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373956 ⟨741696, by decide⟩ :=
  accepted_of_selected 13 373956 ⟨741696, by decide⟩ ⟨13, 2, 0, 741696, 373956, 657, 16384⟩
    (by decide) selected_cut_29376

theorem selected_cut_29377 : selected 8 ⟨741718, by decide⟩
    (prefixPartial 13 373957) = some ⟨13, 2, 0, 741718, 373957, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_373957_741718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373957 ⟨741718, by decide⟩ :=
  accepted_of_selected 13 373957 ⟨741718, by decide⟩ ⟨13, 2, 0, 741718, 373957, 1757, 16384⟩
    (by decide) selected_cut_29377

theorem selected_cut_29378 : selected 8 ⟨741736, by decide⟩
    (prefixPartial 13 373958) = some ⟨13, 2, 0, 741736, 373958, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_373958_741736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373958 ⟨741736, by decide⟩ :=
  accepted_of_selected 13 373958 ⟨741736, by decide⟩ ⟨13, 2, 0, 741736, 373958, 1717, 16384⟩
    (by decide) selected_cut_29378

theorem selected_cut_29379 : selected 8 ⟨741744, by decide⟩
    (prefixPartial 13 373959) = some ⟨13, 2, 0, 741744, 373959, 837, 16384⟩ := by
  decide +kernel

theorem context_13_373959_741744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373959 ⟨741744, by decide⟩ :=
  accepted_of_selected 13 373959 ⟨741744, by decide⟩ ⟨13, 2, 0, 741744, 373959, 837, 16384⟩
    (by decide) selected_cut_29379

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
