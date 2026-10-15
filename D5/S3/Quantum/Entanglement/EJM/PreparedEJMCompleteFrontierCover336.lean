/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover335
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_26982_829017 : frontier 10 ⟨829017, by decide⟩
    (prefixCache 11 26982) (prefixPartial 11 26982) = false := by
  decide +kernel

theorem node_context_11_26982_829017 : EJMOriginalGlobalDAGData.nodes 10 ⟨829017, by decide⟩ =
    .split (coordinate 11) (![⟨828976, by decide⟩,⟨828995, by decide⟩,⟨813979, by decide⟩,⟨829016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26982_829017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26982 ⟨829017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26982
    ⟨829017, by decide⟩ (by decide) (![⟨828976, by decide⟩,⟨828995, by decide⟩,⟨813979, by decide⟩,⟨829016, by decide⟩]) unmarked_context_11_26982_829017 node_context_11_26982_829017
  intro a
  fin_cases a
  · exact context_12_107928_828976
  · exact context_12_107929_828995
  · exact context_12_107930_813979
  · exact context_12_107931_829016

theorem selected_cut_32260 : selected 9 ⟨829040, by decide⟩
    (prefixPartial 12 107932) = some ⟨12, 2, 0, 829040, 107932, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_107932_829040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107932 ⟨829040, by decide⟩ :=
  accepted_of_selected 12 107932 ⟨829040, by decide⟩ ⟨12, 2, 0, 829040, 107932, 1813, 65536⟩
    (by decide) selected_cut_32260

theorem selected_cut_32261 : selected 9 ⟨829058, by decide⟩
    (prefixPartial 12 107933) = some ⟨12, 2, 0, 829058, 107933, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_107933_829058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107933 ⟨829058, by decide⟩ :=
  accepted_of_selected 12 107933 ⟨829058, by decide⟩ ⟨12, 2, 0, 829058, 107933, 1473, 65536⟩
    (by decide) selected_cut_32261

theorem selected_cut_32262 : selected 9 ⟨829102, by decide⟩
    (prefixPartial 12 107934) = some ⟨12, 2, 0, 829102, 107934, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_107934_829102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107934 ⟨829102, by decide⟩ :=
  accepted_of_selected 12 107934 ⟨829102, by decide⟩ ⟨12, 2, 0, 829102, 107934, 2201, 65536⟩
    (by decide) selected_cut_32262

theorem selected_cut_32263 : selected 9 ⟨829125, by decide⟩
    (prefixPartial 12 107935) = some ⟨12, 2, 0, 829125, 107935, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_107935_829125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107935 ⟨829125, by decide⟩ :=
  accepted_of_selected 12 107935 ⟨829125, by decide⟩ ⟨12, 2, 0, 829125, 107935, 1749, 65536⟩
    (by decide) selected_cut_32263

theorem unmarked_context_11_26983_829126 : frontier 10 ⟨829126, by decide⟩
    (prefixCache 11 26983) (prefixPartial 11 26983) = false := by
  decide +kernel

theorem node_context_11_26983_829126 : EJMOriginalGlobalDAGData.nodes 10 ⟨829126, by decide⟩ =
    .split (coordinate 11) (![⟨829040, by decide⟩,⟨829058, by decide⟩,⟨829102, by decide⟩,⟨829125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26983_829126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26983 ⟨829126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26983
    ⟨829126, by decide⟩ (by decide) (![⟨829040, by decide⟩,⟨829058, by decide⟩,⟨829102, by decide⟩,⟨829125, by decide⟩]) unmarked_context_11_26983_829126 node_context_11_26983_829126
  intro a
  fin_cases a
  · exact context_12_107932_829040
  · exact context_12_107933_829058
  · exact context_12_107934_829102
  · exact context_12_107935_829125

theorem unmarked_context_10_6745_829127 : frontier 11 ⟨829127, by decide⟩
    (prefixCache 10 6745) (prefixPartial 10 6745) = false := by
  decide +kernel

theorem node_context_10_6745_829127 : EJMOriginalGlobalDAGData.nodes 11 ⟨829127, by decide⟩ =
    .split (coordinate 10) (![⟨828957, by decide⟩,⟨828959, by decide⟩,⟨829017, by decide⟩,⟨829126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6745_829127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6745 ⟨829127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6745
    ⟨829127, by decide⟩ (by decide) (![⟨828957, by decide⟩,⟨828959, by decide⟩,⟨829017, by decide⟩,⟨829126, by decide⟩]) unmarked_context_10_6745_829127 node_context_10_6745_829127
  intro a
  fin_cases a
  · exact context_11_26980_828957
  · exact context_11_26981_828959
  · exact context_11_26982_829017
  · exact context_11_26983_829126

theorem selected_cut_32264 : selected 10 ⟨829176, by decide⟩
    (prefixPartial 11 26984) = some ⟨11, 2, 0, 829176, 26984, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_26984_829176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26984 ⟨829176, by decide⟩ :=
  accepted_of_selected 11 26984 ⟨829176, by decide⟩ ⟨11, 2, 0, 829176, 26984, 3949, 262144⟩
    (by decide) selected_cut_32264

theorem selected_cut_32265 : selected 10 ⟨829209, by decide⟩
    (prefixPartial 11 26985) = some ⟨11, 2, 0, 829209, 26985, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_26985_829209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26985 ⟨829209, by decide⟩ :=
  accepted_of_selected 11 26985 ⟨829209, by decide⟩ ⟨11, 2, 0, 829209, 26985, 2541, 262144⟩
    (by decide) selected_cut_32265

theorem selected_cut_32266 : selected 9 ⟨829229, by decide⟩
    (prefixPartial 12 107944) = some ⟨12, 2, 0, 829229, 107944, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_107944_829229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107944 ⟨829229, by decide⟩ :=
  accepted_of_selected 12 107944 ⟨829229, by decide⟩ ⟨12, 2, 0, 829229, 107944, 1557, 65536⟩
    (by decide) selected_cut_32266

theorem selected_cut_32267 : selected 9 ⟨829247, by decide⟩
    (prefixPartial 12 107945) = some ⟨12, 2, 0, 829247, 107945, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_107945_829247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107945 ⟨829247, by decide⟩ :=
  accepted_of_selected 12 107945 ⟨829247, by decide⟩ ⟨12, 2, 0, 829247, 107945, 1281, 65536⟩
    (by decide) selected_cut_32267

theorem selected_cut_32268 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 107946) = some ⟨12, 1, 0, 769937, 107946, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107946_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107946 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 107946 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 107946, 1, 65536⟩
    (by decide) selected_cut_32268

theorem selected_cut_32269 : selected 9 ⟨829270, by decide⟩
    (prefixPartial 12 107947) = some ⟨12, 2, 0, 829270, 107947, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_107947_829270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107947 ⟨829270, by decide⟩ :=
  accepted_of_selected 12 107947 ⟨829270, by decide⟩ ⟨12, 2, 0, 829270, 107947, 1317, 65536⟩
    (by decide) selected_cut_32269

theorem unmarked_context_11_26986_829271 : frontier 10 ⟨829271, by decide⟩
    (prefixCache 11 26986) (prefixPartial 11 26986) = false := by
  decide +kernel

theorem node_context_11_26986_829271 : EJMOriginalGlobalDAGData.nodes 10 ⟨829271, by decide⟩ =
    .split (coordinate 11) (![⟨829229, by decide⟩,⟨829247, by decide⟩,⟨769937, by decide⟩,⟨829270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26986_829271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26986 ⟨829271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26986
    ⟨829271, by decide⟩ (by decide) (![⟨829229, by decide⟩,⟨829247, by decide⟩,⟨769937, by decide⟩,⟨829270, by decide⟩]) unmarked_context_11_26986_829271 node_context_11_26986_829271
  intro a
  fin_cases a
  · exact context_12_107944_829229
  · exact context_12_107945_829247
  · exact context_12_107946_769937
  · exact context_12_107947_829270

theorem selected_cut_32270 : selected 10 ⟨829321, by decide⟩
    (prefixPartial 11 26987) = some ⟨11, 2, 0, 829321, 26987, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_26987_829321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26987 ⟨829321, by decide⟩ :=
  accepted_of_selected 11 26987 ⟨829321, by decide⟩ ⟨11, 2, 0, 829321, 26987, 3605, 262144⟩
    (by decide) selected_cut_32270

theorem unmarked_context_10_6746_829322 : frontier 11 ⟨829322, by decide⟩
    (prefixCache 10 6746) (prefixPartial 10 6746) = false := by
  decide +kernel

theorem node_context_10_6746_829322 : EJMOriginalGlobalDAGData.nodes 11 ⟨829322, by decide⟩ =
    .split (coordinate 10) (![⟨829176, by decide⟩,⟨829209, by decide⟩,⟨829271, by decide⟩,⟨829321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6746_829322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6746 ⟨829322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6746
    ⟨829322, by decide⟩ (by decide) (![⟨829176, by decide⟩,⟨829209, by decide⟩,⟨829271, by decide⟩,⟨829321, by decide⟩]) unmarked_context_10_6746_829322 node_context_10_6746_829322
  intro a
  fin_cases a
  · exact context_11_26984_829176
  · exact context_11_26985_829209
  · exact context_11_26986_829271
  · exact context_11_26987_829321

theorem selected_cut_32271 : selected 9 ⟨829334, by decide⟩
    (prefixPartial 12 107952) = some ⟨12, 2, 0, 829334, 107952, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_107952_829334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107952 ⟨829334, by decide⟩ :=
  accepted_of_selected 12 107952 ⟨829334, by decide⟩ ⟨12, 2, 0, 829334, 107952, 1057, 65536⟩
    (by decide) selected_cut_32271

theorem selected_cut_32272 : selected 9 ⟨829342, by decide⟩
    (prefixPartial 12 107953) = some ⟨12, 2, 0, 829342, 107953, 889, 65536⟩ := by
  decide +kernel

theorem context_12_107953_829342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107953 ⟨829342, by decide⟩ :=
  accepted_of_selected 12 107953 ⟨829342, by decide⟩ ⟨12, 2, 0, 829342, 107953, 889, 65536⟩
    (by decide) selected_cut_32272

theorem selected_cut_32273 : selected 9 ⟨829369, by decide⟩
    (prefixPartial 12 107954) = some ⟨12, 2, 0, 829369, 107954, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_107954_829369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107954 ⟨829369, by decide⟩ :=
  accepted_of_selected 12 107954 ⟨829369, by decide⟩ ⟨12, 2, 0, 829369, 107954, 1381, 65536⟩
    (by decide) selected_cut_32273

theorem selected_cut_32274 : selected 9 ⟨829381, by decide⟩
    (prefixPartial 12 107955) = some ⟨12, 2, 0, 829381, 107955, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_107955_829381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107955 ⟨829381, by decide⟩ :=
  accepted_of_selected 12 107955 ⟨829381, by decide⟩ ⟨12, 2, 0, 829381, 107955, 1025, 65536⟩
    (by decide) selected_cut_32274

theorem unmarked_context_11_26988_829382 : frontier 10 ⟨829382, by decide⟩
    (prefixCache 11 26988) (prefixPartial 11 26988) = false := by
  decide +kernel

theorem node_context_11_26988_829382 : EJMOriginalGlobalDAGData.nodes 10 ⟨829382, by decide⟩ =
    .split (coordinate 11) (![⟨829334, by decide⟩,⟨829342, by decide⟩,⟨829369, by decide⟩,⟨829381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26988_829382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26988 ⟨829382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26988
    ⟨829382, by decide⟩ (by decide) (![⟨829334, by decide⟩,⟨829342, by decide⟩,⟨829369, by decide⟩,⟨829381, by decide⟩]) unmarked_context_11_26988_829382 node_context_11_26988_829382
  intro a
  fin_cases a
  · exact context_12_107952_829334
  · exact context_12_107953_829342
  · exact context_12_107954_829369
  · exact context_12_107955_829381

theorem selected_cut_32275 : selected 10 ⟨829404, by decide⟩
    (prefixPartial 11 26989) = some ⟨11, 2, 0, 829404, 26989, 1629, 262144⟩ := by
  decide +kernel

theorem context_11_26989_829404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26989 ⟨829404, by decide⟩ :=
  accepted_of_selected 11 26989 ⟨829404, by decide⟩ ⟨11, 2, 0, 829404, 26989, 1629, 262144⟩
    (by decide) selected_cut_32275

theorem selected_cut_32276 : selected 10 ⟨829451, by decide⟩
    (prefixPartial 11 26990) = some ⟨11, 2, 0, 829451, 26990, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_26990_829451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26990 ⟨829451, by decide⟩ :=
  accepted_of_selected 11 26990 ⟨829451, by decide⟩ ⟨11, 2, 0, 829451, 26990, 2817, 262144⟩
    (by decide) selected_cut_32276

theorem selected_cut_32277 : selected 10 ⟨829483, by decide⟩
    (prefixPartial 11 26991) = some ⟨11, 2, 0, 829483, 26991, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_26991_829483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26991 ⟨829483, by decide⟩ :=
  accepted_of_selected 11 26991 ⟨829483, by decide⟩ ⟨11, 2, 0, 829483, 26991, 2361, 262144⟩
    (by decide) selected_cut_32277

theorem unmarked_context_10_6747_829484 : frontier 11 ⟨829484, by decide⟩
    (prefixCache 10 6747) (prefixPartial 10 6747) = false := by
  decide +kernel

theorem node_context_10_6747_829484 : EJMOriginalGlobalDAGData.nodes 11 ⟨829484, by decide⟩ =
    .split (coordinate 10) (![⟨829382, by decide⟩,⟨829404, by decide⟩,⟨829451, by decide⟩,⟨829483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6747_829484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6747 ⟨829484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6747
    ⟨829484, by decide⟩ (by decide) (![⟨829382, by decide⟩,⟨829404, by decide⟩,⟨829451, by decide⟩,⟨829483, by decide⟩]) unmarked_context_10_6747_829484 node_context_10_6747_829484
  intro a
  fin_cases a
  · exact context_11_26988_829382
  · exact context_11_26989_829404
  · exact context_11_26990_829451
  · exact context_11_26991_829483

theorem unmarked_context_9_1686_829485 : frontier 12 ⟨829485, by decide⟩
    (prefixCache 9 1686) (prefixPartial 9 1686) = false := by
  decide +kernel

theorem node_context_9_1686_829485 : EJMOriginalGlobalDAGData.nodes 12 ⟨829485, by decide⟩ =
    .split (coordinate 9) (![⟨828848, by decide⟩,⟨829127, by decide⟩,⟨829322, by decide⟩,⟨829484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1686_829485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1686 ⟨829485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1686
    ⟨829485, by decide⟩ (by decide) (![⟨828848, by decide⟩,⟨829127, by decide⟩,⟨829322, by decide⟩,⟨829484, by decide⟩]) unmarked_context_9_1686_829485 node_context_9_1686_829485
  intro a
  fin_cases a
  · exact context_10_6744_828848
  · exact context_10_6745_829127
  · exact context_10_6746_829322
  · exact context_10_6747_829484

theorem selected_cut_32278 : selected 10 ⟨829535, by decide⟩
    (prefixPartial 11 26992) = some ⟨11, 2, 0, 829535, 26992, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_26992_829535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26992 ⟨829535, by decide⟩ :=
  accepted_of_selected 11 26992 ⟨829535, by decide⟩ ⟨11, 2, 0, 829535, 26992, 3565, 262144⟩
    (by decide) selected_cut_32278

theorem selected_cut_32279 : selected 10 ⟨829563, by decide⟩
    (prefixPartial 11 26993) = some ⟨11, 2, 0, 829563, 26993, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_26993_829563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26993 ⟨829563, by decide⟩ :=
  accepted_of_selected 11 26993 ⟨829563, by decide⟩ ⟨11, 2, 0, 829563, 26993, 2309, 262144⟩
    (by decide) selected_cut_32279

theorem selected_cut_32280 : selected 10 ⟨829597, by decide⟩
    (prefixPartial 11 26994) = some ⟨11, 2, 0, 829597, 26994, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_26994_829597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26994 ⟨829597, by decide⟩ :=
  accepted_of_selected 11 26994 ⟨829597, by decide⟩ ⟨11, 2, 0, 829597, 26994, 2961, 262144⟩
    (by decide) selected_cut_32280

theorem selected_cut_32281 : selected 10 ⟨829631, by decide⟩
    (prefixPartial 11 26995) = some ⟨11, 2, 0, 829631, 26995, 3093, 262144⟩ := by
  decide +kernel

theorem context_11_26995_829631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26995 ⟨829631, by decide⟩ :=
  accepted_of_selected 11 26995 ⟨829631, by decide⟩ ⟨11, 2, 0, 829631, 26995, 3093, 262144⟩
    (by decide) selected_cut_32281

theorem unmarked_context_10_6748_829632 : frontier 11 ⟨829632, by decide⟩
    (prefixCache 10 6748) (prefixPartial 10 6748) = false := by
  decide +kernel

theorem node_context_10_6748_829632 : EJMOriginalGlobalDAGData.nodes 11 ⟨829632, by decide⟩ =
    .split (coordinate 10) (![⟨829535, by decide⟩,⟨829563, by decide⟩,⟨829597, by decide⟩,⟨829631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6748_829632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6748 ⟨829632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6748
    ⟨829632, by decide⟩ (by decide) (![⟨829535, by decide⟩,⟨829563, by decide⟩,⟨829597, by decide⟩,⟨829631, by decide⟩]) unmarked_context_10_6748_829632 node_context_10_6748_829632
  intro a
  fin_cases a
  · exact context_11_26992_829535
  · exact context_11_26993_829563
  · exact context_11_26994_829597
  · exact context_11_26995_829631

theorem selected_cut_32282 : selected 10 ⟨829656, by decide⟩
    (prefixPartial 11 26996) = some ⟨11, 2, 0, 829656, 26996, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_26996_829656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26996 ⟨829656, by decide⟩ :=
  accepted_of_selected 11 26996 ⟨829656, by decide⟩ ⟨11, 2, 0, 829656, 26996, 2421, 262144⟩
    (by decide) selected_cut_32282

theorem selected_cut_32283 : selected 10 ⟨829659, by decide⟩
    (prefixPartial 11 26997) = some ⟨11, 2, 0, 829659, 26997, 5, 262144⟩ := by
  decide +kernel

theorem context_11_26997_829659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26997 ⟨829659, by decide⟩ :=
  accepted_of_selected 11 26997 ⟨829659, by decide⟩ ⟨11, 2, 0, 829659, 26997, 5, 262144⟩
    (by decide) selected_cut_32283

theorem selected_cut_32284 : selected 10 ⟨829680, by decide⟩
    (prefixPartial 11 26998) = some ⟨11, 2, 0, 829680, 26998, 1901, 262144⟩ := by
  decide +kernel

theorem context_11_26998_829680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26998 ⟨829680, by decide⟩ :=
  accepted_of_selected 11 26998 ⟨829680, by decide⟩ ⟨11, 2, 0, 829680, 26998, 1901, 262144⟩
    (by decide) selected_cut_32284

theorem selected_cut_32285 : selected 10 ⟨829708, by decide⟩
    (prefixPartial 11 26999) = some ⟨11, 2, 0, 829708, 26999, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_26999_829708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26999 ⟨829708, by decide⟩ :=
  accepted_of_selected 11 26999 ⟨829708, by decide⟩ ⟨11, 2, 0, 829708, 26999, 2041, 262144⟩
    (by decide) selected_cut_32285

theorem unmarked_context_10_6749_829709 : frontier 11 ⟨829709, by decide⟩
    (prefixCache 10 6749) (prefixPartial 10 6749) = false := by
  decide +kernel

theorem node_context_10_6749_829709 : EJMOriginalGlobalDAGData.nodes 11 ⟨829709, by decide⟩ =
    .split (coordinate 10) (![⟨829656, by decide⟩,⟨829659, by decide⟩,⟨829680, by decide⟩,⟨829708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6749_829709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6749 ⟨829709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6749
    ⟨829709, by decide⟩ (by decide) (![⟨829656, by decide⟩,⟨829659, by decide⟩,⟨829680, by decide⟩,⟨829708, by decide⟩]) unmarked_context_10_6749_829709 node_context_10_6749_829709
  intro a
  fin_cases a
  · exact context_11_26996_829656
  · exact context_11_26997_829659
  · exact context_11_26998_829680
  · exact context_11_26999_829708

theorem selected_cut_32286 : selected 10 ⟨829725, by decide⟩
    (prefixPartial 11 27000) = some ⟨11, 2, 0, 829725, 27000, 1405, 262144⟩ := by
  decide +kernel

theorem context_11_27000_829725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27000 ⟨829725, by decide⟩ :=
  accepted_of_selected 11 27000 ⟨829725, by decide⟩ ⟨11, 2, 0, 829725, 27000, 1405, 262144⟩
    (by decide) selected_cut_32286

theorem selected_cut_32287 : selected 10 ⟨829737, by decide⟩
    (prefixPartial 11 27001) = some ⟨11, 2, 0, 829737, 27001, 929, 262144⟩ := by
  decide +kernel

theorem context_11_27001_829737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27001 ⟨829737, by decide⟩ :=
  accepted_of_selected 11 27001 ⟨829737, by decide⟩ ⟨11, 2, 0, 829737, 27001, 929, 262144⟩
    (by decide) selected_cut_32287

theorem selected_cut_32288 : selected 10 ⟨829753, by decide⟩
    (prefixPartial 11 27002) = some ⟨11, 2, 0, 829753, 27002, 1065, 262144⟩ := by
  decide +kernel

theorem context_11_27002_829753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27002 ⟨829753, by decide⟩ :=
  accepted_of_selected 11 27002 ⟨829753, by decide⟩ ⟨11, 2, 0, 829753, 27002, 1065, 262144⟩
    (by decide) selected_cut_32288

theorem selected_cut_32289 : selected 10 ⟨829768, by decide⟩
    (prefixPartial 11 27003) = some ⟨11, 2, 0, 829768, 27003, 921, 262144⟩ := by
  decide +kernel

theorem context_11_27003_829768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27003 ⟨829768, by decide⟩ :=
  accepted_of_selected 11 27003 ⟨829768, by decide⟩ ⟨11, 2, 0, 829768, 27003, 921, 262144⟩
    (by decide) selected_cut_32289

theorem unmarked_context_10_6750_829769 : frontier 11 ⟨829769, by decide⟩
    (prefixCache 10 6750) (prefixPartial 10 6750) = false := by
  decide +kernel

theorem node_context_10_6750_829769 : EJMOriginalGlobalDAGData.nodes 11 ⟨829769, by decide⟩ =
    .split (coordinate 10) (![⟨829725, by decide⟩,⟨829737, by decide⟩,⟨829753, by decide⟩,⟨829768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6750_829769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6750 ⟨829769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6750
    ⟨829769, by decide⟩ (by decide) (![⟨829725, by decide⟩,⟨829737, by decide⟩,⟨829753, by decide⟩,⟨829768, by decide⟩]) unmarked_context_10_6750_829769 node_context_10_6750_829769
  intro a
  fin_cases a
  · exact context_11_27000_829725
  · exact context_11_27001_829737
  · exact context_11_27002_829753
  · exact context_11_27003_829768

theorem selected_cut_32290 : selected 11 ⟨829799, by decide⟩
    (prefixPartial 10 6751) = some ⟨10, 2, 0, 829799, 6751, 1441, 1048576⟩ := by
  decide +kernel

theorem context_10_6751_829799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6751 ⟨829799, by decide⟩ :=
  accepted_of_selected 10 6751 ⟨829799, by decide⟩ ⟨10, 2, 0, 829799, 6751, 1441, 1048576⟩
    (by decide) selected_cut_32290

theorem unmarked_context_9_1687_829800 : frontier 12 ⟨829800, by decide⟩
    (prefixCache 9 1687) (prefixPartial 9 1687) = false := by
  decide +kernel

theorem node_context_9_1687_829800 : EJMOriginalGlobalDAGData.nodes 12 ⟨829800, by decide⟩ =
    .split (coordinate 9) (![⟨829632, by decide⟩,⟨829709, by decide⟩,⟨829769, by decide⟩,⟨829799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1687_829800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1687 ⟨829800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1687
    ⟨829800, by decide⟩ (by decide) (![⟨829632, by decide⟩,⟨829709, by decide⟩,⟨829769, by decide⟩,⟨829799, by decide⟩]) unmarked_context_9_1687_829800 node_context_9_1687_829800
  intro a
  fin_cases a
  · exact context_10_6748_829632
  · exact context_10_6749_829709
  · exact context_10_6750_829769
  · exact context_10_6751_829799

theorem unmarked_context_8_421_829801 : frontier 13 ⟨829801, by decide⟩
    (prefixCache 8 421) (prefixPartial 8 421) = false := by
  decide +kernel

theorem node_context_8_421_829801 : EJMOriginalGlobalDAGData.nodes 13 ⟨829801, by decide⟩ =
    .split (coordinate 8) (![⟨825589, by decide⟩,⟨828523, by decide⟩,⟨829485, by decide⟩,⟨829800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_421_829801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 421 ⟨829801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 421
    ⟨829801, by decide⟩ (by decide) (![⟨825589, by decide⟩,⟨828523, by decide⟩,⟨829485, by decide⟩,⟨829800, by decide⟩]) unmarked_context_8_421_829801 node_context_8_421_829801
  intro a
  fin_cases a
  · exact context_9_1684_825589
  · exact context_9_1685_828523
  · exact context_9_1686_829485
  · exact context_9_1687_829800

theorem selected_cut_32291 : selected 13 ⟨158379, by decide⟩
    (prefixPartial 8 422) = some ⟨8, 1, 0, 158379, 422, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_422_158379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 422 ⟨158379, by decide⟩ :=
  accepted_of_selected 8 422 ⟨158379, by decide⟩ ⟨8, 1, 0, 158379, 422, 1, 16777216⟩
    (by decide) selected_cut_32291

theorem selected_cut_32292 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 27072) = some ⟨11, 1, 0, 434745, 27072, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27072_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27072 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 27072 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 27072, 1, 262144⟩
    (by decide) selected_cut_32292

theorem selected_cut_32293 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 27073) = some ⟨11, 1, 0, 167448, 27073, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27073_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27073 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 27073 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 27073, 1, 262144⟩
    (by decide) selected_cut_32293

theorem selected_cut_32294 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 108296) = some ⟨12, 1, 0, 4595, 108296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_108296_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108296 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 108296 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 108296, 1, 65536⟩
    (by decide) selected_cut_32294

theorem selected_cut_32295 : selected 8 ⟨829942, by decide⟩
    (prefixPartial 13 433188) = some ⟨13, 2, 0, 829942, 433188, 3241, 16384⟩ := by
  decide +kernel

theorem context_13_433188_829942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433188 ⟨829942, by decide⟩ :=
  accepted_of_selected 13 433188 ⟨829942, by decide⟩ ⟨13, 2, 0, 829942, 433188, 3241, 16384⟩
    (by decide) selected_cut_32295

theorem selected_cut_32296 : selected 8 ⟨830029, by decide⟩
    (prefixPartial 13 433189) = some ⟨13, 2, 0, 830029, 433189, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_433189_830029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433189 ⟨830029, by decide⟩ :=
  accepted_of_selected 13 433189 ⟨830029, by decide⟩ ⟨13, 2, 0, 830029, 433189, 1793, 16384⟩
    (by decide) selected_cut_32296

theorem selected_cut_32297 : selected 8 ⟨830067, by decide⟩
    (prefixPartial 13 433190) = some ⟨13, 2, 0, 830067, 433190, 569, 16384⟩ := by
  decide +kernel

theorem context_13_433190_830067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433190 ⟨830067, by decide⟩ :=
  accepted_of_selected 13 433190 ⟨830067, by decide⟩ ⟨13, 2, 0, 830067, 433190, 569, 16384⟩
    (by decide) selected_cut_32297

theorem selected_cut_32298 : selected 8 ⟨531816, by decide⟩
    (prefixPartial 13 433191) = some ⟨13, 2, 0, 531816, 433191, 97, 16384⟩ := by
  decide +kernel

theorem context_13_433191_531816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433191 ⟨531816, by decide⟩ :=
  accepted_of_selected 13 433191 ⟨531816, by decide⟩ ⟨13, 2, 0, 531816, 433191, 97, 16384⟩
    (by decide) selected_cut_32298

theorem unmarked_context_12_108297_830068 : frontier 9 ⟨830068, by decide⟩
    (prefixCache 12 108297) (prefixPartial 12 108297) = false := by
  decide +kernel

theorem node_context_12_108297_830068 : EJMOriginalGlobalDAGData.nodes 9 ⟨830068, by decide⟩ =
    .split (coordinate 12) (![⟨829942, by decide⟩,⟨830029, by decide⟩,⟨830067, by decide⟩,⟨531816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108297_830068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108297 ⟨830068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108297
    ⟨830068, by decide⟩ (by decide) (![⟨829942, by decide⟩,⟨830029, by decide⟩,⟨830067, by decide⟩,⟨531816, by decide⟩]) unmarked_context_12_108297_830068 node_context_12_108297_830068
  intro a
  fin_cases a
  · exact context_13_433188_829942
  · exact context_13_433189_830029
  · exact context_13_433190_830067
  · exact context_13_433191_531816

theorem selected_cut_32299 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 108298) = some ⟨12, 1, 0, 4595, 108298, 1, 65536⟩ := by
  decide +kernel

theorem context_12_108298_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108298 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 108298 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 108298, 1, 65536⟩
    (by decide) selected_cut_32299

theorem selected_cut_32300 : selected 8 ⟨830167, by decide⟩
    (prefixPartial 13 433196) = some ⟨13, 2, 0, 830167, 433196, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_433196_830167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433196 ⟨830167, by decide⟩ :=
  accepted_of_selected 13 433196 ⟨830167, by decide⟩ ⟨13, 2, 0, 830167, 433196, 3477, 16384⟩
    (by decide) selected_cut_32300

theorem selected_cut_32301 : selected 7 ⟨830205, by decide⟩
    (prefixPartial 14 1732788) = some ⟨14, 2, 0, 830205, 1732788, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_1732788_830205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1732788 ⟨830205, by decide⟩ :=
  accepted_of_selected 14 1732788 ⟨830205, by decide⟩ ⟨14, 2, 0, 830205, 1732788, 1221, 4096⟩
    (by decide) selected_cut_32301

theorem selected_cut_32302 : selected 7 ⟨830227, by decide⟩
    (prefixPartial 14 1732789) = some ⟨14, 2, 0, 830227, 1732789, 801, 4096⟩ := by
  decide +kernel

theorem context_14_1732789_830227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1732789 ⟨830227, by decide⟩ :=
  accepted_of_selected 14 1732789 ⟨830227, by decide⟩ ⟨14, 2, 0, 830227, 1732789, 801, 4096⟩
    (by decide) selected_cut_32302

theorem selected_cut_32303 : selected 7 ⟨830273, by decide⟩
    (prefixPartial 14 1732790) = some ⟨14, 2, 0, 830273, 1732790, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_1732790_830273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1732790 ⟨830273, by decide⟩ :=
  accepted_of_selected 14 1732790 ⟨830273, by decide⟩ ⟨14, 2, 0, 830273, 1732790, 1321, 4096⟩
    (by decide) selected_cut_32303

theorem selected_cut_32304 : selected 7 ⟨830298, by decide⟩
    (prefixPartial 14 1732791) = some ⟨14, 2, 0, 830298, 1732791, 945, 4096⟩ := by
  decide +kernel

theorem context_14_1732791_830298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1732791 ⟨830298, by decide⟩ :=
  accepted_of_selected 14 1732791 ⟨830298, by decide⟩ ⟨14, 2, 0, 830298, 1732791, 945, 4096⟩
    (by decide) selected_cut_32304

theorem unmarked_context_13_433197_830299 : frontier 8 ⟨830299, by decide⟩
    (prefixCache 13 433197) (prefixPartial 13 433197) = false := by
  decide +kernel

theorem node_context_13_433197_830299 : EJMOriginalGlobalDAGData.nodes 8 ⟨830299, by decide⟩ =
    .split (coordinate 13) (![⟨830205, by decide⟩,⟨830227, by decide⟩,⟨830273, by decide⟩,⟨830298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_433197_830299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433197 ⟨830299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 433197
    ⟨830299, by decide⟩ (by decide) (![⟨830205, by decide⟩,⟨830227, by decide⟩,⟨830273, by decide⟩,⟨830298, by decide⟩]) unmarked_context_13_433197_830299 node_context_13_433197_830299
  intro a
  fin_cases a
  · exact context_14_1732788_830205
  · exact context_14_1732789_830227
  · exact context_14_1732790_830273
  · exact context_14_1732791_830298

theorem selected_cut_32305 : selected 8 ⟨830419, by decide⟩
    (prefixPartial 13 433198) = some ⟨13, 2, 0, 830419, 433198, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_433198_830419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433198 ⟨830419, by decide⟩ :=
  accepted_of_selected 13 433198 ⟨830419, by decide⟩ ⟨13, 2, 0, 830419, 433198, 2225, 16384⟩
    (by decide) selected_cut_32305

theorem selected_cut_32306 : selected 8 ⟨830448, by decide⟩
    (prefixPartial 13 433199) = some ⟨13, 2, 0, 830448, 433199, 873, 16384⟩ := by
  decide +kernel

theorem context_13_433199_830448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433199 ⟨830448, by decide⟩ :=
  accepted_of_selected 13 433199 ⟨830448, by decide⟩ ⟨13, 2, 0, 830448, 433199, 873, 16384⟩
    (by decide) selected_cut_32306

theorem unmarked_context_12_108299_830449 : frontier 9 ⟨830449, by decide⟩
    (prefixCache 12 108299) (prefixPartial 12 108299) = false := by
  decide +kernel

theorem node_context_12_108299_830449 : EJMOriginalGlobalDAGData.nodes 9 ⟨830449, by decide⟩ =
    .split (coordinate 12) (![⟨830167, by decide⟩,⟨830299, by decide⟩,⟨830419, by decide⟩,⟨830448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108299_830449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108299 ⟨830449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108299
    ⟨830449, by decide⟩ (by decide) (![⟨830167, by decide⟩,⟨830299, by decide⟩,⟨830419, by decide⟩,⟨830448, by decide⟩]) unmarked_context_12_108299_830449 node_context_12_108299_830449
  intro a
  fin_cases a
  · exact context_13_433196_830167
  · exact context_13_433197_830299
  · exact context_13_433198_830419
  · exact context_13_433199_830448

theorem unmarked_context_11_27074_830450 : frontier 10 ⟨830450, by decide⟩
    (prefixCache 11 27074) (prefixPartial 11 27074) = false := by
  decide +kernel

theorem node_context_11_27074_830450 : EJMOriginalGlobalDAGData.nodes 10 ⟨830450, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨830068, by decide⟩,⟨4595, by decide⟩,⟨830449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27074_830450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27074 ⟨830450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27074
    ⟨830450, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨830068, by decide⟩,⟨4595, by decide⟩,⟨830449, by decide⟩]) unmarked_context_11_27074_830450 node_context_11_27074_830450
  intro a
  fin_cases a
  · exact context_12_108296_4595
  · exact context_12_108297_830068
  · exact context_12_108298_4595
  · exact context_12_108299_830449

theorem selected_cut_32307 : selected 10 ⟨815335, by decide⟩
    (prefixPartial 11 27075) = some ⟨11, 2, 0, 815335, 27075, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27075_815335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27075 ⟨815335, by decide⟩ :=
  accepted_of_selected 11 27075 ⟨815335, by decide⟩ ⟨11, 2, 0, 815335, 27075, 5, 262144⟩
    (by decide) selected_cut_32307

theorem unmarked_context_10_6768_830451 : frontier 11 ⟨830451, by decide⟩
    (prefixCache 10 6768) (prefixPartial 10 6768) = false := by
  decide +kernel

theorem node_context_10_6768_830451 : EJMOriginalGlobalDAGData.nodes 11 ⟨830451, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨830450, by decide⟩,⟨815335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6768_830451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6768 ⟨830451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6768
    ⟨830451, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨830450, by decide⟩,⟨815335, by decide⟩]) unmarked_context_10_6768_830451 node_context_10_6768_830451
  intro a
  fin_cases a
  · exact context_11_27072_434745
  · exact context_11_27073_167448
  · exact context_11_27074_830450
  · exact context_11_27075_815335

theorem selected_cut_32308 : selected 8 ⟨830482, by decide⟩
    (prefixPartial 13 433216) = some ⟨13, 2, 0, 830482, 433216, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_433216_830482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433216 ⟨830482, by decide⟩ :=
  accepted_of_selected 13 433216 ⟨830482, by decide⟩ ⟨13, 2, 0, 830482, 433216, 2021, 16384⟩
    (by decide) selected_cut_32308

theorem selected_cut_32309 : selected 8 ⟨830524, by decide⟩
    (prefixPartial 13 433217) = some ⟨13, 2, 0, 830524, 433217, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_433217_830524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433217 ⟨830524, by decide⟩ :=
  accepted_of_selected 13 433217 ⟨830524, by decide⟩ ⟨13, 2, 0, 830524, 433217, 2657, 16384⟩
    (by decide) selected_cut_32309

theorem selected_cut_32310 : selected 8 ⟨830545, by decide⟩
    (prefixPartial 13 433218) = some ⟨13, 2, 0, 830545, 433218, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_433218_830545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433218 ⟨830545, by decide⟩ :=
  accepted_of_selected 13 433218 ⟨830545, by decide⟩ ⟨13, 2, 0, 830545, 433218, 1285, 16384⟩
    (by decide) selected_cut_32310

theorem selected_cut_32311 : selected 8 ⟨830562, by decide⟩
    (prefixPartial 13 433219) = some ⟨13, 2, 0, 830562, 433219, 821, 16384⟩ := by
  decide +kernel

theorem context_13_433219_830562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433219 ⟨830562, by decide⟩ :=
  accepted_of_selected 13 433219 ⟨830562, by decide⟩ ⟨13, 2, 0, 830562, 433219, 821, 16384⟩
    (by decide) selected_cut_32311

theorem unmarked_context_12_108304_830563 : frontier 9 ⟨830563, by decide⟩
    (prefixCache 12 108304) (prefixPartial 12 108304) = false := by
  decide +kernel

theorem node_context_12_108304_830563 : EJMOriginalGlobalDAGData.nodes 9 ⟨830563, by decide⟩ =
    .split (coordinate 12) (![⟨830482, by decide⟩,⟨830524, by decide⟩,⟨830545, by decide⟩,⟨830562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108304_830563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108304 ⟨830563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108304
    ⟨830563, by decide⟩ (by decide) (![⟨830482, by decide⟩,⟨830524, by decide⟩,⟨830545, by decide⟩,⟨830562, by decide⟩]) unmarked_context_12_108304_830563 node_context_12_108304_830563
  intro a
  fin_cases a
  · exact context_13_433216_830482
  · exact context_13_433217_830524
  · exact context_13_433218_830545
  · exact context_13_433219_830562

theorem selected_cut_32312 : selected 8 ⟨830599, by decide⟩
    (prefixPartial 13 433220) = some ⟨13, 2, 0, 830599, 433220, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_433220_830599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433220 ⟨830599, by decide⟩ :=
  accepted_of_selected 13 433220 ⟨830599, by decide⟩ ⟨13, 2, 0, 830599, 433220, 2205, 16384⟩
    (by decide) selected_cut_32312

theorem selected_cut_32313 : selected 8 ⟨830647, by decide⟩
    (prefixPartial 13 433221) = some ⟨13, 2, 0, 830647, 433221, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_433221_830647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433221 ⟨830647, by decide⟩ :=
  accepted_of_selected 13 433221 ⟨830647, by decide⟩ ⟨13, 2, 0, 830647, 433221, 2733, 16384⟩
    (by decide) selected_cut_32313

theorem selected_cut_32314 : selected 8 ⟨830677, by decide⟩
    (prefixPartial 13 433222) = some ⟨13, 2, 0, 830677, 433222, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_433222_830677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433222 ⟨830677, by decide⟩ :=
  accepted_of_selected 13 433222 ⟨830677, by decide⟩ ⟨13, 2, 0, 830677, 433222, 1265, 16384⟩
    (by decide) selected_cut_32314

theorem selected_cut_32315 : selected 8 ⟨830687, by decide⟩
    (prefixPartial 13 433223) = some ⟨13, 2, 0, 830687, 433223, 661, 16384⟩ := by
  decide +kernel

theorem context_13_433223_830687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433223 ⟨830687, by decide⟩ :=
  accepted_of_selected 13 433223 ⟨830687, by decide⟩ ⟨13, 2, 0, 830687, 433223, 661, 16384⟩
    (by decide) selected_cut_32315

theorem unmarked_context_12_108305_830688 : frontier 9 ⟨830688, by decide⟩
    (prefixCache 12 108305) (prefixPartial 12 108305) = false := by
  decide +kernel

theorem node_context_12_108305_830688 : EJMOriginalGlobalDAGData.nodes 9 ⟨830688, by decide⟩ =
    .split (coordinate 12) (![⟨830599, by decide⟩,⟨830647, by decide⟩,⟨830677, by decide⟩,⟨830687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108305_830688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108305 ⟨830688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108305
    ⟨830688, by decide⟩ (by decide) (![⟨830599, by decide⟩,⟨830647, by decide⟩,⟨830677, by decide⟩,⟨830687, by decide⟩]) unmarked_context_12_108305_830688 node_context_12_108305_830688
  intro a
  fin_cases a
  · exact context_13_433220_830599
  · exact context_13_433221_830647
  · exact context_13_433222_830677
  · exact context_13_433223_830687

theorem selected_cut_32316 : selected 8 ⟨830719, by decide⟩
    (prefixPartial 13 433224) = some ⟨13, 2, 0, 830719, 433224, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_433224_830719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433224 ⟨830719, by decide⟩ :=
  accepted_of_selected 13 433224 ⟨830719, by decide⟩ ⟨13, 2, 0, 830719, 433224, 1925, 16384⟩
    (by decide) selected_cut_32316

theorem selected_cut_32317 : selected 8 ⟨830762, by decide⟩
    (prefixPartial 13 433225) = some ⟨13, 2, 0, 830762, 433225, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_433225_830762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433225 ⟨830762, by decide⟩ :=
  accepted_of_selected 13 433225 ⟨830762, by decide⟩ ⟨13, 2, 0, 830762, 433225, 2405, 16384⟩
    (by decide) selected_cut_32317

theorem selected_cut_32318 : selected 8 ⟨830785, by decide⟩
    (prefixPartial 13 433226) = some ⟨13, 2, 0, 830785, 433226, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_433226_830785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433226 ⟨830785, by decide⟩ :=
  accepted_of_selected 13 433226 ⟨830785, by decide⟩ ⟨13, 2, 0, 830785, 433226, 1181, 16384⟩
    (by decide) selected_cut_32318

theorem selected_cut_32319 : selected 8 ⟨830793, by decide⟩
    (prefixPartial 13 433227) = some ⟨13, 2, 0, 830793, 433227, 749, 16384⟩ := by
  decide +kernel

theorem context_13_433227_830793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433227 ⟨830793, by decide⟩ :=
  accepted_of_selected 13 433227 ⟨830793, by decide⟩ ⟨13, 2, 0, 830793, 433227, 749, 16384⟩
    (by decide) selected_cut_32319

theorem unmarked_context_12_108306_830794 : frontier 9 ⟨830794, by decide⟩
    (prefixCache 12 108306) (prefixPartial 12 108306) = false := by
  decide +kernel

theorem node_context_12_108306_830794 : EJMOriginalGlobalDAGData.nodes 9 ⟨830794, by decide⟩ =
    .split (coordinate 12) (![⟨830719, by decide⟩,⟨830762, by decide⟩,⟨830785, by decide⟩,⟨830793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108306_830794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108306 ⟨830794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108306
    ⟨830794, by decide⟩ (by decide) (![⟨830719, by decide⟩,⟨830762, by decide⟩,⟨830785, by decide⟩,⟨830793, by decide⟩]) unmarked_context_12_108306_830794 node_context_12_108306_830794
  intro a
  fin_cases a
  · exact context_13_433224_830719
  · exact context_13_433225_830762
  · exact context_13_433226_830785
  · exact context_13_433227_830793

theorem selected_cut_32320 : selected 8 ⟨830822, by decide⟩
    (prefixPartial 13 433228) = some ⟨13, 2, 0, 830822, 433228, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_433228_830822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433228 ⟨830822, by decide⟩ :=
  accepted_of_selected 13 433228 ⟨830822, by decide⟩ ⟨13, 2, 0, 830822, 433228, 2001, 16384⟩
    (by decide) selected_cut_32320

theorem selected_cut_32321 : selected 8 ⟨830861, by decide⟩
    (prefixPartial 13 433229) = some ⟨13, 2, 0, 830861, 433229, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_433229_830861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433229 ⟨830861, by decide⟩ :=
  accepted_of_selected 13 433229 ⟨830861, by decide⟩ ⟨13, 2, 0, 830861, 433229, 2697, 16384⟩
    (by decide) selected_cut_32321

theorem selected_cut_32322 : selected 8 ⟨830890, by decide⟩
    (prefixPartial 13 433230) = some ⟨13, 2, 0, 830890, 433230, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_433230_830890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433230 ⟨830890, by decide⟩ :=
  accepted_of_selected 13 433230 ⟨830890, by decide⟩ ⟨13, 2, 0, 830890, 433230, 1261, 16384⟩
    (by decide) selected_cut_32322

theorem selected_cut_32323 : selected 8 ⟨830900, by decide⟩
    (prefixPartial 13 433231) = some ⟨13, 2, 0, 830900, 433231, 665, 16384⟩ := by
  decide +kernel

theorem context_13_433231_830900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433231 ⟨830900, by decide⟩ :=
  accepted_of_selected 13 433231 ⟨830900, by decide⟩ ⟨13, 2, 0, 830900, 433231, 665, 16384⟩
    (by decide) selected_cut_32323

theorem unmarked_context_12_108307_830901 : frontier 9 ⟨830901, by decide⟩
    (prefixCache 12 108307) (prefixPartial 12 108307) = false := by
  decide +kernel

theorem node_context_12_108307_830901 : EJMOriginalGlobalDAGData.nodes 9 ⟨830901, by decide⟩ =
    .split (coordinate 12) (![⟨830822, by decide⟩,⟨830861, by decide⟩,⟨830890, by decide⟩,⟨830900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108307_830901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108307 ⟨830901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108307
    ⟨830901, by decide⟩ (by decide) (![⟨830822, by decide⟩,⟨830861, by decide⟩,⟨830890, by decide⟩,⟨830900, by decide⟩]) unmarked_context_12_108307_830901 node_context_12_108307_830901
  intro a
  fin_cases a
  · exact context_13_433228_830822
  · exact context_13_433229_830861
  · exact context_13_433230_830890
  · exact context_13_433231_830900

theorem unmarked_context_11_27076_830902 : frontier 10 ⟨830902, by decide⟩
    (prefixCache 11 27076) (prefixPartial 11 27076) = false := by
  decide +kernel

theorem node_context_11_27076_830902 : EJMOriginalGlobalDAGData.nodes 10 ⟨830902, by decide⟩ =
    .split (coordinate 11) (![⟨830563, by decide⟩,⟨830688, by decide⟩,⟨830794, by decide⟩,⟨830901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27076_830902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27076 ⟨830902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27076
    ⟨830902, by decide⟩ (by decide) (![⟨830563, by decide⟩,⟨830688, by decide⟩,⟨830794, by decide⟩,⟨830901, by decide⟩]) unmarked_context_11_27076_830902 node_context_11_27076_830902
  intro a
  fin_cases a
  · exact context_12_108304_830563
  · exact context_12_108305_830688
  · exact context_12_108306_830794
  · exact context_12_108307_830901

theorem selected_cut_32324 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 27077) = some ⟨11, 1, 0, 815620, 27077, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27077_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27077 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 27077 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 27077, 1, 262144⟩
    (by decide) selected_cut_32324

theorem selected_cut_32325 : selected 8 ⟨830928, by decide⟩
    (prefixPartial 13 433248) = some ⟨13, 2, 0, 830928, 433248, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_433248_830928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433248 ⟨830928, by decide⟩ :=
  accepted_of_selected 13 433248 ⟨830928, by decide⟩ ⟨13, 2, 0, 830928, 433248, 1613, 16384⟩
    (by decide) selected_cut_32325

theorem selected_cut_32326 : selected 8 ⟨830960, by decide⟩
    (prefixPartial 13 433249) = some ⟨13, 2, 0, 830960, 433249, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_433249_830960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433249 ⟨830960, by decide⟩ :=
  accepted_of_selected 13 433249 ⟨830960, by decide⟩ ⟨13, 2, 0, 830960, 433249, 2421, 16384⟩
    (by decide) selected_cut_32326

theorem selected_cut_32327 : selected 8 ⟨830988, by decide⟩
    (prefixPartial 13 433250) = some ⟨13, 2, 0, 830988, 433250, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_433250_830988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433250 ⟨830988, by decide⟩ :=
  accepted_of_selected 13 433250 ⟨830988, by decide⟩ ⟨13, 2, 0, 830988, 433250, 1309, 16384⟩
    (by decide) selected_cut_32327

theorem selected_cut_32328 : selected 8 ⟨831004, by decide⟩
    (prefixPartial 13 433251) = some ⟨13, 2, 0, 831004, 433251, 845, 16384⟩ := by
  decide +kernel

theorem context_13_433251_831004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433251 ⟨831004, by decide⟩ :=
  accepted_of_selected 13 433251 ⟨831004, by decide⟩ ⟨13, 2, 0, 831004, 433251, 845, 16384⟩
    (by decide) selected_cut_32328

theorem unmarked_context_12_108312_831005 : frontier 9 ⟨831005, by decide⟩
    (prefixCache 12 108312) (prefixPartial 12 108312) = false := by
  decide +kernel

theorem node_context_12_108312_831005 : EJMOriginalGlobalDAGData.nodes 9 ⟨831005, by decide⟩ =
    .split (coordinate 12) (![⟨830928, by decide⟩,⟨830960, by decide⟩,⟨830988, by decide⟩,⟨831004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108312_831005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108312 ⟨831005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108312
    ⟨831005, by decide⟩ (by decide) (![⟨830928, by decide⟩,⟨830960, by decide⟩,⟨830988, by decide⟩,⟨831004, by decide⟩]) unmarked_context_12_108312_831005 node_context_12_108312_831005
  intro a
  fin_cases a
  · exact context_13_433248_830928
  · exact context_13_433249_830960
  · exact context_13_433250_830988
  · exact context_13_433251_831004

theorem selected_cut_32329 : selected 8 ⟨831033, by decide⟩
    (prefixPartial 13 433252) = some ⟨13, 2, 0, 831033, 433252, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_433252_831033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433252 ⟨831033, by decide⟩ :=
  accepted_of_selected 13 433252 ⟨831033, by decide⟩ ⟨13, 2, 0, 831033, 433252, 1817, 16384⟩
    (by decide) selected_cut_32329

theorem selected_cut_32330 : selected 8 ⟨831068, by decide⟩
    (prefixPartial 13 433253) = some ⟨13, 2, 0, 831068, 433253, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_433253_831068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433253 ⟨831068, by decide⟩ :=
  accepted_of_selected 13 433253 ⟨831068, by decide⟩ ⟨13, 2, 0, 831068, 433253, 2373, 16384⟩
    (by decide) selected_cut_32330

theorem selected_cut_32331 : selected 8 ⟨831099, by decide⟩
    (prefixPartial 13 433254) = some ⟨13, 2, 0, 831099, 433254, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_433254_831099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433254 ⟨831099, by decide⟩ :=
  accepted_of_selected 13 433254 ⟨831099, by decide⟩ ⟨13, 2, 0, 831099, 433254, 1181, 16384⟩
    (by decide) selected_cut_32331

theorem selected_cut_32332 : selected 8 ⟨831106, by decide⟩
    (prefixPartial 13 433255) = some ⟨13, 2, 0, 831106, 433255, 725, 16384⟩ := by
  decide +kernel

theorem context_13_433255_831106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433255 ⟨831106, by decide⟩ :=
  accepted_of_selected 13 433255 ⟨831106, by decide⟩ ⟨13, 2, 0, 831106, 433255, 725, 16384⟩
    (by decide) selected_cut_32332

theorem unmarked_context_12_108313_831107 : frontier 9 ⟨831107, by decide⟩
    (prefixCache 12 108313) (prefixPartial 12 108313) = false := by
  decide +kernel

theorem node_context_12_108313_831107 : EJMOriginalGlobalDAGData.nodes 9 ⟨831107, by decide⟩ =
    .split (coordinate 12) (![⟨831033, by decide⟩,⟨831068, by decide⟩,⟨831099, by decide⟩,⟨831106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108313_831107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108313 ⟨831107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108313
    ⟨831107, by decide⟩ (by decide) (![⟨831033, by decide⟩,⟨831068, by decide⟩,⟨831099, by decide⟩,⟨831106, by decide⟩]) unmarked_context_12_108313_831107 node_context_12_108313_831107
  intro a
  fin_cases a
  · exact context_13_433252_831033
  · exact context_13_433253_831068
  · exact context_13_433254_831099
  · exact context_13_433255_831106

theorem selected_cut_32333 : selected 8 ⟨831138, by decide⟩
    (prefixPartial 13 433256) = some ⟨13, 2, 0, 831138, 433256, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_433256_831138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433256 ⟨831138, by decide⟩ :=
  accepted_of_selected 13 433256 ⟨831138, by decide⟩ ⟨13, 2, 0, 831138, 433256, 1581, 16384⟩
    (by decide) selected_cut_32333

theorem selected_cut_32334 : selected 8 ⟨831173, by decide⟩
    (prefixPartial 13 433257) = some ⟨13, 2, 0, 831173, 433257, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_433257_831173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433257 ⟨831173, by decide⟩ :=
  accepted_of_selected 13 433257 ⟨831173, by decide⟩ ⟨13, 2, 0, 831173, 433257, 2281, 16384⟩
    (by decide) selected_cut_32334

theorem selected_cut_32335 : selected 8 ⟨831199, by decide⟩
    (prefixPartial 13 433258) = some ⟨13, 2, 0, 831199, 433258, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_433258_831199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433258 ⟨831199, by decide⟩ :=
  accepted_of_selected 13 433258 ⟨831199, by decide⟩ ⟨13, 2, 0, 831199, 433258, 1057, 16384⟩
    (by decide) selected_cut_32335

theorem selected_cut_32336 : selected 8 ⟨831210, by decide⟩
    (prefixPartial 13 433259) = some ⟨13, 2, 0, 831210, 433259, 797, 16384⟩ := by
  decide +kernel

theorem context_13_433259_831210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433259 ⟨831210, by decide⟩ :=
  accepted_of_selected 13 433259 ⟨831210, by decide⟩ ⟨13, 2, 0, 831210, 433259, 797, 16384⟩
    (by decide) selected_cut_32336

theorem unmarked_context_12_108314_831211 : frontier 9 ⟨831211, by decide⟩
    (prefixCache 12 108314) (prefixPartial 12 108314) = false := by
  decide +kernel

theorem node_context_12_108314_831211 : EJMOriginalGlobalDAGData.nodes 9 ⟨831211, by decide⟩ =
    .split (coordinate 12) (![⟨831138, by decide⟩,⟨831173, by decide⟩,⟨831199, by decide⟩,⟨831210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108314_831211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108314 ⟨831211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108314
    ⟨831211, by decide⟩ (by decide) (![⟨831138, by decide⟩,⟨831173, by decide⟩,⟨831199, by decide⟩,⟨831210, by decide⟩]) unmarked_context_12_108314_831211 node_context_12_108314_831211
  intro a
  fin_cases a
  · exact context_13_433256_831138
  · exact context_13_433257_831173
  · exact context_13_433258_831199
  · exact context_13_433259_831210

theorem selected_cut_32337 : selected 8 ⟨831238, by decide⟩
    (prefixPartial 13 433260) = some ⟨13, 2, 0, 831238, 433260, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_433260_831238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433260 ⟨831238, by decide⟩ :=
  accepted_of_selected 13 433260 ⟨831238, by decide⟩ ⟨13, 2, 0, 831238, 433260, 1585, 16384⟩
    (by decide) selected_cut_32337

theorem selected_cut_32338 : selected 8 ⟨831283, by decide⟩
    (prefixPartial 13 433261) = some ⟨13, 2, 0, 831283, 433261, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_433261_831283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433261 ⟨831283, by decide⟩ :=
  accepted_of_selected 13 433261 ⟨831283, by decide⟩ ⟨13, 2, 0, 831283, 433261, 2461, 16384⟩
    (by decide) selected_cut_32338

theorem selected_cut_32339 : selected 8 ⟨831304, by decide⟩
    (prefixPartial 13 433262) = some ⟨13, 2, 0, 831304, 433262, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_433262_831304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433262 ⟨831304, by decide⟩ :=
  accepted_of_selected 13 433262 ⟨831304, by decide⟩ ⟨13, 2, 0, 831304, 433262, 1149, 16384⟩
    (by decide) selected_cut_32339

theorem selected_cut_32340 : selected 8 ⟨831309, by decide⟩
    (prefixPartial 13 433263) = some ⟨13, 2, 0, 831309, 433263, 705, 16384⟩ := by
  decide +kernel

theorem context_13_433263_831309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433263 ⟨831309, by decide⟩ :=
  accepted_of_selected 13 433263 ⟨831309, by decide⟩ ⟨13, 2, 0, 831309, 433263, 705, 16384⟩
    (by decide) selected_cut_32340

theorem unmarked_context_12_108315_831310 : frontier 9 ⟨831310, by decide⟩
    (prefixCache 12 108315) (prefixPartial 12 108315) = false := by
  decide +kernel

theorem node_context_12_108315_831310 : EJMOriginalGlobalDAGData.nodes 9 ⟨831310, by decide⟩ =
    .split (coordinate 12) (![⟨831238, by decide⟩,⟨831283, by decide⟩,⟨831304, by decide⟩,⟨831309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108315_831310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108315 ⟨831310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108315
    ⟨831310, by decide⟩ (by decide) (![⟨831238, by decide⟩,⟨831283, by decide⟩,⟨831304, by decide⟩,⟨831309, by decide⟩]) unmarked_context_12_108315_831310 node_context_12_108315_831310
  intro a
  fin_cases a
  · exact context_13_433260_831238
  · exact context_13_433261_831283
  · exact context_13_433262_831304
  · exact context_13_433263_831309

theorem unmarked_context_11_27078_831311 : frontier 10 ⟨831311, by decide⟩
    (prefixCache 11 27078) (prefixPartial 11 27078) = false := by
  decide +kernel

theorem node_context_11_27078_831311 : EJMOriginalGlobalDAGData.nodes 10 ⟨831311, by decide⟩ =
    .split (coordinate 11) (![⟨831005, by decide⟩,⟨831107, by decide⟩,⟨831211, by decide⟩,⟨831310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27078_831311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27078 ⟨831311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27078
    ⟨831311, by decide⟩ (by decide) (![⟨831005, by decide⟩,⟨831107, by decide⟩,⟨831211, by decide⟩,⟨831310, by decide⟩]) unmarked_context_11_27078_831311 node_context_11_27078_831311
  intro a
  fin_cases a
  · exact context_12_108312_831005
  · exact context_12_108313_831107
  · exact context_12_108314_831211
  · exact context_12_108315_831310

theorem selected_cut_32341 : selected 8 ⟨831335, by decide⟩
    (prefixPartial 13 433264) = some ⟨13, 2, 0, 831335, 433264, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_433264_831335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433264 ⟨831335, by decide⟩ :=
  accepted_of_selected 13 433264 ⟨831335, by decide⟩ ⟨13, 2, 0, 831335, 433264, 1525, 16384⟩
    (by decide) selected_cut_32341

theorem selected_cut_32342 : selected 8 ⟨831370, by decide⟩
    (prefixPartial 13 433265) = some ⟨13, 2, 0, 831370, 433265, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_433265_831370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433265 ⟨831370, by decide⟩ :=
  accepted_of_selected 13 433265 ⟨831370, by decide⟩ ⟨13, 2, 0, 831370, 433265, 2617, 16384⟩
    (by decide) selected_cut_32342

theorem selected_cut_32343 : selected 8 ⟨831390, by decide⟩
    (prefixPartial 13 433266) = some ⟨13, 2, 0, 831390, 433266, 973, 16384⟩ := by
  decide +kernel

theorem context_13_433266_831390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433266 ⟨831390, by decide⟩ :=
  accepted_of_selected 13 433266 ⟨831390, by decide⟩ ⟨13, 2, 0, 831390, 433266, 973, 16384⟩
    (by decide) selected_cut_32343

theorem selected_cut_32344 : selected 8 ⟨831403, by decide⟩
    (prefixPartial 13 433267) = some ⟨13, 2, 0, 831403, 433267, 821, 16384⟩ := by
  decide +kernel

theorem context_13_433267_831403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433267 ⟨831403, by decide⟩ :=
  accepted_of_selected 13 433267 ⟨831403, by decide⟩ ⟨13, 2, 0, 831403, 433267, 821, 16384⟩
    (by decide) selected_cut_32344

theorem unmarked_context_12_108316_831404 : frontier 9 ⟨831404, by decide⟩
    (prefixCache 12 108316) (prefixPartial 12 108316) = false := by
  decide +kernel

theorem node_context_12_108316_831404 : EJMOriginalGlobalDAGData.nodes 9 ⟨831404, by decide⟩ =
    .split (coordinate 12) (![⟨831335, by decide⟩,⟨831370, by decide⟩,⟨831390, by decide⟩,⟨831403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108316_831404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108316 ⟨831404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108316
    ⟨831404, by decide⟩ (by decide) (![⟨831335, by decide⟩,⟨831370, by decide⟩,⟨831390, by decide⟩,⟨831403, by decide⟩]) unmarked_context_12_108316_831404 node_context_12_108316_831404
  intro a
  fin_cases a
  · exact context_13_433264_831335
  · exact context_13_433265_831370
  · exact context_13_433266_831390
  · exact context_13_433267_831403

theorem selected_cut_32345 : selected 8 ⟨831439, by decide⟩
    (prefixPartial 13 433268) = some ⟨13, 2, 0, 831439, 433268, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_433268_831439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433268 ⟨831439, by decide⟩ :=
  accepted_of_selected 13 433268 ⟨831439, by decide⟩ ⟨13, 2, 0, 831439, 433268, 1761, 16384⟩
    (by decide) selected_cut_32345

theorem selected_cut_32346 : selected 8 ⟨831493, by decide⟩
    (prefixPartial 13 433269) = some ⟨13, 2, 0, 831493, 433269, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_433269_831493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433269 ⟨831493, by decide⟩ :=
  accepted_of_selected 13 433269 ⟨831493, by decide⟩ ⟨13, 2, 0, 831493, 433269, 2621, 16384⟩
    (by decide) selected_cut_32346

theorem selected_cut_32347 : selected 8 ⟨831513, by decide⟩
    (prefixPartial 13 433270) = some ⟨13, 2, 0, 831513, 433270, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_433270_831513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433270 ⟨831513, by decide⟩ :=
  accepted_of_selected 13 433270 ⟨831513, by decide⟩ ⟨13, 2, 0, 831513, 433270, 1001, 16384⟩
    (by decide) selected_cut_32347

theorem selected_cut_32348 : selected 8 ⟨831520, by decide⟩
    (prefixPartial 13 433271) = some ⟨13, 2, 0, 831520, 433271, 709, 16384⟩ := by
  decide +kernel

theorem context_13_433271_831520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433271 ⟨831520, by decide⟩ :=
  accepted_of_selected 13 433271 ⟨831520, by decide⟩ ⟨13, 2, 0, 831520, 433271, 709, 16384⟩
    (by decide) selected_cut_32348

theorem unmarked_context_12_108317_831521 : frontier 9 ⟨831521, by decide⟩
    (prefixCache 12 108317) (prefixPartial 12 108317) = false := by
  decide +kernel

theorem node_context_12_108317_831521 : EJMOriginalGlobalDAGData.nodes 9 ⟨831521, by decide⟩ =
    .split (coordinate 12) (![⟨831439, by decide⟩,⟨831493, by decide⟩,⟨831513, by decide⟩,⟨831520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108317_831521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108317 ⟨831521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108317
    ⟨831521, by decide⟩ (by decide) (![⟨831439, by decide⟩,⟨831493, by decide⟩,⟨831513, by decide⟩,⟨831520, by decide⟩]) unmarked_context_12_108317_831521 node_context_12_108317_831521
  intro a
  fin_cases a
  · exact context_13_433268_831439
  · exact context_13_433269_831493
  · exact context_13_433270_831513
  · exact context_13_433271_831520

theorem selected_cut_32349 : selected 8 ⟨831544, by decide⟩
    (prefixPartial 13 433272) = some ⟨13, 2, 0, 831544, 433272, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_433272_831544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433272 ⟨831544, by decide⟩ :=
  accepted_of_selected 13 433272 ⟨831544, by decide⟩ ⟨13, 2, 0, 831544, 433272, 1473, 16384⟩
    (by decide) selected_cut_32349

theorem selected_cut_32350 : selected 8 ⟨831581, by decide⟩
    (prefixPartial 13 433273) = some ⟨13, 2, 0, 831581, 433273, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_433273_831581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433273 ⟨831581, by decide⟩ :=
  accepted_of_selected 13 433273 ⟨831581, by decide⟩ ⟨13, 2, 0, 831581, 433273, 2469, 16384⟩
    (by decide) selected_cut_32350

theorem selected_cut_32351 : selected 8 ⟨831598, by decide⟩
    (prefixPartial 13 433274) = some ⟨13, 2, 0, 831598, 433274, 877, 16384⟩ := by
  decide +kernel

theorem context_13_433274_831598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433274 ⟨831598, by decide⟩ :=
  accepted_of_selected 13 433274 ⟨831598, by decide⟩ ⟨13, 2, 0, 831598, 433274, 877, 16384⟩
    (by decide) selected_cut_32351

theorem selected_cut_32352 : selected 8 ⟨831606, by decide⟩
    (prefixPartial 13 433275) = some ⟨13, 2, 0, 831606, 433275, 821, 16384⟩ := by
  decide +kernel

theorem context_13_433275_831606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433275 ⟨831606, by decide⟩ :=
  accepted_of_selected 13 433275 ⟨831606, by decide⟩ ⟨13, 2, 0, 831606, 433275, 821, 16384⟩
    (by decide) selected_cut_32352

theorem unmarked_context_12_108318_831607 : frontier 9 ⟨831607, by decide⟩
    (prefixCache 12 108318) (prefixPartial 12 108318) = false := by
  decide +kernel

theorem node_context_12_108318_831607 : EJMOriginalGlobalDAGData.nodes 9 ⟨831607, by decide⟩ =
    .split (coordinate 12) (![⟨831544, by decide⟩,⟨831581, by decide⟩,⟨831598, by decide⟩,⟨831606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108318_831607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108318 ⟨831607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108318
    ⟨831607, by decide⟩ (by decide) (![⟨831544, by decide⟩,⟨831581, by decide⟩,⟨831598, by decide⟩,⟨831606, by decide⟩]) unmarked_context_12_108318_831607 node_context_12_108318_831607
  intro a
  fin_cases a
  · exact context_13_433272_831544
  · exact context_13_433273_831581
  · exact context_13_433274_831598
  · exact context_13_433275_831606

theorem selected_cut_32353 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 108319) = some ⟨12, 1, 0, 757807, 108319, 1, 65536⟩ := by
  decide +kernel

theorem context_12_108319_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108319 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 108319 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 108319, 1, 65536⟩
    (by decide) selected_cut_32353

theorem unmarked_context_11_27079_831608 : frontier 10 ⟨831608, by decide⟩
    (prefixCache 11 27079) (prefixPartial 11 27079) = false := by
  decide +kernel

theorem node_context_11_27079_831608 : EJMOriginalGlobalDAGData.nodes 10 ⟨831608, by decide⟩ =
    .split (coordinate 11) (![⟨831404, by decide⟩,⟨831521, by decide⟩,⟨831607, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27079_831608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27079 ⟨831608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27079
    ⟨831608, by decide⟩ (by decide) (![⟨831404, by decide⟩,⟨831521, by decide⟩,⟨831607, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_27079_831608 node_context_11_27079_831608
  intro a
  fin_cases a
  · exact context_12_108316_831404
  · exact context_12_108317_831521
  · exact context_12_108318_831607
  · exact context_12_108319_757807

theorem unmarked_context_10_6769_831609 : frontier 11 ⟨831609, by decide⟩
    (prefixCache 10 6769) (prefixPartial 10 6769) = false := by
  decide +kernel

theorem node_context_10_6769_831609 : EJMOriginalGlobalDAGData.nodes 11 ⟨831609, by decide⟩ =
    .split (coordinate 10) (![⟨830902, by decide⟩,⟨815620, by decide⟩,⟨831311, by decide⟩,⟨831608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6769_831609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6769 ⟨831609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6769
    ⟨831609, by decide⟩ (by decide) (![⟨830902, by decide⟩,⟨815620, by decide⟩,⟨831311, by decide⟩,⟨831608, by decide⟩]) unmarked_context_10_6769_831609 node_context_10_6769_831609
  intro a
  fin_cases a
  · exact context_11_27076_830902
  · exact context_11_27077_815620
  · exact context_11_27078_831311
  · exact context_11_27079_831608

theorem selected_cut_32354 : selected 8 ⟨831640, by decide⟩
    (prefixPartial 13 433280) = some ⟨13, 2, 0, 831640, 433280, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_433280_831640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433280 ⟨831640, by decide⟩ :=
  accepted_of_selected 13 433280 ⟨831640, by decide⟩ ⟨13, 2, 0, 831640, 433280, 1425, 16384⟩
    (by decide) selected_cut_32354

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
