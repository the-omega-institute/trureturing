/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover460
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44258 : selected 10 ⟨1215923, by decide⟩
    (prefixPartial 11 88400) = some ⟨11, 2, 0, 1215923, 88400, 5, 262144⟩ := by
  decide +kernel

theorem context_11_88400_1215923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88400 ⟨1215923, by decide⟩ :=
  accepted_of_selected 11 88400 ⟨1215923, by decide⟩ ⟨11, 2, 0, 1215923, 88400, 5, 262144⟩
    (by decide) selected_cut_44258

theorem selected_cut_44259 : selected 10 ⟨1216062, by decide⟩
    (prefixPartial 11 88401) = some ⟨11, 2, 0, 1216062, 88401, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_88401_1216062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88401 ⟨1216062, by decide⟩ :=
  accepted_of_selected 11 88401 ⟨1216062, by decide⟩ ⟨11, 2, 0, 1216062, 88401, 3169, 262144⟩
    (by decide) selected_cut_44259

theorem selected_cut_44260 : selected 10 ⟨1216155, by decide⟩
    (prefixPartial 11 88402) = some ⟨11, 2, 0, 1216155, 88402, 3801, 262144⟩ := by
  decide +kernel

theorem context_11_88402_1216155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88402 ⟨1216155, by decide⟩ :=
  accepted_of_selected 11 88402 ⟨1216155, by decide⟩ ⟨11, 2, 0, 1216155, 88402, 3801, 262144⟩
    (by decide) selected_cut_44260

theorem selected_cut_44261 : selected 10 ⟨1216265, by decide⟩
    (prefixPartial 11 88403) = some ⟨11, 2, 0, 1216265, 88403, 3833, 262144⟩ := by
  decide +kernel

theorem context_11_88403_1216265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88403 ⟨1216265, by decide⟩ :=
  accepted_of_selected 11 88403 ⟨1216265, by decide⟩ ⟨11, 2, 0, 1216265, 88403, 3833, 262144⟩
    (by decide) selected_cut_44261

theorem unmarked_context_10_22100_1216266 : frontier 11 ⟨1216266, by decide⟩
    (prefixCache 10 22100) (prefixPartial 10 22100) = false := by
  decide +kernel

theorem node_context_10_22100_1216266 : EJMOriginalGlobalDAGData.nodes 11 ⟨1216266, by decide⟩ =
    .split (coordinate 10) (![⟨1215923, by decide⟩,⟨1216062, by decide⟩,⟨1216155, by decide⟩,⟨1216265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22100_1216266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22100 ⟨1216266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22100
    ⟨1216266, by decide⟩ (by decide) (![⟨1215923, by decide⟩,⟨1216062, by decide⟩,⟨1216155, by decide⟩,⟨1216265, by decide⟩]) unmarked_context_10_22100_1216266 node_context_10_22100_1216266
  intro a
  fin_cases a
  · exact context_11_88400_1215923
  · exact context_11_88401_1216062
  · exact context_11_88402_1216155
  · exact context_11_88403_1216265

theorem selected_cut_44262 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22101) = some ⟨10, 1, 0, 893098, 22101, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22101_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22101 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22101 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22101, 1, 1048576⟩
    (by decide) selected_cut_44262

theorem selected_cut_44263 : selected 10 ⟨1216353, by decide⟩
    (prefixPartial 11 88408) = some ⟨11, 2, 0, 1216353, 88408, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_88408_1216353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88408 ⟨1216353, by decide⟩ :=
  accepted_of_selected 11 88408 ⟨1216353, by decide⟩ ⟨11, 2, 0, 1216353, 88408, 3137, 262144⟩
    (by decide) selected_cut_44263

theorem selected_cut_44264 : selected 10 ⟨1216439, by decide⟩
    (prefixPartial 11 88409) = some ⟨11, 2, 0, 1216439, 88409, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_88409_1216439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88409 ⟨1216439, by decide⟩ :=
  accepted_of_selected 11 88409 ⟨1216439, by decide⟩ ⟨11, 2, 0, 1216439, 88409, 2513, 262144⟩
    (by decide) selected_cut_44264

theorem selected_cut_44265 : selected 10 ⟨1216552, by decide⟩
    (prefixPartial 11 88410) = some ⟨11, 2, 0, 1216552, 88410, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_88410_1216552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88410 ⟨1216552, by decide⟩ :=
  accepted_of_selected 11 88410 ⟨1216552, by decide⟩ ⟨11, 2, 0, 1216552, 88410, 1645, 262144⟩
    (by decide) selected_cut_44265

theorem selected_cut_44266 : selected 10 ⟨1216635, by decide⟩
    (prefixPartial 11 88411) = some ⟨11, 2, 0, 1216635, 88411, 2945, 262144⟩ := by
  decide +kernel

theorem context_11_88411_1216635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88411 ⟨1216635, by decide⟩ :=
  accepted_of_selected 11 88411 ⟨1216635, by decide⟩ ⟨11, 2, 0, 1216635, 88411, 2945, 262144⟩
    (by decide) selected_cut_44266

theorem unmarked_context_10_22102_1216636 : frontier 11 ⟨1216636, by decide⟩
    (prefixCache 10 22102) (prefixPartial 10 22102) = false := by
  decide +kernel

theorem node_context_10_22102_1216636 : EJMOriginalGlobalDAGData.nodes 11 ⟨1216636, by decide⟩ =
    .split (coordinate 10) (![⟨1216353, by decide⟩,⟨1216439, by decide⟩,⟨1216552, by decide⟩,⟨1216635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22102_1216636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22102 ⟨1216636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22102
    ⟨1216636, by decide⟩ (by decide) (![⟨1216353, by decide⟩,⟨1216439, by decide⟩,⟨1216552, by decide⟩,⟨1216635, by decide⟩]) unmarked_context_10_22102_1216636 node_context_10_22102_1216636
  intro a
  fin_cases a
  · exact context_11_88408_1216353
  · exact context_11_88409_1216439
  · exact context_11_88410_1216552
  · exact context_11_88411_1216635

theorem selected_cut_44267 : selected 10 ⟨1216718, by decide⟩
    (prefixPartial 11 88412) = some ⟨11, 2, 0, 1216718, 88412, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_88412_1216718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88412 ⟨1216718, by decide⟩ :=
  accepted_of_selected 11 88412 ⟨1216718, by decide⟩ ⟨11, 2, 0, 1216718, 88412, 2885, 262144⟩
    (by decide) selected_cut_44267

theorem selected_cut_44268 : selected 10 ⟨1216792, by decide⟩
    (prefixPartial 11 88413) = some ⟨11, 2, 0, 1216792, 88413, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_88413_1216792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88413 ⟨1216792, by decide⟩ :=
  accepted_of_selected 11 88413 ⟨1216792, by decide⟩ ⟨11, 2, 0, 1216792, 88413, 2169, 262144⟩
    (by decide) selected_cut_44268

theorem selected_cut_44269 : selected 10 ⟨1216840, by decide⟩
    (prefixPartial 11 88414) = some ⟨11, 2, 0, 1216840, 88414, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_88414_1216840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88414 ⟨1216840, by decide⟩ :=
  accepted_of_selected 11 88414 ⟨1216840, by decide⟩ ⟨11, 2, 0, 1216840, 88414, 2089, 262144⟩
    (by decide) selected_cut_44269

theorem selected_cut_44270 : selected 10 ⟨1216959, by decide⟩
    (prefixPartial 11 88415) = some ⟨11, 2, 0, 1216959, 88415, 1117, 262144⟩ := by
  decide +kernel

theorem context_11_88415_1216959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88415 ⟨1216959, by decide⟩ :=
  accepted_of_selected 11 88415 ⟨1216959, by decide⟩ ⟨11, 2, 0, 1216959, 88415, 1117, 262144⟩
    (by decide) selected_cut_44270

theorem unmarked_context_10_22103_1216960 : frontier 11 ⟨1216960, by decide⟩
    (prefixCache 10 22103) (prefixPartial 10 22103) = false := by
  decide +kernel

theorem node_context_10_22103_1216960 : EJMOriginalGlobalDAGData.nodes 11 ⟨1216960, by decide⟩ =
    .split (coordinate 10) (![⟨1216718, by decide⟩,⟨1216792, by decide⟩,⟨1216840, by decide⟩,⟨1216959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22103_1216960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22103 ⟨1216960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22103
    ⟨1216960, by decide⟩ (by decide) (![⟨1216718, by decide⟩,⟨1216792, by decide⟩,⟨1216840, by decide⟩,⟨1216959, by decide⟩]) unmarked_context_10_22103_1216960 node_context_10_22103_1216960
  intro a
  fin_cases a
  · exact context_11_88412_1216718
  · exact context_11_88413_1216792
  · exact context_11_88414_1216840
  · exact context_11_88415_1216959

theorem unmarked_context_9_5525_1216961 : frontier 12 ⟨1216961, by decide⟩
    (prefixCache 9 5525) (prefixPartial 9 5525) = false := by
  decide +kernel

theorem node_context_9_5525_1216961 : EJMOriginalGlobalDAGData.nodes 12 ⟨1216961, by decide⟩ =
    .split (coordinate 9) (![⟨1216266, by decide⟩,⟨893098, by decide⟩,⟨1216636, by decide⟩,⟨1216960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5525_1216961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5525 ⟨1216961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5525
    ⟨1216961, by decide⟩ (by decide) (![⟨1216266, by decide⟩,⟨893098, by decide⟩,⟨1216636, by decide⟩,⟨1216960, by decide⟩]) unmarked_context_9_5525_1216961 node_context_9_5525_1216961
  intro a
  fin_cases a
  · exact context_10_22100_1216266
  · exact context_10_22101_893098
  · exact context_10_22102_1216636
  · exact context_10_22103_1216960

theorem selected_cut_44271 : selected 10 ⟨1217029, by decide⟩
    (prefixPartial 11 88416) = some ⟨11, 2, 0, 1217029, 88416, 2417, 262144⟩ := by
  decide +kernel

theorem context_11_88416_1217029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88416 ⟨1217029, by decide⟩ :=
  accepted_of_selected 11 88416 ⟨1217029, by decide⟩ ⟨11, 2, 0, 1217029, 88416, 2417, 262144⟩
    (by decide) selected_cut_44271

theorem selected_cut_44272 : selected 10 ⟨1217074, by decide⟩
    (prefixPartial 11 88417) = some ⟨11, 2, 0, 1217074, 88417, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_88417_1217074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88417 ⟨1217074, by decide⟩ :=
  accepted_of_selected 11 88417 ⟨1217074, by decide⟩ ⟨11, 2, 0, 1217074, 88417, 1873, 262144⟩
    (by decide) selected_cut_44272

theorem selected_cut_44273 : selected 10 ⟨1217160, by decide⟩
    (prefixPartial 11 88418) = some ⟨11, 2, 0, 1217160, 88418, 3501, 262144⟩ := by
  decide +kernel

theorem context_11_88418_1217160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88418 ⟨1217160, by decide⟩ :=
  accepted_of_selected 11 88418 ⟨1217160, by decide⟩ ⟨11, 2, 0, 1217160, 88418, 3501, 262144⟩
    (by decide) selected_cut_44273

theorem selected_cut_44274 : selected 10 ⟨1217225, by decide⟩
    (prefixPartial 11 88419) = some ⟨11, 2, 0, 1217225, 88419, 3481, 262144⟩ := by
  decide +kernel

theorem context_11_88419_1217225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88419 ⟨1217225, by decide⟩ :=
  accepted_of_selected 11 88419 ⟨1217225, by decide⟩ ⟨11, 2, 0, 1217225, 88419, 3481, 262144⟩
    (by decide) selected_cut_44274

theorem unmarked_context_10_22104_1217226 : frontier 11 ⟨1217226, by decide⟩
    (prefixCache 10 22104) (prefixPartial 10 22104) = false := by
  decide +kernel

theorem node_context_10_22104_1217226 : EJMOriginalGlobalDAGData.nodes 11 ⟨1217226, by decide⟩ =
    .split (coordinate 10) (![⟨1217029, by decide⟩,⟨1217074, by decide⟩,⟨1217160, by decide⟩,⟨1217225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22104_1217226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22104 ⟨1217226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22104
    ⟨1217226, by decide⟩ (by decide) (![⟨1217029, by decide⟩,⟨1217074, by decide⟩,⟨1217160, by decide⟩,⟨1217225, by decide⟩]) unmarked_context_10_22104_1217226 node_context_10_22104_1217226
  intro a
  fin_cases a
  · exact context_11_88416_1217029
  · exact context_11_88417_1217074
  · exact context_11_88418_1217160
  · exact context_11_88419_1217225

theorem selected_cut_44275 : selected 10 ⟨1217302, by decide⟩
    (prefixPartial 11 88420) = some ⟨11, 2, 0, 1217302, 88420, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_88420_1217302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88420 ⟨1217302, by decide⟩ :=
  accepted_of_selected 11 88420 ⟨1217302, by decide⟩ ⟨11, 2, 0, 1217302, 88420, 1917, 262144⟩
    (by decide) selected_cut_44275

theorem selected_cut_44276 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88421) = some ⟨11, 1, 0, 892405, 88421, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88421_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88421 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88421 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88421, 1, 262144⟩
    (by decide) selected_cut_44276

theorem selected_cut_44277 : selected 10 ⟨1217344, by decide⟩
    (prefixPartial 11 88422) = some ⟨11, 2, 0, 1217344, 88422, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_88422_1217344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88422 ⟨1217344, by decide⟩ :=
  accepted_of_selected 11 88422 ⟨1217344, by decide⟩ ⟨11, 2, 0, 1217344, 88422, 2237, 262144⟩
    (by decide) selected_cut_44277

theorem selected_cut_44278 : selected 10 ⟨1217406, by decide⟩
    (prefixPartial 11 88423) = some ⟨11, 2, 0, 1217406, 88423, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_88423_1217406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88423 ⟨1217406, by decide⟩ :=
  accepted_of_selected 11 88423 ⟨1217406, by decide⟩ ⟨11, 2, 0, 1217406, 88423, 1589, 262144⟩
    (by decide) selected_cut_44278

theorem unmarked_context_10_22105_1217407 : frontier 11 ⟨1217407, by decide⟩
    (prefixCache 10 22105) (prefixPartial 10 22105) = false := by
  decide +kernel

theorem node_context_10_22105_1217407 : EJMOriginalGlobalDAGData.nodes 11 ⟨1217407, by decide⟩ =
    .split (coordinate 10) (![⟨1217302, by decide⟩,⟨892405, by decide⟩,⟨1217344, by decide⟩,⟨1217406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22105_1217407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22105 ⟨1217407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22105
    ⟨1217407, by decide⟩ (by decide) (![⟨1217302, by decide⟩,⟨892405, by decide⟩,⟨1217344, by decide⟩,⟨1217406, by decide⟩]) unmarked_context_10_22105_1217407 node_context_10_22105_1217407
  intro a
  fin_cases a
  · exact context_11_88420_1217302
  · exact context_11_88421_892405
  · exact context_11_88422_1217344
  · exact context_11_88423_1217406

theorem selected_cut_44279 : selected 11 ⟨1217509, by decide⟩
    (prefixPartial 10 22106) = some ⟨10, 2, 0, 1217509, 22106, 3445, 1048576⟩ := by
  decide +kernel

theorem context_10_22106_1217509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22106 ⟨1217509, by decide⟩ :=
  accepted_of_selected 10 22106 ⟨1217509, by decide⟩ ⟨10, 2, 0, 1217509, 22106, 3445, 1048576⟩
    (by decide) selected_cut_44279

theorem selected_cut_44280 : selected 10 ⟨1217564, by decide⟩
    (prefixPartial 11 88428) = some ⟨11, 2, 0, 1217564, 88428, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_88428_1217564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88428 ⟨1217564, by decide⟩ :=
  accepted_of_selected 11 88428 ⟨1217564, by decide⟩ ⟨11, 2, 0, 1217564, 88428, 2413, 262144⟩
    (by decide) selected_cut_44280

theorem selected_cut_44281 : selected 10 ⟨1217588, by decide⟩
    (prefixPartial 11 88429) = some ⟨11, 2, 0, 1217588, 88429, 917, 262144⟩ := by
  decide +kernel

theorem context_11_88429_1217588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88429 ⟨1217588, by decide⟩ :=
  accepted_of_selected 11 88429 ⟨1217588, by decide⟩ ⟨11, 2, 0, 1217588, 88429, 917, 262144⟩
    (by decide) selected_cut_44281

theorem selected_cut_44282 : selected 10 ⟨1217627, by decide⟩
    (prefixPartial 11 88430) = some ⟨11, 2, 0, 1217627, 88430, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_88430_1217627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88430 ⟨1217627, by decide⟩ :=
  accepted_of_selected 11 88430 ⟨1217627, by decide⟩ ⟨11, 2, 0, 1217627, 88430, 1541, 262144⟩
    (by decide) selected_cut_44282

theorem selected_cut_44283 : selected 10 ⟨1217647, by decide⟩
    (prefixPartial 11 88431) = some ⟨11, 2, 0, 1217647, 88431, 925, 262144⟩ := by
  decide +kernel

theorem context_11_88431_1217647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88431 ⟨1217647, by decide⟩ :=
  accepted_of_selected 11 88431 ⟨1217647, by decide⟩ ⟨11, 2, 0, 1217647, 88431, 925, 262144⟩
    (by decide) selected_cut_44283

theorem unmarked_context_10_22107_1217648 : frontier 11 ⟨1217648, by decide⟩
    (prefixCache 10 22107) (prefixPartial 10 22107) = false := by
  decide +kernel

theorem node_context_10_22107_1217648 : EJMOriginalGlobalDAGData.nodes 11 ⟨1217648, by decide⟩ =
    .split (coordinate 10) (![⟨1217564, by decide⟩,⟨1217588, by decide⟩,⟨1217627, by decide⟩,⟨1217647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22107_1217648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22107 ⟨1217648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22107
    ⟨1217648, by decide⟩ (by decide) (![⟨1217564, by decide⟩,⟨1217588, by decide⟩,⟨1217627, by decide⟩,⟨1217647, by decide⟩]) unmarked_context_10_22107_1217648 node_context_10_22107_1217648
  intro a
  fin_cases a
  · exact context_11_88428_1217564
  · exact context_11_88429_1217588
  · exact context_11_88430_1217627
  · exact context_11_88431_1217647

theorem unmarked_context_9_5526_1217649 : frontier 12 ⟨1217649, by decide⟩
    (prefixCache 9 5526) (prefixPartial 9 5526) = false := by
  decide +kernel

theorem node_context_9_5526_1217649 : EJMOriginalGlobalDAGData.nodes 12 ⟨1217649, by decide⟩ =
    .split (coordinate 9) (![⟨1217226, by decide⟩,⟨1217407, by decide⟩,⟨1217509, by decide⟩,⟨1217648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5526_1217649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5526 ⟨1217649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5526
    ⟨1217649, by decide⟩ (by decide) (![⟨1217226, by decide⟩,⟨1217407, by decide⟩,⟨1217509, by decide⟩,⟨1217648, by decide⟩]) unmarked_context_9_5526_1217649 node_context_9_5526_1217649
  intro a
  fin_cases a
  · exact context_10_22104_1217226
  · exact context_10_22105_1217407
  · exact context_10_22106_1217509
  · exact context_10_22107_1217648

theorem selected_cut_44284 : selected 11 ⟨1217738, by decide⟩
    (prefixPartial 10 22108) = some ⟨10, 2, 0, 1217738, 22108, 3817, 1048576⟩ := by
  decide +kernel

theorem context_10_22108_1217738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22108 ⟨1217738, by decide⟩ :=
  accepted_of_selected 10 22108 ⟨1217738, by decide⟩ ⟨10, 2, 0, 1217738, 22108, 3817, 1048576⟩
    (by decide) selected_cut_44284

theorem selected_cut_44285 : selected 11 ⟨1217781, by decide⟩
    (prefixPartial 10 22109) = some ⟨10, 2, 0, 1217781, 22109, 1577, 1048576⟩ := by
  decide +kernel

theorem context_10_22109_1217781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22109 ⟨1217781, by decide⟩ :=
  accepted_of_selected 10 22109 ⟨1217781, by decide⟩ ⟨10, 2, 0, 1217781, 22109, 1577, 1048576⟩
    (by decide) selected_cut_44285

theorem selected_cut_44286 : selected 11 ⟨1217823, by decide⟩
    (prefixPartial 10 22110) = some ⟨10, 2, 0, 1217823, 22110, 1449, 1048576⟩ := by
  decide +kernel

theorem context_10_22110_1217823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22110 ⟨1217823, by decide⟩ :=
  accepted_of_selected 10 22110 ⟨1217823, by decide⟩ ⟨10, 2, 0, 1217823, 22110, 1449, 1048576⟩
    (by decide) selected_cut_44286

theorem selected_cut_44287 : selected 11 ⟨1217838, by decide⟩
    (prefixPartial 10 22111) = some ⟨10, 2, 0, 1217838, 22111, 197, 1048576⟩ := by
  decide +kernel

theorem context_10_22111_1217838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22111 ⟨1217838, by decide⟩ :=
  accepted_of_selected 10 22111 ⟨1217838, by decide⟩ ⟨10, 2, 0, 1217838, 22111, 197, 1048576⟩
    (by decide) selected_cut_44287

theorem unmarked_context_9_5527_1217839 : frontier 12 ⟨1217839, by decide⟩
    (prefixCache 9 5527) (prefixPartial 9 5527) = false := by
  decide +kernel

theorem node_context_9_5527_1217839 : EJMOriginalGlobalDAGData.nodes 12 ⟨1217839, by decide⟩ =
    .split (coordinate 9) (![⟨1217738, by decide⟩,⟨1217781, by decide⟩,⟨1217823, by decide⟩,⟨1217838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5527_1217839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5527 ⟨1217839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5527
    ⟨1217839, by decide⟩ (by decide) (![⟨1217738, by decide⟩,⟨1217781, by decide⟩,⟨1217823, by decide⟩,⟨1217838, by decide⟩]) unmarked_context_9_5527_1217839 node_context_9_5527_1217839
  intro a
  fin_cases a
  · exact context_10_22108_1217738
  · exact context_10_22109_1217781
  · exact context_10_22110_1217823
  · exact context_10_22111_1217838

theorem unmarked_context_8_1381_1217840 : frontier 13 ⟨1217840, by decide⟩
    (prefixCache 8 1381) (prefixPartial 8 1381) = false := by
  decide +kernel

theorem node_context_8_1381_1217840 : EJMOriginalGlobalDAGData.nodes 13 ⟨1217840, by decide⟩ =
    .split (coordinate 8) (![⟨1215920, by decide⟩,⟨1216961, by decide⟩,⟨1217649, by decide⟩,⟨1217839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1381_1217840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1381 ⟨1217840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1381
    ⟨1217840, by decide⟩ (by decide) (![⟨1215920, by decide⟩,⟨1216961, by decide⟩,⟨1217649, by decide⟩,⟨1217839, by decide⟩]) unmarked_context_8_1381_1217840 node_context_8_1381_1217840
  intro a
  fin_cases a
  · exact context_9_5524_1215920
  · exact context_9_5525_1216961
  · exact context_9_5526_1217649
  · exact context_9_5527_1217839

theorem selected_cut_44288 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88448) = some ⟨11, 1, 0, 434745, 88448, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88448_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88448 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88448 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88448, 1, 262144⟩
    (by decide) selected_cut_44288

theorem selected_cut_44289 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353796) = some ⟨12, 1, 0, 448748, 353796, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353796_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353796 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353796 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353796, 1, 65536⟩
    (by decide) selected_cut_44289

theorem selected_cut_44290 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 353797) = some ⟨12, 1, 0, 34034, 353797, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353797_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353797 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 353797 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 353797, 1, 65536⟩
    (by decide) selected_cut_44290

theorem selected_cut_44291 : selected 9 ⟨1217884, by decide⟩
    (prefixPartial 12 353798) = some ⟨12, 2, 0, 1217884, 353798, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_353798_1217884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353798 ⟨1217884, by decide⟩ :=
  accepted_of_selected 12 353798 ⟨1217884, by decide⟩ ⟨12, 2, 0, 1217884, 353798, 1409, 65536⟩
    (by decide) selected_cut_44291

theorem selected_cut_44292 : selected 9 ⟨1217930, by decide⟩
    (prefixPartial 12 353799) = some ⟨12, 2, 0, 1217930, 353799, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_353799_1217930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353799 ⟨1217930, by decide⟩ :=
  accepted_of_selected 12 353799 ⟨1217930, by decide⟩ ⟨12, 2, 0, 1217930, 353799, 2889, 65536⟩
    (by decide) selected_cut_44292

theorem unmarked_context_11_88449_1217931 : frontier 10 ⟨1217931, by decide⟩
    (prefixCache 11 88449) (prefixPartial 11 88449) = false := by
  decide +kernel

theorem node_context_11_88449_1217931 : EJMOriginalGlobalDAGData.nodes 10 ⟨1217931, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1217884, by decide⟩,⟨1217930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88449_1217931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88449 ⟨1217931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88449
    ⟨1217931, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1217884, by decide⟩,⟨1217930, by decide⟩]) unmarked_context_11_88449_1217931 node_context_11_88449_1217931
  intro a
  fin_cases a
  · exact context_12_353796_448748
  · exact context_12_353797_34034
  · exact context_12_353798_1217884
  · exact context_12_353799_1217930

theorem selected_cut_44293 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353800) = some ⟨12, 1, 0, 448748, 353800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353800_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353800 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353800 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353800, 1, 65536⟩
    (by decide) selected_cut_44293

theorem selected_cut_44294 : selected 9 ⟨1217988, by decide⟩
    (prefixPartial 12 353801) = some ⟨12, 2, 0, 1217988, 353801, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_353801_1217988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353801 ⟨1217988, by decide⟩ :=
  accepted_of_selected 12 353801 ⟨1217988, by decide⟩ ⟨12, 2, 0, 1217988, 353801, 2533, 65536⟩
    (by decide) selected_cut_44294

theorem selected_cut_44295 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 353802) = some ⟨12, 1, 0, 893903, 353802, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353802_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353802 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 353802 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 353802, 1, 65536⟩
    (by decide) selected_cut_44295

theorem selected_cut_44296 : selected 9 ⟨1218057, by decide⟩
    (prefixPartial 12 353803) = some ⟨12, 2, 0, 1218057, 353803, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_353803_1218057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353803 ⟨1218057, by decide⟩ :=
  accepted_of_selected 12 353803 ⟨1218057, by decide⟩ ⟨12, 2, 0, 1218057, 353803, 3413, 65536⟩
    (by decide) selected_cut_44296

theorem unmarked_context_11_88450_1218058 : frontier 10 ⟨1218058, by decide⟩
    (prefixCache 11 88450) (prefixPartial 11 88450) = false := by
  decide +kernel

theorem node_context_11_88450_1218058 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218058, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1217988, by decide⟩,⟨893903, by decide⟩,⟨1218057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88450_1218058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88450 ⟨1218058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88450
    ⟨1218058, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1217988, by decide⟩,⟨893903, by decide⟩,⟨1218057, by decide⟩]) unmarked_context_11_88450_1218058 node_context_11_88450_1218058
  intro a
  fin_cases a
  · exact context_12_353800_448748
  · exact context_12_353801_1217988
  · exact context_12_353802_893903
  · exact context_12_353803_1218057

theorem selected_cut_44297 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353804) = some ⟨12, 1, 0, 448748, 353804, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353804_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353804 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353804 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353804, 1, 65536⟩
    (by decide) selected_cut_44297

theorem selected_cut_44298 : selected 9 ⟨1218096, by decide⟩
    (prefixPartial 12 353805) = some ⟨12, 2, 0, 1218096, 353805, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_353805_1218096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353805 ⟨1218096, by decide⟩ :=
  accepted_of_selected 12 353805 ⟨1218096, by decide⟩ ⟨12, 2, 0, 1218096, 353805, 2449, 65536⟩
    (by decide) selected_cut_44298

theorem selected_cut_44299 : selected 9 ⟨1218151, by decide⟩
    (prefixPartial 12 353806) = some ⟨12, 2, 0, 1218151, 353806, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_353806_1218151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353806 ⟨1218151, by decide⟩ :=
  accepted_of_selected 12 353806 ⟨1218151, by decide⟩ ⟨12, 2, 0, 1218151, 353806, 2837, 65536⟩
    (by decide) selected_cut_44299

theorem selected_cut_44300 : selected 9 ⟨1218208, by decide⟩
    (prefixPartial 12 353807) = some ⟨12, 2, 0, 1218208, 353807, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_353807_1218208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353807 ⟨1218208, by decide⟩ :=
  accepted_of_selected 12 353807 ⟨1218208, by decide⟩ ⟨12, 2, 0, 1218208, 353807, 3057, 65536⟩
    (by decide) selected_cut_44300

theorem unmarked_context_11_88451_1218209 : frontier 10 ⟨1218209, by decide⟩
    (prefixCache 11 88451) (prefixPartial 11 88451) = false := by
  decide +kernel

theorem node_context_11_88451_1218209 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218209, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1218096, by decide⟩,⟨1218151, by decide⟩,⟨1218208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88451_1218209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88451 ⟨1218209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88451
    ⟨1218209, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1218096, by decide⟩,⟨1218151, by decide⟩,⟨1218208, by decide⟩]) unmarked_context_11_88451_1218209 node_context_11_88451_1218209
  intro a
  fin_cases a
  · exact context_12_353804_448748
  · exact context_12_353805_1218096
  · exact context_12_353806_1218151
  · exact context_12_353807_1218208

theorem unmarked_context_10_22112_1218210 : frontier 11 ⟨1218210, by decide⟩
    (prefixCache 10 22112) (prefixPartial 10 22112) = false := by
  decide +kernel

theorem node_context_10_22112_1218210 : EJMOriginalGlobalDAGData.nodes 11 ⟨1218210, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1217931, by decide⟩,⟨1218058, by decide⟩,⟨1218209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22112_1218210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22112 ⟨1218210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22112
    ⟨1218210, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1217931, by decide⟩,⟨1218058, by decide⟩,⟨1218209, by decide⟩]) unmarked_context_10_22112_1218210 node_context_10_22112_1218210
  intro a
  fin_cases a
  · exact context_11_88448_434745
  · exact context_11_88449_1217931
  · exact context_11_88450_1218058
  · exact context_11_88451_1218209

theorem selected_cut_44301 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 353808) = some ⟨12, 1, 0, 435160, 353808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353808_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353808 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 353808 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 353808, 1, 65536⟩
    (by decide) selected_cut_44301

theorem selected_cut_44302 : selected 9 ⟨1218244, by decide⟩
    (prefixPartial 12 353809) = some ⟨12, 2, 0, 1218244, 353809, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_353809_1218244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353809 ⟨1218244, by decide⟩ :=
  accepted_of_selected 12 353809 ⟨1218244, by decide⟩ ⟨12, 2, 0, 1218244, 353809, 2273, 65536⟩
    (by decide) selected_cut_44302

theorem selected_cut_44303 : selected 9 ⟨1218284, by decide⟩
    (prefixPartial 12 353810) = some ⟨12, 2, 0, 1218284, 353810, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_353810_1218284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353810 ⟨1218284, by decide⟩ :=
  accepted_of_selected 12 353810 ⟨1218284, by decide⟩ ⟨12, 2, 0, 1218284, 353810, 2553, 65536⟩
    (by decide) selected_cut_44303

theorem selected_cut_44304 : selected 9 ⟨1218341, by decide⟩
    (prefixPartial 12 353811) = some ⟨12, 2, 0, 1218341, 353811, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_353811_1218341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353811 ⟨1218341, by decide⟩ :=
  accepted_of_selected 12 353811 ⟨1218341, by decide⟩ ⟨12, 2, 0, 1218341, 353811, 3141, 65536⟩
    (by decide) selected_cut_44304

theorem unmarked_context_11_88452_1218342 : frontier 10 ⟨1218342, by decide⟩
    (prefixCache 11 88452) (prefixPartial 11 88452) = false := by
  decide +kernel

theorem node_context_11_88452_1218342 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218342, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1218244, by decide⟩,⟨1218284, by decide⟩,⟨1218341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88452_1218342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88452 ⟨1218342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88452
    ⟨1218342, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1218244, by decide⟩,⟨1218284, by decide⟩,⟨1218341, by decide⟩]) unmarked_context_11_88452_1218342 node_context_11_88452_1218342
  intro a
  fin_cases a
  · exact context_12_353808_435160
  · exact context_12_353809_1218244
  · exact context_12_353810_1218284
  · exact context_12_353811_1218341

theorem selected_cut_44305 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88453) = some ⟨11, 1, 0, 892405, 88453, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88453_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88453 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88453 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88453, 1, 262144⟩
    (by decide) selected_cut_44305

theorem selected_cut_44306 : selected 9 ⟨1218396, by decide⟩
    (prefixPartial 12 353816) = some ⟨12, 2, 0, 1218396, 353816, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_353816_1218396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353816 ⟨1218396, by decide⟩ :=
  accepted_of_selected 12 353816 ⟨1218396, by decide⟩ ⟨12, 2, 0, 1218396, 353816, 2605, 65536⟩
    (by decide) selected_cut_44306

theorem selected_cut_44307 : selected 9 ⟨1218422, by decide⟩
    (prefixPartial 12 353817) = some ⟨12, 2, 0, 1218422, 353817, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_353817_1218422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353817 ⟨1218422, by decide⟩ :=
  accepted_of_selected 12 353817 ⟨1218422, by decide⟩ ⟨12, 2, 0, 1218422, 353817, 2101, 65536⟩
    (by decide) selected_cut_44307

theorem selected_cut_44308 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 353818) = some ⟨12, 1, 0, 893903, 353818, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353818_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353818 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 353818 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 353818, 1, 65536⟩
    (by decide) selected_cut_44308

theorem selected_cut_44309 : selected 9 ⟨1218481, by decide⟩
    (prefixPartial 12 353819) = some ⟨12, 2, 0, 1218481, 353819, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_353819_1218481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353819 ⟨1218481, by decide⟩ :=
  accepted_of_selected 12 353819 ⟨1218481, by decide⟩ ⟨12, 2, 0, 1218481, 353819, 2969, 65536⟩
    (by decide) selected_cut_44309

theorem unmarked_context_11_88454_1218482 : frontier 10 ⟨1218482, by decide⟩
    (prefixCache 11 88454) (prefixPartial 11 88454) = false := by
  decide +kernel

theorem node_context_11_88454_1218482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218482, by decide⟩ =
    .split (coordinate 11) (![⟨1218396, by decide⟩,⟨1218422, by decide⟩,⟨893903, by decide⟩,⟨1218481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88454_1218482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88454 ⟨1218482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88454
    ⟨1218482, by decide⟩ (by decide) (![⟨1218396, by decide⟩,⟨1218422, by decide⟩,⟨893903, by decide⟩,⟨1218481, by decide⟩]) unmarked_context_11_88454_1218482 node_context_11_88454_1218482
  intro a
  fin_cases a
  · exact context_12_353816_1218396
  · exact context_12_353817_1218422
  · exact context_12_353818_893903
  · exact context_12_353819_1218481

theorem selected_cut_44310 : selected 9 ⟨1218523, by decide⟩
    (prefixPartial 12 353820) = some ⟨12, 2, 0, 1218523, 353820, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_353820_1218523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353820 ⟨1218523, by decide⟩ :=
  accepted_of_selected 12 353820 ⟨1218523, by decide⟩ ⟨12, 2, 0, 1218523, 353820, 2501, 65536⟩
    (by decide) selected_cut_44310

theorem selected_cut_44311 : selected 9 ⟨1218548, by decide⟩
    (prefixPartial 12 353821) = some ⟨12, 2, 0, 1218548, 353821, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_353821_1218548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353821 ⟨1218548, by decide⟩ :=
  accepted_of_selected 12 353821 ⟨1218548, by decide⟩ ⟨12, 2, 0, 1218548, 353821, 2045, 65536⟩
    (by decide) selected_cut_44311

theorem selected_cut_44312 : selected 9 ⟨1218585, by decide⟩
    (prefixPartial 12 353822) = some ⟨12, 2, 0, 1218585, 353822, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_353822_1218585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353822 ⟨1218585, by decide⟩ :=
  accepted_of_selected 12 353822 ⟨1218585, by decide⟩ ⟨12, 2, 0, 1218585, 353822, 2401, 65536⟩
    (by decide) selected_cut_44312

theorem selected_cut_44313 : selected 9 ⟨1218624, by decide⟩
    (prefixPartial 12 353823) = some ⟨12, 2, 0, 1218624, 353823, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_353823_1218624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353823 ⟨1218624, by decide⟩ :=
  accepted_of_selected 12 353823 ⟨1218624, by decide⟩ ⟨12, 2, 0, 1218624, 353823, 2681, 65536⟩
    (by decide) selected_cut_44313

theorem unmarked_context_11_88455_1218625 : frontier 10 ⟨1218625, by decide⟩
    (prefixCache 11 88455) (prefixPartial 11 88455) = false := by
  decide +kernel

theorem node_context_11_88455_1218625 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218625, by decide⟩ =
    .split (coordinate 11) (![⟨1218523, by decide⟩,⟨1218548, by decide⟩,⟨1218585, by decide⟩,⟨1218624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88455_1218625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88455 ⟨1218625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88455
    ⟨1218625, by decide⟩ (by decide) (![⟨1218523, by decide⟩,⟨1218548, by decide⟩,⟨1218585, by decide⟩,⟨1218624, by decide⟩]) unmarked_context_11_88455_1218625 node_context_11_88455_1218625
  intro a
  fin_cases a
  · exact context_12_353820_1218523
  · exact context_12_353821_1218548
  · exact context_12_353822_1218585
  · exact context_12_353823_1218624

theorem unmarked_context_10_22113_1218626 : frontier 11 ⟨1218626, by decide⟩
    (prefixCache 10 22113) (prefixPartial 10 22113) = false := by
  decide +kernel

theorem node_context_10_22113_1218626 : EJMOriginalGlobalDAGData.nodes 11 ⟨1218626, by decide⟩ =
    .split (coordinate 10) (![⟨1218342, by decide⟩,⟨892405, by decide⟩,⟨1218482, by decide⟩,⟨1218625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22113_1218626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22113 ⟨1218626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22113
    ⟨1218626, by decide⟩ (by decide) (![⟨1218342, by decide⟩,⟨892405, by decide⟩,⟨1218482, by decide⟩,⟨1218625, by decide⟩]) unmarked_context_10_22113_1218626 node_context_10_22113_1218626
  intro a
  fin_cases a
  · exact context_11_88452_1218342
  · exact context_11_88453_892405
  · exact context_11_88454_1218482
  · exact context_11_88455_1218625

theorem selected_cut_44314 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 353824) = some ⟨12, 1, 0, 1187656, 353824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353824_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353824 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 353824 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 353824, 1, 65536⟩
    (by decide) selected_cut_44314

theorem selected_cut_44315 : selected 9 ⟨1218660, by decide⟩
    (prefixPartial 12 353825) = some ⟨12, 2, 0, 1218660, 353825, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_353825_1218660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353825 ⟨1218660, by decide⟩ :=
  accepted_of_selected 12 353825 ⟨1218660, by decide⟩ ⟨12, 2, 0, 1218660, 353825, 2325, 65536⟩
    (by decide) selected_cut_44315

theorem selected_cut_44316 : selected 9 ⟨1218695, by decide⟩
    (prefixPartial 12 353826) = some ⟨12, 2, 0, 1218695, 353826, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_353826_1218695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353826 ⟨1218695, by decide⟩ :=
  accepted_of_selected 12 353826 ⟨1218695, by decide⟩ ⟨12, 2, 0, 1218695, 353826, 2469, 65536⟩
    (by decide) selected_cut_44316

theorem selected_cut_44317 : selected 9 ⟨1218746, by decide⟩
    (prefixPartial 12 353827) = some ⟨12, 2, 0, 1218746, 353827, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_353827_1218746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353827 ⟨1218746, by decide⟩ :=
  accepted_of_selected 12 353827 ⟨1218746, by decide⟩ ⟨12, 2, 0, 1218746, 353827, 3009, 65536⟩
    (by decide) selected_cut_44317

theorem unmarked_context_11_88456_1218747 : frontier 10 ⟨1218747, by decide⟩
    (prefixCache 11 88456) (prefixPartial 11 88456) = false := by
  decide +kernel

theorem node_context_11_88456_1218747 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218747, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1218660, by decide⟩,⟨1218695, by decide⟩,⟨1218746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88456_1218747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88456 ⟨1218747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88456
    ⟨1218747, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1218660, by decide⟩,⟨1218695, by decide⟩,⟨1218746, by decide⟩]) unmarked_context_11_88456_1218747 node_context_11_88456_1218747
  intro a
  fin_cases a
  · exact context_12_353824_1187656
  · exact context_12_353825_1218660
  · exact context_12_353826_1218695
  · exact context_12_353827_1218746

theorem selected_cut_44318 : selected 9 ⟨1218781, by decide⟩
    (prefixPartial 12 353828) = some ⟨12, 2, 0, 1218781, 353828, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_353828_1218781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353828 ⟨1218781, by decide⟩ :=
  accepted_of_selected 12 353828 ⟨1218781, by decide⟩ ⟨12, 2, 0, 1218781, 353828, 2205, 65536⟩
    (by decide) selected_cut_44318

theorem selected_cut_44319 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 353829) = some ⟨12, 1, 0, 688903, 353829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353829_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353829 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 353829 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 353829, 1, 65536⟩
    (by decide) selected_cut_44319

theorem selected_cut_44320 : selected 9 ⟨1218810, by decide⟩
    (prefixPartial 12 353830) = some ⟨12, 2, 0, 1218810, 353830, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_353830_1218810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353830 ⟨1218810, by decide⟩ :=
  accepted_of_selected 12 353830 ⟨1218810, by decide⟩ ⟨12, 2, 0, 1218810, 353830, 2001, 65536⟩
    (by decide) selected_cut_44320

theorem selected_cut_44321 : selected 9 ⟨1218853, by decide⟩
    (prefixPartial 12 353831) = some ⟨12, 2, 0, 1218853, 353831, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_353831_1218853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353831 ⟨1218853, by decide⟩ :=
  accepted_of_selected 12 353831 ⟨1218853, by decide⟩ ⟨12, 2, 0, 1218853, 353831, 2493, 65536⟩
    (by decide) selected_cut_44321

theorem unmarked_context_11_88457_1218854 : frontier 10 ⟨1218854, by decide⟩
    (prefixCache 11 88457) (prefixPartial 11 88457) = false := by
  decide +kernel

theorem node_context_11_88457_1218854 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218854, by decide⟩ =
    .split (coordinate 11) (![⟨1218781, by decide⟩,⟨688903, by decide⟩,⟨1218810, by decide⟩,⟨1218853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88457_1218854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88457 ⟨1218854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88457
    ⟨1218854, by decide⟩ (by decide) (![⟨1218781, by decide⟩,⟨688903, by decide⟩,⟨1218810, by decide⟩,⟨1218853, by decide⟩]) unmarked_context_11_88457_1218854 node_context_11_88457_1218854
  intro a
  fin_cases a
  · exact context_12_353828_1218781
  · exact context_12_353829_688903
  · exact context_12_353830_1218810
  · exact context_12_353831_1218853

theorem selected_cut_44322 : selected 9 ⟨1218906, by decide⟩
    (prefixPartial 12 353832) = some ⟨12, 2, 0, 1218906, 353832, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_353832_1218906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353832 ⟨1218906, by decide⟩ :=
  accepted_of_selected 12 353832 ⟨1218906, by decide⟩ ⟨12, 2, 0, 1218906, 353832, 2557, 65536⟩
    (by decide) selected_cut_44322

theorem selected_cut_44323 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 353833) = some ⟨12, 1, 0, 661671, 353833, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353833_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353833 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 353833 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 353833, 1, 65536⟩
    (by decide) selected_cut_44323

theorem selected_cut_44324 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 353834) = some ⟨12, 1, 0, 1113261, 353834, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353834_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353834 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 353834 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 353834, 1, 65536⟩
    (by decide) selected_cut_44324

theorem selected_cut_44325 : selected 9 ⟨1218955, by decide⟩
    (prefixPartial 12 353835) = some ⟨12, 2, 0, 1218955, 353835, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_353835_1218955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353835 ⟨1218955, by decide⟩ :=
  accepted_of_selected 12 353835 ⟨1218955, by decide⟩ ⟨12, 2, 0, 1218955, 353835, 2781, 65536⟩
    (by decide) selected_cut_44325

theorem unmarked_context_11_88458_1218956 : frontier 10 ⟨1218956, by decide⟩
    (prefixCache 11 88458) (prefixPartial 11 88458) = false := by
  decide +kernel

theorem node_context_11_88458_1218956 : EJMOriginalGlobalDAGData.nodes 10 ⟨1218956, by decide⟩ =
    .split (coordinate 11) (![⟨1218906, by decide⟩,⟨661671, by decide⟩,⟨1113261, by decide⟩,⟨1218955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88458_1218956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88458 ⟨1218956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88458
    ⟨1218956, by decide⟩ (by decide) (![⟨1218906, by decide⟩,⟨661671, by decide⟩,⟨1113261, by decide⟩,⟨1218955, by decide⟩]) unmarked_context_11_88458_1218956 node_context_11_88458_1218956
  intro a
  fin_cases a
  · exact context_12_353832_1218906
  · exact context_12_353833_661671
  · exact context_12_353834_1113261
  · exact context_12_353835_1218955

theorem selected_cut_44326 : selected 9 ⟨1219011, by decide⟩
    (prefixPartial 12 353836) = some ⟨12, 2, 0, 1219011, 353836, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_353836_1219011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353836 ⟨1219011, by decide⟩ :=
  accepted_of_selected 12 353836 ⟨1219011, by decide⟩ ⟨12, 2, 0, 1219011, 353836, 2601, 65536⟩
    (by decide) selected_cut_44326

theorem selected_cut_44327 : selected 9 ⟨1219043, by decide⟩
    (prefixPartial 12 353837) = some ⟨12, 2, 0, 1219043, 353837, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_353837_1219043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353837 ⟨1219043, by decide⟩ :=
  accepted_of_selected 12 353837 ⟨1219043, by decide⟩ ⟨12, 2, 0, 1219043, 353837, 2141, 65536⟩
    (by decide) selected_cut_44327

theorem selected_cut_44328 : selected 9 ⟨1219084, by decide⟩
    (prefixPartial 12 353838) = some ⟨12, 2, 0, 1219084, 353838, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_353838_1219084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353838 ⟨1219084, by decide⟩ :=
  accepted_of_selected 12 353838 ⟨1219084, by decide⟩ ⟨12, 2, 0, 1219084, 353838, 2313, 65536⟩
    (by decide) selected_cut_44328

theorem selected_cut_44329 : selected 9 ⟨1219132, by decide⟩
    (prefixPartial 12 353839) = some ⟨12, 2, 0, 1219132, 353839, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_353839_1219132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353839 ⟨1219132, by decide⟩ :=
  accepted_of_selected 12 353839 ⟨1219132, by decide⟩ ⟨12, 2, 0, 1219132, 353839, 2657, 65536⟩
    (by decide) selected_cut_44329

theorem unmarked_context_11_88459_1219133 : frontier 10 ⟨1219133, by decide⟩
    (prefixCache 11 88459) (prefixPartial 11 88459) = false := by
  decide +kernel

theorem node_context_11_88459_1219133 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219133, by decide⟩ =
    .split (coordinate 11) (![⟨1219011, by decide⟩,⟨1219043, by decide⟩,⟨1219084, by decide⟩,⟨1219132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88459_1219133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88459 ⟨1219133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88459
    ⟨1219133, by decide⟩ (by decide) (![⟨1219011, by decide⟩,⟨1219043, by decide⟩,⟨1219084, by decide⟩,⟨1219132, by decide⟩]) unmarked_context_11_88459_1219133 node_context_11_88459_1219133
  intro a
  fin_cases a
  · exact context_12_353836_1219011
  · exact context_12_353837_1219043
  · exact context_12_353838_1219084
  · exact context_12_353839_1219132

theorem unmarked_context_10_22114_1219134 : frontier 11 ⟨1219134, by decide⟩
    (prefixCache 10 22114) (prefixPartial 10 22114) = false := by
  decide +kernel

theorem node_context_10_22114_1219134 : EJMOriginalGlobalDAGData.nodes 11 ⟨1219134, by decide⟩ =
    .split (coordinate 10) (![⟨1218747, by decide⟩,⟨1218854, by decide⟩,⟨1218956, by decide⟩,⟨1219133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22114_1219134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22114 ⟨1219134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22114
    ⟨1219134, by decide⟩ (by decide) (![⟨1218747, by decide⟩,⟨1218854, by decide⟩,⟨1218956, by decide⟩,⟨1219133, by decide⟩]) unmarked_context_10_22114_1219134 node_context_10_22114_1219134
  intro a
  fin_cases a
  · exact context_11_88456_1218747
  · exact context_11_88457_1218854
  · exact context_11_88458_1218956
  · exact context_11_88459_1219133

theorem selected_cut_44330 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 353840) = some ⟨12, 1, 0, 1187656, 353840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353840_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353840 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 353840 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 353840, 1, 65536⟩
    (by decide) selected_cut_44330

theorem selected_cut_44331 : selected 9 ⟨1219161, by decide⟩
    (prefixPartial 12 353841) = some ⟨12, 2, 0, 1219161, 353841, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_353841_1219161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353841 ⟨1219161, by decide⟩ :=
  accepted_of_selected 12 353841 ⟨1219161, by decide⟩ ⟨12, 2, 0, 1219161, 353841, 1989, 65536⟩
    (by decide) selected_cut_44331

theorem selected_cut_44332 : selected 9 ⟨1219198, by decide⟩
    (prefixPartial 12 353842) = some ⟨12, 2, 0, 1219198, 353842, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_353842_1219198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353842 ⟨1219198, by decide⟩ :=
  accepted_of_selected 12 353842 ⟨1219198, by decide⟩ ⟨12, 2, 0, 1219198, 353842, 2253, 65536⟩
    (by decide) selected_cut_44332

theorem selected_cut_44333 : selected 9 ⟨1219259, by decide⟩
    (prefixPartial 12 353843) = some ⟨12, 2, 0, 1219259, 353843, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_353843_1219259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353843 ⟨1219259, by decide⟩ :=
  accepted_of_selected 12 353843 ⟨1219259, by decide⟩ ⟨12, 2, 0, 1219259, 353843, 2577, 65536⟩
    (by decide) selected_cut_44333

theorem unmarked_context_11_88460_1219260 : frontier 10 ⟨1219260, by decide⟩
    (prefixCache 11 88460) (prefixPartial 11 88460) = false := by
  decide +kernel

theorem node_context_11_88460_1219260 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219260, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1219161, by decide⟩,⟨1219198, by decide⟩,⟨1219259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88460_1219260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88460 ⟨1219260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88460
    ⟨1219260, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1219161, by decide⟩,⟨1219198, by decide⟩,⟨1219259, by decide⟩]) unmarked_context_11_88460_1219260 node_context_11_88460_1219260
  intro a
  fin_cases a
  · exact context_12_353840_1187656
  · exact context_12_353841_1219161
  · exact context_12_353842_1219198
  · exact context_12_353843_1219259

theorem selected_cut_44334 : selected 9 ⟨1219285, by decide⟩
    (prefixPartial 12 353844) = some ⟨12, 2, 0, 1219285, 353844, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_353844_1219285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353844 ⟨1219285, by decide⟩ :=
  accepted_of_selected 12 353844 ⟨1219285, by decide⟩ ⟨12, 2, 0, 1219285, 353844, 1881, 65536⟩
    (by decide) selected_cut_44334

theorem selected_cut_44335 : selected 9 ⟨1219310, by decide⟩
    (prefixPartial 12 353845) = some ⟨12, 2, 0, 1219310, 353845, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_353845_1219310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353845 ⟨1219310, by decide⟩ :=
  accepted_of_selected 12 353845 ⟨1219310, by decide⟩ ⟨12, 2, 0, 1219310, 353845, 1621, 65536⟩
    (by decide) selected_cut_44335

theorem selected_cut_44336 : selected 9 ⟨1219340, by decide⟩
    (prefixPartial 12 353846) = some ⟨12, 2, 0, 1219340, 353846, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_353846_1219340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353846 ⟨1219340, by decide⟩ :=
  accepted_of_selected 12 353846 ⟨1219340, by decide⟩ ⟨12, 2, 0, 1219340, 353846, 1801, 65536⟩
    (by decide) selected_cut_44336

theorem selected_cut_44337 : selected 9 ⟨1219381, by decide⟩
    (prefixPartial 12 353847) = some ⟨12, 2, 0, 1219381, 353847, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_353847_1219381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353847 ⟨1219381, by decide⟩ :=
  accepted_of_selected 12 353847 ⟨1219381, by decide⟩ ⟨12, 2, 0, 1219381, 353847, 2077, 65536⟩
    (by decide) selected_cut_44337

theorem unmarked_context_11_88461_1219382 : frontier 10 ⟨1219382, by decide⟩
    (prefixCache 11 88461) (prefixPartial 11 88461) = false := by
  decide +kernel

theorem node_context_11_88461_1219382 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219382, by decide⟩ =
    .split (coordinate 11) (![⟨1219285, by decide⟩,⟨1219310, by decide⟩,⟨1219340, by decide⟩,⟨1219381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88461_1219382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88461 ⟨1219382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88461
    ⟨1219382, by decide⟩ (by decide) (![⟨1219285, by decide⟩,⟨1219310, by decide⟩,⟨1219340, by decide⟩,⟨1219381, by decide⟩]) unmarked_context_11_88461_1219382 node_context_11_88461_1219382
  intro a
  fin_cases a
  · exact context_12_353844_1219285
  · exact context_12_353845_1219310
  · exact context_12_353846_1219340
  · exact context_12_353847_1219381

theorem selected_cut_44338 : selected 9 ⟨1219420, by decide⟩
    (prefixPartial 12 353848) = some ⟨12, 2, 0, 1219420, 353848, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_353848_1219420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353848 ⟨1219420, by decide⟩ :=
  accepted_of_selected 12 353848 ⟨1219420, by decide⟩ ⟨12, 2, 0, 1219420, 353848, 2161, 65536⟩
    (by decide) selected_cut_44338

theorem selected_cut_44339 : selected 9 ⟨1219450, by decide⟩
    (prefixPartial 12 353849) = some ⟨12, 2, 0, 1219450, 353849, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_353849_1219450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353849 ⟨1219450, by decide⟩ :=
  accepted_of_selected 12 353849 ⟨1219450, by decide⟩ ⟨12, 2, 0, 1219450, 353849, 1785, 65536⟩
    (by decide) selected_cut_44339

theorem selected_cut_44340 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 353850) = some ⟨12, 1, 0, 893903, 353850, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353850_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353850 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 353850 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 353850, 1, 65536⟩
    (by decide) selected_cut_44340

theorem selected_cut_44341 : selected 9 ⟨1219503, by decide⟩
    (prefixPartial 12 353851) = some ⟨12, 2, 0, 1219503, 353851, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_353851_1219503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353851 ⟨1219503, by decide⟩ :=
  accepted_of_selected 12 353851 ⟨1219503, by decide⟩ ⟨12, 2, 0, 1219503, 353851, 2433, 65536⟩
    (by decide) selected_cut_44341

theorem unmarked_context_11_88462_1219504 : frontier 10 ⟨1219504, by decide⟩
    (prefixCache 11 88462) (prefixPartial 11 88462) = false := by
  decide +kernel

theorem node_context_11_88462_1219504 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219504, by decide⟩ =
    .split (coordinate 11) (![⟨1219420, by decide⟩,⟨1219450, by decide⟩,⟨893903, by decide⟩,⟨1219503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88462_1219504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88462 ⟨1219504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88462
    ⟨1219504, by decide⟩ (by decide) (![⟨1219420, by decide⟩,⟨1219450, by decide⟩,⟨893903, by decide⟩,⟨1219503, by decide⟩]) unmarked_context_11_88462_1219504 node_context_11_88462_1219504
  intro a
  fin_cases a
  · exact context_12_353848_1219420
  · exact context_12_353849_1219450
  · exact context_12_353850_893903
  · exact context_12_353851_1219503

theorem selected_cut_44342 : selected 9 ⟨1219539, by decide⟩
    (prefixPartial 12 353852) = some ⟨12, 2, 0, 1219539, 353852, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_353852_1219539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353852 ⟨1219539, by decide⟩ :=
  accepted_of_selected 12 353852 ⟨1219539, by decide⟩ ⟨12, 2, 0, 1219539, 353852, 1961, 65536⟩
    (by decide) selected_cut_44342

theorem selected_cut_44343 : selected 9 ⟨1219558, by decide⟩
    (prefixPartial 12 353853) = some ⟨12, 2, 0, 1219558, 353853, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_353853_1219558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353853 ⟨1219558, by decide⟩ :=
  accepted_of_selected 12 353853 ⟨1219558, by decide⟩ ⟨12, 2, 0, 1219558, 353853, 1605, 65536⟩
    (by decide) selected_cut_44343

theorem selected_cut_44344 : selected 9 ⟨1219588, by decide⟩
    (prefixPartial 12 353854) = some ⟨12, 2, 0, 1219588, 353854, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_353854_1219588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353854 ⟨1219588, by decide⟩ :=
  accepted_of_selected 12 353854 ⟨1219588, by decide⟩ ⟨12, 2, 0, 1219588, 353854, 1789, 65536⟩
    (by decide) selected_cut_44344

theorem selected_cut_44345 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 353855) = some ⟨12, 1, 0, 1116246, 353855, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353855_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353855 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 353855 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 353855, 1, 65536⟩
    (by decide) selected_cut_44345

theorem unmarked_context_11_88463_1219589 : frontier 10 ⟨1219589, by decide⟩
    (prefixCache 11 88463) (prefixPartial 11 88463) = false := by
  decide +kernel

theorem node_context_11_88463_1219589 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219589, by decide⟩ =
    .split (coordinate 11) (![⟨1219539, by decide⟩,⟨1219558, by decide⟩,⟨1219588, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88463_1219589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88463 ⟨1219589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88463
    ⟨1219589, by decide⟩ (by decide) (![⟨1219539, by decide⟩,⟨1219558, by decide⟩,⟨1219588, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_88463_1219589 node_context_11_88463_1219589
  intro a
  fin_cases a
  · exact context_12_353852_1219539
  · exact context_12_353853_1219558
  · exact context_12_353854_1219588
  · exact context_12_353855_1116246

theorem unmarked_context_10_22115_1219590 : frontier 11 ⟨1219590, by decide⟩
    (prefixCache 10 22115) (prefixPartial 10 22115) = false := by
  decide +kernel

theorem node_context_10_22115_1219590 : EJMOriginalGlobalDAGData.nodes 11 ⟨1219590, by decide⟩ =
    .split (coordinate 10) (![⟨1219260, by decide⟩,⟨1219382, by decide⟩,⟨1219504, by decide⟩,⟨1219589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22115_1219590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22115 ⟨1219590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22115
    ⟨1219590, by decide⟩ (by decide) (![⟨1219260, by decide⟩,⟨1219382, by decide⟩,⟨1219504, by decide⟩,⟨1219589, by decide⟩]) unmarked_context_10_22115_1219590 node_context_10_22115_1219590
  intro a
  fin_cases a
  · exact context_11_88460_1219260
  · exact context_11_88461_1219382
  · exact context_11_88462_1219504
  · exact context_11_88463_1219589

theorem unmarked_context_9_5528_1219591 : frontier 12 ⟨1219591, by decide⟩
    (prefixCache 9 5528) (prefixPartial 9 5528) = false := by
  decide +kernel

theorem node_context_9_5528_1219591 : EJMOriginalGlobalDAGData.nodes 12 ⟨1219591, by decide⟩ =
    .split (coordinate 9) (![⟨1218210, by decide⟩,⟨1218626, by decide⟩,⟨1219134, by decide⟩,⟨1219590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5528_1219591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5528 ⟨1219591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5528
    ⟨1219591, by decide⟩ (by decide) (![⟨1218210, by decide⟩,⟨1218626, by decide⟩,⟨1219134, by decide⟩,⟨1219590, by decide⟩]) unmarked_context_9_5528_1219591 node_context_9_5528_1219591
  intro a
  fin_cases a
  · exact context_10_22112_1218210
  · exact context_10_22113_1218626
  · exact context_10_22114_1219134
  · exact context_10_22115_1219590

theorem selected_cut_44346 : selected 10 ⟨1219655, by decide⟩
    (prefixPartial 11 88464) = some ⟨11, 2, 0, 1219655, 88464, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_88464_1219655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88464 ⟨1219655, by decide⟩ :=
  accepted_of_selected 11 88464 ⟨1219655, by decide⟩ ⟨11, 2, 0, 1219655, 88464, 3537, 262144⟩
    (by decide) selected_cut_44346

theorem selected_cut_44347 : selected 10 ⟨1219717, by decide⟩
    (prefixPartial 11 88465) = some ⟨11, 2, 0, 1219717, 88465, 4057, 262144⟩ := by
  decide +kernel

theorem context_11_88465_1219717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88465 ⟨1219717, by decide⟩ :=
  accepted_of_selected 11 88465 ⟨1219717, by decide⟩ ⟨11, 2, 0, 1219717, 88465, 4057, 262144⟩
    (by decide) selected_cut_44347

theorem selected_cut_44348 : selected 10 ⟨1219773, by decide⟩
    (prefixPartial 11 88466) = some ⟨11, 2, 0, 1219773, 88466, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_88466_1219773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88466 ⟨1219773, by decide⟩ :=
  accepted_of_selected 11 88466 ⟨1219773, by decide⟩ ⟨11, 2, 0, 1219773, 88466, 3469, 262144⟩
    (by decide) selected_cut_44348

theorem selected_cut_44349 : selected 9 ⟨1219796, by decide⟩
    (prefixPartial 12 353868) = some ⟨12, 2, 0, 1219796, 353868, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_353868_1219796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353868 ⟨1219796, by decide⟩ :=
  accepted_of_selected 12 353868 ⟨1219796, by decide⟩ ⟨12, 2, 0, 1219796, 353868, 1545, 65536⟩
    (by decide) selected_cut_44349

theorem selected_cut_44350 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353869) = some ⟨12, 1, 0, 896706, 353869, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353869_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353869 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353869 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353869, 1, 65536⟩
    (by decide) selected_cut_44350

theorem selected_cut_44351 : selected 9 ⟨1219829, by decide⟩
    (prefixPartial 12 353870) = some ⟨12, 2, 0, 1219829, 353870, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_353870_1219829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353870 ⟨1219829, by decide⟩ :=
  accepted_of_selected 12 353870 ⟨1219829, by decide⟩ ⟨12, 2, 0, 1219829, 353870, 1549, 65536⟩
    (by decide) selected_cut_44351

theorem selected_cut_44352 : selected 9 ⟨1219856, by decide⟩
    (prefixPartial 12 353871) = some ⟨12, 2, 0, 1219856, 353871, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_353871_1219856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353871 ⟨1219856, by decide⟩ :=
  accepted_of_selected 12 353871 ⟨1219856, by decide⟩ ⟨12, 2, 0, 1219856, 353871, 1557, 65536⟩
    (by decide) selected_cut_44352

theorem unmarked_context_11_88467_1219857 : frontier 10 ⟨1219857, by decide⟩
    (prefixCache 11 88467) (prefixPartial 11 88467) = false := by
  decide +kernel

theorem node_context_11_88467_1219857 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219857, by decide⟩ =
    .split (coordinate 11) (![⟨1219796, by decide⟩,⟨896706, by decide⟩,⟨1219829, by decide⟩,⟨1219856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88467_1219857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88467 ⟨1219857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88467
    ⟨1219857, by decide⟩ (by decide) (![⟨1219796, by decide⟩,⟨896706, by decide⟩,⟨1219829, by decide⟩,⟨1219856, by decide⟩]) unmarked_context_11_88467_1219857 node_context_11_88467_1219857
  intro a
  fin_cases a
  · exact context_12_353868_1219796
  · exact context_12_353869_896706
  · exact context_12_353870_1219829
  · exact context_12_353871_1219856

theorem unmarked_context_10_22116_1219858 : frontier 11 ⟨1219858, by decide⟩
    (prefixCache 10 22116) (prefixPartial 10 22116) = false := by
  decide +kernel

theorem node_context_10_22116_1219858 : EJMOriginalGlobalDAGData.nodes 11 ⟨1219858, by decide⟩ =
    .split (coordinate 10) (![⟨1219655, by decide⟩,⟨1219717, by decide⟩,⟨1219773, by decide⟩,⟨1219857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22116_1219858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22116 ⟨1219858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22116
    ⟨1219858, by decide⟩ (by decide) (![⟨1219655, by decide⟩,⟨1219717, by decide⟩,⟨1219773, by decide⟩,⟨1219857, by decide⟩]) unmarked_context_10_22116_1219858 node_context_10_22116_1219858
  intro a
  fin_cases a
  · exact context_11_88464_1219655
  · exact context_11_88465_1219717
  · exact context_11_88466_1219773
  · exact context_11_88467_1219857

theorem selected_cut_44353 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22117) = some ⟨10, 1, 0, 893098, 22117, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22117_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22117 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22117 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22117, 1, 1048576⟩
    (by decide) selected_cut_44353

theorem selected_cut_44354 : selected 9 ⟨1219884, by decide⟩
    (prefixPartial 12 353888) = some ⟨12, 2, 0, 1219884, 353888, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_353888_1219884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353888 ⟨1219884, by decide⟩ :=
  accepted_of_selected 12 353888 ⟨1219884, by decide⟩ ⟨12, 2, 0, 1219884, 353888, 1557, 65536⟩
    (by decide) selected_cut_44354

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
