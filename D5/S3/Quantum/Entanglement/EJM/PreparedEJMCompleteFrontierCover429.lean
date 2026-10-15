/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover428
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41187 : selected 9 ⟨1125658, by decide⟩
    (prefixPartial 12 334407) = some ⟨12, 2, 0, 1125658, 334407, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_334407_1125658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334407 ⟨1125658, by decide⟩ :=
  accepted_of_selected 12 334407 ⟨1125658, by decide⟩ ⟨12, 2, 0, 1125658, 334407, 2429, 65536⟩
    (by decide) selected_cut_41187

theorem unmarked_context_11_83601_1125659 : frontier 10 ⟨1125659, by decide⟩
    (prefixCache 11 83601) (prefixPartial 11 83601) = false := by
  decide +kernel

theorem node_context_11_83601_1125659 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125659, by decide⟩ =
    .split (coordinate 11) (![⟨1125580, by decide⟩,⟨170504, by decide⟩,⟨1125616, by decide⟩,⟨1125658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83601_1125659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83601 ⟨1125659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83601
    ⟨1125659, by decide⟩ (by decide) (![⟨1125580, by decide⟩,⟨170504, by decide⟩,⟨1125616, by decide⟩,⟨1125658, by decide⟩]) unmarked_context_11_83601_1125659 node_context_11_83601_1125659
  intro a
  fin_cases a
  · exact context_12_334404_1125580
  · exact context_12_334405_170504
  · exact context_12_334406_1125616
  · exact context_12_334407_1125658

theorem selected_cut_41188 : selected 9 ⟨1125690, by decide⟩
    (prefixPartial 12 334408) = some ⟨12, 2, 0, 1125690, 334408, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_334408_1125690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334408 ⟨1125690, by decide⟩ :=
  accepted_of_selected 12 334408 ⟨1125690, by decide⟩ ⟨12, 2, 0, 1125690, 334408, 1869, 65536⟩
    (by decide) selected_cut_41188

theorem selected_cut_41189 : selected 9 ⟨1125720, by decide⟩
    (prefixPartial 12 334409) = some ⟨12, 2, 0, 1125720, 334409, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_334409_1125720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334409 ⟨1125720, by decide⟩ :=
  accepted_of_selected 12 334409 ⟨1125720, by decide⟩ ⟨12, 2, 0, 1125720, 334409, 2049, 65536⟩
    (by decide) selected_cut_41189

theorem selected_cut_41190 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 334410) = some ⟨12, 1, 0, 893903, 334410, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334410_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334410 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 334410 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 334410, 1, 65536⟩
    (by decide) selected_cut_41190

theorem selected_cut_41191 : selected 9 ⟨1125756, by decide⟩
    (prefixPartial 12 334411) = some ⟨12, 2, 0, 1125756, 334411, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_334411_1125756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334411 ⟨1125756, by decide⟩ :=
  accepted_of_selected 12 334411 ⟨1125756, by decide⟩ ⟨12, 2, 0, 1125756, 334411, 2285, 65536⟩
    (by decide) selected_cut_41191

theorem unmarked_context_11_83602_1125757 : frontier 10 ⟨1125757, by decide⟩
    (prefixCache 11 83602) (prefixPartial 11 83602) = false := by
  decide +kernel

theorem node_context_11_83602_1125757 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125757, by decide⟩ =
    .split (coordinate 11) (![⟨1125690, by decide⟩,⟨1125720, by decide⟩,⟨893903, by decide⟩,⟨1125756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83602_1125757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83602 ⟨1125757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83602
    ⟨1125757, by decide⟩ (by decide) (![⟨1125690, by decide⟩,⟨1125720, by decide⟩,⟨893903, by decide⟩,⟨1125756, by decide⟩]) unmarked_context_11_83602_1125757 node_context_11_83602_1125757
  intro a
  fin_cases a
  · exact context_12_334408_1125690
  · exact context_12_334409_1125720
  · exact context_12_334410_893903
  · exact context_12_334411_1125756

theorem selected_cut_41192 : selected 9 ⟨1125794, by decide⟩
    (prefixPartial 12 334412) = some ⟨12, 2, 0, 1125794, 334412, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_334412_1125794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334412 ⟨1125794, by decide⟩ :=
  accepted_of_selected 12 334412 ⟨1125794, by decide⟩ ⟨12, 2, 0, 1125794, 334412, 2249, 65536⟩
    (by decide) selected_cut_41192

theorem selected_cut_41193 : selected 9 ⟨1125831, by decide⟩
    (prefixPartial 12 334413) = some ⟨12, 2, 0, 1125831, 334413, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_334413_1125831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334413 ⟨1125831, by decide⟩ :=
  accepted_of_selected 12 334413 ⟨1125831, by decide⟩ ⟨12, 2, 0, 1125831, 334413, 2225, 65536⟩
    (by decide) selected_cut_41193

theorem selected_cut_41194 : selected 9 ⟨1125875, by decide⟩
    (prefixPartial 12 334414) = some ⟨12, 2, 0, 1125875, 334414, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_334414_1125875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334414 ⟨1125875, by decide⟩ :=
  accepted_of_selected 12 334414 ⟨1125875, by decide⟩ ⟨12, 2, 0, 1125875, 334414, 2537, 65536⟩
    (by decide) selected_cut_41194

theorem selected_cut_41195 : selected 9 ⟨1125902, by decide⟩
    (prefixPartial 12 334415) = some ⟨12, 2, 0, 1125902, 334415, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_334415_1125902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334415 ⟨1125902, by decide⟩ :=
  accepted_of_selected 12 334415 ⟨1125902, by decide⟩ ⟨12, 2, 0, 1125902, 334415, 2077, 65536⟩
    (by decide) selected_cut_41195

theorem unmarked_context_11_83603_1125903 : frontier 10 ⟨1125903, by decide⟩
    (prefixCache 11 83603) (prefixPartial 11 83603) = false := by
  decide +kernel

theorem node_context_11_83603_1125903 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125903, by decide⟩ =
    .split (coordinate 11) (![⟨1125794, by decide⟩,⟨1125831, by decide⟩,⟨1125875, by decide⟩,⟨1125902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83603_1125903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83603 ⟨1125903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83603
    ⟨1125903, by decide⟩ (by decide) (![⟨1125794, by decide⟩,⟨1125831, by decide⟩,⟨1125875, by decide⟩,⟨1125902, by decide⟩]) unmarked_context_11_83603_1125903 node_context_11_83603_1125903
  intro a
  fin_cases a
  · exact context_12_334412_1125794
  · exact context_12_334413_1125831
  · exact context_12_334414_1125875
  · exact context_12_334415_1125902

theorem unmarked_context_10_20900_1125904 : frontier 11 ⟨1125904, by decide⟩
    (prefixCache 10 20900) (prefixPartial 10 20900) = false := by
  decide +kernel

theorem node_context_10_20900_1125904 : EJMOriginalGlobalDAGData.nodes 11 ⟨1125904, by decide⟩ =
    .split (coordinate 10) (![⟨1125546, by decide⟩,⟨1125659, by decide⟩,⟨1125757, by decide⟩,⟨1125903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20900_1125904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20900 ⟨1125904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20900
    ⟨1125904, by decide⟩ (by decide) (![⟨1125546, by decide⟩,⟨1125659, by decide⟩,⟨1125757, by decide⟩,⟨1125903, by decide⟩]) unmarked_context_10_20900_1125904 node_context_10_20900_1125904
  intro a
  fin_cases a
  · exact context_11_83600_1125546
  · exact context_11_83601_1125659
  · exact context_11_83602_1125757
  · exact context_11_83603_1125903

theorem selected_cut_41196 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20901) = some ⟨10, 1, 0, 893098, 20901, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20901_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20901 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20901 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20901, 1, 1048576⟩
    (by decide) selected_cut_41196

theorem selected_cut_41197 : selected 9 ⟨1125950, by decide⟩
    (prefixPartial 12 334432) = some ⟨12, 2, 0, 1125950, 334432, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_334432_1125950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334432 ⟨1125950, by decide⟩ :=
  accepted_of_selected 12 334432 ⟨1125950, by decide⟩ ⟨12, 2, 0, 1125950, 334432, 2117, 65536⟩
    (by decide) selected_cut_41197

theorem selected_cut_41198 : selected 9 ⟨1125982, by decide⟩
    (prefixPartial 12 334433) = some ⟨12, 2, 0, 1125982, 334433, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_334433_1125982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334433 ⟨1125982, by decide⟩ :=
  accepted_of_selected 12 334433 ⟨1125982, by decide⟩ ⟨12, 2, 0, 1125982, 334433, 2133, 65536⟩
    (by decide) selected_cut_41198

theorem selected_cut_41199 : selected 9 ⟨1126016, by decide⟩
    (prefixPartial 12 334434) = some ⟨12, 2, 0, 1126016, 334434, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_334434_1126016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334434 ⟨1126016, by decide⟩ :=
  accepted_of_selected 12 334434 ⟨1126016, by decide⟩ ⟨12, 2, 0, 1126016, 334434, 2157, 65536⟩
    (by decide) selected_cut_41199

theorem selected_cut_41200 : selected 9 ⟨1126059, by decide⟩
    (prefixPartial 12 334435) = some ⟨12, 2, 0, 1126059, 334435, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_334435_1126059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334435 ⟨1126059, by decide⟩ :=
  accepted_of_selected 12 334435 ⟨1126059, by decide⟩ ⟨12, 2, 0, 1126059, 334435, 2549, 65536⟩
    (by decide) selected_cut_41200

theorem unmarked_context_11_83608_1126060 : frontier 10 ⟨1126060, by decide⟩
    (prefixCache 11 83608) (prefixPartial 11 83608) = false := by
  decide +kernel

theorem node_context_11_83608_1126060 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126060, by decide⟩ =
    .split (coordinate 11) (![⟨1125950, by decide⟩,⟨1125982, by decide⟩,⟨1126016, by decide⟩,⟨1126059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83608_1126060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83608 ⟨1126060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83608
    ⟨1126060, by decide⟩ (by decide) (![⟨1125950, by decide⟩,⟨1125982, by decide⟩,⟨1126016, by decide⟩,⟨1126059, by decide⟩]) unmarked_context_11_83608_1126060 node_context_11_83608_1126060
  intro a
  fin_cases a
  · exact context_12_334432_1125950
  · exact context_12_334433_1125982
  · exact context_12_334434_1126016
  · exact context_12_334435_1126059

theorem selected_cut_41201 : selected 9 ⟨1126098, by decide⟩
    (prefixPartial 12 334436) = some ⟨12, 2, 0, 1126098, 334436, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_334436_1126098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334436 ⟨1126098, by decide⟩ :=
  accepted_of_selected 12 334436 ⟨1126098, by decide⟩ ⟨12, 2, 0, 1126098, 334436, 1977, 65536⟩
    (by decide) selected_cut_41201

theorem selected_cut_41202 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 334437) = some ⟨12, 1, 0, 642794, 334437, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334437_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334437 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 334437 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 334437, 1, 65536⟩
    (by decide) selected_cut_41202

theorem selected_cut_41203 : selected 9 ⟨1126126, by decide⟩
    (prefixPartial 12 334438) = some ⟨12, 2, 0, 1126126, 334438, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_334438_1126126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334438 ⟨1126126, by decide⟩ :=
  accepted_of_selected 12 334438 ⟨1126126, by decide⟩ ⟨12, 2, 0, 1126126, 334438, 1877, 65536⟩
    (by decide) selected_cut_41203

theorem selected_cut_41204 : selected 9 ⟨1126163, by decide⟩
    (prefixPartial 12 334439) = some ⟨12, 2, 0, 1126163, 334439, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_334439_1126163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334439 ⟨1126163, by decide⟩ :=
  accepted_of_selected 12 334439 ⟨1126163, by decide⟩ ⟨12, 2, 0, 1126163, 334439, 2005, 65536⟩
    (by decide) selected_cut_41204

theorem unmarked_context_11_83609_1126164 : frontier 10 ⟨1126164, by decide⟩
    (prefixCache 11 83609) (prefixPartial 11 83609) = false := by
  decide +kernel

theorem node_context_11_83609_1126164 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126164, by decide⟩ =
    .split (coordinate 11) (![⟨1126098, by decide⟩,⟨642794, by decide⟩,⟨1126126, by decide⟩,⟨1126163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83609_1126164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83609 ⟨1126164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83609
    ⟨1126164, by decide⟩ (by decide) (![⟨1126098, by decide⟩,⟨642794, by decide⟩,⟨1126126, by decide⟩,⟨1126163, by decide⟩]) unmarked_context_11_83609_1126164 node_context_11_83609_1126164
  intro a
  fin_cases a
  · exact context_12_334436_1126098
  · exact context_12_334437_642794
  · exact context_12_334438_1126126
  · exact context_12_334439_1126163

theorem selected_cut_41205 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 83610) = some ⟨11, 1, 0, 900587, 83610, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83610_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83610 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 83610 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 83610, 1, 262144⟩
    (by decide) selected_cut_41205

theorem selected_cut_41206 : selected 9 ⟨1126199, by decide⟩
    (prefixPartial 12 334444) = some ⟨12, 2, 0, 1126199, 334444, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_334444_1126199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334444 ⟨1126199, by decide⟩ :=
  accepted_of_selected 12 334444 ⟨1126199, by decide⟩ ⟨12, 2, 0, 1126199, 334444, 2077, 65536⟩
    (by decide) selected_cut_41206

theorem selected_cut_41207 : selected 9 ⟨1126224, by decide⟩
    (prefixPartial 12 334445) = some ⟨12, 2, 0, 1126224, 334445, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_334445_1126224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334445 ⟨1126224, by decide⟩ :=
  accepted_of_selected 12 334445 ⟨1126224, by decide⟩ ⟨12, 2, 0, 1126224, 334445, 1713, 65536⟩
    (by decide) selected_cut_41207

theorem selected_cut_41208 : selected 9 ⟨1126257, by decide⟩
    (prefixPartial 12 334446) = some ⟨12, 2, 0, 1126257, 334446, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_334446_1126257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334446 ⟨1126257, by decide⟩ :=
  accepted_of_selected 12 334446 ⟨1126257, by decide⟩ ⟨12, 2, 0, 1126257, 334446, 1949, 65536⟩
    (by decide) selected_cut_41208

theorem selected_cut_41209 : selected 9 ⟨1126289, by decide⟩
    (prefixPartial 12 334447) = some ⟨12, 2, 0, 1126289, 334447, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_334447_1126289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334447 ⟨1126289, by decide⟩ :=
  accepted_of_selected 12 334447 ⟨1126289, by decide⟩ ⟨12, 2, 0, 1126289, 334447, 1741, 65536⟩
    (by decide) selected_cut_41209

theorem unmarked_context_11_83611_1126290 : frontier 10 ⟨1126290, by decide⟩
    (prefixCache 11 83611) (prefixPartial 11 83611) = false := by
  decide +kernel

theorem node_context_11_83611_1126290 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126290, by decide⟩ =
    .split (coordinate 11) (![⟨1126199, by decide⟩,⟨1126224, by decide⟩,⟨1126257, by decide⟩,⟨1126289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83611_1126290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83611 ⟨1126290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83611
    ⟨1126290, by decide⟩ (by decide) (![⟨1126199, by decide⟩,⟨1126224, by decide⟩,⟨1126257, by decide⟩,⟨1126289, by decide⟩]) unmarked_context_11_83611_1126290 node_context_11_83611_1126290
  intro a
  fin_cases a
  · exact context_12_334444_1126199
  · exact context_12_334445_1126224
  · exact context_12_334446_1126257
  · exact context_12_334447_1126289

theorem unmarked_context_10_20902_1126291 : frontier 11 ⟨1126291, by decide⟩
    (prefixCache 10 20902) (prefixPartial 10 20902) = false := by
  decide +kernel

theorem node_context_10_20902_1126291 : EJMOriginalGlobalDAGData.nodes 11 ⟨1126291, by decide⟩ =
    .split (coordinate 10) (![⟨1126060, by decide⟩,⟨1126164, by decide⟩,⟨900587, by decide⟩,⟨1126290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20902_1126291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20902 ⟨1126291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20902
    ⟨1126291, by decide⟩ (by decide) (![⟨1126060, by decide⟩,⟨1126164, by decide⟩,⟨900587, by decide⟩,⟨1126290, by decide⟩]) unmarked_context_10_20902_1126291 node_context_10_20902_1126291
  intro a
  fin_cases a
  · exact context_11_83608_1126060
  · exact context_11_83609_1126164
  · exact context_11_83610_900587
  · exact context_11_83611_1126290

theorem selected_cut_41210 : selected 9 ⟨1126316, by decide⟩
    (prefixPartial 12 334448) = some ⟨12, 2, 0, 1126316, 334448, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_334448_1126316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334448 ⟨1126316, by decide⟩ :=
  accepted_of_selected 12 334448 ⟨1126316, by decide⟩ ⟨12, 2, 0, 1126316, 334448, 1693, 65536⟩
    (by decide) selected_cut_41210

theorem selected_cut_41211 : selected 9 ⟨1126349, by decide⟩
    (prefixPartial 12 334449) = some ⟨12, 2, 0, 1126349, 334449, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_334449_1126349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334449 ⟨1126349, by decide⟩ :=
  accepted_of_selected 12 334449 ⟨1126349, by decide⟩ ⟨12, 2, 0, 1126349, 334449, 1837, 65536⟩
    (by decide) selected_cut_41211

theorem selected_cut_41212 : selected 9 ⟨1126381, by decide⟩
    (prefixPartial 12 334450) = some ⟨12, 2, 0, 1126381, 334450, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_334450_1126381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334450 ⟨1126381, by decide⟩ :=
  accepted_of_selected 12 334450 ⟨1126381, by decide⟩ ⟨12, 2, 0, 1126381, 334450, 1849, 65536⟩
    (by decide) selected_cut_41212

theorem selected_cut_41213 : selected 9 ⟨1126418, by decide⟩
    (prefixPartial 12 334451) = some ⟨12, 2, 0, 1126418, 334451, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_334451_1126418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334451 ⟨1126418, by decide⟩ :=
  accepted_of_selected 12 334451 ⟨1126418, by decide⟩ ⟨12, 2, 0, 1126418, 334451, 2113, 65536⟩
    (by decide) selected_cut_41213

theorem unmarked_context_11_83612_1126419 : frontier 10 ⟨1126419, by decide⟩
    (prefixCache 11 83612) (prefixPartial 11 83612) = false := by
  decide +kernel

theorem node_context_11_83612_1126419 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126419, by decide⟩ =
    .split (coordinate 11) (![⟨1126316, by decide⟩,⟨1126349, by decide⟩,⟨1126381, by decide⟩,⟨1126418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83612_1126419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83612 ⟨1126419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83612
    ⟨1126419, by decide⟩ (by decide) (![⟨1126316, by decide⟩,⟨1126349, by decide⟩,⟨1126381, by decide⟩,⟨1126418, by decide⟩]) unmarked_context_11_83612_1126419 node_context_11_83612_1126419
  intro a
  fin_cases a
  · exact context_12_334448_1126316
  · exact context_12_334449_1126349
  · exact context_12_334450_1126381
  · exact context_12_334451_1126418

theorem selected_cut_41214 : selected 9 ⟨1126452, by decide⟩
    (prefixPartial 12 334452) = some ⟨12, 2, 0, 1126452, 334452, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_334452_1126452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334452 ⟨1126452, by decide⟩ :=
  accepted_of_selected 12 334452 ⟨1126452, by decide⟩ ⟨12, 2, 0, 1126452, 334452, 1721, 65536⟩
    (by decide) selected_cut_41214

theorem selected_cut_41215 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 334453) = some ⟨12, 1, 0, 642794, 334453, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334453_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334453 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 334453 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 334453, 1, 65536⟩
    (by decide) selected_cut_41215

theorem selected_cut_41216 : selected 9 ⟨1126484, by decide⟩
    (prefixPartial 12 334454) = some ⟨12, 2, 0, 1126484, 334454, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_334454_1126484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334454 ⟨1126484, by decide⟩ :=
  accepted_of_selected 12 334454 ⟨1126484, by decide⟩ ⟨12, 2, 0, 1126484, 334454, 1797, 65536⟩
    (by decide) selected_cut_41216

theorem selected_cut_41217 : selected 9 ⟨1126510, by decide⟩
    (prefixPartial 12 334455) = some ⟨12, 2, 0, 1126510, 334455, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_334455_1126510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334455 ⟨1126510, by decide⟩ :=
  accepted_of_selected 12 334455 ⟨1126510, by decide⟩ ⟨12, 2, 0, 1126510, 334455, 1765, 65536⟩
    (by decide) selected_cut_41217

theorem unmarked_context_11_83613_1126511 : frontier 10 ⟨1126511, by decide⟩
    (prefixCache 11 83613) (prefixPartial 11 83613) = false := by
  decide +kernel

theorem node_context_11_83613_1126511 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126511, by decide⟩ =
    .split (coordinate 11) (![⟨1126452, by decide⟩,⟨642794, by decide⟩,⟨1126484, by decide⟩,⟨1126510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83613_1126511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83613 ⟨1126511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83613
    ⟨1126511, by decide⟩ (by decide) (![⟨1126452, by decide⟩,⟨642794, by decide⟩,⟨1126484, by decide⟩,⟨1126510, by decide⟩]) unmarked_context_11_83613_1126511 node_context_11_83613_1126511
  intro a
  fin_cases a
  · exact context_12_334452_1126452
  · exact context_12_334453_642794
  · exact context_12_334454_1126484
  · exact context_12_334455_1126510

theorem selected_cut_41218 : selected 9 ⟨1126539, by decide⟩
    (prefixPartial 12 334456) = some ⟨12, 2, 0, 1126539, 334456, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_334456_1126539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334456 ⟨1126539, by decide⟩ :=
  accepted_of_selected 12 334456 ⟨1126539, by decide⟩ ⟨12, 2, 0, 1126539, 334456, 1517, 65536⟩
    (by decide) selected_cut_41218

theorem selected_cut_41219 : selected 9 ⟨1126565, by decide⟩
    (prefixPartial 12 334457) = some ⟨12, 2, 0, 1126565, 334457, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_334457_1126565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334457 ⟨1126565, by decide⟩ :=
  accepted_of_selected 12 334457 ⟨1126565, by decide⟩ ⟨12, 2, 0, 1126565, 334457, 1505, 65536⟩
    (by decide) selected_cut_41219

theorem selected_cut_41220 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 334458) = some ⟨12, 1, 0, 893903, 334458, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334458_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334458 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 334458 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 334458, 1, 65536⟩
    (by decide) selected_cut_41220

theorem selected_cut_41221 : selected 9 ⟨1126595, by decide⟩
    (prefixPartial 12 334459) = some ⟨12, 2, 0, 1126595, 334459, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_334459_1126595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334459 ⟨1126595, by decide⟩ :=
  accepted_of_selected 12 334459 ⟨1126595, by decide⟩ ⟨12, 2, 0, 1126595, 334459, 1861, 65536⟩
    (by decide) selected_cut_41221

theorem unmarked_context_11_83614_1126596 : frontier 10 ⟨1126596, by decide⟩
    (prefixCache 11 83614) (prefixPartial 11 83614) = false := by
  decide +kernel

theorem node_context_11_83614_1126596 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126596, by decide⟩ =
    .split (coordinate 11) (![⟨1126539, by decide⟩,⟨1126565, by decide⟩,⟨893903, by decide⟩,⟨1126595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83614_1126596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83614 ⟨1126596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83614
    ⟨1126596, by decide⟩ (by decide) (![⟨1126539, by decide⟩,⟨1126565, by decide⟩,⟨893903, by decide⟩,⟨1126595, by decide⟩]) unmarked_context_11_83614_1126596 node_context_11_83614_1126596
  intro a
  fin_cases a
  · exact context_12_334456_1126539
  · exact context_12_334457_1126565
  · exact context_12_334458_893903
  · exact context_12_334459_1126595

theorem selected_cut_41222 : selected 9 ⟨1126625, by decide⟩
    (prefixPartial 12 334460) = some ⟨12, 2, 0, 1126625, 334460, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_334460_1126625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334460 ⟨1126625, by decide⟩ :=
  accepted_of_selected 12 334460 ⟨1126625, by decide⟩ ⟨12, 2, 0, 1126625, 334460, 1589, 65536⟩
    (by decide) selected_cut_41222

theorem selected_cut_41223 : selected 9 ⟨1126645, by decide⟩
    (prefixPartial 12 334461) = some ⟨12, 2, 0, 1126645, 334461, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_334461_1126645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334461 ⟨1126645, by decide⟩ :=
  accepted_of_selected 12 334461 ⟨1126645, by decide⟩ ⟨12, 2, 0, 1126645, 334461, 1477, 65536⟩
    (by decide) selected_cut_41223

theorem selected_cut_41224 : selected 9 ⟨1126667, by decide⟩
    (prefixPartial 12 334462) = some ⟨12, 2, 0, 1126667, 334462, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_334462_1126667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334462 ⟨1126667, by decide⟩ :=
  accepted_of_selected 12 334462 ⟨1126667, by decide⟩ ⟨12, 2, 0, 1126667, 334462, 1673, 65536⟩
    (by decide) selected_cut_41224

theorem selected_cut_41225 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 334463) = some ⟨12, 1, 0, 1120582, 334463, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334463_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334463 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 334463 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 334463, 1, 65536⟩
    (by decide) selected_cut_41225

theorem unmarked_context_11_83615_1126668 : frontier 10 ⟨1126668, by decide⟩
    (prefixCache 11 83615) (prefixPartial 11 83615) = false := by
  decide +kernel

theorem node_context_11_83615_1126668 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126668, by decide⟩ =
    .split (coordinate 11) (![⟨1126625, by decide⟩,⟨1126645, by decide⟩,⟨1126667, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83615_1126668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83615 ⟨1126668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83615
    ⟨1126668, by decide⟩ (by decide) (![⟨1126625, by decide⟩,⟨1126645, by decide⟩,⟨1126667, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_83615_1126668 node_context_11_83615_1126668
  intro a
  fin_cases a
  · exact context_12_334460_1126625
  · exact context_12_334461_1126645
  · exact context_12_334462_1126667
  · exact context_12_334463_1120582

theorem unmarked_context_10_20903_1126669 : frontier 11 ⟨1126669, by decide⟩
    (prefixCache 10 20903) (prefixPartial 10 20903) = false := by
  decide +kernel

theorem node_context_10_20903_1126669 : EJMOriginalGlobalDAGData.nodes 11 ⟨1126669, by decide⟩ =
    .split (coordinate 10) (![⟨1126419, by decide⟩,⟨1126511, by decide⟩,⟨1126596, by decide⟩,⟨1126668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20903_1126669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20903 ⟨1126669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20903
    ⟨1126669, by decide⟩ (by decide) (![⟨1126419, by decide⟩,⟨1126511, by decide⟩,⟨1126596, by decide⟩,⟨1126668, by decide⟩]) unmarked_context_10_20903_1126669 node_context_10_20903_1126669
  intro a
  fin_cases a
  · exact context_11_83612_1126419
  · exact context_11_83613_1126511
  · exact context_11_83614_1126596
  · exact context_11_83615_1126668

theorem unmarked_context_9_5225_1126670 : frontier 12 ⟨1126670, by decide⟩
    (prefixCache 9 5225) (prefixPartial 9 5225) = false := by
  decide +kernel

theorem node_context_9_5225_1126670 : EJMOriginalGlobalDAGData.nodes 12 ⟨1126670, by decide⟩ =
    .split (coordinate 9) (![⟨1125904, by decide⟩,⟨893098, by decide⟩,⟨1126291, by decide⟩,⟨1126669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5225_1126670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5225 ⟨1126670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5225
    ⟨1126670, by decide⟩ (by decide) (![⟨1125904, by decide⟩,⟨893098, by decide⟩,⟨1126291, by decide⟩,⟨1126669, by decide⟩]) unmarked_context_9_5225_1126670 node_context_9_5225_1126670
  intro a
  fin_cases a
  · exact context_10_20900_1125904
  · exact context_10_20901_893098
  · exact context_10_20902_1126291
  · exact context_10_20903_1126669

theorem selected_cut_41226 : selected 10 ⟨1126725, by decide⟩
    (prefixPartial 11 83616) = some ⟨11, 2, 0, 1126725, 83616, 3037, 262144⟩ := by
  decide +kernel

theorem context_11_83616_1126725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83616 ⟨1126725, by decide⟩ :=
  accepted_of_selected 11 83616 ⟨1126725, by decide⟩ ⟨11, 2, 0, 1126725, 83616, 3037, 262144⟩
    (by decide) selected_cut_41226

theorem selected_cut_41227 : selected 9 ⟨1126749, by decide⟩
    (prefixPartial 12 334468) = some ⟨12, 2, 0, 1126749, 334468, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_334468_1126749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334468 ⟨1126749, by decide⟩ :=
  accepted_of_selected 12 334468 ⟨1126749, by decide⟩ ⟨12, 2, 0, 1126749, 334468, 1205, 65536⟩
    (by decide) selected_cut_41227

theorem selected_cut_41228 : selected 9 ⟨1126780, by decide⟩
    (prefixPartial 12 334469) = some ⟨12, 2, 0, 1126780, 334469, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_334469_1126780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334469 ⟨1126780, by decide⟩ :=
  accepted_of_selected 12 334469 ⟨1126780, by decide⟩ ⟨12, 2, 0, 1126780, 334469, 1633, 65536⟩
    (by decide) selected_cut_41228

theorem selected_cut_41229 : selected 9 ⟨1126803, by decide⟩
    (prefixPartial 12 334470) = some ⟨12, 2, 0, 1126803, 334470, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_334470_1126803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334470 ⟨1126803, by decide⟩ :=
  accepted_of_selected 12 334470 ⟨1126803, by decide⟩ ⟨12, 2, 0, 1126803, 334470, 1301, 65536⟩
    (by decide) selected_cut_41229

theorem selected_cut_41230 : selected 9 ⟨1126823, by decide⟩
    (prefixPartial 12 334471) = some ⟨12, 2, 0, 1126823, 334471, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_334471_1126823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334471 ⟨1126823, by decide⟩ :=
  accepted_of_selected 12 334471 ⟨1126823, by decide⟩ ⟨12, 2, 0, 1126823, 334471, 1257, 65536⟩
    (by decide) selected_cut_41230

theorem unmarked_context_11_83617_1126824 : frontier 10 ⟨1126824, by decide⟩
    (prefixCache 11 83617) (prefixPartial 11 83617) = false := by
  decide +kernel

theorem node_context_11_83617_1126824 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126824, by decide⟩ =
    .split (coordinate 11) (![⟨1126749, by decide⟩,⟨1126780, by decide⟩,⟨1126803, by decide⟩,⟨1126823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83617_1126824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83617 ⟨1126824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83617
    ⟨1126824, by decide⟩ (by decide) (![⟨1126749, by decide⟩,⟨1126780, by decide⟩,⟨1126803, by decide⟩,⟨1126823, by decide⟩]) unmarked_context_11_83617_1126824 node_context_11_83617_1126824
  intro a
  fin_cases a
  · exact context_12_334468_1126749
  · exact context_12_334469_1126780
  · exact context_12_334470_1126803
  · exact context_12_334471_1126823

theorem selected_cut_41231 : selected 10 ⟨1126870, by decide⟩
    (prefixPartial 11 83618) = some ⟨11, 2, 0, 1126870, 83618, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_83618_1126870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83618 ⟨1126870, by decide⟩ :=
  accepted_of_selected 11 83618 ⟨1126870, by decide⟩ ⟨11, 2, 0, 1126870, 83618, 3137, 262144⟩
    (by decide) selected_cut_41231

theorem selected_cut_41232 : selected 9 ⟨1126889, by decide⟩
    (prefixPartial 12 334476) = some ⟨12, 2, 0, 1126889, 334476, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_334476_1126889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334476 ⟨1126889, by decide⟩ :=
  accepted_of_selected 12 334476 ⟨1126889, by decide⟩ ⟨12, 2, 0, 1126889, 334476, 1125, 65536⟩
    (by decide) selected_cut_41232

theorem selected_cut_41233 : selected 9 ⟨1126906, by decide⟩
    (prefixPartial 12 334477) = some ⟨12, 2, 0, 1126906, 334477, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_334477_1126906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334477 ⟨1126906, by decide⟩ :=
  accepted_of_selected 12 334477 ⟨1126906, by decide⟩ ⟨12, 2, 0, 1126906, 334477, 1253, 65536⟩
    (by decide) selected_cut_41233

theorem selected_cut_41234 : selected 9 ⟨1126925, by decide⟩
    (prefixPartial 12 334478) = some ⟨12, 2, 0, 1126925, 334478, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_334478_1126925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334478 ⟨1126925, by decide⟩ :=
  accepted_of_selected 12 334478 ⟨1126925, by decide⟩ ⟨12, 2, 0, 1126925, 334478, 1197, 65536⟩
    (by decide) selected_cut_41234

theorem selected_cut_41235 : selected 9 ⟨1126938, by decide⟩
    (prefixPartial 12 334479) = some ⟨12, 2, 0, 1126938, 334479, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_334479_1126938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334479 ⟨1126938, by decide⟩ :=
  accepted_of_selected 12 334479 ⟨1126938, by decide⟩ ⟨12, 2, 0, 1126938, 334479, 1057, 65536⟩
    (by decide) selected_cut_41235

theorem unmarked_context_11_83619_1126939 : frontier 10 ⟨1126939, by decide⟩
    (prefixCache 11 83619) (prefixPartial 11 83619) = false := by
  decide +kernel

theorem node_context_11_83619_1126939 : EJMOriginalGlobalDAGData.nodes 10 ⟨1126939, by decide⟩ =
    .split (coordinate 11) (![⟨1126889, by decide⟩,⟨1126906, by decide⟩,⟨1126925, by decide⟩,⟨1126938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83619_1126939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83619 ⟨1126939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83619
    ⟨1126939, by decide⟩ (by decide) (![⟨1126889, by decide⟩,⟨1126906, by decide⟩,⟨1126925, by decide⟩,⟨1126938, by decide⟩]) unmarked_context_11_83619_1126939 node_context_11_83619_1126939
  intro a
  fin_cases a
  · exact context_12_334476_1126889
  · exact context_12_334477_1126906
  · exact context_12_334478_1126925
  · exact context_12_334479_1126938

theorem unmarked_context_10_20904_1126940 : frontier 11 ⟨1126940, by decide⟩
    (prefixCache 10 20904) (prefixPartial 10 20904) = false := by
  decide +kernel

theorem node_context_10_20904_1126940 : EJMOriginalGlobalDAGData.nodes 11 ⟨1126940, by decide⟩ =
    .split (coordinate 10) (![⟨1126725, by decide⟩,⟨1126824, by decide⟩,⟨1126870, by decide⟩,⟨1126939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20904_1126940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20904 ⟨1126940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20904
    ⟨1126940, by decide⟩ (by decide) (![⟨1126725, by decide⟩,⟨1126824, by decide⟩,⟨1126870, by decide⟩,⟨1126939, by decide⟩]) unmarked_context_10_20904_1126940 node_context_10_20904_1126940
  intro a
  fin_cases a
  · exact context_11_83616_1126725
  · exact context_11_83617_1126824
  · exact context_11_83618_1126870
  · exact context_11_83619_1126939

theorem selected_cut_41236 : selected 9 ⟨1126956, by decide⟩
    (prefixPartial 12 334480) = some ⟨12, 2, 0, 1126956, 334480, 945, 65536⟩ := by
  decide +kernel

theorem context_12_334480_1126956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334480 ⟨1126956, by decide⟩ :=
  accepted_of_selected 12 334480 ⟨1126956, by decide⟩ ⟨12, 2, 0, 1126956, 334480, 945, 65536⟩
    (by decide) selected_cut_41236

theorem selected_cut_41237 : selected 9 ⟨1126972, by decide⟩
    (prefixPartial 12 334481) = some ⟨12, 2, 0, 1126972, 334481, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_334481_1126972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334481 ⟨1126972, by decide⟩ :=
  accepted_of_selected 12 334481 ⟨1126972, by decide⟩ ⟨12, 2, 0, 1126972, 334481, 1097, 65536⟩
    (by decide) selected_cut_41237

theorem selected_cut_41238 : selected 9 ⟨1126990, by decide⟩
    (prefixPartial 12 334482) = some ⟨12, 2, 0, 1126990, 334482, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_334482_1126990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334482 ⟨1126990, by decide⟩ :=
  accepted_of_selected 12 334482 ⟨1126990, by decide⟩ ⟨12, 2, 0, 1126990, 334482, 1017, 65536⟩
    (by decide) selected_cut_41238

theorem selected_cut_41239 : selected 9 ⟨1127006, by decide⟩
    (prefixPartial 12 334483) = some ⟨12, 2, 0, 1127006, 334483, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_334483_1127006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334483 ⟨1127006, by decide⟩ :=
  accepted_of_selected 12 334483 ⟨1127006, by decide⟩ ⟨12, 2, 0, 1127006, 334483, 1097, 65536⟩
    (by decide) selected_cut_41239

theorem unmarked_context_11_83620_1127007 : frontier 10 ⟨1127007, by decide⟩
    (prefixCache 11 83620) (prefixPartial 11 83620) = false := by
  decide +kernel

theorem node_context_11_83620_1127007 : EJMOriginalGlobalDAGData.nodes 10 ⟨1127007, by decide⟩ =
    .split (coordinate 11) (![⟨1126956, by decide⟩,⟨1126972, by decide⟩,⟨1126990, by decide⟩,⟨1127006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83620_1127007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83620 ⟨1127007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83620
    ⟨1127007, by decide⟩ (by decide) (![⟨1126956, by decide⟩,⟨1126972, by decide⟩,⟨1126990, by decide⟩,⟨1127006, by decide⟩]) unmarked_context_11_83620_1127007 node_context_11_83620_1127007
  intro a
  fin_cases a
  · exact context_12_334480_1126956
  · exact context_12_334481_1126972
  · exact context_12_334482_1126990
  · exact context_12_334483_1127006

theorem selected_cut_41240 : selected 10 ⟨1127041, by decide⟩
    (prefixPartial 11 83621) = some ⟨11, 2, 0, 1127041, 83621, 2029, 262144⟩ := by
  decide +kernel

theorem context_11_83621_1127041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83621 ⟨1127041, by decide⟩ :=
  accepted_of_selected 11 83621 ⟨1127041, by decide⟩ ⟨11, 2, 0, 1127041, 83621, 2029, 262144⟩
    (by decide) selected_cut_41240

theorem selected_cut_41241 : selected 10 ⟨1127078, by decide⟩
    (prefixPartial 11 83622) = some ⟨11, 2, 0, 1127078, 83622, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_83622_1127078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83622 ⟨1127078, by decide⟩ :=
  accepted_of_selected 11 83622 ⟨1127078, by decide⟩ ⟨11, 2, 0, 1127078, 83622, 2521, 262144⟩
    (by decide) selected_cut_41241

theorem selected_cut_41242 : selected 10 ⟨1127139, by decide⟩
    (prefixPartial 11 83623) = some ⟨11, 2, 0, 1127139, 83623, 3593, 262144⟩ := by
  decide +kernel

theorem context_11_83623_1127139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83623 ⟨1127139, by decide⟩ :=
  accepted_of_selected 11 83623 ⟨1127139, by decide⟩ ⟨11, 2, 0, 1127139, 83623, 3593, 262144⟩
    (by decide) selected_cut_41242

theorem unmarked_context_10_20905_1127140 : frontier 11 ⟨1127140, by decide⟩
    (prefixCache 10 20905) (prefixPartial 10 20905) = false := by
  decide +kernel

theorem node_context_10_20905_1127140 : EJMOriginalGlobalDAGData.nodes 11 ⟨1127140, by decide⟩ =
    .split (coordinate 10) (![⟨1127007, by decide⟩,⟨1127041, by decide⟩,⟨1127078, by decide⟩,⟨1127139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20905_1127140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20905 ⟨1127140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20905
    ⟨1127140, by decide⟩ (by decide) (![⟨1127007, by decide⟩,⟨1127041, by decide⟩,⟨1127078, by decide⟩,⟨1127139, by decide⟩]) unmarked_context_10_20905_1127140 node_context_10_20905_1127140
  intro a
  fin_cases a
  · exact context_11_83620_1127007
  · exact context_11_83621_1127041
  · exact context_11_83622_1127078
  · exact context_11_83623_1127139

theorem selected_cut_41243 : selected 10 ⟨1127174, by decide⟩
    (prefixPartial 11 83624) = some ⟨11, 2, 0, 1127174, 83624, 1937, 262144⟩ := by
  decide +kernel

theorem context_11_83624_1127174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83624 ⟨1127174, by decide⟩ :=
  accepted_of_selected 11 83624 ⟨1127174, by decide⟩ ⟨11, 2, 0, 1127174, 83624, 1937, 262144⟩
    (by decide) selected_cut_41243

theorem selected_cut_41244 : selected 10 ⟨1127207, by decide⟩
    (prefixPartial 11 83625) = some ⟨11, 2, 0, 1127207, 83625, 1853, 262144⟩ := by
  decide +kernel

theorem context_11_83625_1127207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83625 ⟨1127207, by decide⟩ :=
  accepted_of_selected 11 83625 ⟨1127207, by decide⟩ ⟨11, 2, 0, 1127207, 83625, 1853, 262144⟩
    (by decide) selected_cut_41244

theorem selected_cut_41245 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 83626) = some ⟨11, 1, 0, 1109453, 83626, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83626_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83626 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 83626 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 83626, 1, 262144⟩
    (by decide) selected_cut_41245

theorem selected_cut_41246 : selected 10 ⟨1127248, by decide⟩
    (prefixPartial 11 83627) = some ⟨11, 2, 0, 1127248, 83627, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_83627_1127248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83627 ⟨1127248, by decide⟩ :=
  accepted_of_selected 11 83627 ⟨1127248, by decide⟩ ⟨11, 2, 0, 1127248, 83627, 2397, 262144⟩
    (by decide) selected_cut_41246

theorem unmarked_context_10_20906_1127249 : frontier 11 ⟨1127249, by decide⟩
    (prefixCache 10 20906) (prefixPartial 10 20906) = false := by
  decide +kernel

theorem node_context_10_20906_1127249 : EJMOriginalGlobalDAGData.nodes 11 ⟨1127249, by decide⟩ =
    .split (coordinate 10) (![⟨1127174, by decide⟩,⟨1127207, by decide⟩,⟨1109453, by decide⟩,⟨1127248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20906_1127249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20906 ⟨1127249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20906
    ⟨1127249, by decide⟩ (by decide) (![⟨1127174, by decide⟩,⟨1127207, by decide⟩,⟨1109453, by decide⟩,⟨1127248, by decide⟩]) unmarked_context_10_20906_1127249 node_context_10_20906_1127249
  intro a
  fin_cases a
  · exact context_11_83624_1127174
  · exact context_11_83625_1127207
  · exact context_11_83626_1109453
  · exact context_11_83627_1127248

theorem selected_cut_41247 : selected 10 ⟨1127305, by decide⟩
    (prefixPartial 11 83628) = some ⟨11, 2, 0, 1127305, 83628, 3429, 262144⟩ := by
  decide +kernel

theorem context_11_83628_1127305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83628 ⟨1127305, by decide⟩ :=
  accepted_of_selected 11 83628 ⟨1127305, by decide⟩ ⟨11, 2, 0, 1127305, 83628, 3429, 262144⟩
    (by decide) selected_cut_41247

theorem selected_cut_41248 : selected 10 ⟨1127364, by decide⟩
    (prefixPartial 11 83629) = some ⟨11, 2, 0, 1127364, 83629, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_83629_1127364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83629 ⟨1127364, by decide⟩ :=
  accepted_of_selected 11 83629 ⟨1127364, by decide⟩ ⟨11, 2, 0, 1127364, 83629, 3377, 262144⟩
    (by decide) selected_cut_41248

theorem selected_cut_41249 : selected 10 ⟨1127400, by decide⟩
    (prefixPartial 11 83630) = some ⟨11, 2, 0, 1127400, 83630, 2029, 262144⟩ := by
  decide +kernel

theorem context_11_83630_1127400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83630 ⟨1127400, by decide⟩ :=
  accepted_of_selected 11 83630 ⟨1127400, by decide⟩ ⟨11, 2, 0, 1127400, 83630, 2029, 262144⟩
    (by decide) selected_cut_41249

theorem selected_cut_41250 : selected 10 ⟨1127437, by decide⟩
    (prefixPartial 11 83631) = some ⟨11, 2, 0, 1127437, 83631, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_83631_1127437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83631 ⟨1127437, by decide⟩ :=
  accepted_of_selected 11 83631 ⟨1127437, by decide⟩ ⟨11, 2, 0, 1127437, 83631, 2093, 262144⟩
    (by decide) selected_cut_41250

theorem unmarked_context_10_20907_1127438 : frontier 11 ⟨1127438, by decide⟩
    (prefixCache 10 20907) (prefixPartial 10 20907) = false := by
  decide +kernel

theorem node_context_10_20907_1127438 : EJMOriginalGlobalDAGData.nodes 11 ⟨1127438, by decide⟩ =
    .split (coordinate 10) (![⟨1127305, by decide⟩,⟨1127364, by decide⟩,⟨1127400, by decide⟩,⟨1127437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20907_1127438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20907 ⟨1127438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20907
    ⟨1127438, by decide⟩ (by decide) (![⟨1127305, by decide⟩,⟨1127364, by decide⟩,⟨1127400, by decide⟩,⟨1127437, by decide⟩]) unmarked_context_10_20907_1127438 node_context_10_20907_1127438
  intro a
  fin_cases a
  · exact context_11_83628_1127305
  · exact context_11_83629_1127364
  · exact context_11_83630_1127400
  · exact context_11_83631_1127437

theorem unmarked_context_9_5226_1127439 : frontier 12 ⟨1127439, by decide⟩
    (prefixCache 9 5226) (prefixPartial 9 5226) = false := by
  decide +kernel

theorem node_context_9_5226_1127439 : EJMOriginalGlobalDAGData.nodes 12 ⟨1127439, by decide⟩ =
    .split (coordinate 9) (![⟨1126940, by decide⟩,⟨1127140, by decide⟩,⟨1127249, by decide⟩,⟨1127438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5226_1127439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5226 ⟨1127439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5226
    ⟨1127439, by decide⟩ (by decide) (![⟨1126940, by decide⟩,⟨1127140, by decide⟩,⟨1127249, by decide⟩,⟨1127438, by decide⟩]) unmarked_context_9_5226_1127439 node_context_9_5226_1127439
  intro a
  fin_cases a
  · exact context_10_20904_1126940
  · exact context_10_20905_1127140
  · exact context_10_20906_1127249
  · exact context_10_20907_1127438

theorem selected_cut_41251 : selected 10 ⟨1127474, by decide⟩
    (prefixPartial 11 83632) = some ⟨11, 2, 0, 1127474, 83632, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_83632_1127474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83632 ⟨1127474, by decide⟩ :=
  accepted_of_selected 11 83632 ⟨1127474, by decide⟩ ⟨11, 2, 0, 1127474, 83632, 2101, 262144⟩
    (by decide) selected_cut_41251

theorem selected_cut_41252 : selected 10 ⟨1127516, by decide⟩
    (prefixPartial 11 83633) = some ⟨11, 2, 0, 1127516, 83633, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_83633_1127516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83633 ⟨1127516, by decide⟩ :=
  accepted_of_selected 11 83633 ⟨1127516, by decide⟩ ⟨11, 2, 0, 1127516, 83633, 2497, 262144⟩
    (by decide) selected_cut_41252

theorem selected_cut_41253 : selected 10 ⟨1127543, by decide⟩
    (prefixPartial 11 83634) = some ⟨11, 2, 0, 1127543, 83634, 1445, 262144⟩ := by
  decide +kernel

theorem context_11_83634_1127543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83634 ⟨1127543, by decide⟩ :=
  accepted_of_selected 11 83634 ⟨1127543, by decide⟩ ⟨11, 2, 0, 1127543, 83634, 1445, 262144⟩
    (by decide) selected_cut_41253

theorem selected_cut_41254 : selected 10 ⟨1127569, by decide⟩
    (prefixPartial 11 83635) = some ⟨11, 2, 0, 1127569, 83635, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_83635_1127569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83635 ⟨1127569, by decide⟩ :=
  accepted_of_selected 11 83635 ⟨1127569, by decide⟩ ⟨11, 2, 0, 1127569, 83635, 1641, 262144⟩
    (by decide) selected_cut_41254

theorem unmarked_context_10_20908_1127570 : frontier 11 ⟨1127570, by decide⟩
    (prefixCache 10 20908) (prefixPartial 10 20908) = false := by
  decide +kernel

theorem node_context_10_20908_1127570 : EJMOriginalGlobalDAGData.nodes 11 ⟨1127570, by decide⟩ =
    .split (coordinate 10) (![⟨1127474, by decide⟩,⟨1127516, by decide⟩,⟨1127543, by decide⟩,⟨1127569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20908_1127570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20908 ⟨1127570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20908
    ⟨1127570, by decide⟩ (by decide) (![⟨1127474, by decide⟩,⟨1127516, by decide⟩,⟨1127543, by decide⟩,⟨1127569, by decide⟩]) unmarked_context_10_20908_1127570 node_context_10_20908_1127570
  intro a
  fin_cases a
  · exact context_11_83632_1127474
  · exact context_11_83633_1127516
  · exact context_11_83634_1127543
  · exact context_11_83635_1127569

theorem selected_cut_41255 : selected 11 ⟨1127630, by decide⟩
    (prefixPartial 10 20909) = some ⟨10, 2, 0, 1127630, 20909, 3977, 1048576⟩ := by
  decide +kernel

theorem context_10_20909_1127630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20909 ⟨1127630, by decide⟩ :=
  accepted_of_selected 10 20909 ⟨1127630, by decide⟩ ⟨10, 2, 0, 1127630, 20909, 3977, 1048576⟩
    (by decide) selected_cut_41255

theorem selected_cut_41256 : selected 11 ⟨1127677, by decide⟩
    (prefixPartial 10 20910) = some ⟨10, 2, 0, 1127677, 20910, 2085, 1048576⟩ := by
  decide +kernel

theorem context_10_20910_1127677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20910 ⟨1127677, by decide⟩ :=
  accepted_of_selected 10 20910 ⟨1127677, by decide⟩ ⟨10, 2, 0, 1127677, 20910, 2085, 1048576⟩
    (by decide) selected_cut_41256

theorem selected_cut_41257 : selected 11 ⟨1127695, by decide⟩
    (prefixPartial 10 20911) = some ⟨10, 2, 0, 1127695, 20911, 517, 1048576⟩ := by
  decide +kernel

theorem context_10_20911_1127695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20911 ⟨1127695, by decide⟩ :=
  accepted_of_selected 10 20911 ⟨1127695, by decide⟩ ⟨10, 2, 0, 1127695, 20911, 517, 1048576⟩
    (by decide) selected_cut_41257

theorem unmarked_context_9_5227_1127696 : frontier 12 ⟨1127696, by decide⟩
    (prefixCache 9 5227) (prefixPartial 9 5227) = false := by
  decide +kernel

theorem node_context_9_5227_1127696 : EJMOriginalGlobalDAGData.nodes 12 ⟨1127696, by decide⟩ =
    .split (coordinate 9) (![⟨1127570, by decide⟩,⟨1127630, by decide⟩,⟨1127677, by decide⟩,⟨1127695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5227_1127696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5227 ⟨1127696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5227
    ⟨1127696, by decide⟩ (by decide) (![⟨1127570, by decide⟩,⟨1127630, by decide⟩,⟨1127677, by decide⟩,⟨1127695, by decide⟩]) unmarked_context_9_5227_1127696 node_context_9_5227_1127696
  intro a
  fin_cases a
  · exact context_10_20908_1127570
  · exact context_10_20909_1127630
  · exact context_10_20910_1127677
  · exact context_10_20911_1127695

theorem unmarked_context_8_1306_1127697 : frontier 13 ⟨1127697, by decide⟩
    (prefixCache 8 1306) (prefixPartial 8 1306) = false := by
  decide +kernel

theorem node_context_8_1306_1127697 : EJMOriginalGlobalDAGData.nodes 13 ⟨1127697, by decide⟩ =
    .split (coordinate 8) (![⟨1125419, by decide⟩,⟨1126670, by decide⟩,⟨1127439, by decide⟩,⟨1127696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1306_1127697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1306 ⟨1127697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1306
    ⟨1127697, by decide⟩ (by decide) (![⟨1125419, by decide⟩,⟨1126670, by decide⟩,⟨1127439, by decide⟩,⟨1127696, by decide⟩]) unmarked_context_8_1306_1127697 node_context_8_1306_1127697
  intro a
  fin_cases a
  · exact context_9_5224_1125419
  · exact context_9_5225_1126670
  · exact context_9_5226_1127439
  · exact context_9_5227_1127696

theorem selected_cut_41258 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 83648) = some ⟨11, 1, 0, 434745, 83648, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83648_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83648 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 83648 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 83648, 1, 262144⟩
    (by decide) selected_cut_41258

theorem selected_cut_41259 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 334596) = some ⟨12, 1, 0, 448748, 334596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334596_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334596 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 334596 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 334596, 1, 65536⟩
    (by decide) selected_cut_41259

theorem selected_cut_41260 : selected 8 ⟨1127753, by decide⟩
    (prefixPartial 13 1338388) = some ⟨13, 2, 0, 1127753, 1338388, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_1338388_1127753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1338388 ⟨1127753, by decide⟩ :=
  accepted_of_selected 13 1338388 ⟨1127753, by decide⟩ ⟨13, 2, 0, 1127753, 1338388, 1749, 16384⟩
    (by decide) selected_cut_41260

theorem selected_cut_41261 : selected 8 ⟨1127770, by decide⟩
    (prefixPartial 13 1338389) = some ⟨13, 2, 0, 1127770, 1338389, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_1338389_1127770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1338389 ⟨1127770, by decide⟩ :=
  accepted_of_selected 13 1338389 ⟨1127770, by decide⟩ ⟨13, 2, 0, 1127770, 1338389, 1021, 16384⟩
    (by decide) selected_cut_41261

theorem selected_cut_41262 : selected 8 ⟨1127794, by decide⟩
    (prefixPartial 13 1338390) = some ⟨13, 2, 0, 1127794, 1338390, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1338390_1127794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1338390 ⟨1127794, by decide⟩ :=
  accepted_of_selected 13 1338390 ⟨1127794, by decide⟩ ⟨13, 2, 0, 1127794, 1338390, 1101, 16384⟩
    (by decide) selected_cut_41262

theorem selected_cut_41263 : selected 8 ⟨1127803, by decide⟩
    (prefixPartial 13 1338391) = some ⟨13, 2, 0, 1127803, 1338391, 541, 16384⟩ := by
  decide +kernel

theorem context_13_1338391_1127803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1338391 ⟨1127803, by decide⟩ :=
  accepted_of_selected 13 1338391 ⟨1127803, by decide⟩ ⟨13, 2, 0, 1127803, 1338391, 541, 16384⟩
    (by decide) selected_cut_41263

theorem unmarked_context_12_334597_1127804 : frontier 9 ⟨1127804, by decide⟩
    (prefixCache 12 334597) (prefixPartial 12 334597) = false := by
  decide +kernel

theorem node_context_12_334597_1127804 : EJMOriginalGlobalDAGData.nodes 9 ⟨1127804, by decide⟩ =
    .split (coordinate 12) (![⟨1127753, by decide⟩,⟨1127770, by decide⟩,⟨1127794, by decide⟩,⟨1127803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_334597_1127804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334597 ⟨1127804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 334597
    ⟨1127804, by decide⟩ (by decide) (![⟨1127753, by decide⟩,⟨1127770, by decide⟩,⟨1127794, by decide⟩,⟨1127803, by decide⟩]) unmarked_context_12_334597_1127804 node_context_12_334597_1127804
  intro a
  fin_cases a
  · exact context_13_1338388_1127753
  · exact context_13_1338389_1127770
  · exact context_13_1338390_1127794
  · exact context_13_1338391_1127803

theorem selected_cut_41264 : selected 9 ⟨1127897, by decide⟩
    (prefixPartial 12 334598) = some ⟨12, 2, 0, 1127897, 334598, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_334598_1127897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334598 ⟨1127897, by decide⟩ :=
  accepted_of_selected 12 334598 ⟨1127897, by decide⟩ ⟨12, 2, 0, 1127897, 334598, 3757, 65536⟩
    (by decide) selected_cut_41264

theorem selected_cut_41265 : selected 9 ⟨1127979, by decide⟩
    (prefixPartial 12 334599) = some ⟨12, 2, 0, 1127979, 334599, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_334599_1127979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334599 ⟨1127979, by decide⟩ :=
  accepted_of_selected 12 334599 ⟨1127979, by decide⟩ ⟨12, 2, 0, 1127979, 334599, 3505, 65536⟩
    (by decide) selected_cut_41265

theorem unmarked_context_11_83649_1127980 : frontier 10 ⟨1127980, by decide⟩
    (prefixCache 11 83649) (prefixPartial 11 83649) = false := by
  decide +kernel

theorem node_context_11_83649_1127980 : EJMOriginalGlobalDAGData.nodes 10 ⟨1127980, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1127804, by decide⟩,⟨1127897, by decide⟩,⟨1127979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83649_1127980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83649 ⟨1127980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83649
    ⟨1127980, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1127804, by decide⟩,⟨1127897, by decide⟩,⟨1127979, by decide⟩]) unmarked_context_11_83649_1127980 node_context_11_83649_1127980
  intro a
  fin_cases a
  · exact context_12_334596_448748
  · exact context_12_334597_1127804
  · exact context_12_334598_1127897
  · exact context_12_334599_1127979

theorem selected_cut_41266 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 334600) = some ⟨12, 1, 0, 448748, 334600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334600_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334600 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 334600 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 334600, 1, 65536⟩
    (by decide) selected_cut_41266

theorem selected_cut_41267 : selected 9 ⟨1128039, by decide⟩
    (prefixPartial 12 334601) = some ⟨12, 2, 0, 1128039, 334601, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_334601_1128039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334601 ⟨1128039, by decide⟩ :=
  accepted_of_selected 12 334601 ⟨1128039, by decide⟩ ⟨12, 2, 0, 1128039, 334601, 3261, 65536⟩
    (by decide) selected_cut_41267

theorem selected_cut_41268 : selected 9 ⟨1128099, by decide⟩
    (prefixPartial 12 334602) = some ⟨12, 2, 0, 1128099, 334602, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_334602_1128099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334602 ⟨1128099, by decide⟩ :=
  accepted_of_selected 12 334602 ⟨1128099, by decide⟩ ⟨12, 2, 0, 1128099, 334602, 3069, 65536⟩
    (by decide) selected_cut_41268

theorem selected_cut_41269 : selected 9 ⟨1128163, by decide⟩
    (prefixPartial 12 334603) = some ⟨12, 2, 0, 1128163, 334603, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_334603_1128163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334603 ⟨1128163, by decide⟩ :=
  accepted_of_selected 12 334603 ⟨1128163, by decide⟩ ⟨12, 2, 0, 1128163, 334603, 3285, 65536⟩
    (by decide) selected_cut_41269

theorem unmarked_context_11_83650_1128164 : frontier 10 ⟨1128164, by decide⟩
    (prefixCache 11 83650) (prefixPartial 11 83650) = false := by
  decide +kernel

theorem node_context_11_83650_1128164 : EJMOriginalGlobalDAGData.nodes 10 ⟨1128164, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1128039, by decide⟩,⟨1128099, by decide⟩,⟨1128163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83650_1128164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83650 ⟨1128164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83650
    ⟨1128164, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1128039, by decide⟩,⟨1128099, by decide⟩,⟨1128163, by decide⟩]) unmarked_context_11_83650_1128164 node_context_11_83650_1128164
  intro a
  fin_cases a
  · exact context_12_334600_448748
  · exact context_12_334601_1128039
  · exact context_12_334602_1128099
  · exact context_12_334603_1128163

theorem selected_cut_41270 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 334604) = some ⟨12, 1, 0, 448748, 334604, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334604_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334604 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 334604 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 334604, 1, 65536⟩
    (by decide) selected_cut_41270

theorem selected_cut_41271 : selected 9 ⟨1128219, by decide⟩
    (prefixPartial 12 334605) = some ⟨12, 2, 0, 1128219, 334605, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_334605_1128219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334605 ⟨1128219, by decide⟩ :=
  accepted_of_selected 12 334605 ⟨1128219, by decide⟩ ⟨12, 2, 0, 1128219, 334605, 3357, 65536⟩
    (by decide) selected_cut_41271

theorem selected_cut_41272 : selected 9 ⟨1128291, by decide⟩
    (prefixPartial 12 334606) = some ⟨12, 2, 0, 1128291, 334606, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_334606_1128291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334606 ⟨1128291, by decide⟩ :=
  accepted_of_selected 12 334606 ⟨1128291, by decide⟩ ⟨12, 2, 0, 1128291, 334606, 3597, 65536⟩
    (by decide) selected_cut_41272

theorem selected_cut_41273 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 334607) = some ⟨12, 1, 0, 903806, 334607, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334607_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334607 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 334607 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 334607, 1, 65536⟩
    (by decide) selected_cut_41273

theorem unmarked_context_11_83651_1128292 : frontier 10 ⟨1128292, by decide⟩
    (prefixCache 11 83651) (prefixPartial 11 83651) = false := by
  decide +kernel

theorem node_context_11_83651_1128292 : EJMOriginalGlobalDAGData.nodes 10 ⟨1128292, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1128219, by decide⟩,⟨1128291, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83651_1128292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83651 ⟨1128292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83651
    ⟨1128292, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1128219, by decide⟩,⟨1128291, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_83651_1128292 node_context_11_83651_1128292
  intro a
  fin_cases a
  · exact context_12_334604_448748
  · exact context_12_334605_1128219
  · exact context_12_334606_1128291
  · exact context_12_334607_903806

theorem unmarked_context_10_20912_1128293 : frontier 11 ⟨1128293, by decide⟩
    (prefixCache 10 20912) (prefixPartial 10 20912) = false := by
  decide +kernel

theorem node_context_10_20912_1128293 : EJMOriginalGlobalDAGData.nodes 11 ⟨1128293, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1127980, by decide⟩,⟨1128164, by decide⟩,⟨1128292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20912_1128293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20912 ⟨1128293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20912
    ⟨1128293, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1127980, by decide⟩,⟨1128164, by decide⟩,⟨1128292, by decide⟩]) unmarked_context_10_20912_1128293 node_context_10_20912_1128293
  intro a
  fin_cases a
  · exact context_11_83648_434745
  · exact context_11_83649_1127980
  · exact context_11_83650_1128164
  · exact context_11_83651_1128292

theorem selected_cut_41274 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334608) = some ⟨12, 1, 0, 1108174, 334608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334608_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334608 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334608 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334608, 1, 65536⟩
    (by decide) selected_cut_41274

theorem selected_cut_41275 : selected 9 ⟨1128348, by decide⟩
    (prefixPartial 12 334609) = some ⟨12, 2, 0, 1128348, 334609, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_334609_1128348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334609 ⟨1128348, by decide⟩ :=
  accepted_of_selected 12 334609 ⟨1128348, by decide⟩ ⟨12, 2, 0, 1128348, 334609, 3437, 65536⟩
    (by decide) selected_cut_41275

theorem selected_cut_41276 : selected 9 ⟨1128417, by decide⟩
    (prefixPartial 12 334610) = some ⟨12, 2, 0, 1128417, 334610, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_334610_1128417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334610 ⟨1128417, by decide⟩ :=
  accepted_of_selected 12 334610 ⟨1128417, by decide⟩ ⟨12, 2, 0, 1128417, 334610, 3825, 65536⟩
    (by decide) selected_cut_41276

theorem selected_cut_41277 : selected 9 ⟨1128492, by decide⟩
    (prefixPartial 12 334611) = some ⟨12, 2, 0, 1128492, 334611, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_334611_1128492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334611 ⟨1128492, by decide⟩ :=
  accepted_of_selected 12 334611 ⟨1128492, by decide⟩ ⟨12, 2, 0, 1128492, 334611, 3461, 65536⟩
    (by decide) selected_cut_41277

theorem unmarked_context_11_83652_1128493 : frontier 10 ⟨1128493, by decide⟩
    (prefixCache 11 83652) (prefixPartial 11 83652) = false := by
  decide +kernel

theorem node_context_11_83652_1128493 : EJMOriginalGlobalDAGData.nodes 10 ⟨1128493, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1128348, by decide⟩,⟨1128417, by decide⟩,⟨1128492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83652_1128493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83652 ⟨1128493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83652
    ⟨1128493, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1128348, by decide⟩,⟨1128417, by decide⟩,⟨1128492, by decide⟩]) unmarked_context_11_83652_1128493 node_context_11_83652_1128493
  intro a
  fin_cases a
  · exact context_12_334608_1108174
  · exact context_12_334609_1128348
  · exact context_12_334610_1128417
  · exact context_12_334611_1128492

theorem selected_cut_41278 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334612) = some ⟨12, 1, 0, 1108174, 334612, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334612_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334612 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334612 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334612, 1, 65536⟩
    (by decide) selected_cut_41278

theorem selected_cut_41279 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 334613) = some ⟨12, 1, 0, 1118965, 334613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334613_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334613 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 334613 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 334613, 1, 65536⟩
    (by decide) selected_cut_41279

theorem selected_cut_41280 : selected 9 ⟨1128559, by decide⟩
    (prefixPartial 12 334614) = some ⟨12, 2, 0, 1128559, 334614, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_334614_1128559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334614 ⟨1128559, by decide⟩ :=
  accepted_of_selected 12 334614 ⟨1128559, by decide⟩ ⟨12, 2, 0, 1128559, 334614, 3445, 65536⟩
    (by decide) selected_cut_41280

theorem selected_cut_41281 : selected 9 ⟨1128626, by decide⟩
    (prefixPartial 12 334615) = some ⟨12, 2, 0, 1128626, 334615, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_334615_1128626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334615 ⟨1128626, by decide⟩ :=
  accepted_of_selected 12 334615 ⟨1128626, by decide⟩ ⟨12, 2, 0, 1128626, 334615, 3165, 65536⟩
    (by decide) selected_cut_41281

theorem unmarked_context_11_83653_1128627 : frontier 10 ⟨1128627, by decide⟩
    (prefixCache 11 83653) (prefixPartial 11 83653) = false := by
  decide +kernel

theorem node_context_11_83653_1128627 : EJMOriginalGlobalDAGData.nodes 10 ⟨1128627, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1128559, by decide⟩,⟨1128626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83653_1128627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83653 ⟨1128627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83653
    ⟨1128627, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1128559, by decide⟩,⟨1128626, by decide⟩]) unmarked_context_11_83653_1128627 node_context_11_83653_1128627
  intro a
  fin_cases a
  · exact context_12_334612_1108174
  · exact context_12_334613_1118965
  · exact context_12_334614_1128559
  · exact context_12_334615_1128626

theorem selected_cut_41282 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334616) = some ⟨12, 1, 0, 1108174, 334616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334616_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334616 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334616 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334616, 1, 65536⟩
    (by decide) selected_cut_41282

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
