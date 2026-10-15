/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover471
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_45315 : selected 9 ⟨1254693, by decide⟩
    (prefixPartial 12 367110) = some ⟨12, 2, 0, 1254693, 367110, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_367110_1254693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367110 ⟨1254693, by decide⟩ :=
  accepted_of_selected 12 367110 ⟨1254693, by decide⟩ ⟨12, 2, 0, 1254693, 367110, 3829, 65536⟩
    (by decide) selected_cut_45315

theorem selected_cut_45316 : selected 8 ⟨1254744, by decide⟩
    (prefixPartial 13 1468444) = some ⟨13, 2, 0, 1254744, 1468444, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_1468444_1254744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1468444 ⟨1254744, by decide⟩ :=
  accepted_of_selected 13 1468444 ⟨1254744, by decide⟩ ⟨13, 2, 0, 1254744, 1468444, 2025, 16384⟩
    (by decide) selected_cut_45316

theorem selected_cut_45317 : selected 8 ⟨1254774, by decide⟩
    (prefixPartial 13 1468445) = some ⟨13, 2, 0, 1254774, 1468445, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_1468445_1254774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1468445 ⟨1254774, by decide⟩ :=
  accepted_of_selected 13 1468445 ⟨1254774, by decide⟩ ⟨13, 2, 0, 1254774, 1468445, 1021, 16384⟩
    (by decide) selected_cut_45317

theorem selected_cut_45318 : selected 8 ⟨1254795, by decide⟩
    (prefixPartial 13 1468446) = some ⟨13, 2, 0, 1254795, 1468446, 669, 16384⟩ := by
  decide +kernel

theorem context_13_1468446_1254795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1468446 ⟨1254795, by decide⟩ :=
  accepted_of_selected 13 1468446 ⟨1254795, by decide⟩ ⟨13, 2, 0, 1254795, 1468446, 669, 16384⟩
    (by decide) selected_cut_45318

theorem selected_cut_45319 : selected 8 ⟨1254810, by decide⟩
    (prefixPartial 13 1468447) = some ⟨13, 2, 0, 1254810, 1468447, 625, 16384⟩ := by
  decide +kernel

theorem context_13_1468447_1254810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1468447 ⟨1254810, by decide⟩ :=
  accepted_of_selected 13 1468447 ⟨1254810, by decide⟩ ⟨13, 2, 0, 1254810, 1468447, 625, 16384⟩
    (by decide) selected_cut_45319

theorem unmarked_context_12_367111_1254811 : frontier 9 ⟨1254811, by decide⟩
    (prefixCache 12 367111) (prefixPartial 12 367111) = false := by
  decide +kernel

theorem node_context_12_367111_1254811 : EJMOriginalGlobalDAGData.nodes 9 ⟨1254811, by decide⟩ =
    .split (coordinate 12) (![⟨1254744, by decide⟩,⟨1254774, by decide⟩,⟨1254795, by decide⟩,⟨1254810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_367111_1254811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367111 ⟨1254811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 367111
    ⟨1254811, by decide⟩ (by decide) (![⟨1254744, by decide⟩,⟨1254774, by decide⟩,⟨1254795, by decide⟩,⟨1254810, by decide⟩]) unmarked_context_12_367111_1254811 node_context_12_367111_1254811
  intro a
  fin_cases a
  · exact context_13_1468444_1254744
  · exact context_13_1468445_1254774
  · exact context_13_1468446_1254795
  · exact context_13_1468447_1254810

theorem unmarked_context_11_91777_1254812 : frontier 10 ⟨1254812, by decide⟩
    (prefixCache 11 91777) (prefixPartial 11 91777) = false := by
  decide +kernel

theorem node_context_11_91777_1254812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1254812, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨1254593, by decide⟩,⟨1254693, by decide⟩,⟨1254811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91777_1254812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91777 ⟨1254812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91777
    ⟨1254812, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨1254593, by decide⟩,⟨1254693, by decide⟩,⟨1254811, by decide⟩]) unmarked_context_11_91777_1254812 node_context_11_91777_1254812
  intro a
  fin_cases a
  · exact context_12_367108_895
  · exact context_12_367109_1254593
  · exact context_12_367110_1254693
  · exact context_12_367111_1254811

theorem selected_cut_45320 : selected 10 ⟨1254918, by decide⟩
    (prefixPartial 11 91778) = some ⟨11, 2, 0, 1254918, 91778, 3833, 262144⟩ := by
  decide +kernel

theorem context_11_91778_1254918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91778 ⟨1254918, by decide⟩ :=
  accepted_of_selected 11 91778 ⟨1254918, by decide⟩ ⟨11, 2, 0, 1254918, 91778, 3833, 262144⟩
    (by decide) selected_cut_45320

theorem selected_cut_45321 : selected 10 ⟨1255009, by decide⟩
    (prefixPartial 11 91779) = some ⟨11, 2, 0, 1255009, 91779, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_91779_1255009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91779 ⟨1255009, by decide⟩ :=
  accepted_of_selected 11 91779 ⟨1255009, by decide⟩ ⟨11, 2, 0, 1255009, 91779, 2185, 262144⟩
    (by decide) selected_cut_45321

theorem unmarked_context_10_22944_1255010 : frontier 11 ⟨1255010, by decide⟩
    (prefixCache 10 22944) (prefixPartial 10 22944) = false := by
  decide +kernel

theorem node_context_10_22944_1255010 : EJMOriginalGlobalDAGData.nodes 11 ⟨1255010, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1254812, by decide⟩,⟨1254918, by decide⟩,⟨1255009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22944_1255010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22944 ⟨1255010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22944
    ⟨1255010, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1254812, by decide⟩,⟨1254918, by decide⟩,⟨1255009, by decide⟩]) unmarked_context_10_22944_1255010 node_context_10_22944_1255010
  intro a
  fin_cases a
  · exact context_11_91776_434745
  · exact context_11_91777_1254812
  · exact context_11_91778_1254918
  · exact context_11_91779_1255009

theorem selected_cut_45322 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 367120) = some ⟨12, 1, 0, 1255011, 367120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367120_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367120 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 367120 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 367120, 1, 65536⟩
    (by decide) selected_cut_45322

theorem selected_cut_45323 : selected 9 ⟨1255106, by decide⟩
    (prefixPartial 12 367121) = some ⟨12, 2, 0, 1255106, 367121, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_367121_1255106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367121 ⟨1255106, by decide⟩ :=
  accepted_of_selected 12 367121 ⟨1255106, by decide⟩ ⟨12, 2, 0, 1255106, 367121, 3361, 65536⟩
    (by decide) selected_cut_45323

theorem selected_cut_45324 : selected 9 ⟨1255180, by decide⟩
    (prefixPartial 12 367122) = some ⟨12, 2, 0, 1255180, 367122, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_367122_1255180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367122 ⟨1255180, by decide⟩ :=
  accepted_of_selected 12 367122 ⟨1255180, by decide⟩ ⟨12, 2, 0, 1255180, 367122, 3037, 65536⟩
    (by decide) selected_cut_45324

theorem selected_cut_45325 : selected 9 ⟨1255272, by decide⟩
    (prefixPartial 12 367123) = some ⟨12, 2, 0, 1255272, 367123, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_367123_1255272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367123 ⟨1255272, by decide⟩ :=
  accepted_of_selected 12 367123 ⟨1255272, by decide⟩ ⟨12, 2, 0, 1255272, 367123, 3781, 65536⟩
    (by decide) selected_cut_45325

theorem unmarked_context_11_91780_1255273 : frontier 10 ⟨1255273, by decide⟩
    (prefixCache 11 91780) (prefixPartial 11 91780) = false := by
  decide +kernel

theorem node_context_11_91780_1255273 : EJMOriginalGlobalDAGData.nodes 10 ⟨1255273, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1255106, by decide⟩,⟨1255180, by decide⟩,⟨1255272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91780_1255273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91780 ⟨1255273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91780
    ⟨1255273, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1255106, by decide⟩,⟨1255180, by decide⟩,⟨1255272, by decide⟩]) unmarked_context_11_91780_1255273 node_context_11_91780_1255273
  intro a
  fin_cases a
  · exact context_12_367120_1255011
  · exact context_12_367121_1255106
  · exact context_12_367122_1255180
  · exact context_12_367123_1255272

theorem selected_cut_45326 : selected 9 ⟨1255346, by decide⟩
    (prefixPartial 12 367124) = some ⟨12, 2, 0, 1255346, 367124, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_367124_1255346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367124 ⟨1255346, by decide⟩ :=
  accepted_of_selected 12 367124 ⟨1255346, by decide⟩ ⟨12, 2, 0, 1255346, 367124, 2757, 65536⟩
    (by decide) selected_cut_45326

theorem selected_cut_45327 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 367125) = some ⟨12, 1, 0, 1118965, 367125, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367125_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367125 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 367125 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 367125, 1, 65536⟩
    (by decide) selected_cut_45327

theorem selected_cut_45328 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 367126) = some ⟨12, 1, 0, 692793, 367126, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367126_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367126 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 367126 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 367126, 1, 65536⟩
    (by decide) selected_cut_45328

theorem selected_cut_45329 : selected 9 ⟨1255433, by decide⟩
    (prefixPartial 12 367127) = some ⟨12, 2, 0, 1255433, 367127, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_367127_1255433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367127 ⟨1255433, by decide⟩ :=
  accepted_of_selected 12 367127 ⟨1255433, by decide⟩ ⟨12, 2, 0, 1255433, 367127, 3473, 65536⟩
    (by decide) selected_cut_45329

theorem unmarked_context_11_91781_1255434 : frontier 10 ⟨1255434, by decide⟩
    (prefixCache 11 91781) (prefixPartial 11 91781) = false := by
  decide +kernel

theorem node_context_11_91781_1255434 : EJMOriginalGlobalDAGData.nodes 10 ⟨1255434, by decide⟩ =
    .split (coordinate 11) (![⟨1255346, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1255433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91781_1255434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91781 ⟨1255434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91781
    ⟨1255434, by decide⟩ (by decide) (![⟨1255346, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1255433, by decide⟩]) unmarked_context_11_91781_1255434 node_context_11_91781_1255434
  intro a
  fin_cases a
  · exact context_12_367124_1255346
  · exact context_12_367125_1118965
  · exact context_12_367126_692793
  · exact context_12_367127_1255433

theorem selected_cut_45330 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 367128) = some ⟨12, 1, 0, 994572, 367128, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367128_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367128 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 367128 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 367128, 1, 65536⟩
    (by decide) selected_cut_45330

theorem selected_cut_45331 : selected 9 ⟨1255495, by decide⟩
    (prefixPartial 12 367129) = some ⟨12, 2, 0, 1255495, 367129, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_367129_1255495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367129 ⟨1255495, by decide⟩ :=
  accepted_of_selected 12 367129 ⟨1255495, by decide⟩ ⟨12, 2, 0, 1255495, 367129, 2717, 65536⟩
    (by decide) selected_cut_45331

theorem selected_cut_45332 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 367130) = some ⟨12, 1, 0, 893903, 367130, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367130_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367130 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 367130 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 367130, 1, 65536⟩
    (by decide) selected_cut_45332

theorem selected_cut_45333 : selected 9 ⟨1255575, by decide⟩
    (prefixPartial 12 367131) = some ⟨12, 2, 0, 1255575, 367131, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_367131_1255575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367131 ⟨1255575, by decide⟩ :=
  accepted_of_selected 12 367131 ⟨1255575, by decide⟩ ⟨12, 2, 0, 1255575, 367131, 3053, 65536⟩
    (by decide) selected_cut_45333

theorem unmarked_context_11_91782_1255576 : frontier 10 ⟨1255576, by decide⟩
    (prefixCache 11 91782) (prefixPartial 11 91782) = false := by
  decide +kernel

theorem node_context_11_91782_1255576 : EJMOriginalGlobalDAGData.nodes 10 ⟨1255576, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1255495, by decide⟩,⟨893903, by decide⟩,⟨1255575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91782_1255576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91782 ⟨1255576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91782
    ⟨1255576, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1255495, by decide⟩,⟨893903, by decide⟩,⟨1255575, by decide⟩]) unmarked_context_11_91782_1255576 node_context_11_91782_1255576
  intro a
  fin_cases a
  · exact context_12_367128_994572
  · exact context_12_367129_1255495
  · exact context_12_367130_893903
  · exact context_12_367131_1255575

theorem selected_cut_45334 : selected 9 ⟨1255651, by decide⟩
    (prefixPartial 12 367132) = some ⟨12, 2, 0, 1255651, 367132, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_367132_1255651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367132 ⟨1255651, by decide⟩ :=
  accepted_of_selected 12 367132 ⟨1255651, by decide⟩ ⟨12, 2, 0, 1255651, 367132, 2969, 65536⟩
    (by decide) selected_cut_45334

theorem selected_cut_45335 : selected 9 ⟨1255721, by decide⟩
    (prefixPartial 12 367133) = some ⟨12, 2, 0, 1255721, 367133, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_367133_1255721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367133 ⟨1255721, by decide⟩ :=
  accepted_of_selected 12 367133 ⟨1255721, by decide⟩ ⟨12, 2, 0, 1255721, 367133, 2913, 65536⟩
    (by decide) selected_cut_45335

theorem selected_cut_45336 : selected 9 ⟨1255781, by decide⟩
    (prefixPartial 12 367134) = some ⟨12, 2, 0, 1255781, 367134, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_367134_1255781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367134 ⟨1255781, by decide⟩ :=
  accepted_of_selected 12 367134 ⟨1255781, by decide⟩ ⟨12, 2, 0, 1255781, 367134, 2741, 65536⟩
    (by decide) selected_cut_45336

theorem selected_cut_45337 : selected 9 ⟨1255839, by decide⟩
    (prefixPartial 12 367135) = some ⟨12, 2, 0, 1255839, 367135, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_367135_1255839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367135 ⟨1255839, by decide⟩ :=
  accepted_of_selected 12 367135 ⟨1255839, by decide⟩ ⟨12, 2, 0, 1255839, 367135, 2649, 65536⟩
    (by decide) selected_cut_45337

theorem unmarked_context_11_91783_1255840 : frontier 10 ⟨1255840, by decide⟩
    (prefixCache 11 91783) (prefixPartial 11 91783) = false := by
  decide +kernel

theorem node_context_11_91783_1255840 : EJMOriginalGlobalDAGData.nodes 10 ⟨1255840, by decide⟩ =
    .split (coordinate 11) (![⟨1255651, by decide⟩,⟨1255721, by decide⟩,⟨1255781, by decide⟩,⟨1255839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91783_1255840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91783 ⟨1255840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91783
    ⟨1255840, by decide⟩ (by decide) (![⟨1255651, by decide⟩,⟨1255721, by decide⟩,⟨1255781, by decide⟩,⟨1255839, by decide⟩]) unmarked_context_11_91783_1255840 node_context_11_91783_1255840
  intro a
  fin_cases a
  · exact context_12_367132_1255651
  · exact context_12_367133_1255721
  · exact context_12_367134_1255781
  · exact context_12_367135_1255839

theorem unmarked_context_10_22945_1255841 : frontier 11 ⟨1255841, by decide⟩
    (prefixCache 10 22945) (prefixPartial 10 22945) = false := by
  decide +kernel

theorem node_context_10_22945_1255841 : EJMOriginalGlobalDAGData.nodes 11 ⟨1255841, by decide⟩ =
    .split (coordinate 10) (![⟨1255273, by decide⟩,⟨1255434, by decide⟩,⟨1255576, by decide⟩,⟨1255840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22945_1255841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22945 ⟨1255841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22945
    ⟨1255841, by decide⟩ (by decide) (![⟨1255273, by decide⟩,⟨1255434, by decide⟩,⟨1255576, by decide⟩,⟨1255840, by decide⟩]) unmarked_context_10_22945_1255841 node_context_10_22945_1255841
  intro a
  fin_cases a
  · exact context_11_91780_1255273
  · exact context_11_91781_1255434
  · exact context_11_91782_1255576
  · exact context_11_91783_1255840

theorem selected_cut_45338 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 367136) = some ⟨12, 1, 0, 435790, 367136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367136_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367136 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 367136 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 367136, 1, 65536⟩
    (by decide) selected_cut_45338

theorem selected_cut_45339 : selected 9 ⟨1255899, by decide⟩
    (prefixPartial 12 367137) = some ⟨12, 2, 0, 1255899, 367137, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_367137_1255899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367137 ⟨1255899, by decide⟩ :=
  accepted_of_selected 12 367137 ⟨1255899, by decide⟩ ⟨12, 2, 0, 1255899, 367137, 2109, 65536⟩
    (by decide) selected_cut_45339

theorem selected_cut_45340 : selected 9 ⟨1255938, by decide⟩
    (prefixPartial 12 367138) = some ⟨12, 2, 0, 1255938, 367138, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_367138_1255938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367138 ⟨1255938, by decide⟩ :=
  accepted_of_selected 12 367138 ⟨1255938, by decide⟩ ⟨12, 2, 0, 1255938, 367138, 1685, 65536⟩
    (by decide) selected_cut_45340

theorem selected_cut_45341 : selected 9 ⟨1255991, by decide⟩
    (prefixPartial 12 367139) = some ⟨12, 2, 0, 1255991, 367139, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_367139_1255991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367139 ⟨1255991, by decide⟩ :=
  accepted_of_selected 12 367139 ⟨1255991, by decide⟩ ⟨12, 2, 0, 1255991, 367139, 1981, 65536⟩
    (by decide) selected_cut_45341

theorem unmarked_context_11_91784_1255992 : frontier 10 ⟨1255992, by decide⟩
    (prefixCache 11 91784) (prefixPartial 11 91784) = false := by
  decide +kernel

theorem node_context_11_91784_1255992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1255992, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1255899, by decide⟩,⟨1255938, by decide⟩,⟨1255991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91784_1255992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91784 ⟨1255992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91784
    ⟨1255992, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1255899, by decide⟩,⟨1255938, by decide⟩,⟨1255991, by decide⟩]) unmarked_context_11_91784_1255992 node_context_11_91784_1255992
  intro a
  fin_cases a
  · exact context_12_367136_435790
  · exact context_12_367137_1255899
  · exact context_12_367138_1255938
  · exact context_12_367139_1255991

theorem selected_cut_45342 : selected 9 ⟨1256044, by decide⟩
    (prefixPartial 12 367140) = some ⟨12, 2, 0, 1256044, 367140, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_367140_1256044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367140 ⟨1256044, by decide⟩ :=
  accepted_of_selected 12 367140 ⟨1256044, by decide⟩ ⟨12, 2, 0, 1256044, 367140, 1925, 65536⟩
    (by decide) selected_cut_45342

theorem selected_cut_45343 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 367141) = some ⟨12, 1, 0, 688903, 367141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367141_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367141 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 367141 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 367141, 1, 65536⟩
    (by decide) selected_cut_45343

theorem selected_cut_45344 : selected 9 ⟨1256090, by decide⟩
    (prefixPartial 12 367142) = some ⟨12, 2, 0, 1256090, 367142, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_367142_1256090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367142 ⟨1256090, by decide⟩ :=
  accepted_of_selected 12 367142 ⟨1256090, by decide⟩ ⟨12, 2, 0, 1256090, 367142, 1813, 65536⟩
    (by decide) selected_cut_45344

theorem selected_cut_45345 : selected 9 ⟨1256147, by decide⟩
    (prefixPartial 12 367143) = some ⟨12, 2, 0, 1256147, 367143, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_367143_1256147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367143 ⟨1256147, by decide⟩ :=
  accepted_of_selected 12 367143 ⟨1256147, by decide⟩ ⟨12, 2, 0, 1256147, 367143, 2053, 65536⟩
    (by decide) selected_cut_45345

theorem unmarked_context_11_91785_1256148 : frontier 10 ⟨1256148, by decide⟩
    (prefixCache 11 91785) (prefixPartial 11 91785) = false := by
  decide +kernel

theorem node_context_11_91785_1256148 : EJMOriginalGlobalDAGData.nodes 10 ⟨1256148, by decide⟩ =
    .split (coordinate 11) (![⟨1256044, by decide⟩,⟨688903, by decide⟩,⟨1256090, by decide⟩,⟨1256147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91785_1256148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91785 ⟨1256148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91785
    ⟨1256148, by decide⟩ (by decide) (![⟨1256044, by decide⟩,⟨688903, by decide⟩,⟨1256090, by decide⟩,⟨1256147, by decide⟩]) unmarked_context_11_91785_1256148 node_context_11_91785_1256148
  intro a
  fin_cases a
  · exact context_12_367140_1256044
  · exact context_12_367141_688903
  · exact context_12_367142_1256090
  · exact context_12_367143_1256147

theorem selected_cut_45346 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 91786) = some ⟨11, 1, 0, 900587, 91786, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91786_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91786 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 91786 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 91786, 1, 262144⟩
    (by decide) selected_cut_45346

theorem selected_cut_45347 : selected 9 ⟨1256193, by decide⟩
    (prefixPartial 12 367148) = some ⟨12, 2, 0, 1256193, 367148, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_367148_1256193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367148 ⟨1256193, by decide⟩ :=
  accepted_of_selected 12 367148 ⟨1256193, by decide⟩ ⟨12, 2, 0, 1256193, 367148, 1817, 65536⟩
    (by decide) selected_cut_45347

theorem selected_cut_45348 : selected 9 ⟨1256242, by decide⟩
    (prefixPartial 12 367149) = some ⟨12, 2, 0, 1256242, 367149, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_367149_1256242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367149 ⟨1256242, by decide⟩ :=
  accepted_of_selected 12 367149 ⟨1256242, by decide⟩ ⟨12, 2, 0, 1256242, 367149, 1877, 65536⟩
    (by decide) selected_cut_45348

theorem selected_cut_45349 : selected 9 ⟨1256273, by decide⟩
    (prefixPartial 12 367150) = some ⟨12, 2, 0, 1256273, 367150, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_367150_1256273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367150 ⟨1256273, by decide⟩ :=
  accepted_of_selected 12 367150 ⟨1256273, by decide⟩ ⟨12, 2, 0, 1256273, 367150, 1565, 65536⟩
    (by decide) selected_cut_45349

theorem selected_cut_45350 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 367151) = some ⟨12, 1, 0, 758968, 367151, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367151_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367151 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 367151 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 367151, 1, 65536⟩
    (by decide) selected_cut_45350

theorem unmarked_context_11_91787_1256274 : frontier 10 ⟨1256274, by decide⟩
    (prefixCache 11 91787) (prefixPartial 11 91787) = false := by
  decide +kernel

theorem node_context_11_91787_1256274 : EJMOriginalGlobalDAGData.nodes 10 ⟨1256274, by decide⟩ =
    .split (coordinate 11) (![⟨1256193, by decide⟩,⟨1256242, by decide⟩,⟨1256273, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91787_1256274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91787 ⟨1256274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91787
    ⟨1256274, by decide⟩ (by decide) (![⟨1256193, by decide⟩,⟨1256242, by decide⟩,⟨1256273, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_91787_1256274 node_context_11_91787_1256274
  intro a
  fin_cases a
  · exact context_12_367148_1256193
  · exact context_12_367149_1256242
  · exact context_12_367150_1256273
  · exact context_12_367151_758968

theorem unmarked_context_10_22946_1256275 : frontier 11 ⟨1256275, by decide⟩
    (prefixCache 10 22946) (prefixPartial 10 22946) = false := by
  decide +kernel

theorem node_context_10_22946_1256275 : EJMOriginalGlobalDAGData.nodes 11 ⟨1256275, by decide⟩ =
    .split (coordinate 10) (![⟨1255992, by decide⟩,⟨1256148, by decide⟩,⟨900587, by decide⟩,⟨1256274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22946_1256275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22946 ⟨1256275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22946
    ⟨1256275, by decide⟩ (by decide) (![⟨1255992, by decide⟩,⟨1256148, by decide⟩,⟨900587, by decide⟩,⟨1256274, by decide⟩]) unmarked_context_10_22946_1256275 node_context_10_22946_1256275
  intro a
  fin_cases a
  · exact context_11_91784_1255992
  · exact context_11_91785_1256148
  · exact context_11_91786_900587
  · exact context_11_91787_1256274

theorem selected_cut_45351 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 367152) = some ⟨12, 1, 0, 1255011, 367152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367152_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367152 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 367152 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 367152, 1, 65536⟩
    (by decide) selected_cut_45351

theorem selected_cut_45352 : selected 9 ⟨1256342, by decide⟩
    (prefixPartial 12 367153) = some ⟨12, 2, 0, 1256342, 367153, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_367153_1256342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367153 ⟨1256342, by decide⟩ :=
  accepted_of_selected 12 367153 ⟨1256342, by decide⟩ ⟨12, 2, 0, 1256342, 367153, 2361, 65536⟩
    (by decide) selected_cut_45352

theorem selected_cut_45353 : selected 9 ⟨1256395, by decide⟩
    (prefixPartial 12 367154) = some ⟨12, 2, 0, 1256395, 367154, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_367154_1256395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367154 ⟨1256395, by decide⟩ :=
  accepted_of_selected 12 367154 ⟨1256395, by decide⟩ ⟨12, 2, 0, 1256395, 367154, 2049, 65536⟩
    (by decide) selected_cut_45353

theorem selected_cut_45354 : selected 9 ⟨1256455, by decide⟩
    (prefixPartial 12 367155) = some ⟨12, 2, 0, 1256455, 367155, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_367155_1256455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367155 ⟨1256455, by decide⟩ :=
  accepted_of_selected 12 367155 ⟨1256455, by decide⟩ ⟨12, 2, 0, 1256455, 367155, 2221, 65536⟩
    (by decide) selected_cut_45354

theorem unmarked_context_11_91788_1256456 : frontier 10 ⟨1256456, by decide⟩
    (prefixCache 11 91788) (prefixPartial 11 91788) = false := by
  decide +kernel

theorem node_context_11_91788_1256456 : EJMOriginalGlobalDAGData.nodes 10 ⟨1256456, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1256342, by decide⟩,⟨1256395, by decide⟩,⟨1256455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91788_1256456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91788 ⟨1256456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91788
    ⟨1256456, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1256342, by decide⟩,⟨1256395, by decide⟩,⟨1256455, by decide⟩]) unmarked_context_11_91788_1256456 node_context_11_91788_1256456
  intro a
  fin_cases a
  · exact context_12_367152_1255011
  · exact context_12_367153_1256342
  · exact context_12_367154_1256395
  · exact context_12_367155_1256455

theorem selected_cut_45355 : selected 9 ⟨1256518, by decide⟩
    (prefixPartial 12 367156) = some ⟨12, 2, 0, 1256518, 367156, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_367156_1256518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367156 ⟨1256518, by decide⟩ :=
  accepted_of_selected 12 367156 ⟨1256518, by decide⟩ ⟨12, 2, 0, 1256518, 367156, 1853, 65536⟩
    (by decide) selected_cut_45355

theorem selected_cut_45356 : selected 9 ⟨1256596, by decide⟩
    (prefixPartial 12 367157) = some ⟨12, 2, 0, 1256596, 367157, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_367157_1256596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367157 ⟨1256596, by decide⟩ :=
  accepted_of_selected 12 367157 ⟨1256596, by decide⟩ ⟨12, 2, 0, 1256596, 367157, 2393, 65536⟩
    (by decide) selected_cut_45356

theorem selected_cut_45357 : selected 9 ⟨1256640, by decide⟩
    (prefixPartial 12 367158) = some ⟨12, 2, 0, 1256640, 367158, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_367158_1256640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367158 ⟨1256640, by decide⟩ :=
  accepted_of_selected 12 367158 ⟨1256640, by decide⟩ ⟨12, 2, 0, 1256640, 367158, 1709, 65536⟩
    (by decide) selected_cut_45357

theorem selected_cut_45358 : selected 9 ⟨1256692, by decide⟩
    (prefixPartial 12 367159) = some ⟨12, 2, 0, 1256692, 367159, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_367159_1256692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367159 ⟨1256692, by decide⟩ :=
  accepted_of_selected 12 367159 ⟨1256692, by decide⟩ ⟨12, 2, 0, 1256692, 367159, 1737, 65536⟩
    (by decide) selected_cut_45358

theorem unmarked_context_11_91789_1256693 : frontier 10 ⟨1256693, by decide⟩
    (prefixCache 11 91789) (prefixPartial 11 91789) = false := by
  decide +kernel

theorem node_context_11_91789_1256693 : EJMOriginalGlobalDAGData.nodes 10 ⟨1256693, by decide⟩ =
    .split (coordinate 11) (![⟨1256518, by decide⟩,⟨1256596, by decide⟩,⟨1256640, by decide⟩,⟨1256692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91789_1256693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91789 ⟨1256693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91789
    ⟨1256693, by decide⟩ (by decide) (![⟨1256518, by decide⟩,⟨1256596, by decide⟩,⟨1256640, by decide⟩,⟨1256692, by decide⟩]) unmarked_context_11_91789_1256693 node_context_11_91789_1256693
  intro a
  fin_cases a
  · exact context_12_367156_1256518
  · exact context_12_367157_1256596
  · exact context_12_367158_1256640
  · exact context_12_367159_1256692

theorem selected_cut_45359 : selected 10 ⟨1256786, by decide⟩
    (prefixPartial 11 91790) = some ⟨11, 2, 0, 1256786, 91790, 3369, 262144⟩ := by
  decide +kernel

theorem context_11_91790_1256786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91790 ⟨1256786, by decide⟩ :=
  accepted_of_selected 11 91790 ⟨1256786, by decide⟩ ⟨11, 2, 0, 1256786, 91790, 3369, 262144⟩
    (by decide) selected_cut_45359

theorem selected_cut_45360 : selected 10 ⟨1256863, by decide⟩
    (prefixPartial 11 91791) = some ⟨11, 2, 0, 1256863, 91791, 2701, 262144⟩ := by
  decide +kernel

theorem context_11_91791_1256863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91791 ⟨1256863, by decide⟩ :=
  accepted_of_selected 11 91791 ⟨1256863, by decide⟩ ⟨11, 2, 0, 1256863, 91791, 2701, 262144⟩
    (by decide) selected_cut_45360

theorem unmarked_context_10_22947_1256864 : frontier 11 ⟨1256864, by decide⟩
    (prefixCache 10 22947) (prefixPartial 10 22947) = false := by
  decide +kernel

theorem node_context_10_22947_1256864 : EJMOriginalGlobalDAGData.nodes 11 ⟨1256864, by decide⟩ =
    .split (coordinate 10) (![⟨1256456, by decide⟩,⟨1256693, by decide⟩,⟨1256786, by decide⟩,⟨1256863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22947_1256864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22947 ⟨1256864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22947
    ⟨1256864, by decide⟩ (by decide) (![⟨1256456, by decide⟩,⟨1256693, by decide⟩,⟨1256786, by decide⟩,⟨1256863, by decide⟩]) unmarked_context_10_22947_1256864 node_context_10_22947_1256864
  intro a
  fin_cases a
  · exact context_11_91788_1256456
  · exact context_11_91789_1256693
  · exact context_11_91790_1256786
  · exact context_11_91791_1256863

theorem unmarked_context_9_5736_1256865 : frontier 12 ⟨1256865, by decide⟩
    (prefixCache 9 5736) (prefixPartial 9 5736) = false := by
  decide +kernel

theorem node_context_9_5736_1256865 : EJMOriginalGlobalDAGData.nodes 12 ⟨1256865, by decide⟩ =
    .split (coordinate 9) (![⟨1255010, by decide⟩,⟨1255841, by decide⟩,⟨1256275, by decide⟩,⟨1256864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5736_1256865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5736 ⟨1256865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5736
    ⟨1256865, by decide⟩ (by decide) (![⟨1255010, by decide⟩,⟨1255841, by decide⟩,⟨1256275, by decide⟩,⟨1256864, by decide⟩]) unmarked_context_9_5736_1256865 node_context_9_5736_1256865
  intro a
  fin_cases a
  · exact context_10_22944_1255010
  · exact context_10_22945_1255841
  · exact context_10_22946_1256275
  · exact context_10_22947_1256864

theorem selected_cut_45361 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 22948) = some ⟨10, 1, 0, 3442, 22948, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22948_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22948 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 22948 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 22948, 1, 1048576⟩
    (by decide) selected_cut_45361

theorem selected_cut_45362 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22949) = some ⟨10, 1, 0, 893098, 22949, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22949_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22949 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22949 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22949, 1, 1048576⟩
    (by decide) selected_cut_45362

theorem selected_cut_45363 : selected 10 ⟨1256929, by decide⟩
    (prefixPartial 11 91800) = some ⟨11, 2, 0, 1256929, 91800, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_91800_1256929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91800 ⟨1256929, by decide⟩ :=
  accepted_of_selected 11 91800 ⟨1256929, by decide⟩ ⟨11, 2, 0, 1256929, 91800, 1805, 262144⟩
    (by decide) selected_cut_45363

theorem selected_cut_45364 : selected 10 ⟨1256992, by decide⟩
    (prefixPartial 11 91801) = some ⟨11, 2, 0, 1256992, 91801, 2533, 262144⟩ := by
  decide +kernel

theorem context_11_91801_1256992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91801 ⟨1256992, by decide⟩ :=
  accepted_of_selected 11 91801 ⟨1256992, by decide⟩ ⟨11, 2, 0, 1256992, 91801, 2533, 262144⟩
    (by decide) selected_cut_45364

theorem selected_cut_45365 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 91802) = some ⟨11, 1, 0, 900587, 91802, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91802_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91802 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 91802 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 91802, 1, 262144⟩
    (by decide) selected_cut_45365

theorem selected_cut_45366 : selected 10 ⟨1257031, by decide⟩
    (prefixPartial 11 91803) = some ⟨11, 2, 0, 1257031, 91803, 1545, 262144⟩ := by
  decide +kernel

theorem context_11_91803_1257031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91803 ⟨1257031, by decide⟩ :=
  accepted_of_selected 11 91803 ⟨1257031, by decide⟩ ⟨11, 2, 0, 1257031, 91803, 1545, 262144⟩
    (by decide) selected_cut_45366

theorem unmarked_context_10_22950_1257032 : frontier 11 ⟨1257032, by decide⟩
    (prefixCache 10 22950) (prefixPartial 10 22950) = false := by
  decide +kernel

theorem node_context_10_22950_1257032 : EJMOriginalGlobalDAGData.nodes 11 ⟨1257032, by decide⟩ =
    .split (coordinate 10) (![⟨1256929, by decide⟩,⟨1256992, by decide⟩,⟨900587, by decide⟩,⟨1257031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22950_1257032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22950 ⟨1257032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22950
    ⟨1257032, by decide⟩ (by decide) (![⟨1256929, by decide⟩,⟨1256992, by decide⟩,⟨900587, by decide⟩,⟨1257031, by decide⟩]) unmarked_context_10_22950_1257032 node_context_10_22950_1257032
  intro a
  fin_cases a
  · exact context_11_91800_1256929
  · exact context_11_91801_1256992
  · exact context_11_91802_900587
  · exact context_11_91803_1257031

theorem selected_cut_45367 : selected 10 ⟨1257121, by decide⟩
    (prefixPartial 11 91804) = some ⟨11, 2, 0, 1257121, 91804, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_91804_1257121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91804 ⟨1257121, by decide⟩ :=
  accepted_of_selected 11 91804 ⟨1257121, by decide⟩ ⟨11, 2, 0, 1257121, 91804, 3149, 262144⟩
    (by decide) selected_cut_45367

theorem selected_cut_45368 : selected 10 ⟨1257164, by decide⟩
    (prefixPartial 11 91805) = some ⟨11, 2, 0, 1257164, 91805, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_91805_1257164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91805 ⟨1257164, by decide⟩ :=
  accepted_of_selected 11 91805 ⟨1257164, by decide⟩ ⟨11, 2, 0, 1257164, 91805, 1809, 262144⟩
    (by decide) selected_cut_45368

theorem selected_cut_45369 : selected 10 ⟨1257195, by decide⟩
    (prefixPartial 11 91806) = some ⟨11, 2, 0, 1257195, 91806, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_91806_1257195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91806 ⟨1257195, by decide⟩ :=
  accepted_of_selected 11 91806 ⟨1257195, by decide⟩ ⟨11, 2, 0, 1257195, 91806, 1069, 262144⟩
    (by decide) selected_cut_45369

theorem selected_cut_45370 : selected 10 ⟨1257210, by decide⟩
    (prefixPartial 11 91807) = some ⟨11, 2, 0, 1257210, 91807, 829, 262144⟩ := by
  decide +kernel

theorem context_11_91807_1257210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91807 ⟨1257210, by decide⟩ :=
  accepted_of_selected 11 91807 ⟨1257210, by decide⟩ ⟨11, 2, 0, 1257210, 91807, 829, 262144⟩
    (by decide) selected_cut_45370

theorem unmarked_context_10_22951_1257211 : frontier 11 ⟨1257211, by decide⟩
    (prefixCache 10 22951) (prefixPartial 10 22951) = false := by
  decide +kernel

theorem node_context_10_22951_1257211 : EJMOriginalGlobalDAGData.nodes 11 ⟨1257211, by decide⟩ =
    .split (coordinate 10) (![⟨1257121, by decide⟩,⟨1257164, by decide⟩,⟨1257195, by decide⟩,⟨1257210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22951_1257211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22951 ⟨1257211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22951
    ⟨1257211, by decide⟩ (by decide) (![⟨1257121, by decide⟩,⟨1257164, by decide⟩,⟨1257195, by decide⟩,⟨1257210, by decide⟩]) unmarked_context_10_22951_1257211 node_context_10_22951_1257211
  intro a
  fin_cases a
  · exact context_11_91804_1257121
  · exact context_11_91805_1257164
  · exact context_11_91806_1257195
  · exact context_11_91807_1257210

theorem unmarked_context_9_5737_1257212 : frontier 12 ⟨1257212, by decide⟩
    (prefixCache 9 5737) (prefixPartial 9 5737) = false := by
  decide +kernel

theorem node_context_9_5737_1257212 : EJMOriginalGlobalDAGData.nodes 12 ⟨1257212, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1257032, by decide⟩,⟨1257211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5737_1257212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5737 ⟨1257212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5737
    ⟨1257212, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1257032, by decide⟩,⟨1257211, by decide⟩]) unmarked_context_9_5737_1257212 node_context_9_5737_1257212
  intro a
  fin_cases a
  · exact context_10_22948_3442
  · exact context_10_22949_893098
  · exact context_10_22950_1257032
  · exact context_10_22951_1257211

theorem selected_cut_45371 : selected 12 ⟨1257309, by decide⟩
    (prefixPartial 9 5738) = some ⟨9, 2, 0, 1257309, 5738, 2481, 4194304⟩ := by
  decide +kernel

theorem context_9_5738_1257309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5738 ⟨1257309, by decide⟩ :=
  accepted_of_selected 9 5738 ⟨1257309, by decide⟩ ⟨9, 2, 0, 1257309, 5738, 2481, 4194304⟩
    (by decide) selected_cut_45371

theorem selected_cut_45372 : selected 12 ⟨1257324, by decide⟩
    (prefixPartial 9 5739) = some ⟨9, 2, 0, 1257324, 5739, 285, 4194304⟩ := by
  decide +kernel

theorem context_9_5739_1257324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5739 ⟨1257324, by decide⟩ :=
  accepted_of_selected 9 5739 ⟨1257324, by decide⟩ ⟨9, 2, 0, 1257324, 5739, 285, 4194304⟩
    (by decide) selected_cut_45372

theorem unmarked_context_8_1434_1257325 : frontier 13 ⟨1257325, by decide⟩
    (prefixCache 8 1434) (prefixPartial 8 1434) = false := by
  decide +kernel

theorem node_context_8_1434_1257325 : EJMOriginalGlobalDAGData.nodes 13 ⟨1257325, by decide⟩ =
    .split (coordinate 8) (![⟨1256865, by decide⟩,⟨1257212, by decide⟩,⟨1257309, by decide⟩,⟨1257324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1434_1257325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1434 ⟨1257325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1434
    ⟨1257325, by decide⟩ (by decide) (![⟨1256865, by decide⟩,⟨1257212, by decide⟩,⟨1257309, by decide⟩,⟨1257324, by decide⟩]) unmarked_context_8_1434_1257325 node_context_8_1434_1257325
  intro a
  fin_cases a
  · exact context_9_5736_1256865
  · exact context_9_5737_1257212
  · exact context_9_5738_1257309
  · exact context_9_5739_1257324

theorem selected_cut_45373 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 91840) = some ⟨11, 1, 0, 434745, 91840, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91840_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91840 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 91840 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 91840, 1, 262144⟩
    (by decide) selected_cut_45373

theorem selected_cut_45374 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 367364) = some ⟨12, 1, 0, 895, 367364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367364_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367364 ⟨895, by decide⟩ :=
  accepted_of_selected 12 367364 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 367364, 1, 65536⟩
    (by decide) selected_cut_45374

theorem selected_cut_45375 : selected 9 ⟨1257460, by decide⟩
    (prefixPartial 12 367365) = some ⟨12, 2, 0, 1257460, 367365, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_367365_1257460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367365 ⟨1257460, by decide⟩ :=
  accepted_of_selected 12 367365 ⟨1257460, by decide⟩ ⟨12, 2, 0, 1257460, 367365, 2929, 65536⟩
    (by decide) selected_cut_45375

theorem selected_cut_45376 : selected 9 ⟨1257565, by decide⟩
    (prefixPartial 12 367366) = some ⟨12, 2, 0, 1257565, 367366, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_367366_1257565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367366 ⟨1257565, by decide⟩ :=
  accepted_of_selected 12 367366 ⟨1257565, by decide⟩ ⟨12, 2, 0, 1257565, 367366, 3957, 65536⟩
    (by decide) selected_cut_45376

theorem selected_cut_45377 : selected 9 ⟨1257655, by decide⟩
    (prefixPartial 12 367367) = some ⟨12, 2, 0, 1257655, 367367, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_367367_1257655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367367 ⟨1257655, by decide⟩ :=
  accepted_of_selected 12 367367 ⟨1257655, by decide⟩ ⟨12, 2, 0, 1257655, 367367, 3905, 65536⟩
    (by decide) selected_cut_45377

theorem unmarked_context_11_91841_1257656 : frontier 10 ⟨1257656, by decide⟩
    (prefixCache 11 91841) (prefixPartial 11 91841) = false := by
  decide +kernel

theorem node_context_11_91841_1257656 : EJMOriginalGlobalDAGData.nodes 10 ⟨1257656, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨1257460, by decide⟩,⟨1257565, by decide⟩,⟨1257655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91841_1257656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91841 ⟨1257656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91841
    ⟨1257656, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨1257460, by decide⟩,⟨1257565, by decide⟩,⟨1257655, by decide⟩]) unmarked_context_11_91841_1257656 node_context_11_91841_1257656
  intro a
  fin_cases a
  · exact context_12_367364_895
  · exact context_12_367365_1257460
  · exact context_12_367366_1257565
  · exact context_12_367367_1257655

theorem selected_cut_45378 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 367368) = some ⟨12, 1, 0, 895, 367368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367368_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367368 ⟨895, by decide⟩ :=
  accepted_of_selected 12 367368 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 367368, 1, 65536⟩
    (by decide) selected_cut_45378

theorem selected_cut_45379 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 367369) = some ⟨12, 1, 0, 895, 367369, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367369_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367369 ⟨895, by decide⟩ :=
  accepted_of_selected 12 367369 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 367369, 1, 65536⟩
    (by decide) selected_cut_45379

theorem selected_cut_45380 : selected 9 ⟨1257712, by decide⟩
    (prefixPartial 12 367370) = some ⟨12, 2, 0, 1257712, 367370, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_367370_1257712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367370 ⟨1257712, by decide⟩ :=
  accepted_of_selected 12 367370 ⟨1257712, by decide⟩ ⟨12, 2, 0, 1257712, 367370, 1953, 65536⟩
    (by decide) selected_cut_45380

theorem selected_cut_45381 : selected 9 ⟨1257790, by decide⟩
    (prefixPartial 12 367371) = some ⟨12, 2, 0, 1257790, 367371, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_367371_1257790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367371 ⟨1257790, by decide⟩ :=
  accepted_of_selected 12 367371 ⟨1257790, by decide⟩ ⟨12, 2, 0, 1257790, 367371, 3893, 65536⟩
    (by decide) selected_cut_45381

theorem unmarked_context_11_91842_1257791 : frontier 10 ⟨1257791, by decide⟩
    (prefixCache 11 91842) (prefixPartial 11 91842) = false := by
  decide +kernel

theorem node_context_11_91842_1257791 : EJMOriginalGlobalDAGData.nodes 10 ⟨1257791, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨1257712, by decide⟩,⟨1257790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91842_1257791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91842 ⟨1257791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91842
    ⟨1257791, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨1257712, by decide⟩,⟨1257790, by decide⟩]) unmarked_context_11_91842_1257791 node_context_11_91842_1257791
  intro a
  fin_cases a
  · exact context_12_367368_895
  · exact context_12_367369_895
  · exact context_12_367370_1257712
  · exact context_12_367371_1257790

theorem selected_cut_45382 : selected 10 ⟨982326, by decide⟩
    (prefixPartial 11 91843) = some ⟨11, 2, 0, 982326, 91843, 5, 262144⟩ := by
  decide +kernel

theorem context_11_91843_982326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91843 ⟨982326, by decide⟩ :=
  accepted_of_selected 11 91843 ⟨982326, by decide⟩ ⟨11, 2, 0, 982326, 91843, 5, 262144⟩
    (by decide) selected_cut_45382

theorem unmarked_context_10_22960_1257792 : frontier 11 ⟨1257792, by decide⟩
    (prefixCache 10 22960) (prefixPartial 10 22960) = false := by
  decide +kernel

theorem node_context_10_22960_1257792 : EJMOriginalGlobalDAGData.nodes 11 ⟨1257792, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1257656, by decide⟩,⟨1257791, by decide⟩,⟨982326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22960_1257792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22960 ⟨1257792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22960
    ⟨1257792, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1257656, by decide⟩,⟨1257791, by decide⟩,⟨982326, by decide⟩]) unmarked_context_10_22960_1257792 node_context_10_22960_1257792
  intro a
  fin_cases a
  · exact context_11_91840_434745
  · exact context_11_91841_1257656
  · exact context_11_91842_1257791
  · exact context_11_91843_982326

theorem selected_cut_45383 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 367376) = some ⟨12, 1, 0, 1255011, 367376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367376_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367376 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 367376 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 367376, 1, 65536⟩
    (by decide) selected_cut_45383

theorem selected_cut_45384 : selected 9 ⟨1257852, by decide⟩
    (prefixPartial 12 367377) = some ⟨12, 2, 0, 1257852, 367377, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_367377_1257852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367377 ⟨1257852, by decide⟩ :=
  accepted_of_selected 12 367377 ⟨1257852, by decide⟩ ⟨12, 2, 0, 1257852, 367377, 3401, 65536⟩
    (by decide) selected_cut_45384

theorem selected_cut_45385 : selected 9 ⟨1257908, by decide⟩
    (prefixPartial 12 367378) = some ⟨12, 2, 0, 1257908, 367378, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_367378_1257908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367378 ⟨1257908, by decide⟩ :=
  accepted_of_selected 12 367378 ⟨1257908, by decide⟩ ⟨12, 2, 0, 1257908, 367378, 3293, 65536⟩
    (by decide) selected_cut_45385

theorem selected_cut_45386 : selected 9 ⟨1257971, by decide⟩
    (prefixPartial 12 367379) = some ⟨12, 2, 0, 1257971, 367379, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_367379_1257971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367379 ⟨1257971, by decide⟩ :=
  accepted_of_selected 12 367379 ⟨1257971, by decide⟩ ⟨12, 2, 0, 1257971, 367379, 3333, 65536⟩
    (by decide) selected_cut_45386

theorem unmarked_context_11_91844_1257972 : frontier 10 ⟨1257972, by decide⟩
    (prefixCache 11 91844) (prefixPartial 11 91844) = false := by
  decide +kernel

theorem node_context_11_91844_1257972 : EJMOriginalGlobalDAGData.nodes 10 ⟨1257972, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1257852, by decide⟩,⟨1257908, by decide⟩,⟨1257971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91844_1257972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91844 ⟨1257972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91844
    ⟨1257972, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1257852, by decide⟩,⟨1257908, by decide⟩,⟨1257971, by decide⟩]) unmarked_context_11_91844_1257972 node_context_11_91844_1257972
  intro a
  fin_cases a
  · exact context_12_367376_1255011
  · exact context_12_367377_1257852
  · exact context_12_367378_1257908
  · exact context_12_367379_1257971

theorem selected_cut_45387 : selected 9 ⟨1258024, by decide⟩
    (prefixPartial 12 367380) = some ⟨12, 2, 0, 1258024, 367380, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_367380_1258024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367380 ⟨1258024, by decide⟩ :=
  accepted_of_selected 12 367380 ⟨1258024, by decide⟩ ⟨12, 2, 0, 1258024, 367380, 2733, 65536⟩
    (by decide) selected_cut_45387

theorem selected_cut_45388 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 367381) = some ⟨12, 1, 0, 1118965, 367381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367381_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367381 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 367381 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 367381, 1, 65536⟩
    (by decide) selected_cut_45388

theorem selected_cut_45389 : selected 9 ⟨1258078, by decide⟩
    (prefixPartial 12 367382) = some ⟨12, 2, 0, 1258078, 367382, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_367382_1258078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367382 ⟨1258078, by decide⟩ :=
  accepted_of_selected 12 367382 ⟨1258078, by decide⟩ ⟨12, 2, 0, 1258078, 367382, 2913, 65536⟩
    (by decide) selected_cut_45389

theorem selected_cut_45390 : selected 9 ⟨1258134, by decide⟩
    (prefixPartial 12 367383) = some ⟨12, 2, 0, 1258134, 367383, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_367383_1258134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367383 ⟨1258134, by decide⟩ :=
  accepted_of_selected 12 367383 ⟨1258134, by decide⟩ ⟨12, 2, 0, 1258134, 367383, 3033, 65536⟩
    (by decide) selected_cut_45390

theorem unmarked_context_11_91845_1258135 : frontier 10 ⟨1258135, by decide⟩
    (prefixCache 11 91845) (prefixPartial 11 91845) = false := by
  decide +kernel

theorem node_context_11_91845_1258135 : EJMOriginalGlobalDAGData.nodes 10 ⟨1258135, by decide⟩ =
    .split (coordinate 11) (![⟨1258024, by decide⟩,⟨1118965, by decide⟩,⟨1258078, by decide⟩,⟨1258134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91845_1258135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91845 ⟨1258135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91845
    ⟨1258135, by decide⟩ (by decide) (![⟨1258024, by decide⟩,⟨1118965, by decide⟩,⟨1258078, by decide⟩,⟨1258134, by decide⟩]) unmarked_context_11_91845_1258135 node_context_11_91845_1258135
  intro a
  fin_cases a
  · exact context_12_367380_1258024
  · exact context_12_367381_1118965
  · exact context_12_367382_1258078
  · exact context_12_367383_1258134

theorem selected_cut_45391 : selected 9 ⟨1258199, by decide⟩
    (prefixPartial 12 367384) = some ⟨12, 2, 0, 1258199, 367384, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_367384_1258199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367384 ⟨1258199, by decide⟩ :=
  accepted_of_selected 12 367384 ⟨1258199, by decide⟩ ⟨12, 2, 0, 1258199, 367384, 2737, 65536⟩
    (by decide) selected_cut_45391

theorem selected_cut_45392 : selected 9 ⟨1258251, by decide⟩
    (prefixPartial 12 367385) = some ⟨12, 2, 0, 1258251, 367385, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_367385_1258251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367385 ⟨1258251, by decide⟩ :=
  accepted_of_selected 12 367385 ⟨1258251, by decide⟩ ⟨12, 2, 0, 1258251, 367385, 2881, 65536⟩
    (by decide) selected_cut_45392

theorem selected_cut_45393 : selected 9 ⟨1258292, by decide⟩
    (prefixPartial 12 367386) = some ⟨12, 2, 0, 1258292, 367386, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_367386_1258292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367386 ⟨1258292, by decide⟩ :=
  accepted_of_selected 12 367386 ⟨1258292, by decide⟩ ⟨12, 2, 0, 1258292, 367386, 2421, 65536⟩
    (by decide) selected_cut_45393

theorem selected_cut_45394 : selected 9 ⟨1258353, by decide⟩
    (prefixPartial 12 367387) = some ⟨12, 2, 0, 1258353, 367387, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_367387_1258353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367387 ⟨1258353, by decide⟩ :=
  accepted_of_selected 12 367387 ⟨1258353, by decide⟩ ⟨12, 2, 0, 1258353, 367387, 2961, 65536⟩
    (by decide) selected_cut_45394

theorem unmarked_context_11_91846_1258354 : frontier 10 ⟨1258354, by decide⟩
    (prefixCache 11 91846) (prefixPartial 11 91846) = false := by
  decide +kernel

theorem node_context_11_91846_1258354 : EJMOriginalGlobalDAGData.nodes 10 ⟨1258354, by decide⟩ =
    .split (coordinate 11) (![⟨1258199, by decide⟩,⟨1258251, by decide⟩,⟨1258292, by decide⟩,⟨1258353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91846_1258354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91846 ⟨1258354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91846
    ⟨1258354, by decide⟩ (by decide) (![⟨1258199, by decide⟩,⟨1258251, by decide⟩,⟨1258292, by decide⟩,⟨1258353, by decide⟩]) unmarked_context_11_91846_1258354 node_context_11_91846_1258354
  intro a
  fin_cases a
  · exact context_12_367384_1258199
  · exact context_12_367385_1258251
  · exact context_12_367386_1258292
  · exact context_12_367387_1258353

theorem selected_cut_45395 : selected 9 ⟨1258410, by decide⟩
    (prefixPartial 12 367388) = some ⟨12, 2, 0, 1258410, 367388, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_367388_1258410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367388 ⟨1258410, by decide⟩ :=
  accepted_of_selected 12 367388 ⟨1258410, by decide⟩ ⟨12, 2, 0, 1258410, 367388, 2545, 65536⟩
    (by decide) selected_cut_45395

theorem selected_cut_45396 : selected 9 ⟨1258462, by decide⟩
    (prefixPartial 12 367389) = some ⟨12, 2, 0, 1258462, 367389, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_367389_1258462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367389 ⟨1258462, by decide⟩ :=
  accepted_of_selected 12 367389 ⟨1258462, by decide⟩ ⟨12, 2, 0, 1258462, 367389, 2817, 65536⟩
    (by decide) selected_cut_45396

theorem selected_cut_45397 : selected 9 ⟨1258507, by decide⟩
    (prefixPartial 12 367390) = some ⟨12, 2, 0, 1258507, 367390, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_367390_1258507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367390 ⟨1258507, by decide⟩ :=
  accepted_of_selected 12 367390 ⟨1258507, by decide⟩ ⟨12, 2, 0, 1258507, 367390, 2725, 65536⟩
    (by decide) selected_cut_45397

theorem selected_cut_45398 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 367391) = some ⟨12, 1, 0, 903806, 367391, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367391_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367391 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 367391 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 367391, 1, 65536⟩
    (by decide) selected_cut_45398

theorem unmarked_context_11_91847_1258508 : frontier 10 ⟨1258508, by decide⟩
    (prefixCache 11 91847) (prefixPartial 11 91847) = false := by
  decide +kernel

theorem node_context_11_91847_1258508 : EJMOriginalGlobalDAGData.nodes 10 ⟨1258508, by decide⟩ =
    .split (coordinate 11) (![⟨1258410, by decide⟩,⟨1258462, by decide⟩,⟨1258507, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91847_1258508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91847 ⟨1258508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91847
    ⟨1258508, by decide⟩ (by decide) (![⟨1258410, by decide⟩,⟨1258462, by decide⟩,⟨1258507, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_91847_1258508 node_context_11_91847_1258508
  intro a
  fin_cases a
  · exact context_12_367388_1258410
  · exact context_12_367389_1258462
  · exact context_12_367390_1258507
  · exact context_12_367391_903806

theorem unmarked_context_10_22961_1258509 : frontier 11 ⟨1258509, by decide⟩
    (prefixCache 10 22961) (prefixPartial 10 22961) = false := by
  decide +kernel

theorem node_context_10_22961_1258509 : EJMOriginalGlobalDAGData.nodes 11 ⟨1258509, by decide⟩ =
    .split (coordinate 10) (![⟨1257972, by decide⟩,⟨1258135, by decide⟩,⟨1258354, by decide⟩,⟨1258508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22961_1258509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22961 ⟨1258509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22961
    ⟨1258509, by decide⟩ (by decide) (![⟨1257972, by decide⟩,⟨1258135, by decide⟩,⟨1258354, by decide⟩,⟨1258508, by decide⟩]) unmarked_context_10_22961_1258509 node_context_10_22961_1258509
  intro a
  fin_cases a
  · exact context_11_91844_1257972
  · exact context_11_91845_1258135
  · exact context_11_91846_1258354
  · exact context_11_91847_1258508

theorem selected_cut_45399 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 367392) = some ⟨12, 1, 0, 435790, 367392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367392_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367392 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 367392 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 367392, 1, 65536⟩
    (by decide) selected_cut_45399

theorem selected_cut_45400 : selected 9 ⟨1258564, by decide⟩
    (prefixPartial 12 367393) = some ⟨12, 2, 0, 1258564, 367393, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_367393_1258564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367393 ⟨1258564, by decide⟩ :=
  accepted_of_selected 12 367393 ⟨1258564, by decide⟩ ⟨12, 2, 0, 1258564, 367393, 2481, 65536⟩
    (by decide) selected_cut_45400

theorem selected_cut_45401 : selected 9 ⟨1258611, by decide⟩
    (prefixPartial 12 367394) = some ⟨12, 2, 0, 1258611, 367394, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_367394_1258611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367394 ⟨1258611, by decide⟩ :=
  accepted_of_selected 12 367394 ⟨1258611, by decide⟩ ⟨12, 2, 0, 1258611, 367394, 2225, 65536⟩
    (by decide) selected_cut_45401

theorem selected_cut_45402 : selected 9 ⟨1258652, by decide⟩
    (prefixPartial 12 367395) = some ⟨12, 2, 0, 1258652, 367395, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_367395_1258652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367395 ⟨1258652, by decide⟩ :=
  accepted_of_selected 12 367395 ⟨1258652, by decide⟩ ⟨12, 2, 0, 1258652, 367395, 2109, 65536⟩
    (by decide) selected_cut_45402

theorem unmarked_context_11_91848_1258653 : frontier 10 ⟨1258653, by decide⟩
    (prefixCache 11 91848) (prefixPartial 11 91848) = false := by
  decide +kernel

theorem node_context_11_91848_1258653 : EJMOriginalGlobalDAGData.nodes 10 ⟨1258653, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1258564, by decide⟩,⟨1258611, by decide⟩,⟨1258652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91848_1258653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91848 ⟨1258653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91848
    ⟨1258653, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1258564, by decide⟩,⟨1258611, by decide⟩,⟨1258652, by decide⟩]) unmarked_context_11_91848_1258653 node_context_11_91848_1258653
  intro a
  fin_cases a
  · exact context_12_367392_435790
  · exact context_12_367393_1258564
  · exact context_12_367394_1258611
  · exact context_12_367395_1258652

theorem selected_cut_45403 : selected 9 ⟨1258710, by decide⟩
    (prefixPartial 12 367396) = some ⟨12, 2, 0, 1258710, 367396, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_367396_1258710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367396 ⟨1258710, by decide⟩ :=
  accepted_of_selected 12 367396 ⟨1258710, by decide⟩ ⟨12, 2, 0, 1258710, 367396, 2409, 65536⟩
    (by decide) selected_cut_45403

theorem selected_cut_45404 : selected 9 ⟨1258793, by decide⟩
    (prefixPartial 12 367397) = some ⟨12, 2, 0, 1258793, 367397, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_367397_1258793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367397 ⟨1258793, by decide⟩ :=
  accepted_of_selected 12 367397 ⟨1258793, by decide⟩ ⟨12, 2, 0, 1258793, 367397, 3057, 65536⟩
    (by decide) selected_cut_45404

theorem selected_cut_45405 : selected 9 ⟨1258834, by decide⟩
    (prefixPartial 12 367398) = some ⟨12, 2, 0, 1258834, 367398, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_367398_1258834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367398 ⟨1258834, by decide⟩ :=
  accepted_of_selected 12 367398 ⟨1258834, by decide⟩ ⟨12, 2, 0, 1258834, 367398, 2161, 65536⟩
    (by decide) selected_cut_45405

theorem selected_cut_45406 : selected 9 ⟨1258879, by decide⟩
    (prefixPartial 12 367399) = some ⟨12, 2, 0, 1258879, 367399, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_367399_1258879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367399 ⟨1258879, by decide⟩ :=
  accepted_of_selected 12 367399 ⟨1258879, by decide⟩ ⟨12, 2, 0, 1258879, 367399, 2017, 65536⟩
    (by decide) selected_cut_45406

theorem unmarked_context_11_91849_1258880 : frontier 10 ⟨1258880, by decide⟩
    (prefixCache 11 91849) (prefixPartial 11 91849) = false := by
  decide +kernel

theorem node_context_11_91849_1258880 : EJMOriginalGlobalDAGData.nodes 10 ⟨1258880, by decide⟩ =
    .split (coordinate 11) (![⟨1258710, by decide⟩,⟨1258793, by decide⟩,⟨1258834, by decide⟩,⟨1258879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91849_1258880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91849 ⟨1258880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91849
    ⟨1258880, by decide⟩ (by decide) (![⟨1258710, by decide⟩,⟨1258793, by decide⟩,⟨1258834, by decide⟩,⟨1258879, by decide⟩]) unmarked_context_11_91849_1258880 node_context_11_91849_1258880
  intro a
  fin_cases a
  · exact context_12_367396_1258710
  · exact context_12_367397_1258793
  · exact context_12_367398_1258834
  · exact context_12_367399_1258879

theorem selected_cut_45407 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 91850) = some ⟨11, 1, 0, 900587, 91850, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91850_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91850 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 91850 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 91850, 1, 262144⟩
    (by decide) selected_cut_45407

theorem selected_cut_45408 : selected 9 ⟨1258929, by decide⟩
    (prefixPartial 12 367404) = some ⟨12, 2, 0, 1258929, 367404, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_367404_1258929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367404 ⟨1258929, by decide⟩ :=
  accepted_of_selected 12 367404 ⟨1258929, by decide⟩ ⟨12, 2, 0, 1258929, 367404, 1965, 65536⟩
    (by decide) selected_cut_45408

theorem selected_cut_45409 : selected 9 ⟨1258961, by decide⟩
    (prefixPartial 12 367405) = some ⟨12, 2, 0, 1258961, 367405, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_367405_1258961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367405 ⟨1258961, by decide⟩ :=
  accepted_of_selected 12 367405 ⟨1258961, by decide⟩ ⟨12, 2, 0, 1258961, 367405, 1993, 65536⟩
    (by decide) selected_cut_45409

theorem selected_cut_45410 : selected 9 ⟨1258998, by decide⟩
    (prefixPartial 12 367406) = some ⟨12, 2, 0, 1258998, 367406, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_367406_1258998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367406 ⟨1258998, by decide⟩ :=
  accepted_of_selected 12 367406 ⟨1258998, by decide⟩ ⟨12, 2, 0, 1258998, 367406, 1861, 65536⟩
    (by decide) selected_cut_45410

theorem selected_cut_45411 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 367407) = some ⟨12, 1, 0, 903806, 367407, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367407_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367407 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 367407 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 367407, 1, 65536⟩
    (by decide) selected_cut_45411

theorem unmarked_context_11_91851_1258999 : frontier 10 ⟨1258999, by decide⟩
    (prefixCache 11 91851) (prefixPartial 11 91851) = false := by
  decide +kernel

theorem node_context_11_91851_1258999 : EJMOriginalGlobalDAGData.nodes 10 ⟨1258999, by decide⟩ =
    .split (coordinate 11) (![⟨1258929, by decide⟩,⟨1258961, by decide⟩,⟨1258998, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91851_1258999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91851 ⟨1258999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91851
    ⟨1258999, by decide⟩ (by decide) (![⟨1258929, by decide⟩,⟨1258961, by decide⟩,⟨1258998, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_91851_1258999 node_context_11_91851_1258999
  intro a
  fin_cases a
  · exact context_12_367404_1258929
  · exact context_12_367405_1258961
  · exact context_12_367406_1258998
  · exact context_12_367407_903806

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
